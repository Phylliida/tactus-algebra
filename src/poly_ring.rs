///  The polynomial ring law kit: commutativity, distributivity,
///  associativity, and full congruence for pmul (cad-01).
///
///  divmod deliberately avoided these; gcd/Bézout cannot — the Euclid
///  invariant g ≡ v·a + (u − v·q)·b needs distributivity over psub,
///  associativity, and congruence in both arguments.
///
///  Proof architecture: everything reduces to structural induction on the
///  first pmul argument plus pointwise (coeff-characterization) lemmas.
///  Commutativity rides on two structural minis — pmul-by-singleton and
///  pmul-by-shiftk on the right — via the cons-as-padd decomposition of the
///  second argument; right-distributivity and left-congruence are then comm
///  conjugates; associativity is a first-argument induction consuming
///  right-distributivity and the scale/shift exchange minis.
use vstd::prelude::*;
use crate::traits::equivalence::Equivalence;
use crate::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use crate::traits::additive_group::AdditiveGroup;
use crate::traits::ring::Ring;
use crate::lemmas::*;
use crate::poly::*;
use crate::poly_mul::*;

verus! {

//  ============================================================
//   Pointwise helpers
//  ============================================================

///  Both eqv-zero polynomials are peqv.
pub proof fn lemma_zpoly_to_peqv<T: Ring>(x: Seq<T>, y: Seq<T>)
    requires zpoly(x), zpoly(y),
    ensures peqv(x, y),
{
    assert forall|i: int| (#[trigger] coeff(x, i)).eqv(coeff(y, i)) by {
        assert(coeff(x, i).eqv(T::zero()));
        assert(coeff(y, i).eqv(T::zero()));
        lemma_eqv_flip(coeff(y, i), T::zero());
        T::axiom_eqv_transitive(coeff(x, i), T::zero(), coeff(y, i));
    }
}

///  padd preserves eqv-zero-ness.
pub proof fn lemma_zpoly_padd<T: Ring>(x: Seq<T>, y: Seq<T>)
    requires zpoly(x), zpoly(y),
    ensures zpoly(padd(x, y)),
{
    assert forall|i: int| (#[trigger] coeff(padd(x, y), i)).eqv(T::zero()) by {
        lemma_coeff_padd(x, y, i);
        assert(coeff(x, i).eqv(T::zero()));
        assert(coeff(y, i).eqv(T::zero()));
        lemma_add_cong_both(coeff(x, i), T::zero(), coeff(y, i), T::zero());
        lemma_zero_add_zero::<T>();
        T::axiom_eqv_transitive(
            coeff(padd(x, y), i),
            coeff(x, i).add(coeff(y, i)),
            T::zero().add(T::zero()),
        );
        T::axiom_eqv_transitive(
            coeff(padd(x, y), i),
            T::zero().add(T::zero()),
            T::zero(),
        );
    }
}

///  pneg respects peqv.
pub proof fn lemma_pneg_cong<T: Ring>(x: Seq<T>, y: Seq<T>)
    requires peqv(x, y),
    ensures peqv(pneg(x), pneg(y)),
{
    assert forall|i: int| (#[trigger] coeff(pneg(x), i)).eqv(coeff(pneg(y), i)) by {
        lemma_coeff_pneg(x, i);
        lemma_coeff_pneg(y, i);
        assert(coeff(x, i).eqv(coeff(y, i)));
        T::axiom_neg_congruence(coeff(x, i), coeff(y, i));
        T::axiom_eqv_transitive(coeff(pneg(x), i), coeff(x, i).neg(), coeff(y, i).neg());
        lemma_eqv_flip(coeff(pneg(y), i), coeff(y, i).neg());
        T::axiom_eqv_transitive(coeff(pneg(x), i), coeff(y, i).neg(), coeff(pneg(y), i));
    }
}

///  scale respects peqv in the polynomial argument.
pub proof fn lemma_scale_cong_poly<T: Ring>(c: T, x: Seq<T>, y: Seq<T>)
    requires peqv(x, y),
    ensures peqv(scale(c, x), scale(c, y)),
{
    assert forall|i: int| (#[trigger] coeff(scale(c, x), i)).eqv(coeff(scale(c, y), i)) by {
        lemma_coeff_scale(c, x, i);
        lemma_coeff_scale(c, y, i);
        assert(coeff(x, i).eqv(coeff(y, i)));
        lemma_mul_cong_right(c, coeff(x, i), coeff(y, i));
        T::axiom_eqv_transitive(coeff(scale(c, x), i), c.mul(coeff(x, i)), c.mul(coeff(y, i)));
        lemma_eqv_flip(coeff(scale(c, y), i), c.mul(coeff(y, i)));
        T::axiom_eqv_transitive(coeff(scale(c, x), i), c.mul(coeff(y, i)), coeff(scale(c, y), i));
    }
}

///  scale respects eqv in the scalar argument.
pub proof fn lemma_scale_cong_scalar<T: Ring>(c: T, d: T, x: Seq<T>)
    requires c.eqv(d),
    ensures peqv(scale(c, x), scale(d, x)),
{
    assert forall|i: int| (#[trigger] coeff(scale(c, x), i)).eqv(coeff(scale(d, x), i)) by {
        lemma_coeff_scale(c, x, i);
        lemma_coeff_scale(d, x, i);
        T::axiom_mul_congruence_left(c, d, coeff(x, i));
        T::axiom_eqv_transitive(coeff(scale(c, x), i), c.mul(coeff(x, i)), d.mul(coeff(x, i)));
        lemma_eqv_flip(coeff(scale(d, x), i), d.mul(coeff(x, i)));
        T::axiom_eqv_transitive(coeff(scale(c, x), i), d.mul(coeff(x, i)), coeff(scale(d, x), i));
    }
}

///  scale distributes over padd.
pub proof fn lemma_scale_padd<T: Ring>(c: T, x: Seq<T>, y: Seq<T>)
    ensures peqv(scale(c, padd(x, y)), padd(scale(c, x), scale(c, y))),
{
    assert forall|i: int|
        (#[trigger] coeff(scale(c, padd(x, y)), i)).eqv(coeff(padd(scale(c, x), scale(c, y)), i))
    by {
        let xi = coeff(x, i);
        let yi = coeff(y, i);
        lemma_coeff_scale(c, padd(x, y), i);
        lemma_coeff_padd(x, y, i);
        lemma_mul_cong_right(c, coeff(padd(x, y), i), xi.add(yi));
        T::axiom_eqv_transitive(
            coeff(scale(c, padd(x, y)), i),
            c.mul(coeff(padd(x, y), i)),
            c.mul(xi.add(yi)),
        );
        T::axiom_mul_distributes_left(c, xi, yi);
        T::axiom_eqv_transitive(
            coeff(scale(c, padd(x, y)), i),
            c.mul(xi.add(yi)),
            c.mul(xi).add(c.mul(yi)),
        );
        //  fold the right side
        lemma_coeff_scale(c, x, i);
        lemma_coeff_scale(c, y, i);
        lemma_eqv_flip(coeff(scale(c, x), i), c.mul(xi));
        lemma_eqv_flip(coeff(scale(c, y), i), c.mul(yi));
        lemma_add_cong_both(c.mul(xi), coeff(scale(c, x), i), c.mul(yi), coeff(scale(c, y), i));
        T::axiom_eqv_transitive(
            coeff(scale(c, padd(x, y)), i),
            c.mul(xi).add(c.mul(yi)),
            coeff(scale(c, x), i).add(coeff(scale(c, y), i)),
        );
        lemma_coeff_padd(scale(c, x), scale(c, y), i);
        lemma_eqv_flip(
            coeff(padd(scale(c, x), scale(c, y)), i),
            coeff(scale(c, x), i).add(coeff(scale(c, y), i)),
        );
        T::axiom_eqv_transitive(
            coeff(scale(c, padd(x, y)), i),
            coeff(scale(c, x), i).add(coeff(scale(c, y), i)),
            coeff(padd(scale(c, x), scale(c, y)), i),
        );
    }
}

///  Nested scaling composes: c·(d·x) ≡ (c·d)·x.
pub proof fn lemma_scale_scale<T: Ring>(c: T, d: T, x: Seq<T>)
    ensures peqv(scale(c, scale(d, x)), scale(c.mul(d), x)),
{
    assert forall|i: int|
        (#[trigger] coeff(scale(c, scale(d, x)), i)).eqv(coeff(scale(c.mul(d), x), i))
    by {
        let xi = coeff(x, i);
        lemma_coeff_scale(c, scale(d, x), i);
        lemma_coeff_scale(d, x, i);
        lemma_mul_cong_right(c, coeff(scale(d, x), i), d.mul(xi));
        T::axiom_eqv_transitive(
            coeff(scale(c, scale(d, x)), i),
            c.mul(coeff(scale(d, x), i)),
            c.mul(d.mul(xi)),
        );
        T::axiom_mul_associative(c, d, xi);
        lemma_eqv_flip(c.mul(d).mul(xi), c.mul(d.mul(xi)));
        T::axiom_eqv_transitive(
            coeff(scale(c, scale(d, x)), i),
            c.mul(d.mul(xi)),
            c.mul(d).mul(xi),
        );
        lemma_coeff_scale(c.mul(d), x, i);
        lemma_eqv_flip(coeff(scale(c.mul(d), x), i), c.mul(d).mul(xi));
        T::axiom_eqv_transitive(
            coeff(scale(c, scale(d, x)), i),
            c.mul(d).mul(xi),
            coeff(scale(c.mul(d), x), i),
        );
    }
}

///  Scaling by one is the identity.
pub proof fn lemma_scale_one<T: Ring>(x: Seq<T>)
    ensures peqv(scale(T::one(), x), x),
{
    assert forall|i: int| (#[trigger] coeff(scale(T::one(), x), i)).eqv(coeff(x, i)) by {
        lemma_coeff_scale(T::one(), x, i);
        lemma_mul_one_left(coeff(x, i));
        T::axiom_eqv_transitive(
            coeff(scale(T::one(), x), i),
            T::one().mul(coeff(x, i)),
            coeff(x, i),
        );
    }
}

///  scale commutes with pneg.
pub proof fn lemma_scale_pneg<T: Ring>(c: T, x: Seq<T>)
    ensures peqv(scale(c, pneg(x)), pneg(scale(c, x))),
{
    assert forall|i: int|
        (#[trigger] coeff(scale(c, pneg(x)), i)).eqv(coeff(pneg(scale(c, x)), i))
    by {
        let xi = coeff(x, i);
        lemma_coeff_scale(c, pneg(x), i);
        lemma_coeff_pneg(x, i);
        lemma_mul_cong_right(c, coeff(pneg(x), i), xi.neg());
        T::axiom_eqv_transitive(
            coeff(scale(c, pneg(x)), i),
            c.mul(coeff(pneg(x), i)),
            c.mul(xi.neg()),
        );
        lemma_mul_neg_right(c, xi);
        T::axiom_eqv_transitive(
            coeff(scale(c, pneg(x)), i),
            c.mul(xi.neg()),
            c.mul(xi).neg(),
        );
        lemma_coeff_pneg(scale(c, x), i);
        lemma_coeff_scale(c, x, i);
        T::axiom_neg_congruence(coeff(scale(c, x), i), c.mul(xi));
        T::axiom_eqv_transitive(
            coeff(pneg(scale(c, x)), i),
            coeff(scale(c, x), i).neg(),
            c.mul(xi).neg(),
        );
        lemma_eqv_flip(coeff(pneg(scale(c, x)), i), c.mul(xi).neg());
        T::axiom_eqv_transitive(
            coeff(scale(c, pneg(x)), i),
            c.mul(xi).neg(),
            coeff(pneg(scale(c, x)), i),
        );
    }
}

///  scale commutes with shiftk.
pub proof fn lemma_scale_shiftk<T: Ring>(c: T, x: Seq<T>, k: nat)
    ensures peqv(scale(c, shiftk(x, k)), shiftk(scale(c, x), k)),
{
    assert forall|i: int|
        (#[trigger] coeff(scale(c, shiftk(x, k)), i)).eqv(coeff(shiftk(scale(c, x), k), i))
    by {
        lemma_coeff_scale(c, shiftk(x, k), i);
        lemma_coeff_shiftk(x, k, i);
        lemma_coeff_shiftk(scale(c, x), k, i);
        if i < k as int {
            //  lhs ≡ c·(shiftk entry ≡ 0) ≡ c·0 ≡ 0; rhs ≡ 0.
            lemma_mul_cong_right(c, coeff(shiftk(x, k), i), T::zero());
            T::axiom_mul_zero_right(c);
            T::axiom_eqv_transitive(
                coeff(scale(c, shiftk(x, k)), i),
                c.mul(coeff(shiftk(x, k), i)),
                c.mul(T::zero()),
            );
            T::axiom_eqv_transitive(
                coeff(scale(c, shiftk(x, k)), i),
                c.mul(T::zero()),
                T::zero(),
            );
            lemma_eqv_flip(coeff(shiftk(scale(c, x), k), i), T::zero());
            T::axiom_eqv_transitive(
                coeff(scale(c, shiftk(x, k)), i),
                T::zero(),
                coeff(shiftk(scale(c, x), k), i),
            );
        } else {
            let j = i - k as int;
            lemma_mul_cong_right(c, coeff(shiftk(x, k), i), coeff(x, j));
            T::axiom_eqv_transitive(
                coeff(scale(c, shiftk(x, k)), i),
                c.mul(coeff(shiftk(x, k), i)),
                c.mul(coeff(x, j)),
            );
            lemma_coeff_scale(c, x, j);
            lemma_eqv_flip(coeff(scale(c, x), j), c.mul(coeff(x, j)));
            T::axiom_eqv_transitive(
                coeff(scale(c, shiftk(x, k)), i),
                c.mul(coeff(x, j)),
                coeff(scale(c, x), j),
            );
            lemma_eqv_flip(coeff(shiftk(scale(c, x), k), i), coeff(scale(c, x), j));
            T::axiom_eqv_transitive(
                coeff(scale(c, shiftk(x, k)), i),
                coeff(scale(c, x), j),
                coeff(shiftk(scale(c, x), k), i),
            );
        }
    }
}

///  padd commutes with pneg.
pub proof fn lemma_padd_pneg<T: Ring>(x: Seq<T>, y: Seq<T>)
    ensures peqv(padd(pneg(x), pneg(y)), pneg(padd(x, y))),
{
    assert forall|i: int|
        (#[trigger] coeff(padd(pneg(x), pneg(y)), i)).eqv(coeff(pneg(padd(x, y)), i))
    by {
        let xi = coeff(x, i);
        let yi = coeff(y, i);
        lemma_coeff_padd(pneg(x), pneg(y), i);
        lemma_coeff_pneg(x, i);
        lemma_coeff_pneg(y, i);
        lemma_add_cong_both(coeff(pneg(x), i), xi.neg(), coeff(pneg(y), i), yi.neg());
        T::axiom_eqv_transitive(
            coeff(padd(pneg(x), pneg(y)), i),
            coeff(pneg(x), i).add(coeff(pneg(y), i)),
            xi.neg().add(yi.neg()),
        );
        lemma_neg_add(xi, yi);
        T::axiom_eqv_transitive(
            coeff(padd(pneg(x), pneg(y)), i),
            xi.neg().add(yi.neg()),
            xi.add(yi).neg(),
        );
        lemma_coeff_pneg(padd(x, y), i);
        lemma_coeff_padd(x, y, i);
        T::axiom_neg_congruence(coeff(padd(x, y), i), xi.add(yi));
        T::axiom_eqv_transitive(
            coeff(pneg(padd(x, y)), i),
            coeff(padd(x, y), i).neg(),
            xi.add(yi).neg(),
        );
        lemma_eqv_flip(coeff(pneg(padd(x, y)), i), xi.add(yi).neg());
        T::axiom_eqv_transitive(
            coeff(padd(pneg(x), pneg(y)), i),
            xi.add(yi).neg(),
            coeff(pneg(padd(x, y)), i),
        );
    }
}

///  Four-term regrouping at the polynomial level.
pub proof fn lemma_padd_regroup<T: Ring>(p: Seq<T>, q: Seq<T>, r: Seq<T>, s: Seq<T>)
    ensures peqv(padd(padd(p, q), padd(r, s)), padd(padd(p, r), padd(q, s))),
{
    assert forall|i: int|
        (#[trigger] coeff(padd(padd(p, q), padd(r, s)), i))
            .eqv(coeff(padd(padd(p, r), padd(q, s)), i))
    by {
        let pi = coeff(p, i);
        let qi = coeff(q, i);
        let ri = coeff(r, i);
        let si = coeff(s, i);
        //  open the left side down to T
        lemma_coeff_padd(padd(p, q), padd(r, s), i);
        lemma_coeff_padd(p, q, i);
        lemma_coeff_padd(r, s, i);
        lemma_add_cong_both(
            coeff(padd(p, q), i), pi.add(qi),
            coeff(padd(r, s), i), ri.add(si),
        );
        T::axiom_eqv_transitive(
            coeff(padd(padd(p, q), padd(r, s)), i),
            coeff(padd(p, q), i).add(coeff(padd(r, s), i)),
            pi.add(qi).add(ri.add(si)),
        );
        //  T-level regroup
        lemma_add_regroup(pi, qi, ri, si);
        T::axiom_eqv_transitive(
            coeff(padd(padd(p, q), padd(r, s)), i),
            pi.add(qi).add(ri.add(si)),
            pi.add(ri).add(qi.add(si)),
        );
        //  fold the right side back up
        lemma_coeff_padd(p, r, i);
        lemma_coeff_padd(q, s, i);
        lemma_eqv_flip(coeff(padd(p, r), i), pi.add(ri));
        lemma_eqv_flip(coeff(padd(q, s), i), qi.add(si));
        lemma_add_cong_both(
            pi.add(ri), coeff(padd(p, r), i),
            qi.add(si), coeff(padd(q, s), i),
        );
        T::axiom_eqv_transitive(
            coeff(padd(padd(p, q), padd(r, s)), i),
            pi.add(ri).add(qi.add(si)),
            coeff(padd(p, r), i).add(coeff(padd(q, s), i)),
        );
        lemma_coeff_padd(padd(p, r), padd(q, s), i);
        lemma_eqv_flip(
            coeff(padd(padd(p, r), padd(q, s)), i),
            coeff(padd(p, r), i).add(coeff(padd(q, s), i)),
        );
        T::axiom_eqv_transitive(
            coeff(padd(padd(p, q), padd(r, s)), i),
            coeff(padd(p, r), i).add(coeff(padd(q, s), i)),
            coeff(padd(padd(p, r), padd(q, s)), i),
        );
    }
}

///  Decompose a nonempty polynomial as head + shifted tail.
pub proof fn lemma_cons_as_padd<T: Ring>(x: Seq<T>)
    requires x.len() > 0,
    ensures peqv(x, padd(seq![x[0]], shiftk(x.skip(1), 1))),
{
    let h = seq![x[0]];
    let st = shiftk(x.skip(1), 1);
    assert forall|i: int| (#[trigger] coeff(x, i)).eqv(coeff(padd(h, st), i)) by {
        lemma_coeff_padd(h, st, i);
        lemma_coeff_shiftk(x.skip(1), 1, i);
        if i == 0 {
            //  x[0] vs x[0] + 0
            //  Explicit seq facts for the Lean gate: the len closes by the
            //  push_len/empty rewrites; the index is the axiom's ret-hyp.
            assert(h.len() == 1);
            vstd::seq::axiom_seq_push_index_same(Seq::<T>::empty(), x[0], 0);
            assert(coeff(h, 0) == x[0]);
            //  coeff(st, 0) is the shiftk head: zero. Verbatim restatement of
            //  the 412 ret-hyp, then the ite arithmetic.
            assert(coeff(st, 0).eqv(if 0 < 1 { T::zero() } else { coeff(x.skip(1), 0 - 1) }));
            assert((if 0 < 1 { T::zero() } else { coeff(x.skip(1), 0 - 1) }) == T::zero());
            lemma_add_cong_right(x[0], coeff(st, 0), T::zero());
            T::axiom_add_zero_right(x[0]);
            T::axiom_eqv_transitive(
                coeff(h, 0).add(coeff(st, 0)),
                x[0].add(T::zero()),
                x[0],
            );
            lemma_eqv_flip(coeff(padd(h, st), 0), coeff(h, 0).add(coeff(st, 0)));
            lemma_eqv_flip(coeff(h, 0).add(coeff(st, 0)), x[0]);
            T::axiom_eqv_transitive(
                x[0],
                coeff(h, 0).add(coeff(st, 0)),
                coeff(padd(h, st), 0),
            );
        } else if 0 < i < x.len() {
            //  x[i] vs 0 + x[i]  (the shifted tail reads x[i] at position i)
            assert(coeff(h, i) == T::zero());
            //  433: restate the 412 ret-hyp verbatim, then the ite arithmetic
            //  (0 < i collapses the guard); the two rewrite into the goal.
            assert(coeff(st, i).eqv(if i < 1 { T::zero() } else { coeff(x.skip(1), i - 1) }));
            assert((if i < 1 { T::zero() } else { coeff(x.skip(1), i - 1) }) == coeff(x.skip(1), i - 1));
            assert(coeff(st, i).eqv(coeff(x.skip(1), i - 1)));
            //  434: the subrange read, with the (i-1)+1 == i bridge explicit.
            vstd::seq::axiom_seq_subrange_len(x, 1, x.len() as int);
            vstd::seq::axiom_seq_subrange_index(x, 1, x.len() as int, i - 1);
            assert((i - 1) + 1 == i);
            assert(coeff(x.skip(1), i - 1) == x[i]);
            T::axiom_eqv_reflexive(T::zero());
            lemma_add_cong_both(coeff(h, i), T::zero(), coeff(st, i), x[i]);
            lemma_add_zero_left(x[i]);
            T::axiom_eqv_transitive(
                coeff(h, i).add(coeff(st, i)),
                T::zero().add(x[i]),
                x[i],
            );
            lemma_eqv_flip(coeff(padd(h, st), i), coeff(h, i).add(coeff(st, i)));
            lemma_eqv_flip(coeff(h, i).add(coeff(st, i)), x[i]);
            T::axiom_eqv_transitive(
                x[i],
                coeff(h, i).add(coeff(st, i)),
                coeff(padd(h, st), i),
            );
        } else {
            //  out of range on both sides: 0 vs 0 + 0
            assert(coeff(x, i) == T::zero());
            assert(coeff(h, i) == T::zero());
            //  454: len st = len x via the subrange_len ret-hyp, so the
            //  guard is arithmetically false; == then refl for the eqv.
            vstd::seq::axiom_seq_subrange_len(x, 1, x.len() as int);
            assert(st.len() == x.len());
            assert(coeff(st, i) == T::zero());
            T::axiom_eqv_reflexive(T::zero());
            assert(coeff(st, i).eqv(T::zero()));
            lemma_add_cong_right(T::zero(), coeff(st, i), T::zero());
            lemma_zero_add_zero::<T>();
            T::axiom_eqv_transitive(
                coeff(h, i).add(coeff(st, i)),
                T::zero().add(T::zero()),
                T::zero(),
            );
            lemma_eqv_flip(coeff(padd(h, st), i), coeff(h, i).add(coeff(st, i)));
            lemma_eqv_flip(coeff(h, i).add(coeff(st, i)), T::zero());
            T::axiom_eqv_transitive(
                T::zero(),
                coeff(h, i).add(coeff(st, i)),
                coeff(padd(h, st), i),
            );
        }
    }
}

///  The inner-shift compose: shiftk(shiftk(p, 1), k) == shiftk(p, k+1).
pub proof fn lemma_shiftk_compose_inner<T: Ring>(p: Seq<T>, k: nat)
    ensures shiftk(shiftk(p, 1), k) == shiftk(p, (k + 1) as nat),
{
    assert(shiftk(shiftk(p, 1), k) =~= shiftk(p, (k + 1) as nat));
}

//  ============================================================
//   Structural minis
//  ============================================================

///  Multiplying by the empty polynomial on the right gives an eqv-zero poly.
pub proof fn lemma_pmul_empty_right<T: Ring>(q: Seq<T>)
    ensures zpoly(pmul(q, Seq::<T>::empty())),
    decreases q.len(),
{
    if q.len() == 0 {
        //  == fact for the Lean gate: zpoly of the product rewrites to
        //  zpoly of the empty seq, which is the ret-hyp below.
        assert(pmul(q, Seq::<T>::empty()) == Seq::<T>::empty());
        lemma_zpoly_empty::<T>();
    } else {
        let t = q.skip(1);
        //  Len fact for the Lean gate: makes the recursion-termination obligation
        //  omega-closable (see lemma_pmul_push).
        vstd::seq::axiom_seq_subrange_len(q, 1, q.len() as int);
        assert(pmul(q, Seq::<T>::empty())
            == padd(scale(q[0], Seq::<T>::empty()), shiftk(pmul(t, Seq::<T>::empty()), 1)));
        assert(scale(q[0], Seq::<T>::empty()) =~= Seq::<T>::empty());
        lemma_zpoly_empty::<T>();
        lemma_pmul_empty_right(t);
        lemma_zpoly_shiftk(pmul(t, Seq::<T>::empty()), 1);
        lemma_zpoly_padd(scale(q[0], Seq::<T>::empty()), shiftk(pmul(t, Seq::<T>::empty()), 1));
    }
}

///  pmul respects peqv in the second argument.
pub proof fn lemma_pmul_cong_right<T: Ring>(p: Seq<T>, q1: Seq<T>, q2: Seq<T>)
    requires peqv(q1, q2),
    ensures peqv(pmul(p, q1), pmul(p, q2)),
    decreases p.len(),
{
    if p.len() == 0 {
        //  == facts for the Lean gate: both products rewrite to empty, so
        //  the peqv postcondition closes against the refl ret-hyp.
        assert(pmul(p, q1) == Seq::<T>::empty());
        assert(pmul(p, q2) == Seq::<T>::empty());
        lemma_peqv_refl(pmul(p, q1));
    } else {
        let t = p.skip(1);
        //  Len fact for the Lean gate: makes the recursion-termination obligation
        //  omega-closable (see lemma_pmul_push).
        vstd::seq::axiom_seq_subrange_len(p, 1, p.len() as int);
        assert(pmul(p, q1) == padd(scale(p[0], q1), shiftk(pmul(t, q1), 1)));
        assert(pmul(p, q2) == padd(scale(p[0], q2), shiftk(pmul(t, q2), 1)));
        lemma_scale_cong_poly(p[0], q1, q2);
        lemma_pmul_cong_right(t, q1, q2);
        lemma_shiftk_cong(pmul(t, q1), pmul(t, q2), 1);
        lemma_padd_cong(
            scale(p[0], q1), scale(p[0], q2),
            shiftk(pmul(t, q1), 1), shiftk(pmul(t, q2), 1),
        );
    }
}

///  Left-distributivity: p * (q + r) ≡ p*q + p*r.
pub proof fn lemma_pmul_padd_right<T: Ring>(p: Seq<T>, q: Seq<T>, r: Seq<T>)
    ensures peqv(pmul(p, padd(q, r)), padd(pmul(p, q), pmul(p, r))),
    decreases p.len(),
{
    if p.len() == 0 {
        //  == facts for the Lean gate: let the =~= goal rewrite to
        //  `padd empty empty =~= empty` (the scale(x, empty) shape).
        assert(pmul(p, q) == Seq::<T>::empty());
        assert(pmul(p, r) == Seq::<T>::empty());
        assert(pmul(p, padd(q, r)) == Seq::<T>::empty());
        assert(padd(pmul(p, q), pmul(p, r)) =~= Seq::<T>::empty());
        lemma_peqv_refl(Seq::<T>::empty());
    } else {
        let h = p[0];
        let t = p.skip(1);
        //  Len fact for the Lean gate: makes the recursion-termination obligation
        //  omega-closable (see lemma_pmul_push).
        vstd::seq::axiom_seq_subrange_len(p, 1, p.len() as int);
        assert(pmul(p, padd(q, r)) == padd(scale(h, padd(q, r)), shiftk(pmul(t, padd(q, r)), 1)));
        //  head: h·(q+r) ≡ h·q + h·r
        lemma_scale_padd(h, q, r);
        //  tail: x·(t*(q+r)) ≡ x·(t*q + t*r) ≡ x·(t*q) + x·(t*r)
        lemma_pmul_padd_right(t, q, r);
        lemma_shiftk_cong(pmul(t, padd(q, r)), padd(pmul(t, q), pmul(t, r)), 1);
        lemma_shiftk_padd(pmul(t, q), pmul(t, r), 1);
        lemma_peqv_trans(
            shiftk(pmul(t, padd(q, r)), 1),
            shiftk(padd(pmul(t, q), pmul(t, r)), 1),
            padd(shiftk(pmul(t, q), 1), shiftk(pmul(t, r), 1)),
        );
        //  combine
        lemma_padd_cong(
            scale(h, padd(q, r)), padd(scale(h, q), scale(h, r)),
            shiftk(pmul(t, padd(q, r)), 1), padd(shiftk(pmul(t, q), 1), shiftk(pmul(t, r), 1)),
        );
        //  regroup (h·q + h·r) + (x(t*q) + x(t*r)) into (h·q + x(t*q)) + (h·r + x(t*r))
        lemma_padd_regroup(scale(h, q), scale(h, r), shiftk(pmul(t, q), 1), shiftk(pmul(t, r), 1));
        //  The first trans leg as single links (the Lean gate matches each
        //  requires against ONE named fact): == unfold bridge (peqv_of_eq),
        //  then the padd_cong fact (558).
        lemma_peqv_of_eq(
            pmul(p, padd(q, r)),
            padd(scale(h, padd(q, r)), shiftk(pmul(t, padd(q, r)), 1)),
        );
        lemma_peqv_trans(
            pmul(p, padd(q, r)),
            padd(scale(h, padd(q, r)), shiftk(pmul(t, padd(q, r)), 1)),
            padd(padd(scale(h, q), scale(h, r)),
                 padd(shiftk(pmul(t, q), 1), shiftk(pmul(t, r), 1))),
        );
        lemma_peqv_trans(
            pmul(p, padd(q, r)),
            padd(padd(scale(h, q), scale(h, r)),
                 padd(shiftk(pmul(t, q), 1), shiftk(pmul(t, r), 1))),
            padd(padd(scale(h, q), shiftk(pmul(t, q), 1)),
                 padd(scale(h, r), shiftk(pmul(t, r), 1))),
        );
        assert(pmul(p, q) == padd(scale(h, q), shiftk(pmul(t, q), 1)));
        assert(pmul(p, r) == padd(scale(h, r), shiftk(pmul(t, r), 1)));
        //  Fold the == forms back into pmul(p, ·) with single links.
        //  (peqv_of_eq takes the pmul-headed == so the precondition is a
        //  form-B unfold, not a Seq-Eq simp target.)
        lemma_peqv_of_eq(pmul(p, q), padd(scale(h, q), shiftk(pmul(t, q), 1)));
        lemma_peqv_of_eq(pmul(p, r), padd(scale(h, r), shiftk(pmul(t, r), 1)));
        lemma_peqv_sym(pmul(p, q), padd(scale(h, q), shiftk(pmul(t, q), 1)));
        lemma_peqv_sym(pmul(p, r), padd(scale(h, r), shiftk(pmul(t, r), 1)));
        lemma_padd_cong(
            padd(scale(h, q), shiftk(pmul(t, q), 1)), pmul(p, q),
            padd(scale(h, r), shiftk(pmul(t, r), 1)), pmul(p, r),
        );
        lemma_peqv_trans(
            pmul(p, padd(q, r)),
            padd(padd(scale(h, q), shiftk(pmul(t, q), 1)),
                 padd(scale(h, r), shiftk(pmul(t, r), 1))),
            padd(pmul(p, q), pmul(p, r)),
        );
    }
}

///  p * (-q) ≡ -(p * q).
pub proof fn lemma_pmul_pneg_right<T: Ring>(p: Seq<T>, q: Seq<T>)
    ensures peqv(pmul(p, pneg(q)), pneg(pmul(p, q))),
    decreases p.len(),
{
    if p.len() == 0 {
        assert(pmul(p, q) == Seq::<T>::empty());
        assert(pmul(p, pneg(q)) == Seq::<T>::empty());
        assert(pneg(pmul(p, q)) =~= Seq::<T>::empty());
        lemma_peqv_refl(Seq::<T>::empty());
    } else {
        let h = p[0];
        let t = p.skip(1);
        //  Len fact for the Lean gate: makes the recursion-termination obligation
        //  omega-closable (see lemma_pmul_push).
        vstd::seq::axiom_seq_subrange_len(p, 1, p.len() as int);
        assert(pmul(p, pneg(q)) == padd(scale(h, pneg(q)), shiftk(pmul(t, pneg(q)), 1)));
        lemma_scale_pneg(h, q);
        lemma_pmul_pneg_right(t, q);
        lemma_shiftk_cong(pmul(t, pneg(q)), pneg(pmul(t, q)), 1);
        lemma_shiftk_pneg_swap(pmul(t, q), 1);
        lemma_peqv_trans(
            shiftk(pmul(t, pneg(q)), 1),
            shiftk(pneg(pmul(t, q)), 1),
            pneg(shiftk(pmul(t, q), 1)),
        );
        lemma_padd_cong(
            scale(h, pneg(q)), pneg(scale(h, q)),
            shiftk(pmul(t, pneg(q)), 1), pneg(shiftk(pmul(t, q), 1)),
        );
        lemma_padd_pneg(scale(h, q), shiftk(pmul(t, q), 1));
        lemma_peqv_trans(
            pmul(p, pneg(q)),
            padd(pneg(scale(h, q)), pneg(shiftk(pmul(t, q), 1))),
            pneg(padd(scale(h, q), shiftk(pmul(t, q), 1))),
        );
        assert(pmul(p, q) == padd(scale(h, q), shiftk(pmul(t, q), 1)));
        //  Fold: pneg of the == form, single links for the Lean gate.
        lemma_peqv_of_eq(pmul(p, q), padd(scale(h, q), shiftk(pmul(t, q), 1)));
        lemma_peqv_sym(pmul(p, q), padd(scale(h, q), shiftk(pmul(t, q), 1)));
        lemma_pneg_cong(padd(scale(h, q), shiftk(pmul(t, q), 1)), pmul(p, q));
        lemma_peqv_trans(
            pmul(p, pneg(q)),
            pneg(padd(scale(h, q), shiftk(pmul(t, q), 1))),
            pneg(pmul(p, q)),
        );
    }
}

///  shiftk commutes with pneg.
pub proof fn lemma_shiftk_pneg_swap<T: Ring>(x: Seq<T>, k: nat)
    ensures peqv(shiftk(pneg(x), k), pneg(shiftk(x, k))),
{
    assert forall|i: int|
        (#[trigger] coeff(shiftk(pneg(x), k), i)).eqv(coeff(pneg(shiftk(x, k)), i))
    by {
        lemma_coeff_shiftk(pneg(x), k, i);
        lemma_coeff_pneg(shiftk(x, k), i);
        lemma_coeff_shiftk(x, k, i);
        if i < k as int {
            //  lhs ≡ 0; rhs ≡ (coeff shiftk).neg ≡ 0.neg ≡ 0
            T::axiom_neg_congruence(coeff(shiftk(x, k), i), T::zero());
            lemma_neg_zero::<T>();
            T::axiom_eqv_transitive(
                coeff(pneg(shiftk(x, k)), i),
                coeff(shiftk(x, k), i).neg(),
                T::zero().neg(),
            );
            T::axiom_eqv_transitive(
                coeff(pneg(shiftk(x, k)), i),
                T::zero().neg(),
                T::zero(),
            );
            lemma_eqv_flip(coeff(pneg(shiftk(x, k)), i), T::zero());
            T::axiom_eqv_transitive(
                coeff(shiftk(pneg(x), k), i),
                T::zero(),
                coeff(pneg(shiftk(x, k)), i),
            );
        } else {
            let j = i - k as int;
            //  lhs ≡ coeff(pneg x, j) ≡ x_j.neg; rhs ≡ (coeff shiftk).neg ≡ x_j.neg
            lemma_coeff_pneg(x, j);
            T::axiom_eqv_transitive(
                coeff(shiftk(pneg(x), k), i),
                coeff(pneg(x), j),
                coeff(x, j).neg(),
            );
            T::axiom_neg_congruence(coeff(shiftk(x, k), i), coeff(x, j));
            lemma_eqv_flip(coeff(pneg(shiftk(x, k)), i), coeff(shiftk(x, k), i).neg());
            T::axiom_eqv_transitive(
                coeff(pneg(shiftk(x, k)), i),
                coeff(shiftk(x, k), i).neg(),
                coeff(x, j).neg(),
            );
            lemma_eqv_flip(coeff(pneg(shiftk(x, k)), i), coeff(x, j).neg());
            T::axiom_eqv_transitive(
                coeff(shiftk(pneg(x), k), i),
                coeff(x, j).neg(),
                coeff(pneg(shiftk(x, k)), i),
            );
        }
    }
}

///  p * (q - r) ≡ p*q - p*r.
pub proof fn lemma_pmul_psub_right<T: Ring>(p: Seq<T>, q: Seq<T>, r: Seq<T>)
    ensures peqv(pmul(p, psub(q, r)), psub(pmul(p, q), pmul(p, r))),
{
    //  psub(q, r) = padd(q, pneg(r)); distribute, then fold the pneg.
    lemma_pmul_padd_right(p, q, pneg(r));
    lemma_pmul_pneg_right(p, r);
    lemma_peqv_refl(pmul(p, q));
    lemma_padd_cong(
        pmul(p, q), pmul(p, q),
        pmul(p, pneg(r)), pneg(pmul(p, r)),
    );
    //  psub unfolds to padd(·, pneg ·): name the == and bridge it, so the
    //  first trans leg is a single-hop match against padd_right's ensures.
    assert(psub(q, r) =~= padd(q, pneg(r)));
    lemma_peqv_of_eq(pmul(p, psub(q, r)), pmul(p, padd(q, pneg(r))));
    lemma_peqv_trans(
        pmul(p, psub(q, r)),
        pmul(p, padd(q, pneg(r))),
        padd(pmul(p, q), pmul(p, pneg(r))),
    );
    lemma_peqv_trans(
        pmul(p, psub(q, r)),
        padd(pmul(p, q), pmul(p, pneg(r))),
        padd(pmul(p, q), pneg(pmul(p, r))),
    );
}

///  Multiplying by a singleton on the right is scaling.
pub proof fn lemma_pmul_singleton_right<T: Ring>(q: Seq<T>, v: T)
    ensures peqv(pmul(q, seq![v]), scale(v, q)),
    decreases q.len(),
{
    if q.len() == 0 {
        assert(pmul(q, seq![v]) == Seq::<T>::empty());
        assert(scale(v, q) =~= Seq::<T>::empty());
        lemma_peqv_refl(Seq::<T>::empty());
    } else {
        let h = q[0];
        let t = q.skip(1);
        //  Len fact for the Lean gate: makes the recursion-termination obligation
        //  omega-closable (see lemma_pmul_push).
        vstd::seq::axiom_seq_subrange_len(q, 1, q.len() as int);
        assert(pmul(q, seq![v]) == padd(scale(h, seq![v]), shiftk(pmul(t, seq![v]), 1)));
        //  head: scale(h, [v]) is the singleton [h·v] ≡ [v·h]
        assert(scale(h, seq![v]) =~= seq![h.mul(v)]);
        assert forall|i: int|
            (#[trigger] coeff(seq![h.mul(v)], i)).eqv(coeff(seq![v.mul(h)], i))
        by {
            if i == 0 {
                T::axiom_mul_commutative(h, v);
            } else {
                T::axiom_eqv_reflexive(T::zero());
            }
        }
        //  tail: pmul(t,[v]) ≡ scale(v,t), shifted
        lemma_pmul_singleton_right(t, v);
        lemma_shiftk_cong(pmul(t, seq![v]), scale(v, t), 1);
        //  combine into padd([v·h], shiftk(scale(v,t),1))
        lemma_padd_cong(
            seq![h.mul(v)], seq![v.mul(h)],
            shiftk(pmul(t, seq![v]), 1), shiftk(scale(v, t), 1),
        );
        //  and that is the cons-decomposition of scale(v, q)
        lemma_cons_as_padd(scale(v, q));
        assert(scale(v, q).len() == q.len());
        assert(scale(v, q)[0] == v.mul(h));
        assert(scale(v, q).skip(1) =~= scale(v, t));
        assert(seq![scale(v, q)[0]] =~= seq![v.mul(h)]);
        //  peqv(pmul(q, [v]), mid) as single links for the Lean gate:
        //  == unfold (703), then padd_cong of the head and tail facts.
        lemma_peqv_of_eq(pmul(q, seq![v]), padd(scale(h, seq![v]), shiftk(pmul(t, seq![v]), 1)));
        //  peqv(scale(h, [v]), [h·v]) at the coeff level: the == form's
        //  Seq-Eq goal explodes under the ext-equal broadcast haves.
        assert forall|i: int| (#[trigger] coeff(scale(h, seq![v]), i)).eqv(coeff(seq![h.mul(v)], i)) by {
            lemma_coeff_scale(h, seq![v], i);
            assert((seq![v]).len() == 1);
            assert((seq![h.mul(v)]).len() == 1);
            vstd::seq::axiom_seq_push_index_same(Seq::<T>::empty(), v, 0);
            vstd::seq::axiom_seq_push_index_same(Seq::<T>::empty(), h.mul(v), 0);
            if i == 0 {
                T::axiom_eqv_reflexive(h.mul(v));
            } else {
                assert(coeff(seq![v], i) == T::zero());
                assert(coeff(seq![h.mul(v)], i) == T::zero());
                T::axiom_mul_zero_right(h);
                T::axiom_eqv_transitive(
                    coeff(scale(h, seq![v]), i),
                    h.mul(T::zero()),
                    T::zero(),
                );
            }
        }
        assert(peqv(scale(h, seq![v]), seq![h.mul(v)]));
        lemma_padd_cong(
            scale(h, seq![v]), seq![h.mul(v)],
            shiftk(pmul(t, seq![v]), 1), shiftk(scale(v, t), 1),
        );
        lemma_peqv_trans(
            pmul(q, seq![v]),
            padd(scale(h, seq![v]), shiftk(pmul(t, seq![v]), 1)),
            padd(seq![v.mul(h)], shiftk(scale(v, t), 1)),
        );
        //  peqv(mid, scale(v, q)) as single links: padd_cong of the cons
        //  facts (728, 727), sym, then sym of cons_as_padd (724).
        lemma_peqv_of_eq(seq![scale(v, q)[0]], seq![v.mul(h)]);
        //  shiftk of the skip congruence: 727's =~= fact is the peqv_of_eq
        //  precondition verbatim, and shiftk_cong lifts it — no Seq-Eq
        //  simp goal anywhere on this path.
        lemma_peqv_of_eq(scale(v, q).skip(1), scale(v, t));
        lemma_shiftk_cong(scale(v, q).skip(1), scale(v, t), 1);
        lemma_padd_cong(
            seq![scale(v, q)[0]], seq![v.mul(h)],
            shiftk(scale(v, q).skip(1), 1), shiftk(scale(v, t), 1),
        );
        lemma_peqv_sym(
            padd(seq![scale(v, q)[0]], shiftk(scale(v, q).skip(1), 1)),
            padd(seq![v.mul(h)], shiftk(scale(v, t), 1)),
        );
        lemma_peqv_sym(scale(v, q), padd(seq![scale(v, q)[0]], shiftk(scale(v, q).skip(1), 1)));
        lemma_peqv_trans(
            padd(seq![v.mul(h)], shiftk(scale(v, t), 1)),
            padd(seq![scale(v, q)[0]], shiftk(scale(v, q).skip(1), 1)),
            scale(v, q),
        );
        lemma_peqv_trans(
            pmul(q, seq![v]),
            padd(seq![v.mul(h)], shiftk(scale(v, t), 1)),
            scale(v, q),
        );
    }
}

///  Multiplying by a shifted polynomial on the right shifts the product.
pub proof fn lemma_pmul_shiftk_right<T: Ring>(q: Seq<T>, x: Seq<T>, k: nat)
    ensures peqv(pmul(q, shiftk(x, k)), shiftk(pmul(q, x), k)),
    decreases q.len(),
{
    if q.len() == 0 {
        lemma_zpoly_empty::<T>();
        lemma_zpoly_shiftk(Seq::<T>::empty(), k);
        assert(pmul(q, shiftk(x, k)) == Seq::<T>::empty());
        assert(pmul(q, x) == Seq::<T>::empty());
        assert(shiftk(pmul(q, x), k) == shiftk(Seq::<T>::empty(), k));
        lemma_zpoly_to_peqv(Seq::<T>::empty(), shiftk(Seq::<T>::empty(), k));
    } else {
        let h = q[0];
        let t = q.skip(1);
        //  Len fact for the Lean gate: makes the recursion-termination obligation
        //  omega-closable (see lemma_pmul_push).
        vstd::seq::axiom_seq_subrange_len(q, 1, q.len() as int);
        assert(pmul(q, shiftk(x, k)) == padd(scale(h, shiftk(x, k)), shiftk(pmul(t, shiftk(x, k)), 1)));
        //  head
        lemma_scale_shiftk(h, x, k);
        //  tail: IH, then merge the two shifts
        lemma_pmul_shiftk_right(t, x, k);
        lemma_shiftk_cong(pmul(t, shiftk(x, k)), shiftk(pmul(t, x), k), 1);
        lemma_shiftk_compose(pmul(t, x), k);
        assert(shiftk(shiftk(pmul(t, x), k), 1) == shiftk(pmul(t, x), (k + 1) as nat));
        //  peqv(shiftk(pmul(t, shiftk(x,k)),1), shiftk(pmul(t,x),(k+1))) as
        //  two links for the Lean gate: shiftk_cong (760) + == bridge (762).
        lemma_peqv_of_eq(shiftk(shiftk(pmul(t, x), k), 1), shiftk(pmul(t, x), (k + 1) as nat));
        lemma_peqv_trans(
            shiftk(pmul(t, shiftk(x, k)), 1),
            shiftk(shiftk(pmul(t, x), k), 1),
            shiftk(pmul(t, x), (k + 1) as nat),
        );
        //  combine
        lemma_padd_cong(
            scale(h, shiftk(x, k)), shiftk(scale(h, x), k),
            shiftk(pmul(t, shiftk(x, k)), 1), shiftk(pmul(t, x), (k + 1) as nat),
        );
        //  the target unfolds the same way
        assert(pmul(q, x) == padd(scale(h, x), shiftk(pmul(t, x), 1)));
        lemma_shiftk_padd(scale(h, x), shiftk(pmul(t, x), 1), k);
        lemma_shiftk_compose_inner(pmul(t, x), k);
        assert(shiftk(shiftk(pmul(t, x), 1), k) == shiftk(pmul(t, x), (k + 1) as nat));
        //  shiftk(pmul(q,x),k) ≡ padd(shiftk(scale(h,x),k), shiftk(pmul(t,x),(k+1)))
        //  in three links: == bridge (769), shiftk_padd (770), compose cong (772).
        lemma_peqv_of_eq(
            shiftk(pmul(q, x), k),
            shiftk(padd(scale(h, x), shiftk(pmul(t, x), 1)), k),
        );
        lemma_peqv_of_eq(shiftk(shiftk(pmul(t, x), 1), k), shiftk(pmul(t, x), (k + 1) as nat));
        lemma_peqv_refl(shiftk(scale(h, x), k));
        lemma_padd_cong(
            shiftk(scale(h, x), k), shiftk(scale(h, x), k),
            shiftk(shiftk(pmul(t, x), 1), k), shiftk(pmul(t, x), (k + 1) as nat),
        );
        lemma_peqv_trans(
            shiftk(padd(scale(h, x), shiftk(pmul(t, x), 1)), k),
            padd(shiftk(scale(h, x), k), shiftk(shiftk(pmul(t, x), 1), k)),
            padd(shiftk(scale(h, x), k), shiftk(pmul(t, x), (k + 1) as nat)),
        );
        lemma_peqv_trans(
            shiftk(pmul(q, x), k),
            shiftk(padd(scale(h, x), shiftk(pmul(t, x), 1)), k),
            padd(shiftk(scale(h, x), k), shiftk(pmul(t, x), (k + 1) as nat)),
        );
        lemma_peqv_sym(
            shiftk(pmul(q, x), k),
            padd(shiftk(scale(h, x), k), shiftk(pmul(t, x), (k + 1) as nat)),
        );
        lemma_peqv_trans(
            pmul(q, shiftk(x, k)),
            padd(shiftk(scale(h, x), k), shiftk(pmul(t, x), (k + 1) as nat)),
            shiftk(pmul(q, x), k),
        );
    }
}

///  Multiplying a one-shifted polynomial on the LEFT shifts the product.
pub proof fn lemma_pmul_shift1_left<T: Ring>(z: Seq<T>, r: Seq<T>)
    ensures peqv(pmul(shiftk(z, 1), r), shiftk(pmul(z, r), 1)),
{
    let s = shiftk(z, 1);
    assert(s.len() == z.len() + 1);
    assert(s[0] == T::zero());
    assert(s.skip(1) =~= z);
    assert(pmul(s, r) == padd(scale(T::zero(), r), shiftk(pmul(z, r), 1)));
    T::axiom_eqv_reflexive(T::zero());
    lemma_zpoly_scale(T::zero(), r);
    lemma_padd_zpoly_left(scale(T::zero(), r), shiftk(pmul(z, r), 1));
}

///  pmul absorbs a scale on the right argument.
pub proof fn lemma_pmul_scale_right<T: Ring>(r: Seq<T>, h: T, q: Seq<T>)
    ensures peqv(pmul(r, scale(h, q)), scale(h, pmul(r, q))),
    decreases r.len(),
{
    if r.len() == 0 {
        assert(pmul(r, q) == Seq::<T>::empty());
        assert(pmul(r, scale(h, q)) == Seq::<T>::empty());
        assert(scale(h, pmul(r, q)) =~= Seq::<T>::empty());
        lemma_peqv_refl(Seq::<T>::empty());
    } else {
        let c = r[0];
        let t = r.skip(1);
        //  Len fact for the Lean gate: makes the recursion-termination obligation
        //  omega-closable (see lemma_pmul_push).
        vstd::seq::axiom_seq_subrange_len(r, 1, r.len() as int);
        assert(pmul(r, scale(h, q)) == padd(scale(c, scale(h, q)), shiftk(pmul(t, scale(h, q)), 1)));
        //  head: c·(h·q) ≡ (c·h)·q ≡ (h·c)·q ≡ h·(c·q)
        lemma_scale_scale(c, h, q);
        T::axiom_mul_commutative(c, h);
        lemma_scale_cong_scalar(c.mul(h), h.mul(c), q);
        lemma_scale_scale(h, c, q);
        lemma_peqv_sym(scale(h, scale(c, q)), scale(h.mul(c), q));
        lemma_peqv_trans(scale(c, scale(h, q)), scale(c.mul(h), q), scale(h.mul(c), q));
        lemma_peqv_trans(scale(c, scale(h, q)), scale(h.mul(c), q), scale(h, scale(c, q)));
        //  tail: IH + push the shift inside the scale
        lemma_pmul_scale_right(t, h, q);
        lemma_shiftk_cong(pmul(t, scale(h, q)), scale(h, pmul(t, q)), 1);
        lemma_scale_shiftk(h, pmul(t, q), 1);
        lemma_peqv_sym(scale(h, shiftk(pmul(t, q), 1)), shiftk(scale(h, pmul(t, q)), 1));
        lemma_peqv_trans(
            shiftk(pmul(t, scale(h, q)), 1),
            shiftk(scale(h, pmul(t, q)), 1),
            scale(h, shiftk(pmul(t, q), 1)),
        );
        //  combine and fold with scale-over-padd
        lemma_padd_cong(
            scale(c, scale(h, q)), scale(h, scale(c, q)),
            shiftk(pmul(t, scale(h, q)), 1), scale(h, shiftk(pmul(t, q), 1)),
        );
        lemma_scale_padd(h, scale(c, q), shiftk(pmul(t, q), 1));
        lemma_peqv_sym(
            scale(h, padd(scale(c, q), shiftk(pmul(t, q), 1))),
            padd(scale(h, scale(c, q)), scale(h, shiftk(pmul(t, q), 1))),
        );
        lemma_peqv_trans(
            pmul(r, scale(h, q)),
            padd(scale(h, scale(c, q)), scale(h, shiftk(pmul(t, q), 1))),
            scale(h, padd(scale(c, q), shiftk(pmul(t, q), 1))),
        );
        assert(pmul(r, q) == padd(scale(c, q), shiftk(pmul(t, q), 1)));
        //  Fold: scale of the == form, single links for the Lean gate.
        lemma_peqv_of_eq(pmul(r, q), padd(scale(c, q), shiftk(pmul(t, q), 1)));
        lemma_peqv_sym(pmul(r, q), padd(scale(c, q), shiftk(pmul(t, q), 1)));
        lemma_scale_cong_poly(h, padd(scale(c, q), shiftk(pmul(t, q), 1)), pmul(r, q));
        lemma_peqv_trans(
            pmul(r, scale(h, q)),
            scale(h, padd(scale(c, q), shiftk(pmul(t, q), 1))),
            scale(h, pmul(r, q)),
        );
    }
}

//  ============================================================
//   The main laws
//  ============================================================

///  Commutativity: p * q ≡ q * p.
pub proof fn lemma_pmul_comm<T: Ring>(p: Seq<T>, q: Seq<T>)
    ensures peqv(pmul(p, q), pmul(q, p)),
    decreases p.len(),
{
    if p.len() == 0 {
        assert(p =~= Seq::<T>::empty());
        lemma_zpoly_empty::<T>();
        lemma_pmul_empty_right(q);
        lemma_zpoly_to_peqv(Seq::<T>::empty(), pmul(q, Seq::<T>::empty()));
        assert(pmul(p, q) == Seq::<T>::empty());
        assert(pmul(q, p) == pmul(q, Seq::<T>::empty()));
    } else {
        let h = p[0];
        let t = p.skip(1);
        //  Len fact for the Lean gate: makes the recursion-termination obligation
        //  omega-closable (see lemma_pmul_push).
        vstd::seq::axiom_seq_subrange_len(p, 1, p.len() as int);
        //  decompose p in the second argument: p ≡ [h] + x·t
        lemma_cons_as_padd(p);
        lemma_pmul_cong_right(q, p, padd(seq![h], shiftk(t, 1)));
        lemma_pmul_padd_right(q, seq![h], shiftk(t, 1));
        lemma_peqv_trans(
            pmul(q, p),
            pmul(q, padd(seq![h], shiftk(t, 1))),
            padd(pmul(q, seq![h]), pmul(q, shiftk(t, 1))),
        );
        //  the two pieces
        lemma_pmul_singleton_right(q, h);
        lemma_pmul_shiftk_right(q, t, 1);
        //  IH (flipped): pmul(q, t) ≡ pmul(t, q)
        lemma_pmul_comm(t, q);
        lemma_peqv_sym(pmul(t, q), pmul(q, t));
        lemma_peqv_sym(pmul(q, t), pmul(t, q));
        lemma_shiftk_cong(pmul(q, t), pmul(t, q), 1);
        lemma_peqv_trans(pmul(q, shiftk(t, 1)), shiftk(pmul(q, t), 1), shiftk(pmul(t, q), 1));
        //  combine
        lemma_padd_cong(
            pmul(q, seq![h]), scale(h, q),
            pmul(q, shiftk(t, 1)), shiftk(pmul(t, q), 1),
        );
        lemma_peqv_trans(
            pmul(q, p),
            padd(pmul(q, seq![h]), pmul(q, shiftk(t, 1))),
            padd(scale(h, q), shiftk(pmul(t, q), 1)),
        );
        assert(pmul(p, q) == padd(scale(h, q), shiftk(pmul(t, q), 1)));
        lemma_peqv_sym(pmul(q, p), pmul(p, q));
    }
}

///  Right-distributivity: (p + q) * r ≡ p*r + q*r.
pub proof fn lemma_pmul_padd_left<T: Ring>(p: Seq<T>, q: Seq<T>, r: Seq<T>)
    ensures peqv(pmul(padd(p, q), r), padd(pmul(p, r), pmul(q, r))),
{
    lemma_pmul_comm(padd(p, q), r);
    lemma_pmul_padd_right(r, p, q);
    lemma_peqv_trans(
        pmul(padd(p, q), r),
        pmul(r, padd(p, q)),
        padd(pmul(r, p), pmul(r, q)),
    );
    lemma_pmul_comm(r, p);
    lemma_pmul_comm(r, q);
    lemma_padd_cong(pmul(r, p), pmul(p, r), pmul(r, q), pmul(q, r));
    lemma_peqv_trans(
        pmul(padd(p, q), r),
        padd(pmul(r, p), pmul(r, q)),
        padd(pmul(p, r), pmul(q, r)),
    );
}

///  Right-distributivity over subtraction: (p - q) * r ≡ p*r - q*r.
pub proof fn lemma_pmul_psub_left<T: Ring>(p: Seq<T>, q: Seq<T>, r: Seq<T>)
    ensures peqv(pmul(psub(p, q), r), psub(pmul(p, r), pmul(q, r))),
{
    lemma_pmul_comm(psub(p, q), r);
    lemma_pmul_psub_right(r, p, q);
    lemma_peqv_trans(
        pmul(psub(p, q), r),
        pmul(r, psub(p, q)),
        psub(pmul(r, p), pmul(r, q)),
    );
    lemma_pmul_comm(r, p);
    lemma_pmul_comm(r, q);
    lemma_pneg_cong(pmul(r, q), pmul(q, r));
    lemma_padd_cong(pmul(r, p), pmul(p, r), pneg(pmul(r, q)), pneg(pmul(q, r)));
    lemma_peqv_trans(
        pmul(psub(p, q), r),
        psub(pmul(r, p), pmul(r, q)),
        psub(pmul(p, r), pmul(q, r)),
    );
}

///  Associativity: (p * q) * r ≡ p * (q * r).
pub proof fn lemma_pmul_assoc<T: Ring>(p: Seq<T>, q: Seq<T>, r: Seq<T>)
    ensures peqv(pmul(pmul(p, q), r), pmul(p, pmul(q, r))),
    decreases p.len(),
{
    if p.len() == 0 {
        assert(pmul(p, q) == Seq::<T>::empty());
        assert(pmul(pmul(p, q), r) == Seq::<T>::empty());
        assert(pmul(p, pmul(q, r)) == Seq::<T>::empty());
        lemma_peqv_refl(Seq::<T>::empty());
    } else {
        let h = p[0];
        let t = p.skip(1);
        //  Len fact for the Lean gate: makes the recursion-termination obligation
        //  omega-closable (see lemma_pmul_push).
        vstd::seq::axiom_seq_subrange_len(p, 1, p.len() as int);
        assert(pmul(p, q) == padd(scale(h, q), shiftk(pmul(t, q), 1)));
        //  (A + B) * r ≡ A*r + B*r
        lemma_pmul_padd_left(scale(h, q), shiftk(pmul(t, q), 1), r);
        //  A*r = scale(h,q)*r ≡ h·(q*r):  comm, absorb the scale, comm back
        lemma_pmul_comm(scale(h, q), r);
        lemma_pmul_scale_right(r, h, q);
        lemma_peqv_trans(pmul(scale(h, q), r), pmul(r, scale(h, q)), scale(h, pmul(r, q)));
        lemma_pmul_comm(r, q);
        lemma_scale_cong_poly(h, pmul(r, q), pmul(q, r));
        lemma_peqv_trans(pmul(scale(h, q), r), scale(h, pmul(r, q)), scale(h, pmul(q, r)));
        //  B*r = (x·(t*q))*r ≡ x·((t*q)*r) ≡ x·(t*(q*r))
        lemma_pmul_shift1_left(pmul(t, q), r);
        lemma_pmul_assoc(t, q, r);
        lemma_shiftk_cong(pmul(pmul(t, q), r), pmul(t, pmul(q, r)), 1);
        lemma_peqv_trans(
            pmul(shiftk(pmul(t, q), 1), r),
            shiftk(pmul(pmul(t, q), r), 1),
            shiftk(pmul(t, pmul(q, r)), 1),
        );
        //  combine
        lemma_padd_cong(
            pmul(scale(h, q), r), scale(h, pmul(q, r)),
            pmul(shiftk(pmul(t, q), 1), r), shiftk(pmul(t, pmul(q, r)), 1),
        );
        //  The first trans leg as two links for the Lean gate:
        //  pmul_cong_left of the == unfold (965), then pmul_padd_left (967).
        lemma_peqv_of_eq(pmul(p, q), padd(scale(h, q), shiftk(pmul(t, q), 1)));
        lemma_pmul_cong_left(pmul(p, q), padd(scale(h, q), shiftk(pmul(t, q), 1)), r);
        lemma_peqv_trans(
            pmul(pmul(p, q), r),
            pmul(padd(scale(h, q), shiftk(pmul(t, q), 1)), r),
            padd(pmul(scale(h, q), r), pmul(shiftk(pmul(t, q), 1), r)),
        );
        lemma_peqv_trans(
            pmul(pmul(p, q), r),
            padd(pmul(scale(h, q), r), pmul(shiftk(pmul(t, q), 1), r)),
            padd(scale(h, pmul(q, r)), shiftk(pmul(t, pmul(q, r)), 1)),
        );
        assert(pmul(p, pmul(q, r)) == padd(scale(h, pmul(q, r)), shiftk(pmul(t, pmul(q, r)), 1)));
    }
}

///  pmul respects peqv in the first argument.
pub proof fn lemma_pmul_cong_left<T: Ring>(p1: Seq<T>, p2: Seq<T>, q: Seq<T>)
    requires peqv(p1, p2),
    ensures peqv(pmul(p1, q), pmul(p2, q)),
{
    lemma_pmul_comm(p1, q);
    lemma_pmul_cong_right(q, p1, p2);
    lemma_peqv_trans(pmul(p1, q), pmul(q, p1), pmul(q, p2));
    lemma_pmul_comm(q, p2);
    lemma_peqv_trans(pmul(p1, q), pmul(q, p2), pmul(p2, q));
}

///  pmul respects peqv in both arguments.
pub proof fn lemma_pmul_cong_both<T: Ring>(p1: Seq<T>, p2: Seq<T>, q1: Seq<T>, q2: Seq<T>)
    requires peqv(p1, p2), peqv(q1, q2),
    ensures peqv(pmul(p1, q1), pmul(p2, q2)),
{
    lemma_pmul_cong_left(p1, p2, q1);
    lemma_pmul_cong_right(p2, q1, q2);
    lemma_peqv_trans(pmul(p1, q1), pmul(p2, q1), pmul(p2, q2));
}

///  The constant-one polynomial is a left identity for pmul.
pub proof fn lemma_pmul_one_left<T: Ring>(a: Seq<T>)
    ensures peqv(pmul(seq![T::one()], a), a),
{
    let one_p = seq![T::one()];
    assert(one_p.len() == 1);
    //  Explicit axiom calls for the Lean gate (see lemma_pmul_push).
    vstd::seq::axiom_seq_push_index_same(Seq::<T>::empty(), T::one(), 0);
    assert(one_p[0] == T::one());
    vstd::seq::axiom_seq_subrange_len(one_p, 1, one_p.len() as int);
    assert(one_p.skip(1).len() == Seq::<T>::empty().len());
    assert forall|i: int| 0 <= i < one_p.skip(1).len() implies one_p.skip(1)[i] == Seq::<T>::empty()[i] by {
    }
    vstd::seq::axiom_seq_ext_equal(one_p.skip(1), Seq::<T>::empty());
    assert(one_p.skip(1) =~= Seq::<T>::empty());
    assert(pmul(one_p, a) == padd(scale(T::one(), a), shiftk(pmul(Seq::<T>::empty(), a), 1)));
    assert(pmul(Seq::<T>::empty(), a) == Seq::<T>::empty());
    lemma_zpoly_empty::<T>();
    lemma_zpoly_shiftk(Seq::<T>::empty(), 1);
    lemma_padd_zpoly_right(scale(T::one(), a), shiftk(Seq::<T>::empty(), 1));
    lemma_scale_one(a);
    lemma_peqv_trans(pmul(one_p, a), scale(T::one(), a), a);
}

} //  verus!
