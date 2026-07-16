///  Multiplication lemmas for polynomials: the inductive workhorses behind
///  polynomial division.
///
///  The two main results:
///  - `lemma_pmul_push` (push-decomposition): p.push(c) * q ≡ p*q + x^{len(p)}·(c·q).
///  - `lemma_pmul_pad` (pad absorption): trailing syntactic zeros in the first
///    factor do not change the product (up to peqv).
///
///  Together they let polynomial division build its quotient positionally
///  (`pad(q1, s).push(f)`) without needing commutativity, associativity, or
///  general distributivity of pmul — those come later for gcd/Bézout.
use vstd::prelude::*;
use crate::traits::equivalence::Equivalence;
use crate::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use crate::traits::additive_group::AdditiveGroup;
use crate::traits::ring::Ring;
use crate::lemmas::*;
use crate::poly::*;

verus! {

//  ============================================================
//   Small helpers
//  ============================================================

pub proof fn lemma_zpoly_empty<T: Ring>()
    ensures zpoly(Seq::<T>::empty()),
{
    assert forall|i: int| (#[trigger] coeff(Seq::<T>::empty(), i)).eqv(T::zero()) by {
        T::axiom_eqv_reflexive(T::zero());
    }
}

///  Adding an (eqv-)zero polynomial on the left changes nothing.
pub proof fn lemma_padd_zpoly_left<T: Ring>(z: Seq<T>, p: Seq<T>)
    requires zpoly(z),
    ensures peqv(padd(z, p), p),
{
    lemma_padd_comm(z, p);
    lemma_padd_zpoly_right(p, z);
    lemma_peqv_trans(padd(z, p), padd(p, z), p);
}

///  Shifting by zero is the identity (syntactically).
pub proof fn lemma_shiftk_zero<T: Ring>(p: Seq<T>)
    ensures shiftk(p, 0) == p,
{
    assert(shiftk(p, 0) =~= p);
}

///  Composing shifts: one more shift on the outside is one more zero.
pub proof fn lemma_shiftk_compose<T: Ring>(p: Seq<T>, k: nat)
    ensures shiftk(shiftk(p, k), 1) == shiftk(p, (k + 1) as nat),
{
    assert(shiftk(shiftk(p, k), 1) =~= shiftk(p, (k + 1) as nat));
}

///  shiftk respects peqv.
pub proof fn lemma_shiftk_cong<T: Ring>(x: Seq<T>, y: Seq<T>, k: nat)
    requires peqv(x, y),
    ensures peqv(shiftk(x, k), shiftk(y, k)),
{
    assert forall|i: int| (#[trigger] coeff(shiftk(x, k), i)).eqv(coeff(shiftk(y, k), i)) by {
        lemma_coeff_shiftk(x, k, i);
        lemma_coeff_shiftk(y, k, i);
        if i < k as int {
            //  both ≡ zero
            lemma_eqv_flip(coeff(shiftk(y, k), i), T::zero());
            T::axiom_eqv_transitive(coeff(shiftk(x, k), i), T::zero(), coeff(shiftk(y, k), i));
        } else {
            assert(coeff(x, i - k as int).eqv(coeff(y, i - k as int)));
            lemma_eqv_flip(coeff(shiftk(y, k), i), coeff(y, i - k as int));
            T::axiom_eqv_transitive(
                coeff(shiftk(x, k), i),
                coeff(x, i - k as int),
                coeff(y, i - k as int),
            );
            T::axiom_eqv_transitive(
                coeff(shiftk(x, k), i),
                coeff(y, i - k as int),
                coeff(shiftk(y, k), i),
            );
        }
    }
}

///  shiftk distributes over padd (up to peqv).
pub proof fn lemma_shiftk_padd<T: Ring>(x: Seq<T>, y: Seq<T>, k: nat)
    ensures peqv(shiftk(padd(x, y), k), padd(shiftk(x, k), shiftk(y, k))),
{
    assert forall|i: int|
        (#[trigger] coeff(shiftk(padd(x, y), k), i)).eqv(coeff(padd(shiftk(x, k), shiftk(y, k)), i))
    by {
        lemma_coeff_shiftk(padd(x, y), k, i);
        lemma_coeff_padd(shiftk(x, k), shiftk(y, k), i);
        lemma_coeff_shiftk(x, k, i);
        lemma_coeff_shiftk(y, k, i);
        if i < k as int {
            //  lhs ≡ 0; rhs ≡ shx_i + shy_i ≡ 0 + 0 ≡ 0.
            lemma_add_cong_both(
                coeff(shiftk(x, k), i), T::zero(),
                coeff(shiftk(y, k), i), T::zero(),
            );
            lemma_zero_add_zero::<T>();
            T::axiom_eqv_transitive(
                coeff(padd(shiftk(x, k), shiftk(y, k)), i),
                coeff(shiftk(x, k), i).add(coeff(shiftk(y, k), i)),
                T::zero().add(T::zero()),
            );
            T::axiom_eqv_transitive(
                coeff(padd(shiftk(x, k), shiftk(y, k)), i),
                T::zero().add(T::zero()),
                T::zero(),
            );
            lemma_eqv_flip(coeff(padd(shiftk(x, k), shiftk(y, k)), i), T::zero());
            T::axiom_eqv_transitive(
                coeff(shiftk(padd(x, y), k), i),
                T::zero(),
                coeff(padd(shiftk(x, k), shiftk(y, k)), i),
            );
        } else {
            //  lhs ≡ coeff(padd(x,y), i-k) ≡ x_{i-k} + y_{i-k}
            //  rhs ≡ shx_i + shy_i ≡ x_{i-k} + y_{i-k}
            let j = i - k as int;
            lemma_coeff_padd(x, y, j);
            T::axiom_eqv_transitive(
                coeff(shiftk(padd(x, y), k), i),
                coeff(padd(x, y), j),
                coeff(x, j).add(coeff(y, j)),
            );
            lemma_add_cong_both(
                coeff(shiftk(x, k), i), coeff(x, j),
                coeff(shiftk(y, k), i), coeff(y, j),
            );
            T::axiom_eqv_transitive(
                coeff(padd(shiftk(x, k), shiftk(y, k)), i),
                coeff(shiftk(x, k), i).add(coeff(shiftk(y, k), i)),
                coeff(x, j).add(coeff(y, j)),
            );
            lemma_eqv_flip(
                coeff(padd(shiftk(x, k), shiftk(y, k)), i),
                coeff(x, j).add(coeff(y, j)),
            );
            T::axiom_eqv_transitive(
                coeff(shiftk(padd(x, y), k), i),
                coeff(x, j).add(coeff(y, j)),
                coeff(padd(shiftk(x, k), shiftk(y, k)), i),
            );
        }
    }
}

//  ============================================================
//   Push-decomposition: the inductive workhorse
//  ============================================================

///  p.push(c) * q ≡ p*q + x^{len(p)}·(c·q).
pub proof fn lemma_pmul_push<T: Ring>(p: Seq<T>, c: T, q: Seq<T>)
    ensures peqv(pmul(p.push(c), q), padd(pmul(p, q), shiftk(scale(c, q), p.len()))),
    decreases p.len(),
{
    if p.len() == 0 {
        //  p.push(c) is the singleton [c].
        assert(p.push(c).len() == 1);
        assert(p.push(c)[0] == c);
        assert(p.push(c).skip(1) =~= Seq::<T>::empty());
        //  lhs = padd(scale(c, q), shiftk(pmul(empty, q), 1))
        //      = padd(scale(c, q), shiftk(empty, 1))  — an eqv-zero tail.
        assert(pmul(p.push(c), q) == padd(scale(c, q), shiftk(pmul(Seq::<T>::empty(), q), 1)));
        assert(pmul(Seq::<T>::empty(), q) == Seq::<T>::empty());
        lemma_zpoly_empty::<T>();
        lemma_zpoly_shiftk(Seq::<T>::empty(), 1);
        lemma_padd_zpoly_right(scale(c, q), shiftk(Seq::<T>::empty(), 1));
        //  rhs = padd(empty, shiftk(scale(c, q), 0)) = padd(empty, scale(c, q)).
        assert(pmul(p, q) == Seq::<T>::empty());
        lemma_shiftk_zero(scale(c, q));
        lemma_padd_zpoly_left(Seq::<T>::empty(), scale(c, q));
        //  chain: lhs ≡ scale(c,q) ≡ rhs
        lemma_peqv_sym(padd(Seq::<T>::empty(), scale(c, q)), scale(c, q));
        lemma_peqv_trans(
            pmul(p.push(c), q),
            scale(c, q),
            padd(Seq::<T>::empty(), scale(c, q)),
        );
    } else {
        let h = p[0];
        let t = p.skip(1);
        //  Structure of the pushed sequence.
        assert(p.push(c).len() == p.len() + 1);
        assert(p.push(c)[0] == h);
        assert(p.push(c).skip(1) =~= t.push(c));
        assert(pmul(p.push(c), q) == padd(scale(h, q), shiftk(pmul(t.push(c), q), 1)));
        //  Induction hypothesis on the tail.
        lemma_pmul_push(t, c, q);
        //  Shift the IH by one.
        lemma_shiftk_cong(
            pmul(t.push(c), q),
            padd(pmul(t, q), shiftk(scale(c, q), t.len())),
            1,
        );
        lemma_shiftk_padd(pmul(t, q), shiftk(scale(c, q), t.len()), 1);
        lemma_shiftk_compose(scale(c, q), t.len());
        assert(shiftk(shiftk(scale(c, q), t.len()), 1) == shiftk(scale(c, q), p.len()));
        lemma_peqv_trans(
            shiftk(pmul(t.push(c), q), 1),
            shiftk(padd(pmul(t, q), shiftk(scale(c, q), t.len())), 1),
            padd(shiftk(pmul(t, q), 1), shiftk(scale(c, q), p.len())),
        );
        //  Add the head term on the left and reassociate.
        lemma_peqv_refl(scale(h, q));
        lemma_padd_cong(
            scale(h, q), scale(h, q),
            shiftk(pmul(t.push(c), q), 1),
            padd(shiftk(pmul(t, q), 1), shiftk(scale(c, q), p.len())),
        );
        //  (h·q) + (x·(t*q) + x^len·(c·q)) ≡ ((h·q) + x·(t*q)) + x^len·(c·q)
        lemma_padd_assoc(scale(h, q), shiftk(pmul(t, q), 1), shiftk(scale(c, q), p.len()));
        lemma_peqv_sym(
            padd(padd(scale(h, q), shiftk(pmul(t, q), 1)), shiftk(scale(c, q), p.len())),
            padd(scale(h, q), padd(shiftk(pmul(t, q), 1), shiftk(scale(c, q), p.len()))),
        );
        //  Fold the definition of pmul(p, q).
        assert(pmul(p, q) == padd(scale(h, q), shiftk(pmul(t, q), 1)));
        //  Chain everything.
        lemma_peqv_trans(
            pmul(p.push(c), q),
            padd(scale(h, q), padd(shiftk(pmul(t, q), 1), shiftk(scale(c, q), p.len()))),
            padd(pmul(p, q), shiftk(scale(c, q), p.len())),
        );
    }
}

//  ============================================================
//   Pad absorption
//  ============================================================

///  Trailing syntactic zeros in the first factor do not change the product.
pub proof fn lemma_pmul_pad<T: Ring>(p: Seq<T>, k: nat, q: Seq<T>)
    requires p.len() <= k,
    ensures peqv(pmul(pad(p, k), q), pmul(p, q)),
    decreases k - p.len(),
{
    if k == p.len() {
        assert(pad(p, k) =~= p);
        lemma_peqv_refl(pmul(p, q));
    } else {
        //  pad(p, k) is pad(p, k-1) with one more zero pushed on.
        let k1 = (k - 1) as nat;
        assert(pad(p, k) =~= pad(p, k1).push(T::zero()));
        lemma_pmul_push(pad(p, k1), T::zero(), q);
        assert(pad(p, k1).len() == k1);
        //  The pushed term is an eqv-zero polynomial.
        T::axiom_eqv_reflexive(T::zero());
        lemma_zpoly_scale(T::zero(), q);
        lemma_zpoly_shiftk(scale(T::zero(), q), k1);
        lemma_padd_zpoly_right(pmul(pad(p, k1), q), shiftk(scale(T::zero(), q), k1));
        lemma_peqv_trans(
            pmul(pad(p, k), q),
            padd(pmul(pad(p, k1), q), shiftk(scale(T::zero(), q), k1)),
            pmul(pad(p, k1), q),
        );
        //  Induction.
        lemma_pmul_pad(p, k1, q);
        lemma_peqv_trans(pmul(pad(p, k), q), pmul(pad(p, k1), q), pmul(p, q));
    }
}

} //  verus!
