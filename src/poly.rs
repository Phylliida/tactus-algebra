///  Polynomials over a generic Ring/Field, represented as `Seq<T>` of
///  coefficients (index i = coefficient of x^i).
///
///  Design (see tactus-quadratic-extension/DESIGN.md §M0):
///  - `coeff` is a total accessor (zero beyond the stored length), so every
///    pointwise statement is uniform — no in-range/out-of-range case splits
///    at use sites.
///  - `peqv` is pointwise equivalence of total coefficients. It deliberately
///    ignores length: a polynomial is `peqv` to itself with trailing
///    (eqv-)zeros appended or dropped. Polynomial division lives on this,
///    since the division step produces a leading coefficient that is
///    eqv-zero but not syntactically zero.
///  - `pmul` is defined by structural recursion on the first argument
///    (math-comp style), not as a convolution sum — inductive proofs over it
///    are what the Lean backend is good at.
use vstd::prelude::*;
use crate::traits::equivalence::Equivalence;
use crate::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use crate::traits::additive_group::AdditiveGroup;
use crate::traits::ring::Ring;
use crate::lemmas::*;

verus! {

//  ============================================================
//   Definitions
//  ============================================================

pub open spec fn nmax(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

///  Total coefficient accessor: zero beyond the stored length.
pub open spec fn coeff<T: Ring>(p: Seq<T>, i: int) -> T {
    if 0 <= i < p.len() { p[i] } else { T::zero() }
}

///  Pointwise equivalence of total coefficients (length-agnostic).
pub open spec fn peqv<T: Ring>(p: Seq<T>, q: Seq<T>) -> bool {
    forall|i: int| (#[trigger] coeff(p, i)).eqv(coeff(q, i))
}

///  The zero polynomial, up to eqv (all total coefficients eqv-zero).
pub open spec fn zpoly<T: Ring>(p: Seq<T>) -> bool {
    forall|i: int| (#[trigger] coeff(p, i)).eqv(T::zero())
}

///  Pointwise addition, out to the longer length.
pub open spec fn padd<T: Ring>(p: Seq<T>, q: Seq<T>) -> Seq<T> {
    Seq::new(nmax(p.len(), q.len()), |i: int| coeff(p, i).add(coeff(q, i)))
}

///  Pointwise negation.
pub open spec fn pneg<T: Ring>(p: Seq<T>) -> Seq<T> {
    Seq::new(p.len(), |i: int| p[i].neg())
}

///  Subtraction: p + (-q).
pub open spec fn psub<T: Ring>(p: Seq<T>, q: Seq<T>) -> Seq<T> {
    padd(p, pneg(q))
}

///  Scalar multiple: c * p.
pub open spec fn scale<T: Ring>(c: T, p: Seq<T>) -> Seq<T> {
    Seq::new(p.len(), |i: int| c.mul(p[i]))
}

///  Multiplication by x^k: prepend k zeros.
pub open spec fn shiftk<T: Ring>(p: Seq<T>, k: nat) -> Seq<T> {
    Seq::new(k + p.len(), |i: int| if i < k as int { T::zero() } else { p[i - k as int] })
}

///  Pad with trailing (syntactic) zeros out to length k (at least p.len()).
pub open spec fn pad<T: Ring>(p: Seq<T>, k: nat) -> Seq<T> {
    Seq::new(nmax(k, p.len()), |i: int| if i < p.len() { p[i] } else { T::zero() })
}

///  Product, by structural recursion on the first argument:
///  (c + x·t) * q = c·q + x·(t * q).
pub open spec fn pmul<T: Ring>(p: Seq<T>, q: Seq<T>) -> Seq<T>
    decreases p.len(),
{
    if p.len() == 0 {
        Seq::<T>::empty()
    } else {
        padd(scale(p[0], q), shiftk(pmul(p.skip(1), q), 1))
    }
}

//  ============================================================
//   peqv framework
//  ============================================================

pub proof fn lemma_peqv_refl<T: Ring>(p: Seq<T>)
    ensures peqv(p, p),
{
    assert forall|i: int| (#[trigger] coeff(p, i)).eqv(coeff(p, i)) by {
        T::axiom_eqv_reflexive(coeff(p, i));
    }
}

///  Syntactic equality implies coefficient equivalence: the == bridge.
///  Lets a proof turn a definitional-unfold fact (`pmul(p,q) == padd(...)`)
///  into a peqv chain link with one named call (see the 2026-07-21 handoff).
pub proof fn lemma_peqv_of_eq<T: Ring>(p: Seq<T>, q: Seq<T>)
    requires p == q,
    ensures peqv(p, q),
{
    lemma_peqv_refl(p);
}

pub proof fn lemma_peqv_sym<T: Ring>(p: Seq<T>, q: Seq<T>)
    requires peqv(p, q),
    ensures peqv(q, p),
{
    assert forall|i: int| (#[trigger] coeff(q, i)).eqv(coeff(p, i)) by {
        assert(coeff(p, i).eqv(coeff(q, i)));
        T::axiom_eqv_symmetric(coeff(p, i), coeff(q, i));
    }
}

pub proof fn lemma_peqv_trans<T: Ring>(p: Seq<T>, q: Seq<T>, r: Seq<T>)
    requires peqv(p, q), peqv(q, r),
    ensures peqv(p, r),
{
    assert forall|i: int| (#[trigger] coeff(p, i)).eqv(coeff(r, i)) by {
        assert(coeff(p, i).eqv(coeff(q, i)));
        assert(coeff(q, i).eqv(coeff(r, i)));
        T::axiom_eqv_transitive(coeff(p, i), coeff(q, i), coeff(r, i));
    }
}

//  ============================================================
//   Coefficient characterizations (total, up to eqv)
//  ============================================================

pub proof fn lemma_coeff_padd<T: Ring>(p: Seq<T>, q: Seq<T>, i: int)
    ensures coeff(padd(p, q), i).eqv(coeff(p, i).add(coeff(q, i))),
{
    if 0 <= i < padd(p, q).len() {
        T::axiom_eqv_reflexive(coeff(p, i).add(coeff(q, i)));
    } else {
        //  Out of range of the sum means out of range of both, so the goal
        //  is 0 ≡ 0 + 0.
        lemma_zero_add_zero::<T>();
        lemma_eqv_flip(T::zero().add(T::zero()), T::zero());
    }
}

pub proof fn lemma_coeff_pneg<T: Ring>(p: Seq<T>, i: int)
    ensures coeff(pneg(p), i).eqv(coeff(p, i).neg()),
{
    if 0 <= i < p.len() {
        T::axiom_eqv_reflexive(coeff(p, i).neg());
    } else {
        //  0 ≡ -0.
        lemma_neg_zero::<T>();
        lemma_eqv_flip(T::zero().neg(), T::zero());
    }
}

pub proof fn lemma_coeff_psub<T: Ring>(p: Seq<T>, q: Seq<T>, i: int)
    ensures coeff(psub(p, q), i).eqv(coeff(p, i).add(coeff(q, i).neg())),
{
    lemma_coeff_padd(p, pneg(q), i);
    lemma_coeff_pneg(q, i);
    lemma_add_cong_right(coeff(p, i), coeff(pneg(q), i), coeff(q, i).neg());
    T::axiom_eqv_transitive(
        coeff(psub(p, q), i),
        coeff(p, i).add(coeff(pneg(q), i)),
        coeff(p, i).add(coeff(q, i).neg()),
    );
}

pub proof fn lemma_coeff_scale<T: Ring>(c: T, p: Seq<T>, i: int)
    ensures coeff(scale(c, p), i).eqv(c.mul(coeff(p, i))),
{
    if 0 <= i < p.len() {
        T::axiom_eqv_reflexive(c.mul(coeff(p, i)));
    } else {
        //  0 ≡ c * 0.
        T::axiom_mul_zero_right(c);
        lemma_eqv_flip(c.mul(T::zero()), T::zero());
    }
}

pub proof fn lemma_coeff_shiftk<T: Ring>(p: Seq<T>, k: nat, i: int)
    ensures coeff(shiftk(p, k), i).eqv(
        if i < k as int { T::zero() } else { coeff(p, i - k as int) }
    ),
{
    if i < k as int {
        T::axiom_eqv_reflexive(T::zero());
    } else {
        T::axiom_eqv_reflexive(coeff(p, i - k as int));
    }
}

///  Padding does not change total coefficients — syntactic equality.
pub proof fn lemma_coeff_pad<T: Ring>(p: Seq<T>, k: nat, i: int)
    ensures coeff(pad(p, k), i) == coeff(p, i),
{
}

pub proof fn lemma_pad_peqv<T: Ring>(p: Seq<T>, k: nat)
    ensures peqv(pad(p, k), p),
{
    assert forall|i: int| (#[trigger] coeff(pad(p, k), i)).eqv(coeff(p, i)) by {
        lemma_coeff_pad(p, k, i);
        T::axiom_eqv_reflexive(coeff(p, i));
    }
}

//  ============================================================
//   Pointwise algebra at the peqv level
//  ============================================================

pub proof fn lemma_padd_comm<T: Ring>(p: Seq<T>, q: Seq<T>)
    ensures peqv(padd(p, q), padd(q, p)),
{
    assert forall|i: int| (#[trigger] coeff(padd(p, q), i)).eqv(coeff(padd(q, p), i)) by {
        lemma_coeff_padd(p, q, i);
        T::axiom_add_commutative(coeff(p, i), coeff(q, i));
        lemma_coeff_padd(q, p, i);
        lemma_eqv_flip(coeff(padd(q, p), i), coeff(q, i).add(coeff(p, i)));
        T::axiom_eqv_transitive(
            coeff(padd(p, q), i),
            coeff(p, i).add(coeff(q, i)),
            coeff(q, i).add(coeff(p, i)),
        );
        T::axiom_eqv_transitive(
            coeff(padd(p, q), i),
            coeff(q, i).add(coeff(p, i)),
            coeff(padd(q, p), i),
        );
    }
}

pub proof fn lemma_padd_assoc<T: Ring>(p: Seq<T>, q: Seq<T>, r: Seq<T>)
    ensures peqv(padd(padd(p, q), r), padd(p, padd(q, r))),
{
    assert forall|i: int|
        (#[trigger] coeff(padd(padd(p, q), r), i)).eqv(coeff(padd(p, padd(q, r)), i))
    by {
        let pi = coeff(p, i);
        let qi = coeff(q, i);
        let ri = coeff(r, i);
        //  lhs ≡ (p_i + q_i) + r_i
        lemma_coeff_padd(padd(p, q), r, i);
        lemma_coeff_padd(p, q, i);
        T::axiom_add_congruence_left(coeff(padd(p, q), i), pi.add(qi), ri);
        T::axiom_eqv_transitive(
            coeff(padd(padd(p, q), r), i),
            coeff(padd(p, q), i).add(ri),
            pi.add(qi).add(ri),
        );
        //  T-level associativity
        T::axiom_add_associative(pi, qi, ri);
        T::axiom_eqv_transitive(
            coeff(padd(padd(p, q), r), i),
            pi.add(qi).add(ri),
            pi.add(qi.add(ri)),
        );
        //  fold the right-hand side back up
        lemma_coeff_padd(q, r, i);
        lemma_eqv_flip(coeff(padd(q, r), i), qi.add(ri));
        lemma_add_cong_right(pi, qi.add(ri), coeff(padd(q, r), i));
        T::axiom_eqv_transitive(
            coeff(padd(padd(p, q), r), i),
            pi.add(qi.add(ri)),
            pi.add(coeff(padd(q, r), i)),
        );
        lemma_coeff_padd(p, padd(q, r), i);
        lemma_eqv_flip(coeff(padd(p, padd(q, r)), i), pi.add(coeff(padd(q, r), i)));
        T::axiom_eqv_transitive(
            coeff(padd(padd(p, q), r), i),
            pi.add(coeff(padd(q, r), i)),
            coeff(padd(p, padd(q, r)), i),
        );
    }
}

pub proof fn lemma_padd_cong<T: Ring>(p1: Seq<T>, p2: Seq<T>, q1: Seq<T>, q2: Seq<T>)
    requires peqv(p1, p2), peqv(q1, q2),
    ensures peqv(padd(p1, q1), padd(p2, q2)),
{
    assert forall|i: int| (#[trigger] coeff(padd(p1, q1), i)).eqv(coeff(padd(p2, q2), i)) by {
        lemma_coeff_padd(p1, q1, i);
        assert(coeff(p1, i).eqv(coeff(p2, i)));
        assert(coeff(q1, i).eqv(coeff(q2, i)));
        lemma_add_cong_both(coeff(p1, i), coeff(p2, i), coeff(q1, i), coeff(q2, i));
        T::axiom_eqv_transitive(
            coeff(padd(p1, q1), i),
            coeff(p1, i).add(coeff(q1, i)),
            coeff(p2, i).add(coeff(q2, i)),
        );
        lemma_coeff_padd(p2, q2, i);
        lemma_eqv_flip(coeff(padd(p2, q2), i), coeff(p2, i).add(coeff(q2, i)));
        T::axiom_eqv_transitive(
            coeff(padd(p1, q1), i),
            coeff(p2, i).add(coeff(q2, i)),
            coeff(padd(p2, q2), i),
        );
    }
}

///  Adding an (eqv-)zero polynomial on the right changes nothing.
pub proof fn lemma_padd_zpoly_right<T: Ring>(p: Seq<T>, z: Seq<T>)
    requires zpoly(z),
    ensures peqv(padd(p, z), p),
{
    assert forall|i: int| (#[trigger] coeff(padd(p, z), i)).eqv(coeff(p, i)) by {
        lemma_coeff_padd(p, z, i);
        assert(coeff(z, i).eqv(T::zero()));
        lemma_add_cong_right(coeff(p, i), coeff(z, i), T::zero());
        T::axiom_add_zero_right(coeff(p, i));
        T::axiom_eqv_transitive(
            coeff(padd(p, z), i),
            coeff(p, i).add(coeff(z, i)),
            coeff(p, i).add(T::zero()),
        );
        T::axiom_eqv_transitive(
            coeff(padd(p, z), i),
            coeff(p, i).add(T::zero()),
            coeff(p, i),
        );
    }
}

///  Scaling by an eqv-zero scalar gives an eqv-zero polynomial.
pub proof fn lemma_zpoly_scale<T: Ring>(c: T, p: Seq<T>)
    requires c.eqv(T::zero()),
    ensures zpoly(scale(c, p)),
{
    assert forall|i: int| (#[trigger] coeff(scale(c, p), i)).eqv(T::zero()) by {
        lemma_coeff_scale(c, p, i);
        T::axiom_mul_congruence_left(c, T::zero(), coeff(p, i));
        lemma_mul_zero_left(coeff(p, i));
        T::axiom_eqv_transitive(
            c.mul(coeff(p, i)),
            T::zero().mul(coeff(p, i)),
            T::zero(),
        );
        T::axiom_eqv_transitive(
            coeff(scale(c, p), i),
            c.mul(coeff(p, i)),
            T::zero(),
        );
    }
}

///  Shifting an eqv-zero polynomial gives an eqv-zero polynomial.
pub proof fn lemma_zpoly_shiftk<T: Ring>(p: Seq<T>, k: nat)
    requires zpoly(p),
    ensures zpoly(shiftk(p, k)),
{
    assert forall|i: int| (#[trigger] coeff(shiftk(p, k), i)).eqv(T::zero()) by {
        lemma_coeff_shiftk(p, k, i);
        if i < k as int {
            T::axiom_eqv_reflexive(T::zero());
        } else {
            assert(coeff(p, i - k as int).eqv(T::zero()));
            T::axiom_eqv_transitive(
                coeff(shiftk(p, k), i),
                coeff(p, i - k as int),
                T::zero(),
            );
        }
    }
}

///  Dropping a trailing eqv-zero coefficient preserves peqv.
pub proof fn lemma_drop_last_peqv<T: Ring>(p: Seq<T>)
    requires p.len() > 0, p.last().eqv(T::zero()),
    ensures peqv(p, p.drop_last()),
{
    assert forall|i: int| (#[trigger] coeff(p, i)).eqv(coeff(p.drop_last(), i)) by {
        if 0 <= i < p.len() - 1 {
            //  In range of both: the subrange read, for the Lean gate.
            vstd::seq::axiom_seq_subrange_len(p, 0, (p.len() - 1) as int);
            vstd::seq::axiom_seq_subrange_index(p, 0, (p.len() - 1) as int, i);
            assert(coeff(p.drop_last(), i) == coeff(p, i));
            T::axiom_eqv_reflexive(coeff(p, i));
        } else if i == p.len() - 1 {
            //  coeff(p, i) is the last entry (≡ 0); the dropped poly reads 0.
            vstd::seq::axiom_seq_subrange_len(p, 0, (p.len() - 1) as int);
            assert(p.drop_last().len() == p.len() - 1);
            assert(coeff(p.drop_last(), i) == T::zero());
        } else {
            T::axiom_eqv_reflexive(T::zero());
        }
    }
}

///  Recovery at the polynomial level: a ≡ t + (a - t).
pub proof fn lemma_precover<T: Ring>(a: Seq<T>, t: Seq<T>)
    ensures peqv(a, padd(t, psub(a, t))),
{
    assert forall|i: int| (#[trigger] coeff(a, i)).eqv(coeff(padd(t, psub(a, t)), i)) by {
        let x = coeff(a, i);
        let y = coeff(t, i);
        //  y + (x + -y) ≡ x, flipped.
        lemma_recover(x, y);
        lemma_eqv_flip(y.add(x.add(y.neg())), x);
        //  fold x + -y into coeff(psub(a,t), i)
        lemma_coeff_psub(a, t, i);
        lemma_eqv_flip(coeff(psub(a, t), i), x.add(y.neg()));
        lemma_add_cong_right(y, x.add(y.neg()), coeff(psub(a, t), i));
        T::axiom_eqv_transitive(
            x,
            y.add(x.add(y.neg())),
            y.add(coeff(psub(a, t), i)),
        );
        //  fold into coeff(padd(t, psub(a,t)), i)
        lemma_coeff_padd(t, psub(a, t), i);
        lemma_eqv_flip(coeff(padd(t, psub(a, t)), i), y.add(coeff(psub(a, t), i)));
        T::axiom_eqv_transitive(
            x,
            y.add(coeff(psub(a, t), i)),
            coeff(padd(t, psub(a, t)), i),
        );
    }
}

} //  verus!
