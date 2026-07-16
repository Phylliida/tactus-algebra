///  Derived generic lemmas over the trait ladder: consequences of the Ring /
///  Field axioms that downstream code (especially the polynomial module's
///  pointwise proofs) uses constantly. Everything here is proven from the
///  trait axioms alone — no instance-specific facts.
use vstd::prelude::*;
use crate::traits::equivalence::Equivalence;
use crate::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use crate::traits::additive_group::AdditiveGroup;
use crate::traits::ring::Ring;
use crate::traits::field::Field;

verus! {

//  ---- equivalence ergonomics ----

///  Flip an equivalence (the symmetry axiom gives boolean equality; this
///  packages the common directional use).
pub proof fn lemma_eqv_flip<T: Equivalence>(a: T, b: T)
    requires a.eqv(b),
    ensures b.eqv(a),
{
    T::axiom_eqv_symmetric(a, b);
}

//  ---- additive laws ----

///  Left identity: 0 + a ≡ a.
pub proof fn lemma_add_zero_left<T: AdditiveCommutativeMonoid>(a: T)
    ensures T::zero().add(a).eqv(a),
{
    T::axiom_add_commutative(T::zero(), a);
    T::axiom_add_zero_right(a);
    T::axiom_eqv_transitive(T::zero().add(a), a.add(T::zero()), a);
}

///  0 + 0 ≡ 0.
pub proof fn lemma_zero_add_zero<T: AdditiveCommutativeMonoid>()
    ensures T::zero().add(T::zero()).eqv(T::zero()),
{
    T::axiom_add_zero_right(T::zero());
}

///  Addition respects equivalence on the right.
pub proof fn lemma_add_cong_right<T: AdditiveCommutativeMonoid>(c: T, a: T, b: T)
    requires a.eqv(b),
    ensures c.add(a).eqv(c.add(b)),
{
    T::axiom_add_commutative(c, a);
    T::axiom_add_congruence_left(a, b, c);
    T::axiom_add_commutative(b, c);
    T::axiom_eqv_transitive(c.add(a), a.add(c), b.add(c));
    T::axiom_eqv_transitive(c.add(a), b.add(c), c.add(b));
}

///  Addition respects equivalence in both arguments.
pub proof fn lemma_add_cong_both<T: AdditiveCommutativeMonoid>(a1: T, a2: T, b1: T, b2: T)
    requires a1.eqv(a2), b1.eqv(b2),
    ensures a1.add(b1).eqv(a2.add(b2)),
{
    T::axiom_add_congruence_left(a1, a2, b1);
    lemma_add_cong_right(a2, b1, b2);
    T::axiom_eqv_transitive(a1.add(b1), a2.add(b1), a2.add(b2));
}

///  -0 ≡ 0.
pub proof fn lemma_neg_zero<T: AdditiveGroup>()
    ensures T::zero().neg().eqv(T::zero()),
{
    //  0 + (-0) ≡ 0 by the inverse axiom; 0 + (-0) ≡ -0 by left identity.
    T::axiom_add_inverse_right(T::zero());
    lemma_add_zero_left(T::zero().neg());
    lemma_eqv_flip(T::zero().add(T::zero().neg()), T::zero().neg());
    T::axiom_eqv_transitive(
        T::zero().neg(),
        T::zero().add(T::zero().neg()),
        T::zero(),
    );
}

///  a - a ≡ 0.
pub proof fn lemma_sub_self<T: AdditiveGroup>(a: T)
    ensures a.sub(a).eqv(T::zero()),
{
    T::axiom_sub_is_add_neg(a, a);
    T::axiom_add_inverse_right(a);
    T::axiom_eqv_transitive(a.sub(a), a.add(a.neg()), T::zero());
}

///  Recovery: y + (x + (-y)) ≡ x. This is the pointwise fact behind
///  "a ≡ t + (a - t)" in polynomial division.
pub proof fn lemma_recover<T: AdditiveGroup>(x: T, y: T)
    ensures y.add(x.add(y.neg())).eqv(x),
{
    //  y + (x + -y) ≡ y + (-y + x)   [inner commutativity]
    T::axiom_add_commutative(x, y.neg());
    lemma_add_cong_right(y, x.add(y.neg()), y.neg().add(x));
    //  y + (-y + x) ≡ (y + -y) + x   [associativity, flipped]
    T::axiom_add_associative(y, y.neg(), x);
    lemma_eqv_flip(y.add(y.neg()).add(x), y.add(y.neg().add(x)));
    //  (y + -y) + x ≡ 0 + x          [inverse]
    T::axiom_add_inverse_right(y);
    T::axiom_add_congruence_left(y.add(y.neg()), T::zero(), x);
    //  0 + x ≡ x                     [left identity]
    lemma_add_zero_left(x);
    //  chain
    T::axiom_eqv_transitive(
        y.add(x.add(y.neg())),
        y.add(y.neg().add(x)),
        y.add(y.neg()).add(x),
    );
    T::axiom_eqv_transitive(
        y.add(x.add(y.neg())),
        y.add(y.neg()).add(x),
        T::zero().add(x),
    );
    T::axiom_eqv_transitive(
        y.add(x.add(y.neg())),
        T::zero().add(x),
        x,
    );
}

//  ---- multiplicative laws ----

///  Left annihilation: 0 * a ≡ 0.
pub proof fn lemma_mul_zero_left<T: Ring>(a: T)
    ensures T::zero().mul(a).eqv(T::zero()),
{
    T::axiom_mul_commutative(T::zero(), a);
    T::axiom_mul_zero_right(a);
    T::axiom_eqv_transitive(T::zero().mul(a), a.mul(T::zero()), T::zero());
}

///  Left identity: 1 * a ≡ a.
pub proof fn lemma_mul_one_left<T: Ring>(a: T)
    ensures T::one().mul(a).eqv(a),
{
    T::axiom_mul_commutative(T::one(), a);
    T::axiom_mul_one_right(a);
    T::axiom_eqv_transitive(T::one().mul(a), a.mul(T::one()), a);
}

///  Multiplication respects equivalence on the right.
pub proof fn lemma_mul_cong_right<T: Ring>(c: T, a: T, b: T)
    requires a.eqv(b),
    ensures c.mul(a).eqv(c.mul(b)),
{
    T::axiom_mul_commutative(c, a);
    T::axiom_mul_congruence_left(a, b, c);
    T::axiom_mul_commutative(b, c);
    T::axiom_eqv_transitive(c.mul(a), a.mul(c), b.mul(c));
    T::axiom_eqv_transitive(c.mul(a), b.mul(c), c.mul(b));
}

///  Multiplication respects equivalence in both arguments.
pub proof fn lemma_mul_cong_both<T: Ring>(a1: T, a2: T, b1: T, b2: T)
    requires a1.eqv(a2), b1.eqv(b2),
    ensures a1.mul(b1).eqv(a2.mul(b2)),
{
    T::axiom_mul_congruence_left(a1, a2, b1);
    lemma_mul_cong_right(a2, b1, b2);
    T::axiom_eqv_transitive(a1.mul(b1), a2.mul(b1), a2.mul(b2));
}

///  Negation respects equivalence, packaged with a zero target:
///  a ≡ 0 implies -a ≡ 0.
pub proof fn lemma_neg_of_eqv_zero<T: AdditiveGroup>(a: T)
    requires a.eqv(T::zero()),
    ensures a.neg().eqv(T::zero()),
{
    T::axiom_neg_congruence(a, T::zero());
    lemma_neg_zero::<T>();
    T::axiom_eqv_transitive(a.neg(), T::zero().neg(), T::zero());
}

//  ---- field laws ----

///  Reciprocal cancellation: (x * y⁻¹) * y ≡ x for nonzero y.
pub proof fn lemma_mul_recip_cancel<T: Field>(x: T, y: T)
    requires !y.eqv(T::zero()),
    ensures x.mul(y.recip()).mul(y).eqv(x),
{
    //  (x * y⁻¹) * y ≡ x * (y⁻¹ * y)   [associativity]
    T::axiom_mul_associative(x, y.recip(), y);
    //  y⁻¹ * y ≡ y * y⁻¹ ≡ 1           [commutativity + recip axiom]
    T::axiom_mul_commutative(y.recip(), y);
    T::axiom_mul_recip_right(y);
    T::axiom_eqv_transitive(y.recip().mul(y), y.mul(y.recip()), T::one());
    //  x * (y⁻¹ * y) ≡ x * 1 ≡ x
    lemma_mul_cong_right(x, y.recip().mul(y), T::one());
    T::axiom_mul_one_right(x);
    T::axiom_eqv_transitive(x.mul(y.recip().mul(y)), x.mul(T::one()), x);
    //  chain
    T::axiom_eqv_transitive(
        x.mul(y.recip()).mul(y),
        x.mul(y.recip().mul(y)),
        x,
    );
}

///  The division-step kill: x + (-((x * y⁻¹) * y)) ≡ 0 for nonzero y.
///  This is exactly the leading coefficient of `a - (lc(a)/lc(b))·x^s·b`.
pub proof fn lemma_kill_top<T: Field>(x: T, y: T)
    requires !y.eqv(T::zero()),
    ensures x.add(x.mul(y.recip()).mul(y).neg()).eqv(T::zero()),
{
    let z = x.mul(y.recip()).mul(y);
    lemma_mul_recip_cancel(x, y);
    //  z ≡ x, so -z ≡ -x, so x + (-z) ≡ x + (-x) ≡ 0.
    T::axiom_neg_congruence(z, x);
    lemma_add_cong_right(x, z.neg(), x.neg());
    T::axiom_add_inverse_right(x);
    T::axiom_eqv_transitive(x.add(z.neg()), x.add(x.neg()), T::zero());
}

} //  verus!
