use vstd::prelude::*;
use crate::traits::additive_group::AdditiveGroup;

verus! {

///  Commutative ring with unity.
///
///  Extends `AdditiveGroup` with multiplication, a multiplicative identity (one),
///  and the standard ring axioms including commutativity of multiplication.
pub trait Ring: AdditiveGroup {
    //  ---- operations ----

    ///  The multiplicative identity element.
    spec fn one() -> Self;

    ///  Multiplication of two elements.
    spec fn mul(self, other: Self) -> Self;

    //  ---- axioms: ring laws ----

    ///  Commutativity: a * b ≡ b * a.
    proof fn axiom_mul_commutative(a: Self, b: Self)
        ensures
            a.mul(b).eqv(b.mul(a)),
    ;

    ///  Associativity: (a * b) * c ≡ a * (b * c).
    proof fn axiom_mul_associative(a: Self, b: Self, c: Self)
        ensures
            a.mul(b).mul(c).eqv(a.mul(b.mul(c))),
    ;

    ///  Right identity: a * 1 ≡ a.
    proof fn axiom_mul_one_right(a: Self)
        ensures
            a.mul(Self::one()).eqv(a),
    ;

    ///  Zero annihilates: a * 0 ≡ 0.
    proof fn axiom_mul_zero_right(a: Self)
        ensures
            a.mul(Self::zero()).eqv(Self::zero()),
    ;

    ///  Left distributivity: a * (b + c) ≡ a*b + a*c.
    proof fn axiom_mul_distributes_left(a: Self, b: Self, c: Self)
        ensures
            a.mul(b.add(c)).eqv(a.mul(b).add(a.mul(c))),
    ;

    //  ---- axioms: non-degeneracy ----

    ///  The multiplicative and additive identities are distinct: 1 ≢ 0.
    proof fn axiom_one_ne_zero()
        ensures !Self::one().eqv(Self::zero()),
    ;

    //  ---- axioms: congruence ----

    ///  Multiplication respects equivalence on the left.
    proof fn axiom_mul_congruence_left(a: Self, b: Self, c: Self)
        requires
            a.eqv(b),
        ensures
            a.mul(c).eqv(b.mul(c)),
    ;
}

} //  verus!
