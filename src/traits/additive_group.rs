use vstd::prelude::*;
use crate::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;

verus! {

///  Abelian group under addition with a compatible equivalence relation.
///
///  Extends `AdditiveCommutativeMonoid` with negation and subtraction.
///  Implementors must prove the inverse axiom, that subtraction equals
///  addition of the negation, and that negation respects `eqv`.
pub trait AdditiveGroup: AdditiveCommutativeMonoid {
    //  ---- operations ----

    ///  Additive inverse (negation).
    spec fn neg(self) -> Self;

    ///  Subtraction, defined as `self + (-other)`.
    ///  Implementors may override with a more efficient definition, but must
    ///  prove it equivalent via `axiom_sub_is_add_neg`.
    spec fn sub(self, other: Self) -> Self;

    //  ---- axioms: group laws ----

    ///  Right inverse: a + (-a) ≡ 0.
    proof fn axiom_add_inverse_right(a: Self)
        ensures
            a.add(a.neg()).eqv(Self::zero()),
    ;

    ///  Subtraction is addition of the negation.
    proof fn axiom_sub_is_add_neg(a: Self, b: Self)
        ensures
            a.sub(b).eqv(a.add(b.neg())),
    ;

    //  ---- axioms: congruence ----

    ///  Negation respects equivalence.
    proof fn axiom_neg_congruence(a: Self, b: Self)
        requires
            a.eqv(b),
        ensures
            a.neg().eqv(b.neg()),
    ;
}

} //  verus!
