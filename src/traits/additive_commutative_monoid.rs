use vstd::prelude::*;
use crate::traits::equivalence::Equivalence;

verus! {

///  Commutative monoid under addition with a compatible equivalence relation.
///
///  Provides zero and add. Implementors must prove commutativity, associativity,
///  right identity, and left congruence with respect to `eqv`.
///
///  This is a weaker structure than `AdditiveGroup` — it does not require
///  negation or inverses. Types like intervals that lack additive inverses
///  can still implement this trait.
pub trait AdditiveCommutativeMonoid: Equivalence {
    //  ---- operations ----

    ///  The additive identity element.
    spec fn zero() -> Self;

    ///  Addition of two elements.
    spec fn add(self, other: Self) -> Self;

    //  ---- axioms: monoid laws ----

    ///  Commutativity: a + b ≡ b + a.
    proof fn axiom_add_commutative(a: Self, b: Self)
        ensures
            a.add(b).eqv(b.add(a)),
    ;

    ///  Associativity: (a + b) + c ≡ a + (b + c).
    proof fn axiom_add_associative(a: Self, b: Self, c: Self)
        ensures
            a.add(b).add(c).eqv(a.add(b.add(c))),
    ;

    ///  Right identity: a + 0 ≡ a.
    proof fn axiom_add_zero_right(a: Self)
        ensures
            a.add(Self::zero()).eqv(a),
    ;

    //  ---- axioms: congruence ----

    ///  Addition respects equivalence on the left.
    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self)
        requires
            a.eqv(b),
        ensures
            a.add(c).eqv(b.add(c)),
    ;
}

} //  verus!
