use vstd::prelude::*;

verus! {

///  Semantic equality relation.
///
///  Types that implement `Equivalence` provide a notion of equivalence that is
///  reflexive, symmetric, and transitive. This is needed because some
///  representations (e.g. rationals as num/denom pairs) have multiple
///  representations of the same mathematical value.
pub trait Equivalence: Sized {
    ///  Returns true when `self` and `other` represent the same value.
    spec fn eqv(self, other: Self) -> bool;

    ///  Reflexivity: every element is equivalent to itself.
    proof fn axiom_eqv_reflexive(a: Self)
        ensures
            a.eqv(a),
    ;

    ///  Symmetry: equivalence is bidirectional.
    proof fn axiom_eqv_symmetric(a: Self, b: Self)
        ensures
            a.eqv(b) == b.eqv(a),
    ;

    ///  Transitivity: equivalence chains.
    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self)
        requires
            a.eqv(b),
            b.eqv(c),
        ensures
            a.eqv(c),
    ;

    ///  Equality implies equivalence: if a == b, then a ≡ b.
    ///  This is a fundamental property of any reasonable equivalence relation:
    ///  syntactic equality should imply semantic equivalence.
    proof fn axiom_eq_implies_eqv(a: Self, b: Self)
        requires
            a == b,
        ensures
            a.eqv(b),
    ;
}

} //  verus!
