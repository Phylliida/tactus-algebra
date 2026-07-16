use vstd::prelude::*;
use crate::traits::equivalence::Equivalence;

verus! {

///  Partial order compatible with an equivalence relation.
///
///  Provides a `le` relation satisfying reflexivity, antisymmetry (up to eqv),
///  transitivity, and congruence with respect to `eqv`.
///
///  This is a weaker structure than `OrderedRing` — it does not require
///  totality or compatibility with ring operations. Types like intervals
///  ordered by containment can implement this trait.
pub trait PartialOrder: Equivalence {
    //  ---- operations ----

    ///  Less-than-or-equal comparison.
    spec fn le(self, other: Self) -> bool;

    //  ---- axioms: partial order ----

    ///  Reflexivity: a <= a.
    proof fn axiom_le_reflexive(a: Self)
        ensures
            a.le(a),
    ;

    ///  Antisymmetry: a <= b && b <= a implies a ≡ b.
    proof fn axiom_le_antisymmetric(a: Self, b: Self)
        requires
            a.le(b),
            b.le(a),
        ensures
            a.eqv(b),
    ;

    ///  Transitivity: a <= b && b <= c implies a <= c.
    proof fn axiom_le_transitive(a: Self, b: Self, c: Self)
        requires
            a.le(b),
            b.le(c),
        ensures
            a.le(c),
    ;

    //  ---- axioms: congruence ----

    ///  Order respects equivalence.
    proof fn axiom_le_congruence(a1: Self, a2: Self, b1: Self, b2: Self)
        requires
            a1.eqv(a2),
            b1.eqv(b2),
            a1.le(b1),
        ensures
            a2.le(b2),
    ;
}

} //  verus!
