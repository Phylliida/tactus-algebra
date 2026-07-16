use vstd::prelude::*;
use crate::traits::ring::Ring;
use crate::traits::ordered_ring::OrderedRing;

verus! {

///  A field: a commutative ring where every nonzero element has a
///  multiplicative inverse.
///
///  `recip` returns the inverse for nonzero elements. Its value on zero is
///  unspecified (implementors may choose any value).
///  `div` is defaulted to multiplication by the reciprocal.
pub trait Field: Ring {
    //  ---- operations ----

    ///  Multiplicative inverse (reciprocal) for nonzero elements.
    spec fn recip(self) -> Self;

    ///  Division, defined as `self * recip(other)`.
    ///  Implementors may override, but must prove equivalence via
    ///  `axiom_div_is_mul_recip`.
    spec fn div(self, other: Self) -> Self;

    //  ---- axioms ----

    ///  Multiplicative inverse identity: for nonzero a, a * recip(a) ≡ 1.
    proof fn axiom_mul_recip_right(a: Self)
        requires
            !a.eqv(Self::zero()),
        ensures
            a.mul(a.recip()).eqv(Self::one()),
    ;

    ///  Division is multiplication by the reciprocal.
    proof fn axiom_div_is_mul_recip(a: Self, b: Self)
        ensures
            a.div(b).eqv(a.mul(b.recip())),
    ;

    ///  Reciprocal respects equivalence.
    proof fn axiom_recip_congruence(a: Self, b: Self)
        requires
            a.eqv(b),
            !a.eqv(Self::zero()),
        ensures
            a.recip().eqv(b.recip()),
    ;
}

///  An ordered field: a field that is also a totally ordered ring, where the
///  order and field operations are compatible.
pub trait OrderedField: OrderedRing + Field {}

} //  verus!
