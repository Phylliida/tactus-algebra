///  Implementation of Ring and OrderedRing for the built-in `int` type.
///
///  Since `int` has native arithmetic, all axioms are trivially provable.
///  This enables using `sum::<int>` and all summation lemmas directly with integers.
use vstd::prelude::*;
use crate::traits::equivalence::Equivalence;
use crate::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use crate::traits::additive_group::AdditiveGroup;
use crate::traits::partial_order::PartialOrder;
use crate::traits::ring::Ring;
use crate::traits::ordered_ring::OrderedRing;

verus! {

impl Equivalence for int {
    open spec fn eqv(self, other: Self) -> bool {
        self == other
    }

    proof fn axiom_eqv_reflexive(a: Self) {}

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {}

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {}

    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {}
}

impl AdditiveCommutativeMonoid for int {
    open spec fn zero() -> Self {
        0
    }

    open spec fn add(self, other: Self) -> Self {
        self + other
    }

    proof fn axiom_add_commutative(a: Self, b: Self) {}

    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {}

    proof fn axiom_add_zero_right(a: Self) {}

    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {}
}

impl AdditiveGroup for int {
    open spec fn neg(self) -> Self {
        -self
    }

    open spec fn sub(self, other: Self) -> Self {
        self - other
    }

    proof fn axiom_add_inverse_right(a: Self) {}

    proof fn axiom_sub_is_add_neg(a: Self, b: Self) {}

    proof fn axiom_neg_congruence(a: Self, b: Self) {}
}

impl Ring for int {
    open spec fn one() -> Self {
        1
    }

    open spec fn mul(self, other: Self) -> Self {
        self * other
    }

    proof fn axiom_mul_commutative(a: Self, b: Self) {
        assert(a * b == b * a) by(nonlinear_arith);
    }

    proof fn axiom_mul_associative(a: Self, b: Self, c: Self) {
        assert((a * b) * c == a * (b * c)) by(nonlinear_arith);
    }

    proof fn axiom_mul_one_right(a: Self) {}

    proof fn axiom_mul_zero_right(a: Self) {}

    proof fn axiom_mul_distributes_left(a: Self, b: Self, c: Self) {
        assert(a * (b + c) == a * b + a * c) by(nonlinear_arith);
    }

    proof fn axiom_one_ne_zero() {}

    proof fn axiom_mul_congruence_left(a: Self, b: Self, c: Self) {}
}

impl PartialOrder for int {
    open spec fn le(self, other: Self) -> bool {
        self <= other
    }

    proof fn axiom_le_reflexive(a: Self) {}

    proof fn axiom_le_antisymmetric(a: Self, b: Self) {}

    proof fn axiom_le_transitive(a: Self, b: Self, c: Self) {}

    proof fn axiom_le_congruence(a1: Self, a2: Self, b1: Self, b2: Self) {}
}

impl OrderedRing for int {
    open spec fn lt(self, other: Self) -> bool {
        self < other
    }

    proof fn axiom_le_total(a: Self, b: Self) {}

    proof fn axiom_lt_iff_le_and_not_eqv(a: Self, b: Self) {}

    proof fn axiom_le_add_monotone(a: Self, b: Self, c: Self) {}

    proof fn axiom_le_mul_nonneg_monotone(a: Self, b: Self, c: Self) {
        assert(a <= b && 0int <= c ==> a * c <= b * c) by(nonlinear_arith);
    }
}

} //  verus!
