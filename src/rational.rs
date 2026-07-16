///  Exact rational arithmetic: the base field for tactus-algebra.
///
///  `den` stores `(effective_denominator - 1)`, so the effective denominator
///  `denom() == den + 1` is positive by construction and no well-formedness
///  invariant is needed. The spec model is ported from verus-rational; the
///  proofs are written fresh against the Lean backend instead of porting the
///  Z3-era lemma chains.
use vstd::prelude::*;
use crate::traits::equivalence::Equivalence;
use crate::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use crate::traits::additive_group::AdditiveGroup;
use crate::traits::partial_order::PartialOrder;
use crate::traits::ring::Ring;
use crate::traits::ordered_ring::OrderedRing;
use crate::traits::field::{Field, OrderedField};

verus! {

///  Exact rational number: `num / (den + 1)`.
pub struct Rational {
    pub num: int,
    pub den: nat,
}

impl Rational {
    ///  Effective denominator as a nat (always >= 1).
    pub open spec fn denom_nat(self) -> nat {
        self.den + 1
    }

    ///  Effective denominator as an int (always >= 1).
    pub open spec fn denom(self) -> int {
        self.denom_nat() as int
    }

    ///  Construct a rational from an integer (denominator = 1).
    pub open spec fn from_int_spec(value: int) -> Self {
        Rational { num: value, den: 0 }
    }

    ///  Spec-level construction from numerator and denominator. The sign of
    ///  the denominator is moved to the numerator so the effective
    ///  denominator is always positive.
    pub open spec fn from_frac_spec(num: int, den: int) -> Self
        recommends den != 0,
    {
        if den > 0 {
            Rational { num: num, den: (den - 1) as nat }
        } else {
            Rational { num: -num, den: (-den - 1) as nat }
        }
    }

    ///  Spec-level addition: a/b + c/d = (a*d + c*b) / (b*d).
    pub open spec fn add_spec(self, rhs: Self) -> Self {
        let d1 = self.denom_nat();
        let d2 = rhs.denom_nat();
        Rational {
            num: self.num * (d2 as int) + rhs.num * (d1 as int),
            den: self.den * rhs.den + self.den + rhs.den,
        }
    }

    ///  Spec-level negation: -(a/b) = (-a)/b.
    pub open spec fn neg_spec(self) -> Self {
        Rational { num: -self.num, den: self.den }
    }

    ///  Spec-level subtraction: a - b = a + (-b).
    pub open spec fn sub_spec(self, rhs: Self) -> Self {
        self.add_spec(rhs.neg_spec())
    }

    ///  Spec-level multiplication: (a/b) * (c/d) = (a*c) / (b*d).
    pub open spec fn mul_spec(self, rhs: Self) -> Self {
        Rational {
            num: self.num * rhs.num,
            den: self.den * rhs.den + self.den + rhs.den,
        }
    }

    ///  Spec-level reciprocal: value on zero is arbitrary (returns self).
    pub open spec fn reciprocal_spec(self) -> Self {
        if self.num > 0 {
            Rational { num: self.denom(), den: (self.num as nat - 1) as nat }
        } else if self.num < 0 {
            Rational { num: -self.denom(), den: ((-self.num) as nat - 1) as nat }
        } else {
            self
        }
    }

    ///  Spec-level division: a / b = a * recip(b). Callers ensure b nonzero.
    pub open spec fn div_spec(self, rhs: Self) -> Self {
        self.mul_spec(rhs.reciprocal_spec())
    }

    ///  Sign of the rational: 1, -1, or 0.
    pub open spec fn signum(self) -> int {
        if self.num > 0 { 1 } else if self.num < 0 { -1 } else { 0 }
    }

    ///  Semantic equality via cross-multiplication: a/b ≡ c/d iff a*d == c*b.
    pub open spec fn eqv_spec(self, rhs: Self) -> bool {
        self.num * rhs.denom() == rhs.num * self.denom()
    }

    ///  Less-than-or-equal via cross-multiplication.
    pub open spec fn le_spec(self, rhs: Self) -> bool {
        self.num * rhs.denom() <= rhs.num * self.denom()
    }

    ///  Strict less-than via cross-multiplication.
    pub open spec fn lt_spec(self, rhs: Self) -> bool {
        self.num * rhs.denom() < rhs.num * self.denom()
    }

    //  ---- foundation lemmas ----

    ///  The denominator is positive.
    pub proof fn lemma_denom_pos(a: Self)
        ensures a.denom() > 0,
    {
    }

    ///  Closed forms for the fields of an addition result.
    pub proof fn lemma_add_parts(a: Self, b: Self)
        ensures
            a.add_spec(b).num == a.num * b.denom() + b.num * a.denom(),
            a.add_spec(b).denom() == a.denom() * b.denom(),
    {
        assert(((a.den * b.den + a.den + b.den + 1) as int)
            == ((a.den + 1) as int) * ((b.den + 1) as int)) by (nonlinear_arith);
    }

    ///  Closed forms for the fields of a multiplication result.
    pub proof fn lemma_mul_parts(a: Self, b: Self)
        ensures
            a.mul_spec(b).num == a.num * b.num,
            a.mul_spec(b).denom() == a.denom() * b.denom(),
    {
        assert(((a.den * b.den + a.den + b.den + 1) as int)
            == ((a.den + 1) as int) * ((b.den + 1) as int)) by (nonlinear_arith);
    }

    ///  a ≡ 0 iff a.num == 0.
    pub proof fn lemma_eqv_zero_iff_num_zero(a: Self)
        ensures a.eqv_spec(Self::from_int_spec(0)) == (a.num == 0),
    {
        assert((a.num * 1 == 0 * a.denom()) == (a.num == 0)) by (nonlinear_arith);
    }

    ///  Distributivity numerator scaling, over plain int atoms and split into
    ///  single-product steps so each nonlinear query stays small.
    proof fn lemma_distrib_scale(an: int, bn: int, cn: int, ad: int, bd: int, cd: int)
        ensures
            (an * bn) * (ad * cd) + (an * cn) * (ad * bd)
                == ad * (an * (bn * cd + cn * bd)),
    {
        assert((an * bn) * (ad * cd) == ad * (an * (bn * cd))) by (nonlinear_arith);
        assert((an * cn) * (ad * bd) == ad * (an * (cn * bd))) by (nonlinear_arith);
        assert(an * (bn * cd + cn * bd) == an * (bn * cd) + an * (cn * bd))
            by (nonlinear_arith);
        assert(ad * (an * (bn * cd) + an * (cn * bd))
            == ad * (an * (bn * cd)) + ad * (an * (cn * bd))) by (nonlinear_arith);
    }
}

impl Equivalence for Rational {
    open spec fn eqv(self, other: Self) -> bool {
        self.eqv_spec(other)
    }

    proof fn axiom_eqv_reflexive(a: Self) {}

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {}

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {
        Self::lemma_denom_pos(b);
        assert(a.num * c.denom() == c.num * a.denom()) by (nonlinear_arith)
            requires
                a.num * b.denom() == b.num * a.denom(),
                b.num * c.denom() == c.num * b.denom(),
                b.denom() > 0,
        ;
    }

    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {}
}

impl AdditiveCommutativeMonoid for Rational {
    open spec fn zero() -> Self {
        Rational::from_int_spec(0)
    }

    open spec fn add(self, other: Self) -> Self {
        self.add_spec(other)
    }

    proof fn axiom_add_commutative(a: Self, b: Self) {
        let ab = a.add_spec(b);
        let ba = b.add_spec(a);
        assert(ab.num == ba.num);
        assert(ab.den == ba.den) by (nonlinear_arith)
            requires
                ab.den == a.den * b.den + a.den + b.den,
                ba.den == b.den * a.den + b.den + a.den,
        ;
        assert(ab == ba);
    }

    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {
        let l = a.add_spec(b).add_spec(c);
        let r = a.add_spec(b.add_spec(c));
        Self::lemma_add_parts(a, b);
        Self::lemma_add_parts(b, c);
        Self::lemma_add_parts(a.add_spec(b), c);
        Self::lemma_add_parts(a, b.add_spec(c));
        //  Both sides over the common denominator da*db*dc.
        assert(l.num == r.num) by (nonlinear_arith)
            requires
                l.num == (a.num * b.denom() + b.num * a.denom()) * c.denom()
                    + c.num * (a.denom() * b.denom()),
                r.num == a.num * (b.denom() * c.denom())
                    + (b.num * c.denom() + c.num * b.denom()) * a.denom(),
        ;
        assert(l.denom() == r.denom()) by (nonlinear_arith)
            requires
                l.denom() == (a.denom() * b.denom()) * c.denom(),
                r.denom() == a.denom() * (b.denom() * c.denom()),
        ;
        //  Same num and same denom means same den (denom is den + 1 cast to int).
        assert(l.den == r.den);
        assert(l == r);
    }

    proof fn axiom_add_zero_right(a: Self) {
        let z = Self::zero();
        let az = a.add_spec(z);
        assert(az.num == a.num) by (nonlinear_arith)
            requires az.num == a.num * 1 + 0 * a.denom(),
        ;
        assert(az.den == a.den) by (nonlinear_arith)
            requires az.den == a.den * 0 + a.den + 0,
        ;
        assert(az == a);
    }

    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {
        let ac = a.add_spec(c);
        let bc = b.add_spec(c);
        Self::lemma_add_parts(a, c);
        Self::lemma_add_parts(b, c);
        Self::lemma_denom_pos(a);
        Self::lemma_denom_pos(b);
        Self::lemma_denom_pos(c);
        assert(ac.num * bc.denom() == bc.num * ac.denom()) by (nonlinear_arith)
            requires
                a.num * b.denom() == b.num * a.denom(),
                ac.num == a.num * c.denom() + c.num * a.denom(),
                bc.num == b.num * c.denom() + c.num * b.denom(),
                ac.denom() == a.denom() * c.denom(),
                bc.denom() == b.denom() * c.denom(),
        ;
    }
}

impl AdditiveGroup for Rational {
    open spec fn neg(self) -> Self {
        self.neg_spec()
    }

    open spec fn sub(self, other: Self) -> Self {
        self.sub_spec(other)
    }

    proof fn axiom_add_inverse_right(a: Self) {
        let s = a.add_spec(a.neg_spec());
        assert(s.num == 0) by (nonlinear_arith)
            requires s.num == a.num * a.denom() + (-a.num) * a.denom(),
        ;
        assert(s.num * 1 == 0 * s.denom()) by (nonlinear_arith)
            requires s.num == 0,
        ;
    }

    proof fn axiom_sub_is_add_neg(a: Self, b: Self) {}

    proof fn axiom_neg_congruence(a: Self, b: Self) {
        assert((-a.num) * b.denom() == (-b.num) * a.denom()) by (nonlinear_arith)
            requires a.num * b.denom() == b.num * a.denom(),
        ;
    }
}

impl Ring for Rational {
    open spec fn one() -> Self {
        Rational::from_int_spec(1)
    }

    open spec fn mul(self, other: Self) -> Self {
        self.mul_spec(other)
    }

    proof fn axiom_mul_commutative(a: Self, b: Self) {
        let ab = a.mul_spec(b);
        let ba = b.mul_spec(a);
        assert(ab.num == ba.num) by (nonlinear_arith)
            requires
                ab.num == a.num * b.num,
                ba.num == b.num * a.num,
        ;
        assert(ab.den == ba.den) by (nonlinear_arith)
            requires
                ab.den == a.den * b.den + a.den + b.den,
                ba.den == b.den * a.den + b.den + a.den,
        ;
        assert(ab == ba);
    }

    proof fn axiom_mul_associative(a: Self, b: Self, c: Self) {
        let l = a.mul_spec(b).mul_spec(c);
        let r = a.mul_spec(b.mul_spec(c));
        Self::lemma_mul_parts(a, b);
        Self::lemma_mul_parts(b, c);
        Self::lemma_mul_parts(a.mul_spec(b), c);
        Self::lemma_mul_parts(a, b.mul_spec(c));
        assert(l.num == r.num) by (nonlinear_arith)
            requires
                l.num == (a.num * b.num) * c.num,
                r.num == a.num * (b.num * c.num),
        ;
        assert(l.denom() == r.denom()) by (nonlinear_arith)
            requires
                l.denom() == (a.denom() * b.denom()) * c.denom(),
                r.denom() == a.denom() * (b.denom() * c.denom()),
        ;
        assert(l.den == r.den);
        assert(l == r);
    }

    proof fn axiom_mul_one_right(a: Self) {
        let a1 = a.mul_spec(Self::one());
        assert(a1.num == a.num) by (nonlinear_arith)
            requires a1.num == a.num * 1,
        ;
        assert(a1.den == a.den) by (nonlinear_arith)
            requires a1.den == a.den * 0 + a.den + 0,
        ;
        assert(a1 == a);
    }

    proof fn axiom_mul_zero_right(a: Self) {
        let s = a.mul_spec(Self::zero());
        assert(s.num == 0) by (nonlinear_arith)
            requires s.num == a.num * 0,
        ;
        assert(s.num * 1 == 0 * s.denom()) by (nonlinear_arith)
            requires s.num == 0,
        ;
    }

    proof fn axiom_mul_distributes_left(a: Self, b: Self, c: Self) {
        let l = a.mul_spec(b.add_spec(c));
        let r = a.mul_spec(b).add_spec(a.mul_spec(c));
        Self::lemma_add_parts(b, c);
        Self::lemma_mul_parts(a, b.add_spec(c));
        Self::lemma_mul_parts(a, b);
        Self::lemma_mul_parts(a, c);
        Self::lemma_add_parts(a.mul_spec(b), a.mul_spec(c));
        //  l = (a.num * (b.num*dc + c.num*db)) / (da*db*dc)
        //  r = (a.num*b.num*(da*dc) + a.num*c.num*(da*db)) / (da*db*da*dc)
        //  r is exactly l scaled by da in both numerator and denominator,
        //  so prove the scaling equations separately (low degree), then
        //  cross-multiply with num/denom as opaque atoms.
        Self::lemma_distrib_scale(a.num, b.num, c.num, a.denom(), b.denom(), c.denom());
        assert(r.num == a.denom() * l.num);
        assert(r.denom() == a.denom() * l.denom()) by (nonlinear_arith)
            requires
                l.denom() == a.denom() * (b.denom() * c.denom()),
                r.denom() == (a.denom() * b.denom()) * (a.denom() * c.denom()),
        ;
        assert(l.num * r.denom() == r.num * l.denom()) by (nonlinear_arith)
            requires
                r.num == a.denom() * l.num,
                r.denom() == a.denom() * l.denom(),
        ;
    }

    proof fn axiom_one_ne_zero() {}

    proof fn axiom_mul_congruence_left(a: Self, b: Self, c: Self) {
        let ac = a.mul_spec(c);
        let bc = b.mul_spec(c);
        Self::lemma_mul_parts(a, c);
        Self::lemma_mul_parts(b, c);
        assert(ac.num * bc.denom() == bc.num * ac.denom()) by (nonlinear_arith)
            requires
                a.num * b.denom() == b.num * a.denom(),
                ac.num == a.num * c.num,
                bc.num == b.num * c.num,
                ac.denom() == a.denom() * c.denom(),
                bc.denom() == b.denom() * c.denom(),
        ;
    }
}

impl PartialOrder for Rational {
    open spec fn le(self, other: Self) -> bool {
        self.le_spec(other)
    }

    proof fn axiom_le_reflexive(a: Self) {}

    proof fn axiom_le_antisymmetric(a: Self, b: Self) {}

    proof fn axiom_le_transitive(a: Self, b: Self, c: Self) {
        Self::lemma_denom_pos(b);
        assert(a.num * c.denom() <= c.num * a.denom()) by (nonlinear_arith)
            requires
                a.num * b.denom() <= b.num * a.denom(),
                b.num * c.denom() <= c.num * b.denom(),
                a.denom() > 0,
                b.denom() > 0,
                c.denom() > 0,
        ;
    }

    proof fn axiom_le_congruence(a1: Self, a2: Self, b1: Self, b2: Self) {
        Self::lemma_denom_pos(a1);
        Self::lemma_denom_pos(a2);
        Self::lemma_denom_pos(b1);
        Self::lemma_denom_pos(b2);
        assert(a2.num * b2.denom() <= b2.num * a2.denom()) by (nonlinear_arith)
            requires
                a1.num * a2.denom() == a2.num * a1.denom(),
                b1.num * b2.denom() == b2.num * b1.denom(),
                a1.num * b1.denom() <= b1.num * a1.denom(),
                a1.denom() > 0,
                a2.denom() > 0,
                b1.denom() > 0,
                b2.denom() > 0,
        ;
    }
}

impl OrderedRing for Rational {
    open spec fn lt(self, other: Self) -> bool {
        self.lt_spec(other)
    }

    proof fn axiom_le_total(a: Self, b: Self) {}

    proof fn axiom_lt_iff_le_and_not_eqv(a: Self, b: Self) {}

    proof fn axiom_le_add_monotone(a: Self, b: Self, c: Self) {
        let ac = a.add_spec(c);
        let bc = b.add_spec(c);
        Self::lemma_add_parts(a, c);
        Self::lemma_add_parts(b, c);
        Self::lemma_denom_pos(a);
        Self::lemma_denom_pos(b);
        Self::lemma_denom_pos(c);
        assert(ac.num * bc.denom() <= bc.num * ac.denom()) by (nonlinear_arith)
            requires
                a.num * b.denom() <= b.num * a.denom(),
                ac.num == a.num * c.denom() + c.num * a.denom(),
                bc.num == b.num * c.denom() + c.num * b.denom(),
                ac.denom() == a.denom() * c.denom(),
                bc.denom() == b.denom() * c.denom(),
                c.denom() > 0,
        ;
    }

    proof fn axiom_le_mul_nonneg_monotone(a: Self, b: Self, c: Self) {
        let ac = a.mul_spec(c);
        let bc = b.mul_spec(c);
        Self::lemma_mul_parts(a, c);
        Self::lemma_mul_parts(b, c);
        Self::lemma_denom_pos(c);
        //  zero.le(c) unfolds to 0 * c.denom() <= c.num * 1, i.e. c.num >= 0.
        assert(c.num >= 0) by (nonlinear_arith)
            requires 0 * c.denom() <= c.num * 1,
        ;
        assert(ac.num * bc.denom() <= bc.num * ac.denom()) by (nonlinear_arith)
            requires
                a.num * b.denom() <= b.num * a.denom(),
                c.num >= 0,
                ac.num == a.num * c.num,
                bc.num == b.num * c.num,
                ac.denom() == a.denom() * c.denom(),
                bc.denom() == b.denom() * c.denom(),
                c.denom() > 0,
        ;
    }
}

impl Field for Rational {
    open spec fn recip(self) -> Self {
        self.reciprocal_spec()
    }

    open spec fn div(self, other: Self) -> Self {
        self.div_spec(other)
    }

    proof fn axiom_mul_recip_right(a: Self) {
        Self::lemma_eqv_zero_iff_num_zero(a);
        let r = a.reciprocal_spec();
        let p = a.mul_spec(r);
        Self::lemma_mul_parts(a, r);
        if a.num > 0 {
            //  r = denom(a) / a.num
            assert(r.denom() == a.num);
            assert(p.num * 1 == 1 * p.denom()) by (nonlinear_arith)
                requires
                    p.num == a.num * a.denom(),
                    p.denom() == a.denom() * a.num,
            ;
        } else {
            assert(a.num < 0);
            //  r = -denom(a) / (-a.num)
            assert(r.denom() == -a.num);
            assert(p.num * 1 == 1 * p.denom()) by (nonlinear_arith)
                requires
                    p.num == a.num * (-a.denom()),
                    p.denom() == a.denom() * (-a.num),
            ;
        }
    }

    proof fn axiom_div_is_mul_recip(a: Self, b: Self) {}

    proof fn axiom_recip_congruence(a: Self, b: Self) {
        Self::lemma_eqv_zero_iff_num_zero(a);
        Self::lemma_eqv_zero_iff_num_zero(b);
        Self::lemma_denom_pos(a);
        Self::lemma_denom_pos(b);
        //  Signs of a.num and b.num agree, and b.num != 0.
        if b.num == 0 {
            assert(a.num == 0) by (nonlinear_arith)
                requires
                    a.num * b.denom() == b.num * a.denom(),
                    b.num == 0,
                    b.denom() > 0,
            ;
            assert(false);
        }
        if a.num > 0 {
            assert(b.num > 0) by (nonlinear_arith)
                requires
                    a.num * b.denom() == b.num * a.denom(),
                    a.num > 0,
                    a.denom() > 0,
                    b.denom() > 0,
            ;
            let ra = a.reciprocal_spec();
            let rb = b.reciprocal_spec();
            assert(ra.denom() == a.num);
            assert(rb.denom() == b.num);
            assert(ra.num * rb.denom() == rb.num * ra.denom()) by (nonlinear_arith)
                requires
                    a.num * b.denom() == b.num * a.denom(),
                    ra.num == a.denom(),
                    rb.num == b.denom(),
                    ra.denom() == a.num,
                    rb.denom() == b.num,
            ;
        } else {
            assert(a.num < 0);
            assert(b.num < 0) by (nonlinear_arith)
                requires
                    a.num * b.denom() == b.num * a.denom(),
                    a.num < 0,
                    a.denom() > 0,
                    b.denom() > 0,
            ;
            let ra = a.reciprocal_spec();
            let rb = b.reciprocal_spec();
            assert(ra.denom() == -a.num);
            assert(rb.denom() == -b.num);
            assert(ra.num * rb.denom() == rb.num * ra.denom()) by (nonlinear_arith)
                requires
                    a.num * b.denom() == b.num * a.denom(),
                    ra.num == -a.denom(),
                    rb.num == -b.denom(),
                    ra.denom() == -a.num,
                    rb.denom() == -b.num,
            ;
        }
    }
}

impl OrderedField for Rational {}

} //  verus!
