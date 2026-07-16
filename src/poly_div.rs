///  Polynomial division with remainder over a Field.
///
///  `divmod(a, b)` returns (q, r) with  a ≡ q·b + r  (peqv) and
///  len(r) < len(b), for any divisor with a non-eqv-zero leading
///  coefficient. The quotient is built positionally — `pad(q1, s).push(f)`
///  places each new coefficient at its monomial's slot — so correctness
///  needs only push-decomposition and pad absorption from poly_mul, not
///  commutativity/associativity/distributivity of pmul.
///
///  The classical division step: with n = len(a), s = n - len(b),
///  f = lc(a)/lc(b), subtract t = x^s·(f·b) from a. The top coefficient of
///  the difference is eqv-zero (lemma_kill_top), so it can be dropped and
///  the length strictly decreases — that drop is exactly why `peqv` is
///  length-agnostic.
use vstd::prelude::*;
use crate::traits::equivalence::Equivalence;
use crate::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use crate::traits::additive_group::AdditiveGroup;
use crate::traits::ring::Ring;
use crate::traits::field::Field;
use crate::lemmas::*;
use crate::poly::*;
use crate::poly_mul::*;

verus! {

pub proof fn divmod<T: Field>(a: Seq<T>, b: Seq<T>) -> (res: (Seq<T>, Seq<T>))
    requires
        b.len() >= 1,
        !b.last().eqv(T::zero()),
    ensures
        peqv(a, padd(pmul(res.0, b), res.1)),
        res.1.len() < b.len(),
        res.0.len() as int == if a.len() >= b.len() { a.len() - b.len() + 1 } else { 0int },
    decreases a.len(),
{
    if a.len() < b.len() {
        //  Base: quotient 0, remainder a.
        let q = Seq::<T>::empty();
        assert(pmul(q, b) == Seq::<T>::empty());
        lemma_zpoly_empty::<T>();
        lemma_padd_zpoly_left(Seq::<T>::empty(), a);
        lemma_peqv_sym(padd(Seq::<T>::empty(), a), a);
        (q, a)
    } else {
        let n = a.len();
        let s = (n - b.len()) as nat;
        let lb = b.last();
        let la = a.last();
        let f = la.mul(lb.recip());
        //  The term to subtract: t = x^s · (f · b), same length as a.
        let t = shiftk(scale(f, b), s);
        assert(t.len() == n);
        let a2 = psub(a, t);
        assert(a2.len() == n);
        //  The top coefficient of a2 is la - f·lb, which is eqv-zero.
        assert(t[n as int - 1] == f.mul(lb));
        assert(a2[n as int - 1] == la.add(f.mul(lb).neg()));
        lemma_kill_top(la, lb);
        assert(a2.last().eqv(T::zero()));
        //  Drop it and recurse on the strictly shorter polynomial.
        lemma_drop_last_peqv(a2);
        let a3 = a2.drop_last();
        assert(a3.len() == n - 1);
        let (q1, r) = divmod(a3, b);
        //  Place the new coefficient at slot s.
        assert(q1.len() <= s);
        let qq = pad(q1, s).push(f);
        assert(pad(q1, s).len() == s);
        assert(qq.len() == s + 1);

        //  (1) pmul(qq, b) ≡ pmul(q1, b) + t.
        lemma_pmul_push(pad(q1, s), f, b);
        lemma_pmul_pad(q1, s, b);
        lemma_peqv_refl(t);
        lemma_padd_cong(pmul(pad(q1, s), b), pmul(q1, b), t, t);
        lemma_peqv_trans(
            pmul(qq, b),
            padd(pmul(pad(q1, s), b), t),
            padd(pmul(q1, b), t),
        );

        //  (2) a ≡ t + a2 ≡ t + a3 ≡ t + (q1·b + r).
        lemma_precover(a, t);
        lemma_padd_cong(t, t, a2, a3);
        lemma_peqv_trans(a, padd(t, a2), padd(t, a3));
        lemma_padd_cong(t, t, a3, padd(pmul(q1, b), r));
        lemma_peqv_trans(a, padd(t, a3), padd(t, padd(pmul(q1, b), r)));

        //  (3) shuffle: t + (q1·b + r) ≡ (q1·b + t) + r.
        let u = pmul(q1, b);
        lemma_padd_assoc(t, u, r);
        lemma_peqv_sym(padd(padd(t, u), r), padd(t, padd(u, r)));
        lemma_peqv_trans(a, padd(t, padd(u, r)), padd(padd(t, u), r));
        lemma_padd_comm(t, u);
        lemma_peqv_refl(r);
        lemma_padd_cong(padd(t, u), padd(u, t), r, r);
        lemma_peqv_trans(a, padd(padd(t, u), r), padd(padd(u, t), r));

        //  (4) fold back: (q1·b + t) ≡ qq·b.
        lemma_peqv_sym(pmul(qq, b), padd(u, t));
        lemma_padd_cong(padd(u, t), pmul(qq, b), r, r);
        lemma_peqv_trans(a, padd(padd(u, t), r), padd(pmul(qq, b), r));

        (qq, r)
    }
}

} //  verus!
