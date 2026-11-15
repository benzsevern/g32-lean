import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.Algebra.Algebra.Tower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The canonical adic map preserves the actual cotangent module of a finitely generated ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
def s2e_adic_ideal_cotangent_equiv
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (I : Ideal R) (hI : I.FG) :
    I.Cotangent ≃ₗ[k] (I.map (algebraMap R (AdicCompletion I R))).Cotangent := by
  let A := AdicCompletion I R
  let J := I.map (algebraMap R A)
  let φ := IsScalarTower.toAlgHom k R A
  let f := Ideal.mapCotangent I J φ Ideal.le_comap_map
  have hmem (n : ℕ) (x : A) : x ∈ J ^ n ↔ x.val n = 0 := by
    change x ∈ (I.map (algebraMap R A)) ^ n ↔ _
    rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval hI]
    rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    change J.toCotangent ⟨algebraMap R A x.val, _⟩ = 0 at hx
    have h := (hmem 2 _).mp ((J.toCotangent_eq_zero _).mp hx)
    have hx2 : x.val ∈ I ^ 2 := by
      change Ideal.Quotient.mk (I ^ 2 • ⊤ : Ideal R) x.val = 0 at h
      simpa only [smul_eq_mul, Ideal.mul_top, Ideal.Quotient.eq_zero_iff_mem] using h
    exact (I.toCotangent_eq_zero x).mpr hx2
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨y, rfl⟩ := J.toCotangent_surjective y
    obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (y.val.val 2)
    have hy1 : y.val.val 1 = 0 := (hmem 1 y.val).mp (by simpa only [pow_one] using y.property)
    have hc := y.val.property (Nat.le_succ 1)
    have hrI : r ∈ I := by
      rw [← hr, hy1] at hc
      change Ideal.Quotient.mk (I ^ 1 • ⊤ : Ideal R) r = 0 at hc
      simpa only [smul_eq_mul, Ideal.mul_top, pow_one, Ideal.Quotient.eq_zero_iff_mem] using hc
    refine ⟨I.toCotangent ⟨r, hrI⟩, ?_⟩
    change J.toCotangent ⟨algebraMap R A r, _⟩ = J.toCotangent y
    apply J.toCotangent_eq.mpr
    apply (hmem 2 _).mpr
    change (AdicCompletion.of I R r).val 2 - y.val.val 2 = 0
    exact sub_eq_zero.mpr hr
  exact LinearEquiv.ofBijective f ⟨hinj, hsurj⟩

#print axioms s2e_adic_ideal_cotangent_equiv
end HodgeLean.Foundations.Program
