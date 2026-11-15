import HodgeLean.Foundations.Program.SchoenTowerPointJets
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- A denominator nonzero at a field-valued point has an inverse modulo the square of its kernel.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3, localization. -/
theorem s2t_inverse_point_jet {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (φ : A →ₐ[K] K) (s : A) (hs : φ s ≠ 0) :
    ∃ v : A, s * v - 1 ∈ RingHom.ker φ.toRingHom ^ 2 := by
  let w := algebraMap K A (φ s)⁻¹
  have hz : 1 - w * s ∈ RingHom.ker φ.toRingHom := by
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      map_sub, map_one, map_mul, w, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, inv_mul_cancel₀ hs, sub_self]
  refine ⟨w * (2 - w * s), ?_⟩
  have hsq := Ideal.pow_mem_pow hz 2
  have heq : s * (w * (2 - w * s)) - 1 = -(1 - w * s) ^ 2 := by ring
  rw [heq]
  exact Submodule.neg_mem _ hsq

/-- Every element of a localization at a field-valued point has a global representative to
first order at that point.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3, localization. -/
theorem s2t_localization_point_jet_lift {K A B : Type*}
    [Field K] [CommRing A] [CommRing B] [Algebra K A] (φ : A →ₐ[K] K)
    [(RingHom.ker φ.toRingHom).IsPrime] [Algebra A B]
    [IsLocalization (RingHom.ker φ.toRingHom).primeCompl B] (t : B) :
    ∃ a : A, algebraMap A B a - t ∈
      (Ideal.map (algebraMap A B) (RingHom.ker φ.toRingHom)) ^ 2 := by
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (RingHom.ker φ.toRingHom).primeCompl t
  have hs : φ s ≠ 0 := by
    simpa only [Ideal.mem_primeCompl_iff, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] using s.property
  obtain ⟨v, hv⟩ := s2t_inverse_point_jet φ s hs
  have hf : algebraMap A B (s * v - 1) ∈
      (Ideal.map (algebraMap A B) (RingHom.ker φ.toRingHom)) ^ 2 := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hv
  refine ⟨a * v, ?_⟩
  have heq : algebraMap A B (a * v) - t = t * algebraMap A B (s * v - 1) := by
    rw [map_sub, map_mul, map_mul, map_one, ← h]
    ring
  rw [heq]
  exact Ideal.mul_mem_left _ t hf

end HodgeLean.Foundations.Program
