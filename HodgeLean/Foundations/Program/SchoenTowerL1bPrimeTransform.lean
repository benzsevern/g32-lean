import HodgeLean.Foundations.Program.SchoenTowerL1bTransformLocality

/-! Exact reduced-transform ideals on prime affine charts.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Removing a centre that does not contain the generic point leaves the same prime divisor. -/
theorem s2v_l1b_prime_divisor_dense {R : Type*} [CommRing R]
    (P K : Ideal R) [P.IsPrime] (hK : ¬ K ≤ P) :
    closure (PrimeSpectrum.zeroLocus (P : Set R) \
      PrimeSpectrum.zeroLocus (K : Set R)) = PrimeSpectrum.zeroLocus (P : Set R) := by
  apply Set.Subset.antisymm
  · exact closure_minimal Set.sdiff_subset (PrimeSpectrum.isClosed_zeroLocus _)
  · have hs : ({(⟨P, inferInstance⟩ : PrimeSpectrum R)} : Set (PrimeSpectrum R)) ⊆
        PrimeSpectrum.zeroLocus (P : Set R) \
          PrimeSpectrum.zeroLocus (K : Set R) := by
      intro p hp
      have hp' : p = (⟨P, inferInstance⟩ : PrimeSpectrum R) := Set.mem_singleton_iff.mp hp
      subst p
      change (P : Set R) ⊆ P ∧ ¬ (K : Set R) ⊆ P
      exact ⟨Set.Subset.rfl, hK⟩
    simpa only [PrimeSpectrum.closure_singleton] using closure_mono hs

end HodgeLean.Foundations.Program
