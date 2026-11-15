import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every Proj point lies in a basic open defined by a nonzero positive-degree homogeneous element. -/
theorem s2_proj_exists_homogeneous_basicOpen {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (p : Proj 𝒜) :
    ∃ (n : ℕ) (_ : 0 < n) (a : A), a ∈ 𝒜 n ∧ a ≠ 0 ∧ p ∈ Proj.basicOpen 𝒜 a := by
  change _root_.ProjectiveSpectrum 𝒜 at p
  have hex : ∃ (n : ℕ), 0 < n ∧ ∃ a : A, a ∈ 𝒜 n ∧ a ∉ p.asHomogeneousIdeal := by
    by_contra! h
    exact p.not_irrelevant_le ((HomogeneousIdeal.irrelevant_le 𝒜).mpr
      (fun n hn a ha => h n hn a ha))
  obtain ⟨n, hn, a, ha, hnot⟩ := hex
  refine ⟨n, hn, a, ha, ?_, hnot⟩
  intro ha0
  exact hnot (ha0 ▸ p.asHomogeneousIdeal.zero_mem)

end HodgeLean.Foundations.Program
