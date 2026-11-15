import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelCoclassOverlap
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelZeroSupport
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.RelativeCohomologySheaf

/-! # Local purity of the original kernel zero support -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicTopology.Singular CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Arbitrarily small actual zero-support neighborhoods have no relative cohomology off the complex normal degree. -/
theorem normalKernelZeroSupport_exists_relativeCohomology_vanishing (k : ℕ)
    (v : ProjectiveNormalTotalSpace k) (U : Opens (ProjectiveNormalTotalSpace k)) (hvU : v ∈ U) :
    ∃ W : Opens (ProjectiveNormalTotalSpace k), W ≤ U ∧ v ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * k →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ProjectiveNormalTotalSpace k))
            {w | w.1.2 = 0}) n)) := by
  by_cases hv : v.1.2 = 0
  · obtain ⟨j, hj⟩ := normalCoordinateKernelChart_cover k v
    let e := (normalCoordinateKernelChart k j).restrOpen U U.isOpen
    have he : v ∈ e.source := ⟨hj, hvU⟩
    have hS : ∀ w ∈ e.source, w ∈ {w : ProjectiveNormalTotalSpace k | w.1.2 = 0} ↔
        (e w).2 = 0 := fun w hw => normalCoordinateKernelChart_support k j w hw.1
    have h0 : (e v).2 = 0 := (hS v he).mp hv
    let W := flattenedSupportNeighborhood (Fin k → ℂ) k e v he
    refine ⟨W, (fun w hw => (flattenedSupportNeighborhood_subset_source
      (Fin k → ℂ) k e v he hw).2), mem_flattenedSupportNeighborhood (Fin k → ℂ) k e v he, ?_⟩
    intro n hn
    exact relativeCohomology_isZero ℚ _ n
      ((standardComplexLocalHomology_isZero_of_ne k n hn).of_iso
        (flattenedSupportRelativeHomologyIso (Fin k → ℂ) k e v he _ hS h0 n))
  · let W : Opens (ProjectiveNormalTotalSpace k) :=
      U ⊓ ⟨{w : ProjectiveNormalTotalSpace k | w.1.2 = 0}ᶜ,
        (isClosed_normalKernelZeroSection k).isOpen_compl⟩
    refine ⟨W, inf_le_left, ⟨hvU, hv⟩, ?_⟩
    intro n hn
    letI := neighborhoodSupportRelativeCohomology_subsingleton
      (TopCat.of (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0} n W (fun w hw => hw.2)
    exact ModuleCat.isZero_of_subsingleton _

#print axioms normalKernelZeroSupport_exists_relativeCohomology_vanishing
end HodgeLean.Foundations.Program.G32Native.EulerModel
