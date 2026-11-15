import HodgeLean.Foundations.BundleThom.ImmersionDefs
import HodgeLean.Foundations.AlgebraicTopology.RelativeCohomology.ProductTrace

/-! # Chartwise normalization detects a pulled-back complex Thom class -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

/-- A pullback with the complex chart normalization is the selected Thom class.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, uniqueness
of the normalized Thom class. -/
theorem bundleThom_pullback_of_chart_normalization
    {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    {A : TopPair}
    (F : TopPair.ofSubset (X := i1_totalSpace k E) (i1_zeroSupport k E)ᶜ ⟶ A)
    (u : RelativeCohomology ℚ A (2 * k))
    (hnormalized : ∀ (e : Trivialization (Fin k → ℂ)
      (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B)) (he : e.IsLinear ℂ),
      relativeCohomologyMap ℚ (2 * k) (i1_chartInclusion k E e ≫ F) u =
        i1_chartOrientation k E e) :
    relativeCohomologyMap ℚ (2 * k) F u = i1_bundleThom k E := by
  apply (i1_bundleThom_exists_unique k E).unique
  · intro e he
    have h := hnormalized e he
    rw [relativeCohomologyMap_comp, LinearMap.comp_apply] at h
    exact h
  · exact Classical.choose_spec (i1_bundleThom_exists_unique k E).exists

/-- A zero-section square transports Euler after the supported Thom comparison.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, Euler as
zero-section pullback; Hatcher, Algebraic Topology, §3.1, relative naturality. -/
theorem bundleEuler_of_supported_pullback
    {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    (k : ℕ) (E : B → Type)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    {A : TopPair} {X : TopCat}
    (F : TopPair.ofSubset (X := i1_totalSpace k E) (i1_zeroSupport k E)ᶜ ⟶ A)
    (b : TopCat.of B ⟶ X) (z : X ⟶ A.fst)
    (u : RelativeCohomology ℚ A (2 * k))
    (hzero : TopCat.ofHom (i1_zeroSection k E) ≫ TopPair.Hom.fst F = b ≫ z)
    (hclass : relativeCohomologyMap ℚ (2 * k) F u = i1_bundleThom k E) :
    i1_bundleEuler k E = cohomologyMap ℚ (2 * k) b
      (cohomologyMap ℚ (2 * k) z (relativeCohomologyToAbsolute ℚ A (2 * k) u)) := by
  have hnat := RelativeTrace.forget_naturality F (2 * k) u
  have he : forgetSupport ℚ (i1_totalSpace k E) (i1_zeroSupport k E) (2 * k)
      (i1_bundleThom k E) =
      cohomologyMap ℚ (2 * k) (TopPair.Hom.fst F)
        (relativeCohomologyToAbsolute ℚ A (2 * k) u) := by
    rw [← hclass]
    exact hnat
  unfold i1_bundleEuler i1_zeroPullback
  rw [LinearMap.comp_apply, he]
  have hl := LinearMap.congr_fun (cohomologyMap_comp ℚ (2 * k)
    (TopCat.ofHom (i1_zeroSection k E)) (TopPair.Hom.fst F))
    (relativeCohomologyToAbsolute ℚ A (2 * k) u)
  have hr := LinearMap.congr_fun (cohomologyMap_comp ℚ (2 * k) b z)
    (relativeCohomologyToAbsolute ℚ A (2 * k) u)
  rw [hzero] at hl
  exact hl.symm.trans hr

#print axioms bundleEuler_of_supported_pullback
#print axioms bundleThom_pullback_of_chart_normalization
end HodgeLean.Foundations.BundleThom
