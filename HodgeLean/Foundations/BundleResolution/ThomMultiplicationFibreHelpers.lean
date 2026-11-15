import HodgeLean.Foundations.BundleResolution.ChernNormalPointCupHelpers
import HodgeLean.Foundations.BundleResolution.ChernThomMultiplicationHelpers
import HodgeLean.Foundations.BundleResolution.ChernRelativeCupPullbackHelpers
import HodgeLean.Foundations.BundleResolution.ComplexBundleThomFibreHelpers

/-! # Actual fibre restriction of independently selected Thom multiplication

The original fibre inclusion followed by the bundle projection is the
constant map at its base point.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Bundle AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom HodgeLean.RealDefs
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {k : ℕ} (E : I1ComplexBundle B k)
variable (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) E.fibre)) [e.IsLinear ℂ]
variable (b : B) (hb : b ∈ e.baseSet)

theorem i1_complexBundleThomMultiplication_fibre_zeroDegree
    (α : Cohomology ℚ (TopCat.of B) 0) :
    relativeCohomologyMap ℚ (2 * k) (i1_complexBundleFibrePairMap E e b hb)
      (i1_complexBundleThomMultiplication E 0 α) =
      i1_normalPointCupMap k
        (cohomologyMap ℚ 0 (TopCat.ofHom (ContinuousMap.const PUnit b)) α) := by
  let f := i1_complexBundleFibrePairMap E e b hb
  have hs : TopPair.Hom.fst f ≫ TopCat.ofHom (i1_complexBundleTotalProjection E) =
      TopCat.ofHom (ContinuousMap.const (Fin k → ℂ) PUnit.unit) ≫
        TopCat.ofHom (ContinuousMap.const PUnit b) := by
    apply ConcreteCategory.hom_ext
    intro w
    rfl
  have hα : cohomologyMap ℚ 0 (TopPair.Hom.fst f)
      (cohomologyMap ℚ 0 (TopCat.ofHom (i1_complexBundleTotalProjection E)) α) =
      cohomologyMap ℚ 0 (TopCat.ofHom (ContinuousMap.const (Fin k → ℂ) PUnit.unit))
        (cohomologyMap ℚ 0 (TopCat.ofHom (ContinuousMap.const PUnit b)) α) := by
    calc
      _ = cohomologyMap ℚ 0
          (TopPair.Hom.fst f ≫ TopCat.ofHom (i1_complexBundleTotalProjection E)) α :=
        (LinearMap.congr_fun (cohomologyMap_comp ℚ 0 (TopPair.Hom.fst f)
          (TopCat.ofHom (i1_complexBundleTotalProjection E))) α).symm
      _ = cohomologyMap ℚ 0
          (TopCat.ofHom (ContinuousMap.const (Fin k → ℂ) PUnit.unit) ≫
            TopCat.ofHom (ContinuousMap.const PUnit b)) α :=
        congrArg (fun g => cohomologyMap ℚ 0 g α) hs
      _ = _ := LinearMap.congr_fun (cohomologyMap_comp ℚ 0
        (TopCat.ofHom (ContinuousMap.const (Fin k → ℂ) PUnit.unit))
        (TopCat.ofHom (ContinuousMap.const PUnit b))) α
  have hn := i1_relativeCup_naturality f (2 * k) 0 (i1_bundleThom k E.fibre)
    (cohomologyMap ℚ 0 (TopCat.ofHom (i1_complexBundleTotalProjection E)) α)
  exact hn.trans (congrArg₂
    (fun u v => i1_relativeCup (puncturedPair ℂ k) (2 * k) 0 u v)
    (i1_complexBundleThom_fibre E e b hb) hα)

end HodgeLean.Foundations.BundleResolution
