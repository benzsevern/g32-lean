import HodgeLean.Foundations.BundleResolution.ChernNormalProductThomHelpers
import HodgeLean.Foundations.BundleResolution.ChernNormalProductSwapHelpers
import HodgeLean.Foundations.BundleThom.RelativePairIsoCoclassHelpers

/-! # Actual Thom multiplication in base-first normal coordinates

The fixed normal-pair coordinates used by bundle charts carry the same
actual multiplication as the relative Kunneth product coordinates.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular HodgeLean.Foundations.BundleThom HodgeLean.RealDefs
namespace HodgeLean.Foundations.BundleResolution

def i1_productNormalThomMultiplication (k : ℕ) (Y : TopCat) (n : ℕ) :
    Cohomology ℚ Y n →ₗ[ℚ] RelativeCohomology ℚ (i1_productNormalPair Y k) (2 * k + n) :=
  (i1_relativeCup (i1_productNormalPair Y k) (2 * k) n
    (relativeCohomologyMap ℚ (2 * k) (i1_productNormalProjection Y k)
      (normalizedPointCoclass k))).comp
    (cohomologyMap ℚ n (productFirst Y (TopCat.of (Fin k → ℂ))))

theorem i1_productNormalThomMultiplication_swap (k : ℕ) (Y : TopCat) (n : ℕ)
    (α : Cohomology ℚ Y n) :
    relativeCohomologyMap ℚ (2 * k + n) (i1_normalProductPairSwap k Y).hom
      (i1_productNormalThomMultiplication k Y n α) = i1_normalProductThomMultiplication k Y n α := by
  have hn : relativeCohomologyMap ℚ (2 * k) (i1_normalProductPairSwap k Y).hom
      (relativeCohomologyMap ℚ (2 * k) (i1_productNormalProjection Y k) (normalizedPointCoclass k)) =
    relativeCohomologyMap ℚ (2 * k) (i1_relativeProductFirst (puncturedPair ℂ k) Y)
      (normalizedPointCoclass k) := by
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
      i1_normalProductPairSwap_comp_projection]
  have hb : cohomologyMap ℚ n (TopPair.Hom.fst (i1_normalProductPairSwap k Y).hom)
      (cohomologyMap ℚ n (productFirst Y (TopCat.of (Fin k → ℂ))) α) =
    cohomologyMap ℚ n (productSecond (puncturedPair ℂ k).fst Y) α := by
    have h := congrArg (fun l => l α) (cohomologyMap_comp ℚ n
      (TopPair.Hom.fst (i1_normalProductPairSwap k Y).hom)
      (productFirst Y (TopCat.of (Fin k → ℂ))))
    exact h.symm.trans (congrArg (fun f => cohomologyMap ℚ n f α)
      (i1_normalProductPairSwap_comp_base k Y))
  simp only [i1_productNormalThomMultiplication, i1_normalProductThomMultiplication, LinearMap.comp_apply]
  exact (i1_relativeCup_naturality (i1_normalProductPairSwap k Y).hom (2 * k) n
    (relativeCohomologyMap ℚ (2 * k) (i1_productNormalProjection Y k) (normalizedPointCoclass k))
    (cohomologyMap ℚ n (productFirst Y (TopCat.of (Fin k → ℂ))) α)).trans
      (congrArg₂ (fun u v => i1_relativeCup (i1_relativeProductPair (puncturedPair ℂ k) Y)
        (2 * k) n u v) hn hb)

theorem i1_productNormalThomMultiplication_bijective (k : ℕ) (Y : TopCat) (n : ℕ) :
    Function.Bijective (i1_productNormalThomMultiplication k Y n) := by
  have hf := i1_relativeCohomologyMap_iso_injective (i1_normalProductPairSwap k Y) (2 * k + n)
  have ht := i1_normalProductThomMultiplication_bijective k Y n
  constructor
  · intro α β h
    apply ht.1
    exact (i1_productNormalThomMultiplication_swap k Y n α).symm.trans
      ((congrArg (relativeCohomologyMap ℚ (2 * k + n) (i1_normalProductPairSwap k Y).hom) h).trans
        (i1_productNormalThomMultiplication_swap k Y n β))
  · intro y
    obtain ⟨α, hα⟩ := ht.2
      (relativeCohomologyMap ℚ (2 * k + n) (i1_normalProductPairSwap k Y).hom y)
    refine ⟨α, hf ?_⟩
    exact (i1_productNormalThomMultiplication_swap k Y n α).trans hα

end HodgeLean.Foundations.BundleResolution
