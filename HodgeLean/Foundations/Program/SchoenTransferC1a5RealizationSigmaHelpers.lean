import HodgeLean.Foundations.Program.SchoenTransferC1a5SigmaCollarHelpers
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-! Literal realization coproduct identifications and their naturality.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- The actual realization of a coproduct identifies with the disjoint union of realizations.
Source: Mathlib sigmaComparison and TopCat.sigmaIsoSigma. -/
def c1a5_realization_sigma_iso {I : Type} (K : I → SSet.{0}) :
    SSet.toTop.obj (∐ K) ≅ TopCat.of (Σ i, SSet.toTop.obj (K i)) :=
  (asIso (sigmaComparison SSet.toTop K)).symm ≪≫
    TopCat.sigmaIsoSigma (fun i ↦ SSet.toTop.obj (K i))

example {I : Type} (K : I → SSet.{0}) := c1a5_realization_sigma_iso K

/-- The coproduct realization isomorphism retains each literal realized summand inclusion.
Source: Mathlib ι_comp_sigmaComparison and TopCat.sigmaIsoSigma_hom_ι. -/
@[reassoc]
lemma c1a5_realization_sigma_iso_inclusion {I : Type} (K : I → SSet.{0}) (i : I) :
    SSet.toTop.map (Sigma.ι K i) ≫ (c1a5_realization_sigma_iso K).hom =
      TopCat.sigmaι (fun i ↦ SSet.toTop.obj (K i)) i := by
  rw [← ι_comp_sigmaComparison SSet.toTop K i]
  simp only [c1a5_realization_sigma_iso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  change Sigma.ι (fun i ↦ SSet.toTop.obj (K i)) i ≫
    (asIso (sigmaComparison SSet.toTop K)).hom ≫
    (asIso (sigmaComparison SSet.toTop K)).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]
  exact TopCat.sigmaIsoSigma_hom_ι _ _

/-- The actual realization coproduct isomorphisms commute with the actual disjoint-union map.
Source: Mathlib coproduct universal property and the literal realized summand inclusions. -/
lemma c1a5_realization_sigma_iso_naturality {I : Type} {K L : I → SSet.{0}}
    (f : ∀ i, K i ⟶ L i) :
    SSet.toTop.map (CategoryTheory.Limits.Sigma.map f) ≫ (c1a5_realization_sigma_iso L).hom =
      (c1a5_realization_sigma_iso K).hom ≫ c1a5_sigma_map (fun i ↦ SSet.toTop.map (f i)) := by
  apply (cancel_epi (sigmaComparison SSet.toTop K)).1
  apply Sigma.hom_ext
  intro i
  rw [ι_comp_sigmaComparison_assoc]
  rw [← SSet.toTop.map_comp_assoc, CategoryTheory.Limits.Sigma.ι_map]
  rw [SSet.toTop.map_comp, Category.assoc, c1a5_realization_sigma_iso_inclusion]
  rw [← Category.assoc, ι_comp_sigmaComparison, c1a5_realization_sigma_iso_inclusion_assoc]
  rfl

end HodgeLean.Foundations.Program
