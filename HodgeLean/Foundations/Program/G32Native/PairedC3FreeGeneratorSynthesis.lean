import HodgeLean.Foundations.Program.G32Native.PairedC3FiniteFrameCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedC3FreeSectionCoordinates

/-! # Finite synthesis in the canonical free-sheaf generators -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
variable {X : Scheme.{0}} {σ : Type} [Fintype σ]

/-- The original section of the free summand at its specified label. -/
def pairedC3FreeGenerator (X : Scheme.{0}) (σ : Type) (V : X.Opens) (b : σ) :
    Γ((SheafOfModules.free (R := X.ringCatSheaf) σ : X.Modules), V) :=
  Scheme.Modules.Hom.app (X := X) (SheafOfModules.ιFree (R := X.ringCatSheaf) b) V
    (1 : Γ(X, V))

/-- The original free generators retain their labels under restriction. -/
theorem paired_c3_free_generator_restrict (U V : X.Opens) (h : V ≤ U) (b : σ) :
    pairedC3ModuleRestrict (SheafOfModules.free (R := X.ringCatSheaf) σ) h
      (pairedC3FreeGenerator X σ U b) = pairedC3FreeGenerator X σ V b := by
  have hn := PresheafOfModules.naturality_apply (SheafOfModules.ιFree (R := X.ringCatSheaf) b).val
    (homOfLE h).op (1 : Γ(X, U))
  change (SheafOfModules.ιFree (R := X.ringCatSheaf) b).val.app (op V)
    ((X.presheaf.map (homOfLE h).op) (1 : Γ(X, U))) = _ at hn
  rw [map_one] at hn
  exact hn.symm

/-- The canonical finite coproduct-to-product isomorphism. -/
def pairedC3FreePiIso (X : Scheme.{0}) (σ : Type) [Fintype σ] :
    (SheafOfModules.free (R := X.ringCatSheaf) σ : X.Modules) ≅
      ∏ᶜ (fun _ : σ => (SheafOfModules.unit X.ringCatSheaf : X.Modules)) := by
  letI : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  let P : σ → X.Modules := fun _ => SheafOfModules.unit X.ringCatSheaf
  exact (biproduct.isoCoproduct P).symm ≪≫ biproduct.isoProduct P

/-- Original scalar coordinates of finite free sections. -/
def pairedC3FreeCoordinates (X : Scheme.{0}) (σ : Type) [Fintype σ] (V : X.Opens) :
    Γ((SheafOfModules.free (R := X.ringCatSheaf) σ : X.Modules), V) ≃ₗ[Γ(X, V)]
      (σ → Γ(X, V)) :=
  (pairedC3ModuleIsoSectionEquiv X (pairedC3FreePiIso X σ) V).trans
    (pairedC3ProductSectionEquiv (fun _ : σ => SheafOfModules.unit X.ringCatSheaf) V)

/-- The canonical free-section coordinate is its labelled unit vector. -/
theorem paired_c3_free_coordinates_generator [DecidableEq σ] (V : X.Opens) (b : σ) :
    pairedC3FreeCoordinates X σ V (pairedC3FreeGenerator X σ V b) = Pi.single b 1 := by
  classical
  funext a
  rw [pairedC3FreeCoordinates, LinearEquiv.trans_apply]
  erw [paired_c3_product_section_coordinate]
  change Scheme.Modules.Hom.app (X := X)
    (SheafOfModules.ιFree (R := X.ringCatSheaf) b ≫ (pairedC3FreePiIso X σ).hom ≫
      Pi.π (fun _ : σ => (SheafOfModules.unit X.ringCatSheaf : X.Modules)) a) V
      (1 : Γ(X, V)) = _
  letI : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  simp only [pairedC3FreePiIso, Iso.trans_hom, Iso.symm_hom,
    biproduct.isoCoproduct_inv, biproduct.isoProduct_hom, Category.assoc,
    SheafOfModules.ιFree, Sigma.ι_desc_assoc]
  erw [Pi.lift_comp_π]
  by_cases h : b = a
  · subst a
    erw [biproduct.ι_π_self]
    simp only [Scheme.Modules.Hom.id_app, CategoryTheory.id_apply, Pi.single_eq_same]
  · erw [biproduct.ι_π_ne _ h]
    rw [Pi.single_eq_of_ne (Ne.symm h)]
    rfl

/-- The canonical free generators give bijective finite synthesis on every open. -/
theorem paired_c3_free_generator_synthesis_bijective (V : X.Opens) :
    Function.Bijective (pairedC3FiniteFrameSynthesis
      (pairedC3FreeGenerator X σ ⊤) V le_top) := by
  classical
  have heq : (pairedC3FiniteFrameSynthesis (pairedC3FreeGenerator X σ ⊤) V le_top :
      (σ → Γ(X, V)) → Γ(SheafOfModules.free (R := X.ringCatSheaf) σ, V)) =
      (pairedC3FreeCoordinates X σ V).symm := by
    funext c
    apply (pairedC3FreeCoordinates X σ V).injective
    rw [LinearEquiv.apply_symm_apply]
    change pairedC3FreeCoordinates X σ V (∑ b, c b • _) = c
    rw [map_sum]
    simp only [map_smul, paired_c3_free_generator_restrict, paired_c3_free_coordinates_generator]
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [heq]
  exact (pairedC3FreeCoordinates X σ V).symm.bijective

/-- A global section supplies its original restriction family. -/
def pairedC3GlobalSection {X : Scheme.{0}} (M : X.Modules) (s : Γ(M, ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk
    (fun V => M.val.map (homOfLE le_top).op s) (by
      intro V W h
      rw [← M.val.map_comp_apply]
      rfl)

/-- The free arrow with the specified original global generators. -/
def pairedC3FreeGeneratorArrow {X : Scheme.{0}} (M : X.Modules) {σ : Type}
    (g : σ → Γ(M, ⊤)) : (SheafOfModules.free (R := X.ringCatSheaf) σ : X.Modules) ⟶ M :=
  M.freeHomEquiv.symm (fun b => pairedC3GlobalSection M (g b))

/-- The free arrow sends each original free generator to the original restricted section. -/
theorem paired_c3_free_generator_arrow_apply {X : Scheme.{0}} (M : X.Modules) {σ : Type}
    (g : σ → Γ(M, ⊤)) (V : X.Opens) (b : σ) :
    Scheme.Modules.Hom.app (X := X) (pairedC3FreeGeneratorArrow M g) V (pairedC3FreeGenerator X σ V b) =
      pairedC3ModuleRestrict M le_top (g b) := by
  have h := SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
    (fun b => pairedC3GlobalSection M (g b)) b
  exact congrArg (fun s => s.val (op V)) h

#print axioms paired_c3_free_generator_synthesis_bijective
#print axioms paired_c3_free_generator_arrow_apply
end HodgeLean.Foundations.Program.G32Native
