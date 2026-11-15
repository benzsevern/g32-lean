import HodgeLean.Foundations.Program.G32Native.PairedC3LocalModuleComparison

/-! # Isomorphisms from compatible local linear comparisons -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
variable {X : Scheme.{0}} {M N : X.Modules} {ι : Type} {U : ι → X.Opens}

/-- The inverse local comparisons remain natural and agree on overlaps. -/
def PairedC3LocalModuleComparison.symm (D : PairedC3LocalModuleComparison M N U) :
    PairedC3LocalModuleComparison N M U where
  equiv i V h := (D.equiv i V h).symm
  restrict i V W h hV s := by
    apply (D.equiv i W (h.trans hV)).injective
    rw [LinearEquiv.apply_symm_apply, D.restrict i V W h hV,
      LinearEquiv.apply_symm_apply]
  agree i j V hi hj s := by
    apply (D.equiv i V hi).injective
    rw [LinearEquiv.apply_symm_apply, D.agree i j V hi hj,
      LinearEquiv.apply_symm_apply]

variable (D : PairedC3LocalModuleComparison M N U) (hU : ⨆ i, U i = ⊤)
include hU

/-- The glued images are additive. -/
theorem paired_c3_local_module_image_add (V : X.Opens) (s t : Γ(M, V)) :
    pairedC3LocalModuleImage D hU V (s + t) =
      pairedC3LocalModuleImage D hU V s + pairedC3LocalModuleImage D hU V t := by
  apply paired_c3_module_eq_of_chart_restrict hU
  intro i
  simp only [map_add, paired_c3_local_module_image_restrict]

/-- The glued images respect the structure-sheaf action. -/
theorem paired_c3_local_module_image_smul (V : X.Opens) (a : Γ(X, V)) (s : Γ(M, V)) :
    pairedC3LocalModuleImage D hU V (a • s) = a • pairedC3LocalModuleImage D hU V s := by
  apply paired_c3_module_eq_of_chart_restrict hU
  intro i
  rw [paired_c3_local_module_image_restrict]
  simp only [pairedC3ModuleRestrict, Scheme.Modules.map_smul, map_smul,
    paired_c3_local_module_image_restrict]

/-- The glued images commute with restriction. -/
theorem paired_c3_local_module_image_natural (V W : X.Opens) (h : W ≤ V) (s : Γ(M, V)) :
    pairedC3LocalModuleImage D hU W (pairedC3ModuleRestrict M h s) =
      pairedC3ModuleRestrict N h (pairedC3LocalModuleImage D hU V s) := by
  apply paired_c3_module_eq_of_chart_restrict hU
  intro i
  rw [paired_c3_local_module_image_restrict, paired_c3_module_restrict_comp,
    paired_c3_module_restrict_comp]
  exact (paired_c3_local_module_image_restrict_of_le D hU V (W ⊓ U i)
    (inf_le_left.trans h) i inf_le_right s).symm

/-- The natural local comparisons give a global morphism of module sheaves. -/
def pairedC3LocalModuleHom : M ⟶ N :=
  ⟨{ app := fun V => ModuleCat.ofHom
       { toFun := pairedC3LocalModuleImage D hU V.unop
         map_add' := paired_c3_local_module_image_add D hU V.unop
         map_smul' := paired_c3_local_module_image_smul D hU V.unop }
     naturality := fun {V W} f => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro s
       exact paired_c3_local_module_image_natural D hU V.unop W.unop f.unop.le s }⟩

/-- Applying a comparison and then its inverse recovers each section. -/
theorem paired_c3_local_module_image_inverse (V : X.Opens) (s : Γ(M, V)) :
    pairedC3LocalModuleImage D.symm hU V (pairedC3LocalModuleImage D hU V s) = s := by
  apply paired_c3_module_eq_of_chart_restrict hU
  intro i
  rw [paired_c3_local_module_image_restrict, paired_c3_local_module_image_restrict]
  exact (D.equiv i (V ⊓ U i) inf_le_right).symm_apply_apply _

/-- The local comparisons glue to an actual global isomorphism. -/
def pairedC3LocalModuleIso : M ≅ N where
  hom := pairedC3LocalModuleHom D hU
  inv := pairedC3LocalModuleHom D.symm hU
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact paired_c3_local_module_image_inverse D hU V.unop s
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change pairedC3LocalModuleImage D hU V.unop
      (pairedC3LocalModuleImage D.symm hU V.unop s) = s
    apply paired_c3_module_eq_of_chart_restrict hU
    intro i
    rw [paired_c3_local_module_image_restrict, paired_c3_local_module_image_restrict]
    exact (D.equiv i (V.unop ⊓ U i) inf_le_right).apply_symm_apply _

end HodgeLean.Foundations.Program.G32Native
