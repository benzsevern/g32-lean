import HodgeLean.Foundations.BundleResolution.ModuleTopology

/-! # Global sections and lifting from free module sheaves

A map surjective on global sections lifts maps from free sheaves with
arbitrary index sets by simultaneous choices of generator lifts.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.BundleResolution

def i1_module_sectionsTopEquiv {X : Scheme.{0}} (M : X.Modules) :
    M.sections ≃ Γ(M, ⊤) where
  toFun s := s.val (op ⊤)
  invFun a := PresheafOfModules.sectionsMk
    (fun U => M.val.map (homOfLE le_top).op a)
    (fun U V f => by
      change M.val.presheaf.map f (M.val.presheaf.map _ a) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE (le_top : U.unop ≤ ⊤)).op
  right_inv a := by
    change M.val.presheaf.map (𝟙 _) a = a
    exact CategoryTheory.congr_fun (M.val.presheaf.map_id _) a

def i1_module_unitHomEquivTop {X : Scheme.{0}} (M : X.Modules) :
    (SheafOfModules.unit X.ringCatSheaf ⟶ M) ≃ Γ(M, ⊤) :=
  M.unitHomEquiv.trans (i1_module_sectionsTopEquiv M)

theorem i1_module_unitHomEquivTop_comp {X : Scheme.{0}} {M N : X.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M) (q : M ⟶ N) :
    i1_module_unitHomEquivTop N (s ≫ q) =
      q.val.app (op ⊤) (i1_module_unitHomEquivTop M s) := rfl

theorem i1_module_free_lift_of_surjective_top {X : Scheme.{0}} {M N : X.Modules}
    (I : Type) (q : M ⟶ N) (hq : Function.Surjective (q.val.app (op ⊤)))
    (g : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ N) :
    ∃ h : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ M, h ≫ q = g := by
  classical
  have hunit : ∀ s : SheafOfModules.unit X.ringCatSheaf ⟶ N,
      ∃ t : SheafOfModules.unit X.ringCatSheaf ⟶ M, t ≫ q = s := by
    intro s
    obtain ⟨a, ha⟩ := hq (i1_module_unitHomEquivTop N s)
    refine ⟨(i1_module_unitHomEquivTop M).symm a, ?_⟩
    apply (i1_module_unitHomEquivTop N).injective
    rw [i1_module_unitHomEquivTop_comp, Equiv.apply_symm_apply, ha]
  choose h hh using fun i : I => hunit (SheafOfModules.ιFree i ≫ g)
  refine ⟨Sigma.desc h, ?_⟩
  apply Sigma.hom_ext
  intro i
  exact (Sigma.ι_comp_desc_assoc h i q).trans (hh i)

end HodgeLean.Foundations.BundleResolution
