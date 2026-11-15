import HodgeLean.Foundations.Program.G32Native.ModuleOpenSectionRefineNaturality
import HodgeLean.Foundations.Program.G32Native.ModuleSectionFactorizationNaturality

/-! # Local pullback of original module sections through nested ambient opens -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

/-- Reflexive pullback comparisons have identity component maps. -/
theorem modulePullbackCongr_refl {X Y : Scheme.{0}} (f : X ⟶ Y) :
    (Scheme.Modules.pullbackCongr (rfl : f = f)).hom = 𝟙 (Scheme.Modules.pullback f) := by
  rfl

/-- Reversing equality of maps inverts the pullback comparison. -/
theorem modulePullbackCongr_symm_inv {X Y : Scheme.{0}}
    {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h.symm).inv.app M =
      (Scheme.Modules.pullbackCongr h).hom.app M := by
  subst g
  rfl

/-- The pullback comparison for an original ambient open square. -/
def moduleLocalPullbackIso {Q W : Scheme.{0}} (j : Q ⟶ W)
    (M : W.Modules) (A : W.Opens) :
    (Scheme.Modules.pullback (j ⁻¹ᵁ A).ι).obj ((Scheme.Modules.pullback j).obj M) ≅
      (Scheme.Modules.pullback (j ∣_ A)).obj ((Scheme.Modules.pullback A.ι).obj M) :=
  (Scheme.Modules.pullbackComp (j ⁻¹ᵁ A).ι j).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι j A).symm).app M ≪≫
      (Scheme.Modules.pullbackComp (j ∣_ A) A.ι).symm.app M

/-- Pull a section on an ambient open back to its inverse-image open. -/
def moduleLocalPullbackSection {Q W : Scheme.{0}} (j : Q ⟶ W)
    (M : W.Modules) (A : W.Opens)
    (s : SheafOfModules.unit.{0} A.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback A.ι).obj M) :
    SheafOfModules.unit.{0} (j ⁻¹ᵁ A).toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback (j ⁻¹ᵁ A).ι).obj ((Scheme.Modules.pullback j).obj M) :=
  i1_module_sectionPullback (j ∣_ A) ((Scheme.Modules.pullback A.ι).obj M) s ≫
    (moduleLocalPullbackIso j M A).inv

/-- Local pullback retains the original factorization into the ambient scheme. -/
theorem moduleLocalPullbackSection_fac {Q W : Scheme.{0}} (j : Q ⟶ W)
    (M : W.Modules) (A : W.Opens)
    (s : SheafOfModules.unit.{0} A.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback A.ι).obj M) :
    moduleLocalPullbackSection j M A s ≫ (Scheme.Modules.pullbackComp (j ⁻¹ᵁ A).ι j).hom.app M =
      i1_module_sectionPullback (j ∣_ A) ((Scheme.Modules.pullback A.ι).obj M) s ≫
        (Scheme.Modules.pullbackComp (j ∣_ A) A.ι).hom.app M ≫
          (Scheme.Modules.pullbackCongr (morphismRestrict_ι j A)).hom.app M := by
  dsimp only [moduleLocalPullbackSection, moduleLocalPullbackIso, Iso.trans_inv,
    Iso.symm_inv, Iso.app_inv, Iso.app_hom]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [modulePullbackCongr_symm_inv]

/-- Local pullback preserves refinement of sections on nested ambient opens. -/
theorem moduleLocalPullbackSection_refine {Q W : Scheme.{0}} (j : Q ⟶ W)
    (M : W.Modules) {A B : W.Opens} (h : B ≤ A)
    (sA : SheafOfModules.unit.{0} A.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback A.ι).obj M)
    (sB : SheafOfModules.unit.{0} B.toScheme.ringCatSheaf ⟶ (Scheme.Modules.pullback B.ι).obj M)
    (hs : i1_module_sectionPullback (W.homOfLE h) ((Scheme.Modules.pullback A.ι).obj M) sA ≫
      (Scheme.Modules.pullbackComp (W.homOfLE h) A.ι).hom.app M ≫
        (Scheme.Modules.pullbackCongr (W.homOfLE_ι h)).hom.app M = sB) :
    i1_module_sectionPullback (Q.homOfLE (j.preimage_mono h))
        ((Scheme.Modules.pullback (j ⁻¹ᵁ A).ι).obj ((Scheme.Modules.pullback j).obj M))
        (moduleLocalPullbackSection j M A sA) ≫
      (Scheme.Modules.pullbackComp (Q.homOfLE (j.preimage_mono h)) (j ⁻¹ᵁ A).ι).hom.app
        ((Scheme.Modules.pullback j).obj M) ≫
      (Scheme.Modules.pullbackCongr (Q.homOfLE_ι (j.preimage_mono h))).hom.app
        ((Scheme.Modules.pullback j).obj M) = moduleLocalPullbackSection j M B sB := by
  have hxv : (Q.homOfLE (j.preimage_mono h)) ≫ ((j ⁻¹ᵁ A).ι ≫ j) = (j ⁻¹ᵁ B).ι ≫ j := by
    rw [← Category.assoc, Q.homOfLE_ι]
  have hxu : ((j ∣_ B) ≫ W.homOfLE h) ≫ A.ι = (j ⁻¹ᵁ B).ι ≫ j := by
    rw [Category.assoc, W.homOfLE_ι, morphismRestrict_ι]
  have hw : (Q.homOfLE (j.preimage_mono h)) ≫ (j ∣_ A) = ((j ∣_ B) ≫ W.homOfLE h) := (morphismRestrict_homOfLE j B A h).symm
  have hsrc := i1_module_pullback_factorization_coherence (Q.homOfLE (j.preimage_mono h)) (j ⁻¹ᵁ A).ι j
    ((j ⁻¹ᵁ A).ι ≫ j) (j ⁻¹ᵁ B).ι ((j ⁻¹ᵁ B).ι ≫ j) rfl
    (Q.homOfLE_ι (j.preimage_mono h)) hxv rfl M
  simp only [modulePullbackCongr_refl, NatTrans.id_app, Category.comp_id] at hsrc
  apply (cancel_mono ((Scheme.Modules.pullbackComp (j ⁻¹ᵁ B).ι j).hom.app M)).1
  simp only [Category.assoc]
  rw [moduleLocalPullbackSection_fac j M B sB, ← hsrc]
  rw [← reassoc_of% (conormalSection_pullback_map (Q.homOfLE (j.preimage_mono h)) (moduleLocalPullbackSection j M A sA)
    ((Scheme.Modules.pullbackComp (j ⁻¹ᵁ A).ι j).hom.app M))]
  rw [moduleLocalPullbackSection_fac j M A sA]
  rw [moduleSection_factorization (Q.homOfLE (j.preimage_mono h)) (j ∣_ A) A.ι ((j ⁻¹ᵁ A).ι ≫ j) ((j ∣_ B) ≫ W.homOfLE h)
    ((j ⁻¹ᵁ B).ι ≫ j) (morphismRestrict_ι j A) hw hxv hxu M sA]
  rw [← hs, moduleSection_factorization (j ∣_ B) (W.homOfLE h) A.ι B.ι ((j ∣_ B) ≫ W.homOfLE h)
    ((j ⁻¹ᵁ B).ι ≫ j) (W.homOfLE_ι h) rfl (morphismRestrict_ι j B) hxu M sA]

/-- Local pullback of an original value commutes with restriction of that value. -/
theorem moduleLocalPullbackSection_value_refine {Q W : Scheme.{0}} (j : Q ⟶ W)
    (M : W.Modules) {A B : W.Opens} (h : B ≤ A) (t : Γ(M, A)) :
    i1_module_sectionPullback (Q.homOfLE (j.preimage_mono h))
        ((Scheme.Modules.pullback (j ⁻¹ᵁ A).ι).obj ((Scheme.Modules.pullback j).obj M))
        (moduleLocalPullbackSection j M A (moduleOpenSectionPullbackOfValue M A t)) ≫
      (Scheme.Modules.pullbackComp (Q.homOfLE (j.preimage_mono h)) (j ⁻¹ᵁ A).ι).hom.app
        ((Scheme.Modules.pullback j).obj M) ≫
      (Scheme.Modules.pullbackCongr (Q.homOfLE_ι (j.preimage_mono h))).hom.app
        ((Scheme.Modules.pullback j).obj M) =
      moduleLocalPullbackSection j M B
        (moduleOpenSectionPullbackOfValue M B (M.presheaf.map (homOfLE h).op t)) :=
  moduleLocalPullbackSection_refine j M h _ _ (moduleOpenSectionPullbackOfValue_refine M h t)

end HodgeLean.Foundations.TubularEuler
