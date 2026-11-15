import HodgeLean.Foundations.Program.G32Native.OriginalConormalIntrinsicSection
import HodgeLean.Foundations.Program.G32Native.ModuleLocalPullbackSectionNaturality
import HodgeLean.Foundations.Program.G32Native.ConormalIdealRestrictionNaturality
import HodgeLean.Foundations.BundleResolution.ModuleSectionRefineHelpers

/-! # Restriction of the intrinsic original conormal equation section -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleResolution

/-- The actual ambient-open ideal comparison in pullback coordinates. -/
def originalIdealOpenPullbackIso {Q W : Scheme.{0}} (j : Q ⟶ W) (A : W.Opens) :
    (Scheme.Modules.pullback A.ι).obj (Conormal.idealModule j) ≅
      Conormal.idealModule (j ∣_ A) :=
  (Scheme.Modules.restrictFunctorIsoPullback A.ι).symm.app (Conormal.idealModule j) ≪≫
    s2e_idealModule_restrict_iso j A

/-- The normalized original ideal value gives the original restricted ideal section. -/
theorem originalIdealOpenSection_pullback
    {Q W : Scheme.{0}} (j : Q ⟶ W) (A : W.Opens)
    (u : RingHom.ker (j.app A).hom) :
    moduleOpenSectionPullbackOfValue (Conormal.idealModule j) A
        ((s2e_idealModule_sections_equiv j A).symm u) ≫
      (originalIdealOpenPullbackIso j A).hom = originalIdealOpenSection j A u := by
  dsimp only [moduleOpenSectionPullbackOfValue, originalIdealOpenPullbackIso,
    originalIdealOpenSection, Iso.trans_hom, Iso.symm_hom, Iso.app_inv]
  rw [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]

/-- The original conormal comparison is local module pullback followed by the ideal comparison. -/
theorem originalConormalOpenIso_pullback_construction
    {Q W : Scheme.{0}} (j : Q ⟶ W) (A : W.Opens) :
    originalConormalOpenIso j A =
      moduleLocalPullbackIso j (Conormal.idealModule j) A ≪≫
        (Scheme.Modules.pullback (j ∣_ A)).mapIso (originalIdealOpenPullbackIso j A) := by
  apply Iso.ext
  dsimp only [originalConormalOpenIso, originalIdealOpenPullbackIso,
    moduleLocalPullbackIso, s2e_conormal_restrict_ambient_open_iso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]

/-- The intrinsic conormal section is the local pullback of its original ideal value. -/
theorem originalConormalIntrinsicSection_eq_local
    {Q W : Scheme.{0}} (j : Q ⟶ W) (A : W.Opens)
    (u : RingHom.ker (j.app A).hom) :
    originalConormalIntrinsicSection j A u =
      moduleLocalPullbackSection j (Conormal.idealModule j) A
        (moduleOpenSectionPullbackOfValue (Conormal.idealModule j) A
          ((s2e_idealModule_sections_equiv j A).symm u)) := by
  dsimp only [originalConormalIntrinsicSection, moduleLocalPullbackSection]
  rw [originalConormalOpenIso_pullback_construction j A,
    ← originalIdealOpenSection_pullback j A u]
  dsimp only [Iso.trans_inv, Functor.mapIso_inv]
  rw [conormalSection_pullback_map]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id,
    (Scheme.Modules.pullback (j ∣_ A)).map_id, Category.id_comp]

/-- Refinement of the intrinsic conormal section retains the restricted original equation. -/
theorem originalConormalIntrinsicSection_refine
    {Q : Over (Spec ↧ℂ)} {W : Scheme.{0}} (j : Q.left ⟶ W)
    (A B : W.Opens) (h : B ≤ A)
    (u : RingHom.ker (j.app A).hom) (v : RingHom.ker (j.app B).hom)
    (hv : v.val = W.presheaf.map (homOfLE h).op u.val) :
    i1_moduleSectionRefine (Conormal.sheaf j) (j.preimage_mono h)
      (originalConormalIntrinsicSection j A u) = originalConormalIntrinsicSection j B v := by
  dsimp only [i1_moduleSectionRefine]
  rw [originalConormalIntrinsicSection_eq_local j A u,
    originalConormalIntrinsicSection_eq_local j B v]
  erw [moduleLocalPullbackSection_value_refine j (Conormal.idealModule j) h
    ((s2e_idealModule_sections_equiv j A).symm u)]
  erw [originalIdealSection_restrict j h u v hv]

end HodgeLean.Foundations.TubularEuler
