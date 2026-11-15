import HodgeLean.Foundations.BundleThom.LocalSectionSpecializationHelpers
import HodgeLean.Foundations.BundleThom.ConormalSectionAlgebraHelpers
import Mathlib.CategoryTheory.Limits.Final

/-! # Specialization of regular coefficients through the unit sheaf

Pullback of a unit endomorphism is compared with the actual map on regular functions.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- Unit-endomorphism pullback satisfies the original ringed-space morphism's square.
Source: Hartshorne, Algebraic Geometry, II.5, pullback of module sheaves. -/
theorem i1_unitPullback_endomorphism_square {S T : Scheme.{0}} (a : S ⟶ T)
    (t : SheafOfModules.unit.{0} T.ringCatSheaf ⟶ SheafOfModules.unit.{0} T.ringCatSheaf) :
    letI : (TopologicalSpace.Opens.map a.base).Final := inferInstance
    letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
      (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
    let u : (Scheme.Modules.pullback a).obj (SheafOfModules.unit.{0} T.ringCatSheaf) ⟶
        SheafOfModules.unit.{0} S.ringCatSheaf :=
      SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom
    letI : IsIso u := inferInstanceAs (IsIso
      (SheafOfModules.pullbackObjUnitToUnit (F := TopologicalSpace.Opens.map a.base)
        a.toRingCatSheafHom))
    SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward a).map (inv u ≫ (Scheme.Modules.pullback a).map t ≫ u) =
      t ≫ SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom := by
  letI : (TopologicalSpace.Opens.map a.base).Final := inferInstance
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  let F := Scheme.Modules.pullback a
  let G := Scheme.Modules.pushforward a
  let adj := SheafOfModules.pullbackPushforwardAdjunction a.toRingCatSheafHom
  let u : F.obj (SheafOfModules.unit.{0} T.ringCatSheaf) ⟶
      SheafOfModules.unit.{0} S.ringCatSheaf :=
    SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom
  letI : IsIso u := inferInstanceAs (IsIso
      (SheafOfModules.pullbackObjUnitToUnit (F := TopologicalSpace.Opens.map a.base)
        a.toRingCatSheafHom))
  let v := SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom
  let h := inv u ≫ F.map t ≫ u
  have hc : u ≫ h = F.map t ≫ u :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (F.map t ≫ u)) (IsIso.hom_inv_id u)).trans
        (Category.id_comp _))
  have hu : adj.homEquiv _ _ u = v :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hr := adj.homEquiv_naturality_right u h
  have hl := adj.homEquiv_naturality_left t u
  calc
    v ≫ G.map h = adj.homEquiv _ _ (u ≫ h) := by
      exact (congrArg (fun z => z ≫ G.map h) hu.symm).trans hr.symm
    _ = adj.homEquiv _ _ (F.map t ≫ u) := congrArg (adj.homEquiv _ _) hc
    _ = t ≫ v := hl.trans (congrArg (fun z => t ≫ z) hu)

/-- Pullback of a unit endomorphism evaluates its original regular coefficient.
Source: Hartshorne, Algebraic Geometry, II.5, pullback on regular functions. -/
theorem i1_unitPullback_endomorphism_apply {S T : Scheme.{0}} (a : S ⟶ T)
    (t : SheafOfModules.unit.{0} T.ringCatSheaf ⟶ SheafOfModules.unit.{0} T.ringCatSheaf)
    (A : T.Opens) :
    letI : (TopologicalSpace.Opens.map a.base).Final := inferInstance
    letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
      (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
    let u : (Scheme.Modules.pullback a).obj (SheafOfModules.unit.{0} T.ringCatSheaf) ⟶
        SheafOfModules.unit.{0} S.ringCatSheaf :=
      SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom
    letI : IsIso u := inferInstanceAs (IsIso
      (SheafOfModules.pullbackObjUnitToUnit (F := TopologicalSpace.Opens.map a.base)
        a.toRingCatSheafHom))
    (inv u ≫ (Scheme.Modules.pullback a).map t ≫ u).val.app (.op (a ⁻¹ᵁ A))
      (1 : Γ(S, a ⁻¹ᵁ A)) = (a.app A) (t.val.app (.op A) (1 : Γ(T, A))) := by
  letI : (TopologicalSpace.Opens.map a.base).Final := inferInstance
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  let u : (Scheme.Modules.pullback a).obj (SheafOfModules.unit.{0} T.ringCatSheaf) ⟶
      SheafOfModules.unit.{0} S.ringCatSheaf :=
    SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom
  letI : IsIso u := inferInstanceAs (IsIso
    (SheafOfModules.pullbackObjUnitToUnit (F := TopologicalSpace.Opens.map a.base)
      a.toRingCatSheafHom))
  let h := inv u ≫ (Scheme.Modules.pullback a).map t ≫ u
  have hs := i1_unitPullback_endomorphism_square a t
  have hev := congrArg (fun f : SheafOfModules.unit.{0} T.ringCatSheaf ⟶
      (Scheme.Modules.pushforward a).obj (SheafOfModules.unit.{0} S.ringCatSheaf) =>
      (f.val.app (.op A)).hom (1 : Γ(T, A))) hs
  change (h.val.app (.op (a ⁻¹ᵁ A))).hom ((a.app A) (1 : Γ(T, A))) =
    (a.app A) ((t.val.app (.op A)).hom (1 : Γ(T, A))) at hev
  have hone : (a.app A) (1 : Γ(T, A)) = 1 := map_one _
  exact (congrArg (fun r => (h.val.app (.op (a ⁻¹ᵁ A))).hom r) hone).symm.trans hev

/-- Evaluation of a global regular function agrees with the actual complex point's section map.
Source: Hartshorne, Algebraic Geometry, II.2, morphisms from spectra of local rings. -/
theorem i1_regularEvaluation_top_eq_appTop (Q : Over (Spec ↧ℂ))
    (x : ComplexPoint Q) (r : Γ(Q.left, ⊤)) :
    Point.evaluate ⊤ r x = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (x.left.appTop r) := by
  rw [Point.evaluate, dif_pos (show x.underlying ∈ (⊤ : Q.left.Opens) from trivial)]
  have h := ConcreteCategory.congr_hom
    (Scheme.germ_stalkClosedPointTo x.left ⊤ trivial) r
  exact h

/-- The coefficient of a specialized unit endomorphism is its regular function value.
Source: Hartshorne, Algebraic Geometry, II.5, fibres and evaluation of coefficients. -/
theorem i1_unitPullback_endomorphism_coefficient (Q : Over (Spec ↧ℂ))
    (t : SheafOfModules.unit.{0} Q.left.ringCatSheaf ⟶
      SheafOfModules.unit.{0} Q.left.ringCatSheaf) (x : ComplexPoint Q) :
    letI : (TopologicalSpace.Opens.map x.left.base).Final := inferInstance
    letI : (SheafOfModules.pushforward x.left.toRingCatSheafHom).IsRightAdjoint :=
      (inferInstance : (Scheme.Modules.pushforward x.left).IsRightAdjoint)
    let u : (Scheme.Modules.pullback x.left).obj
        (SheafOfModules.unit.{0} Q.left.ringCatSheaf) ⟶
        SheafOfModules.unit.{0} (Spec ↧ℂ).ringCatSheaf :=
      SheafOfModules.pullbackObjUnitToUnit x.left.toRingCatSheafHom
    letI : IsIso u := inferInstanceAs (IsIso
      (SheafOfModules.pullbackObjUnitToUnit (F := TopologicalSpace.Opens.map x.left.base)
        x.left.toRingCatSheafHom))
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((inv u ≫ (Scheme.Modules.pullback x.left).map t ≫ u).val.app (.op ⊤)
        (1 : Γ(Spec ↧ℂ, ⊤))) =
      Point.evaluate ⊤ (t.val.app (.op ⊤) (1 : Γ(Q.left, ⊤))) x := by
  letI : (TopologicalSpace.Opens.map x.left.base).Final := inferInstance
  letI : (SheafOfModules.pushforward x.left.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward x.left).IsRightAdjoint)
  have h := i1_unitPullback_endomorphism_apply x.left t ⊤
  have h' := congrArg (fun r : Γ(Spec ↧ℂ, ⊤) =>
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r) h
  exact h'.trans (i1_regularEvaluation_top_eq_appTop Q x
    (t.val.app (.op ⊤) (1 : Γ(Q.left, ⊤)))).symm

/-- Global regular function evaluation is continuous on the analytic point space.
Source: Hartshorne, Algebraic Geometry, II.2, regular functions and analytification. -/
theorem i1_regularEvaluation_global_continuous (Q : Over (Spec ↧ℂ))
    (r : Γ(Q.left, ⊤)) :
    Continuous (fun x : ComplexPoint Q => Point.evaluate ⊤ r x) := by
  apply continuous_def.mpr
  intro O hO
  have h := Point.isOpen_overOpen_inter_preimage (X := Q) ⊤ r O hO
  change IsOpen ((Set.univ : Set (ComplexPoint Q)) ∩
    (fun x : ComplexPoint Q => Point.evaluate ⊤ r x) ⁻¹' O) at h
  simpa only [Set.univ_inter] using h

/-- Specialized unit-endomorphism coefficients vary continuously with the complex point.
Source: Hartshorne, Algebraic Geometry, II.5, analytification of regular coefficients. -/
theorem i1_unitPullback_endomorphism_coefficient_continuous (Q : Over (Spec ↧ℂ))
    (t : SheafOfModules.unit.{0} Q.left.ringCatSheaf ⟶
      SheafOfModules.unit.{0} Q.left.ringCatSheaf) :
    Continuous (fun x : ComplexPoint Q =>
    letI : (TopologicalSpace.Opens.map x.left.base).Final := inferInstance
    letI : (SheafOfModules.pushforward x.left.toRingCatSheafHom).IsRightAdjoint :=
      (inferInstance : (Scheme.Modules.pushforward x.left).IsRightAdjoint)
    let u : (Scheme.Modules.pullback x.left).obj
        (SheafOfModules.unit.{0} Q.left.ringCatSheaf) ⟶
        SheafOfModules.unit.{0} (Spec ↧ℂ).ringCatSheaf :=
      SheafOfModules.pullbackObjUnitToUnit x.left.toRingCatSheafHom
    letI : IsIso u := inferInstanceAs (IsIso
      (SheafOfModules.pullbackObjUnitToUnit (F := TopologicalSpace.Opens.map x.left.base)
        x.left.toRingCatSheafHom))
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((inv u ≫ (Scheme.Modules.pullback x.left).map t ≫ u).val.app (.op ⊤)
        (1 : Γ(Spec ↧ℂ, ⊤)))) := by
  exact (i1_regularEvaluation_global_continuous Q
    (t.val.app (.op ⊤) (1 : Γ(Q.left, ⊤)))).congr
      (fun x => (i1_unitPullback_endomorphism_coefficient Q t x).symm)

end HodgeLean.Foundations.BundleThom
