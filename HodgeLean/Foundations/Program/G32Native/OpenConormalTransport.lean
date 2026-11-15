import HodgeLean.Foundations.AlgebraicGeometry.ConormalFramesDefs
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Conormal transport through an ambient open immersion

The actual conormal isomorphism is retained, including any subsequent supplied
presentation. No normal splitting is introduced.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native

private theorem open_restriction_preserves_finite_limits
    {U B : Scheme} (a : U ⟶ B) [IsOpenImmersion a] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor a) := by
  let F := Scheme.Modules.restrictFunctor a
  let G := SheafOfModules.forget U.ringCatSheaf ⋙
    PresheafOfModules.toPresheaf U.ringCatSheaf.obj
  have hpres : PreservesFiniteLimits (F ⋙ G) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget B.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf B.ringCatSheaf.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj a.opensFunctor.op)
    infer_instance
  have hreflect : ReflectsFiniteLimits G :=
    ⟨fun _ => reflectsLimitsOfShape_of_reflectsIsomorphisms⟩
  exact @preservesFiniteLimits_of_reflects_of_preserves _ _ _ _ _ _ F G hpres hreflect


private theorem idealModule_open_transport
    {K U B : Scheme} (k : K ⟶ U) (a : U ⟶ B) [IsOpenImmersion a] :
    Nonempty ((Scheme.Modules.pullback a).obj (s2c_idealModule (k ≫ a)) ≅
      s2c_idealModule k) := by
  let F := Scheme.Modules.restrictFunctor a
  let : PreservesFiniteLimits F := open_restriction_preserves_finite_limits a
  let t := SheafOfModules.unitToPushforwardObjUnit (k ≫ a).toRingCatSheafHom
  let t' := SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom
  let ε := Scheme.Modules.restrictUnitIso a
  let χ : F.obj ((Scheme.Modules.pushforward (k ≫ a)).obj
      (SheafOfModules.unit K.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward k).obj (SheafOfModules.unit K.ringCatSheaf) :=
    F.mapIso ((Scheme.Modules.pushforwardComp k a).symm.app _) ≪≫
      (Scheme.Modules.restrictFunctorAdjCounitIso a).app _
  have hcomm : F.map t ≫ χ.hom = ε.hom ≫ t' := by
    apply (cancel_epi ε.inv).mp
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    apply (SheafOfModules.unitHomEquiv _).injective
    ext V
    change (χ.hom.val.app V) ((F.map t).val.app V (ε.inv.val.app V (1 : Γ(U, V.unop)))) =
      (t'.val.app V) (1 : Γ(U, V.unop))
    have hε : ε.inv.val.app V (1 : Γ(U, V.unop)) =
        (1 : Γ(B, a ''ᵁ V.unop)) := by
      change (a.appIso V.unop).inv 1 = 1
      exact map_one _
    rw [hε]
    have ht : (F.map t).val.app V (1 : Γ(B, a ''ᵁ V.unop)) =
        (1 : Γ(K, (k ≫ a) ⁻¹ᵁ (a ''ᵁ V.unop))) := by
      change ((k ≫ a).app (a ''ᵁ V.unop)) 1 = 1
      exact map_one _
    rw [ht]
    change χ.hom.val.app V (1 : Γ(K, (k ≫ a) ⁻¹ᵁ (a ''ᵁ V.unop))) =
      (k.app V.unop) 1
    rw [map_one (k.app V.unop).hom]
    change (((Scheme.Modules.restrictFunctorAdjCounitIso a).hom.app
      ((Scheme.Modules.pushforward k).obj (SheafOfModules.unit K.ringCatSheaf))).val.app V)
        (1 : Γ(K, (k ≫ a) ⁻¹ᵁ (a ''ᵁ V.unop))) = (1 : Γ(K, k ⁻¹ᵁ V.unop))
    change (K.presheaf.map _).hom (1 : _) = 1
    exact map_one _

  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback a).symm.app _ ≪≫
    PreservesKernel.iso F t ≪≫ kernel.mapIso (F.map t) t' ε χ hcomm⟩


/-- The conormal identification for the specified ambient open factorization.
Source: Hartshorne, Algebraic Geometry, II.8, localization of the conormal sequence. -/
theorem i1_openConormalIso_aux {Q W : Over (Spec ↧ℂ)} (ι : Q ⟶ W)
    [IsClosedImmersion ι.left] {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
    (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left) :
    Nonempty (Conormal.sheaf j ≅ Conormal.sheaf ι.left) := by
  obtain ⟨e⟩ := idealModule_open_transport j v
  let eC : Conormal.sheaf (j ≫ v) ≅ Conormal.sheaf j :=
    (Scheme.Modules.pullbackComp j v).symm.app _ ≪≫
      (Scheme.Modules.pullback j).mapIso e
  exact ⟨eC.symm ≪≫ eqToIso (congrArg Conormal.sheaf hj)⟩

#print axioms i1_openConormalIso_aux

end HodgeLean.Foundations.Program.G32Native
