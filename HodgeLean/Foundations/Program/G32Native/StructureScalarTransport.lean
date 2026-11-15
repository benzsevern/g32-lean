import HodgeLean.Foundations.Program.G32Native.OriginalIdealIsomorphismComparison
import HodgeLean.Foundations.BundleResolution.ModulePointValueAlgebraHelpers

/-! # Scalar transport through the canonical structure-module map -/
noncomputable section
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.Algebraic

/-- The structure-module map transports multiplication by a global function
by the actual pullback of that function.
Source: `Scheme.Hom.naturality` and `f5sheaf_scal_app`. -/
theorem structureModule_scalar_transport {X Y : Scheme.{0}} (f : X ⟶ Y)
    (c : Γ(Y, ⊤)) :
    f5sheaf_scal c ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map (f5sheaf_scal (f.appTop c)) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext
  change f.app U.unop ((f5sheaf_scal c).val.app U (1 : Γ(Y, U.unop))) =
    (f5sheaf_scal (f.appTop c)).val.app (.op (f ⁻¹ᵁ U.unop)) (f.app U.unop (1 : Γ(Y, U.unop)))
  rw [f5sheaf_scal_app, f5sheaf_scal_app, map_one, one_mul, one_mul]
  exact congrArg (fun g => g c) (f.naturality (homOfLE (le_top : U.unop ≤ ⊤)).op)

/-- An ambient isomorphism conjugates scalar multiplication by the global
function in its original inverse coordinates.
Source: `structureModule_scalar_transport` and `Scheme.Hom.comp_appTop`. -/
theorem structureModule_scalar_conjugation {X Y : Scheme.{0}} (e : X ≅ Y)
    (c : Γ(X, ⊤)) :
    letI := s2e_structureModule_map_isIso e.hom
    let η := SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom
    η ≫ (Scheme.Modules.pushforward e.hom).map (f5sheaf_scal c) ≫ inv η =
      f5sheaf_scal (e.inv.appTop c) := by
  letI := s2e_structureModule_map_isIso e.hom
  let η := SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom
  have hc : e.hom.appTop (e.inv.appTop c) = c := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.hom_inv_id,
      Scheme.Hom.id_appTop, CommRingCat.id_apply]
  have hs := structureModule_scalar_transport e.hom (e.inv.appTop c)
  rw [hc] at hs
  have h := congrArg (fun q => q ≫ inv η) hs
  have hz : (f5sheaf_scal (e.inv.appTop c) ≫ η) ≫ inv η =
      f5sheaf_scal (e.inv.appTop c) := by
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  exact (Category.assoc η _ _).symm.trans (h.symm.trans hz)

#print axioms structureModule_scalar_transport
#print axioms structureModule_scalar_conjugation
end HodgeLean.Foundations.TubularEuler
