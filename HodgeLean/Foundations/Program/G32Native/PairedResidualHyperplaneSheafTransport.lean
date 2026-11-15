import HodgeLean.Foundations.Program.G32Native.PairedResidualAnyHyperplane
import HodgeLean.Foundations.Program.G32Native.UnionConormalIsoPushforwardObject
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Structure sheaves of hyperplanes under actual coordinate changes -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Pullback by a scheme isomorphism retains the structure sheaf of the actual pulled subscheme.
Source: Hartshorne, Algebraic Geometry, II.5, pullback and direct image. -/
def residualComapStructureSheafIso {X Y : Scheme.{0}} (e : X ≅ Y)
    (I : Y.IdealSheafData) :
    (Scheme.Modules.pullback e.hom).obj
      ((Scheme.Modules.pushforward I.subschemeι).obj (SheafOfModules.unit I.subscheme.ringCatSheaf)) ≅
    (Scheme.Modules.pushforward (I.comap e.hom).subschemeι).obj
      (SheafOfModules.unit (I.comap e.hom).subscheme.ringCatSheaf) := by
  let b := (I.comapIso e.hom).hom ≫ pullback.snd e.hom I.subschemeι
  haveI : IsIso b := by dsimp only [b]; infer_instance
  have hb : b ≫ I.subschemeι = (I.comap e.hom).subschemeι ≫ e.hom := by
    dsimp only [b]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  letI : (TopologicalSpace.Opens.map b.base).Final := inferInstance
  letI : (SheafOfModules.pushforward b.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward b).IsRightAdjoint
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit b.toRingCatSheafHom) :=
    inferInstanceAs (IsIso (SheafOfModules.pullbackObjUnitToUnit
      (F := TopologicalSpace.Opens.map b.base) b.toRingCatSheafHom))
  exact unionConormalIsoPushforwardObjectIso I.subschemeι
      (I.comap e.hom).subschemeι b e.hom hb (SheafOfModules.unit I.subscheme.ringCatSheaf) ≪≫
    (Scheme.Modules.pushforward (I.comap e.hom).subschemeι).mapIso
      (asIso (SheafOfModules.pullbackObjUnitToUnit b.toRingCatSheafHom))

example {X Y : Scheme.{0}} (e : X ≅ Y) (I : Y.IdealSheafData) :
    (Scheme.Modules.pullback e.hom).obj
      ((Scheme.Modules.pushforward I.subschemeι).obj (SheafOfModules.unit I.subscheme.ringCatSheaf)) ≅
    (Scheme.Modules.pushforward (I.comap e.hom).subschemeι).obj
      (SheafOfModules.unit (I.comap e.hom).subscheme.ringCatSheaf) :=
  residualComapStructureSheafIso e I

/-- Returning from a linear hyperplane's actual coordinates recovers the standard hyperplane ideal.
Source: Hartshorne, Algebraic Geometry, II.7.1. -/
theorem residual_linear_hyperplane_comap_inverse (k : ℕ)
    (a : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ)) :
    (residualLinearHyperplane k a).comap (s2e_linearProjectiveOverIso a).inv.left =
      s2e_hyperplaneIdeal k := by
  unfold residualLinearHyperplane
  rw [← Scheme.IdealSheafData.comap_comp]
  have he := congrArg (fun f => f.left) (s2e_linearProjectiveOverIso a).inv_hom_id
  change _ ≫ _ = 𝟙 _ at he
  rw [he, Scheme.IdealSheafData.comap_id]

#print axioms residualComapStructureSheafIso
#print axioms residual_linear_hyperplane_comap_inverse
end HodgeLean.Foundations.Program.G32Native
