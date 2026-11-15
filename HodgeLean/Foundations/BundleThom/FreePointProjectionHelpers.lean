import HodgeLean.Foundations.BundleThom.AnalyticNormalFramesHelpers
import HodgeLean.Foundations.BundleThom.FreeSheafProjectionHelpers

/-! # Finite coordinates and free-sheaf projections at the complex point

The coordinates retain the actual summand and projection morphisms.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- The standard free point basis consists of the actual sheaf generator values.
Source: Hartshorne, Algebraic Geometry, II.5, affine sections of a free sheaf. -/
theorem i1_freePointBasis_apply (k : ℕ) (j : Fin k) :
    Module.Basis.ofEquivFun (i1_freePointCoordinates k) j =
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (SheafOfModules.ιFree (R := (Spec ↧ℂ).ringCatSheaf) j)
          (1 : Γ(Spec ↧ℂ, ⊤)) := by
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let e := i1_freePointCoordinates k
  have hu := congrArg (fun v : G.obj (SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf) =>
    e (G.map (SheafOfModules.ιFree j) v)) i1_pointUnitComparison_one
  have hg := hu.symm.trans (i1_freePointCoordinates_generator k j)
  have hb := congrFun (Module.Basis.coe_ofEquivFun e) j
  have hv := congrArg e.symm hg
  exact hb.trans (hv.symm.trans (LinearEquiv.symm_apply_apply _ _))

/-- Actual projection of a point-generator value gives the specified scalar coordinate.
Source: Hartshorne, Algebraic Geometry, II.5, coordinate projections of free modules. -/
theorem i1_freePointProjection_generator_value (k : ℕ) (i j : Fin k) :
    i1_unitPointCoordinates
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (i1_freeSheafProjection (Spec ↧ℂ) k i)
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
          (SheafOfModules.ιFree (R := (Spec ↧ℂ).ringCatSheaf) j)
          (1 : Γ(Spec ↧ℂ, ⊤)))) = if j = i then 1 else 0 := by
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let A := SheafOfModules.unit.{0} (Spec ↧ℂ).ringCatSheaf
  have hm := (G.map_comp (SheafOfModules.ιFree j)
    (i1_freeSheafProjection (Spec ↧ℂ) k i)).symm.trans
      (congrArg (fun z => G.map z) (i1_freeSheafProjection_generator (Spec ↧ℂ) k i j))
  have hv := congrArg (fun z : G.obj A ⟶ G.obj A =>
    i1_unitPointCoordinates (z.hom (1 : Γ(Spec ↧ℂ, ⊤)))) hm
  apply hv.trans
  by_cases hj : j = i
  · simp only [if_pos hj]
    have hi := congrArg (fun z : G.obj A ⟶ G.obj A =>
      i1_unitPointCoordinates (z.hom (1 : Γ(Spec ↧ℂ, ⊤)))) (G.map_id A)
    exact hi.trans ((i1_unitPointCoordinates_apply (1 : Γ(Spec ↧ℂ, ⊤))).trans (map_one _))
  · simp only [if_neg hj]
    change i1_unitPointCoordinates (0 : Γ(Spec ↧ℂ, ⊤)) = 0
    exact map_zero _

/-- Finite point coordinates agree with the actual free-sheaf projection linear maps.
Source: Hartshorne, Algebraic Geometry, II.5, affine coordinates of finite free modules. -/
theorem i1_freePointCoordinates_projection_linearMap (k : ℕ) (i : Fin k) :
    (LinearMap.proj i).comp (i1_freePointCoordinates k).toLinearMap =
      i1_unitPointCoordinates.toLinearMap.comp
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
          (i1_freeSheafProjection (Spec ↧ℂ) k i)).hom := by
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let e := i1_freePointCoordinates k
  let b := Module.Basis.ofEquivFun e
  apply b.ext
  intro j
  change e (b j) i = i1_unitPointCoordinates
    (G.map (i1_freeSheafProjection (Spec ↧ℂ) k i) (b j))
  have hl : e (b j) i = if j = i then 1 else 0 :=
    (Module.Basis.ofEquivFun_repr_apply e (b j) i).symm.trans (b.repr_self_apply j i)
  have hr := congrArg (fun v : G.obj
      (SheafOfModules.free (R := (Spec ↧ℂ).ringCatSheaf) (Fin k)) =>
    i1_unitPointCoordinates (G.map (i1_freeSheafProjection (Spec ↧ℂ) k i) v))
      (i1_freePointBasis_apply k j)
  exact hl.trans (hr.trans (i1_freePointProjection_generator_value k i j)).symm

/-- Every coordinate of a free point section is the scalar of its actual sheaf projection.
Source: Hartshorne, Algebraic Geometry, II.5, affine free sheaf coordinates. -/
theorem i1_freePointCoordinates_projection (k : ℕ)
    (v : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      (SheafOfModules.free (R := (Spec ↧ℂ).ringCatSheaf) (Fin k))) (i : Fin k) :
    i1_freePointCoordinates k v i =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
          (i1_freeSheafProjection (Spec ↧ℂ) k i) v) := by
  exact (LinearMap.congr_fun (i1_freePointCoordinates_projection_linearMap k i) v).trans
    (i1_unitPointCoordinates_apply _)

end HodgeLean.Foundations.BundleThom
