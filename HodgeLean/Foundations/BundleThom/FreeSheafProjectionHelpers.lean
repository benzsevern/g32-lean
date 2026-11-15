import HodgeLean.Foundations.BundleThom.FreeSheafGeneratorHelpers
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Coordinate projections of finite free module sheaves

These maps extract actual regular coefficients of local frame sections.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- Projection onto one specified coordinate of the actual finite free module sheaf.
Source: Hartshorne, Algebraic Geometry, II.5, finite free sheaves and local frames. -/
def i1_freeSheafProjection (T : Scheme.{0}) (k : ℕ) (i : Fin k) :
    SheafOfModules.free.{0} (R := T.ringCatSheaf) (Fin k) ⟶
      SheafOfModules.unit.{0} T.ringCatSheaf :=
  Sigma.desc (fun j : Fin k => if j = i then 𝟙 _ else 0)

/-- A free-sheaf coordinate projection has its specified values on all summand injections.
Source: Hartshorne, Algebraic Geometry, II.5, coordinate maps of free sheaves. -/
theorem i1_freeSheafProjection_generator (T : Scheme.{0}) (k : ℕ) (i j : Fin k) :
    SheafOfModules.ιFree (R := T.ringCatSheaf) j ≫ i1_freeSheafProjection T k i =
      if j = i then 𝟙 _ else 0 := by
  exact Sigma.ι_comp_desc (fun j : Fin k => if j = i then 𝟙 _ else 0) j

/-- Pullback of each coordinate projection commutes with the actual free-sheaf comparison.
Source: Hartshorne, Algebraic Geometry, II.5, pullback of finite free sheaves. -/
theorem i1_freeSheafProjection_pullback {S T : Scheme.{0}} (a : S ⟶ T)
    (k : ℕ) (i : Fin k) :
    letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
      (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
    (Scheme.Modules.pullback a).map (i1_freeSheafProjection T k i) ≫
      SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom =
      (SheafOfModules.pullbackObjFreeIso a.toRingCatSheafHom (Fin k)).hom ≫
        i1_freeSheafProjection S k i := by
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  let F := Scheme.Modules.pullback a
  letI := (SheafOfModules.pullbackPushforwardAdjunction a.toRingCatSheafHom).leftAdjoint_preservesColimits
  let p := SheafOfModules.pullbackObjFreeIso a.toRingCatSheafHom (Fin k)
  let u := SheafOfModules.pullbackObjUnitToUnit a.toRingCatSheafHom
  apply (isColimitOfPreserves F
    (SheafOfModules.isColimitFreeCofan (R := T.ringCatSheaf) (Fin k))).hom_ext
  intro j
  change F.map (SheafOfModules.ιFree j.as) ≫
      (F.map (i1_freeSheafProjection T k i) ≫ u) =
    F.map (SheafOfModules.ιFree j.as) ≫ (p.hom ≫ i1_freeSheafProjection S k i)
  have hgen : F.map (SheafOfModules.ιFree j.as) ≫ p.hom =
      u ≫ SheafOfModules.ιFree j.as :=
    SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom
      (φ := a.toRingCatSheafHom) j.as
  have hleft : F.map (SheafOfModules.ιFree j.as) ≫
      F.map (i1_freeSheafProjection T k i) ≫ u =
      F.map (if j.as = i then 𝟙 _ else 0) ≫ u := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ u) (F.map_comp _ _).symm).trans
        (congrArg (fun z => F.map z ≫ u) (i1_freeSheafProjection_generator T k i j.as)))
  have hright : F.map (SheafOfModules.ιFree j.as) ≫ p.hom ≫
      i1_freeSheafProjection S k i = u ≫ (if j.as = i then 𝟙 _ else 0) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ i1_freeSheafProjection S k i) hgen).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z => u ≫ z) (i1_freeSheafProjection_generator S k i j.as))))
  apply hleft.trans
  apply Eq.trans _ hright.symm
  by_cases hj : j.as = i
  · simp only [if_pos hj, Category.comp_id]
    exact (congrArg (fun z => z ≫ u) (F.map_id _)).trans (Category.id_comp _)
  · simp only [if_neg hj, Functor.map_zero, comp_zero, zero_comp]

end HodgeLean.Foundations.BundleThom
