import HodgeLean.Foundations.Program.G32Native.NormalEvaluationTopology
import HodgeLean.Foundations.Curves.Picard.LineBundles.UnitComparisonForms

/-! # The original module section specialization retains the structure-module unit -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual local section specialization carries the canonical unit section
to one under the original point's structure-module comparison. -/
theorem moduleSectionValue_unit (W : Over (Spec ↧ℂ)) (U : W.left.Opens)
    (p : ComplexPoint W) (hp : p ∈ Point.overOpen U) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit p.left).hom
      (moduleSectionValue (unit W.left) U
        (pullbackUnit U.ι).inv p hp) = (1 : Γ(Spec ↧ℂ, ⊤)) := by
  let a := liftToOpen W U p hp
  let t := (pullbackUnit a).inv ≫
    (Scheme.Modules.pullback a).map (pullbackUnit U.ι).inv ≫
    ((Scheme.Modules.pullbackComp a U.ι).app (unit W.left)).hom ≫
    ((Scheme.Modules.pullbackCongr (liftToOpen_fac W U p hp)).app
      (unit W.left)).hom
  have hc := pullbackUnit_composition_hom a U.ι
  have hg := pullbackUnit_congr (liftToOpen_fac W U p hp)
  have ht : t ≫ (pullbackUnit p.left).hom = 𝟙 _ := by
    dsimp only [t]
    simp only [Category.assoc]
    rw [hg, ← hc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, (Scheme.Modules.pullback a).map_id,
      Category.id_comp, Iso.inv_hom_id]
  change (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit p.left).hom
    ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map t (1 : Γ(Spec ↧ℂ, ⊤))) = _
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, ht]
  rfl

/-- The canonical unit section specializes to the inverse image of one
under the original point pullback-unit comparison. -/
theorem moduleSectionValue_unit_inverse (W : Over (Spec ↧ℂ)) (U : W.left.Opens)
    (p : ComplexPoint W) (hp : p ∈ Point.overOpen U) :
    moduleSectionValue (unit W.left) U (pullbackUnit U.ι).inv p hp =
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit p.left).inv
        (1 : Γ(Spec ↧ℂ, ⊤)) := by
  let e := ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    (pullbackUnit p.left)).toLinearEquiv
  exact (e.symm_apply_eq.mpr (moduleSectionValue_unit W U p hp).symm).symm

/-- A pulled-back original global section specializes by pulling that same
morphism to the point and applying it to the original point unit. -/
theorem moduleSectionValue_global (W : Over (Spec ↧ℂ)) (M : W.left.Modules)
    (s : unit W.left ⟶ M) (U : W.left.Opens)
    (p : ComplexPoint W) (hp : p ∈ Point.overOpen U) :
    moduleSectionValue M U
      ((pullbackUnit U.ι).inv ≫ (Scheme.Modules.pullback U.ι).map s) p hp =
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullback p.left).map s)
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit p.left).inv
          (1 : Γ(Spec ↧ℂ, ⊤))) := by
  rw [moduleSectionValue_transport, moduleSectionValue_unit_inverse]

#print axioms moduleSectionValue_global
#print axioms moduleSectionValue_unit_inverse
#print axioms moduleSectionValue_unit
end HodgeLean.Foundations.Program.G32Native
