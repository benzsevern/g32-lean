import HodgeLean.Adapters.NormalConeB4aGysinBridgeDefs
import HodgeLean.Adapters.NormalConeB4aGysinGlobalEvaluation

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluating a complex constant section returns that constant. -/
theorem a3b4a_gysin_evaluate_sectionConst
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of ℂ)) (U : X.Opens)
    (w : ComplexPoint (Over.mk q)) (hw : w.underlying ∈ U) (c : ℂ) :
    Point.evaluate (X := Over.mk q) U (a3b4a_gysin_sectionConst q U c) w = c := by
  let s := q.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)
  have hres := Point.evaluate_res (X := Over.mk q) (show U ≤ ⊤ from le_top) s w hw
  have hsection : a3b4a_gysin_sectionConst q U c =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s := rfl
  rw [hsection]
  exact hres.symm.trans (a3b4a_gysin_evaluate_global_constant q w c)

end HodgeLean.Adapters
