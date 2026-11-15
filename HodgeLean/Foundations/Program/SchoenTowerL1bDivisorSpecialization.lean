import Mathlib.AlgebraicGeometry.FunctionField

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Specializing the stalk argument does not change its image in the actual function field. -/
theorem s2v_l1b_divisor_specialization_function_field
    (X : Scheme.{0}) [IsIntegral X] {x y : X} (h : x ⤳ y)
    (a : X.presheaf.stalk y) :
    algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.stalkSpecializes h).hom a) =
      algebraMap (X.presheaf.stalk y) X.functionField a := by
  have H := X.presheaf.stalkSpecializes_comp (genericPoint_specializes x) h
  exact congrArg (fun f : X.presheaf.stalk y ⟶ X.functionField => f.hom a) H

end HodgeLean.Foundations.Program
