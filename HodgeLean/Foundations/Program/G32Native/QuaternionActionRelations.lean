import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.LinearMap.End

noncomputable section
set_option maxHeartbeats 200000
open scoped Quaternion TensorProduct
namespace HodgeLean.Foundations.Program.QuaternionGraph
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {a b : ℚ}

/-- The first pure quaternion generator. -/
def quaternionI (a b : ℚ) : ℍ[ℚ,a,0,b] := ⟨0,1,0,0⟩
/-- The second pure quaternion generator. -/
def quaternionJ (a b : ℚ) : ℍ[ℚ,a,0,b] := ⟨0,0,1,0⟩

/-- Quaternion coordinates in the ordered basis `1,i,j,ij`. -/
theorem quaternion_coordinates (q : ℍ[ℚ,a,0,b]) :
    q = q.re • 1 + q.imI • quaternionI a b + q.imJ • quaternionJ a b +
      q.imK • (quaternionI a b * quaternionJ a b) := by
  ext <;> simp [quaternionI, quaternionJ]

/-- The contravariant rational action associated with a quaternion algebra map. -/
def quaternionAction (ρ : ℍ[ℚ,a,0,b] →ₐ[ℚ] (Module.End ℚ V)ᵐᵒᵖ)
    (q : ℍ[ℚ,a,0,b]) : Module.End ℚ V := (ρ q).unop

/-- The same action after extending scalars to the complex numbers. -/
def quaternionActionC (ρ : ℍ[ℚ,a,0,b] →ₐ[ℚ] (Module.End ℚ V)ᵐᵒᵖ)
    (q : ℍ[ℚ,a,0,b]) : Module.End ℂ (ℂ ⊗[ℚ] V) :=
  (quaternionAction ρ q).baseChange ℂ

/-- The first generator retains its prescribed scalar square. -/
theorem quaternionAction_i_sq (ρ : ℍ[ℚ,a,0,b] →ₐ[ℚ] (Module.End ℚ V)ᵐᵒᵖ) :
    (quaternionAction ρ (quaternionI a b)).comp (quaternionAction ρ (quaternionI a b)) =
      a • LinearMap.id := by
  have h : quaternionI a b * quaternionI a b = a • (1 : ℍ[ℚ,a,0,b]) := by
    ext <;> simp [quaternionI]
  have he := congrArg (fun q => (ρ q).unop) h
  simpa only [map_mul, map_smul, map_one, MulOpposite.unop_mul,
    MulOpposite.unop_smul, MulOpposite.unop_one, quaternionAction, Module.End.mul_eq_comp, Module.End.one_eq_id] using he

/-- The second generator retains its prescribed scalar square. -/
theorem quaternionAction_j_sq (ρ : ℍ[ℚ,a,0,b] →ₐ[ℚ] (Module.End ℚ V)ᵐᵒᵖ) :
    (quaternionAction ρ (quaternionJ a b)).comp (quaternionAction ρ (quaternionJ a b)) =
      b • LinearMap.id := by
  have h : quaternionJ a b * quaternionJ a b = b • (1 : ℍ[ℚ,a,0,b]) := by
    ext <;> simp [quaternionJ]
  have he := congrArg (fun q => (ρ q).unop) h
  simpa only [map_mul, map_smul, map_one, MulOpposite.unop_mul,
    MulOpposite.unop_smul, MulOpposite.unop_one, quaternionAction, Module.End.mul_eq_comp, Module.End.one_eq_id] using he

/-- Contravariance preserves anticommutation of the two pure generators. -/
theorem quaternionAction_anticommute (ρ : ℍ[ℚ,a,0,b] →ₐ[ℚ] (Module.End ℚ V)ᵐᵒᵖ) :
    (quaternionAction ρ (quaternionI a b)).comp (quaternionAction ρ (quaternionJ a b)) =
      -((quaternionAction ρ (quaternionJ a b)).comp (quaternionAction ρ (quaternionI a b))) := by
  have h : quaternionJ a b * quaternionI a b = -(quaternionI a b * quaternionJ a b) := by
    ext <;> simp [quaternionI, quaternionJ]
  have he := congrArg (fun q => (ρ q).unop) h
  simpa only [map_mul, map_neg, MulOpposite.unop_mul, MulOpposite.unop_neg,
    quaternionAction, Module.End.mul_eq_comp, Module.End.one_eq_id] using he

/-- The action of an arbitrary quaternion uses four uniform frame coefficients. -/
theorem quaternionAction_coordinates (ρ : ℍ[ℚ,a,0,b] →ₐ[ℚ] (Module.End ℚ V)ᵐᵒᵖ)
    (q : ℍ[ℚ,a,0,b]) :
    quaternionAction ρ q = q.re • LinearMap.id + q.imI • quaternionAction ρ (quaternionI a b) +
      q.imJ • quaternionAction ρ (quaternionJ a b) +
      q.imK • ((quaternionAction ρ (quaternionJ a b)).comp
        (quaternionAction ρ (quaternionI a b))) := by
  have he := congrArg (fun q => (ρ q).unop) (quaternion_coordinates q)
  simpa only [map_add, map_mul, map_smul, map_one, MulOpposite.unop_add,
    MulOpposite.unop_mul, MulOpposite.unop_smul, MulOpposite.unop_one, quaternionAction, Module.End.mul_eq_comp, Module.End.one_eq_id] using he

#print axioms quaternionAction_coordinates
#print axioms quaternionAction_anticommute
end HodgeLean.Foundations.Program.QuaternionGraph
