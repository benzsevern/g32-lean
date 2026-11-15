import HodgeLean.Foundations.Program.G32Native.QuaternionActionRelations
import Mathlib.Tactic.Module

noncomputable section
set_option maxHeartbeats 200000
open scoped Quaternion TensorProduct
namespace HodgeLean.Foundations.Program.QuaternionGraph
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {a b : ℚ}

/-- Complex scalar extension converts rational scalar multiplication to its complex image. -/
theorem baseChange_rat_smul (r : ℚ) (f : Module.End ℚ V) :
    (r • f).baseChange ℂ = (r : ℂ) • f.baseChange ℂ := by
  rw [LinearMap.baseChange_smul]
  apply LinearMap.ext
  intro x
  exact (algebraMap_smul ℂ r (f.baseChange ℂ x)).symm

/-- The complexified second generator has the same nonzero scalar square. -/
theorem quaternionActionC_j_sq (ρ : ℍ[ℚ,a,0,b] →ₐ[ℚ] (Module.End ℚ V)ᵐᵒᵖ) :
    (quaternionActionC ρ (quaternionJ a b)).comp (quaternionActionC ρ (quaternionJ a b)) =
      (b : ℂ) • LinearMap.id := by
  unfold quaternionActionC
  rw [← LinearMap.baseChange_comp, quaternionAction_j_sq, baseChange_rat_smul,
    LinearMap.baseChange_id]

/-- The complexified pure generators anticommute. -/
theorem quaternionActionC_anticommute (ρ : ℍ[ℚ,a,0,b] →ₐ[ℚ] (Module.End ℚ V)ᵐᵒᵖ) :
    (quaternionActionC ρ (quaternionI a b)).comp (quaternionActionC ρ (quaternionJ a b)) =
      -((quaternionActionC ρ (quaternionJ a b)).comp (quaternionActionC ρ (quaternionI a b))) := by
  unfold quaternionActionC
  rw [← LinearMap.baseChange_comp, quaternionAction_anticommute,
    LinearMap.baseChange_neg, LinearMap.baseChange_comp]

/-- Complexified quaternion coordinates retain the contravariant product order. -/
theorem quaternionActionC_coordinates (ρ : ℍ[ℚ,a,0,b] →ₐ[ℚ] (Module.End ℚ V)ᵐᵒᵖ)
    (q : ℍ[ℚ,a,0,b]) :
    quaternionActionC ρ q = (q.re : ℂ) • LinearMap.id +
      (q.imI : ℂ) • quaternionActionC ρ (quaternionI a b) +
      (q.imJ : ℂ) • quaternionActionC ρ (quaternionJ a b) +
      (q.imK : ℂ) • ((quaternionActionC ρ (quaternionJ a b)).comp
        (quaternionActionC ρ (quaternionI a b))) := by
  unfold quaternionActionC
  rw [quaternionAction_coordinates]
  simp only [LinearMap.baseChange_add, baseChange_rat_smul, LinearMap.baseChange_id,
    LinearMap.baseChange_comp]

/-- On one eigenspace, every quaternion has two frame-independent coefficients. -/
theorem quaternionActionC_eigenvector (ρ : ℍ[ℚ,a,0,b] →ₐ[ℚ] (Module.End ℚ V)ᵐᵒᵖ)
    (q : ℍ[ℚ,a,0,b]) (w : ℂ) (x : ℂ ⊗[ℚ] V)
    (hx : quaternionActionC ρ (quaternionI a b) x = w • x) :
    quaternionActionC ρ q x = ((q.re : ℂ) + (q.imI : ℂ)*w) • x +
      ((q.imJ : ℂ) + (q.imK : ℂ)*w) • quaternionActionC ρ (quaternionJ a b) x := by
  rw [quaternionActionC_coordinates]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.comp_apply, hx, map_smul]
  module

/-- The action on the paired opposite-eigenvector frame uses the same four coordinates. -/
theorem quaternionActionC_paired (ρ : ℍ[ℚ,a,0,b] →ₐ[ℚ] (Module.End ℚ V)ᵐᵒᵖ)
    (q : ℍ[ℚ,a,0,b]) (w : ℂ) (x : ℂ ⊗[ℚ] V)
    (hx : quaternionActionC ρ (quaternionI a b) x = w • x) :
    quaternionActionC ρ q (quaternionActionC ρ (quaternionJ a b) x) =
      ((b : ℂ)*((q.imJ : ℂ) - (q.imK : ℂ)*w)) • x +
      ((q.re : ℂ) - (q.imI : ℂ)*w) • quaternionActionC ρ (quaternionJ a b) x := by
  let I := quaternionActionC ρ (quaternionI a b)
  let J := quaternionActionC ρ (quaternionJ a b)
  have hI : I (J x) = (-w) • J x := by
    have h := LinearMap.congr_fun (quaternionActionC_anticommute ρ) x
    simpa only [LinearMap.comp_apply, LinearMap.neg_apply, hx, map_smul, neg_smul] using h
  have hJ : J (J x) = (b : ℂ) • x :=
    LinearMap.congr_fun (quaternionActionC_j_sq ρ) x
  rw [quaternionActionC_eigenvector ρ q (-w) (J x) hI]
  change _ • J x + _ • J (J x) = _
  rw [hJ]
  module

#print axioms quaternionActionC_paired
end HodgeLean.Foundations.Program.QuaternionGraph
