import HodgeLean.Foundations.Program.SchoenCycleU1Germs

/-! # Analytic germs evaluated to first order -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- Differentiation at zero is well defined on actual analytic function germs.
Source: Mathlib, `Filter.EventuallyEq.deriv_eq`; Hartshorne, Algebraic Geometry, II.8. -/
def s2e_u1_germDerivative (f : s2e_u1_analyticGermRing) : ℂ :=
  f.val.liftOn (fun F : ℂ → ℂ => deriv F 0) (fun _ _ h => h.deriv_eq)

/-- The first Taylor jet of an analytic germ, valued in the complex dual numbers.
Source: Hartshorne, Algebraic Geometry, II.8, tangent vectors;
Mathlib, `deriv_add` and `deriv_mul`. -/
def s2e_u1_analyticGermJet : s2e_u1_analyticGermRing →+* DualNumber ℂ where
  toFun f := TrivSqZeroExt.inl f.val.value + TrivSqZeroExt.inr (s2e_u1_germDerivative f)
  map_zero' := by
    change TrivSqZeroExt.inl (0 : ℂ) + TrivSqZeroExt.inr (deriv (fun _ : ℂ => (0 : ℂ)) 0) = 0
    simp
  map_one' := by
    change TrivSqZeroExt.inl (1 : ℂ) + TrivSqZeroExt.inr (deriv (fun _ : ℂ => (1 : ℂ)) 0) = 1
    simp
  map_add' f g := by
    rcases f with ⟨_, F, hF, rfl⟩
    rcases g with ⟨_, G, hG, rfl⟩
    change TrivSqZeroExt.inl (F 0 + G 0) +
      TrivSqZeroExt.inr (deriv (fun z => F z + G z) 0) =
        (TrivSqZeroExt.inl (F 0) + TrivSqZeroExt.inr (deriv F 0)) +
          (TrivSqZeroExt.inl (G 0) + TrivSqZeroExt.inr (deriv G 0))
    rw [deriv_fun_add hF.differentiableAt hG.differentiableAt]
    ext <;> simp
  map_mul' f g := by
    rcases f with ⟨_, F, hF, rfl⟩
    rcases g with ⟨_, G, hG, rfl⟩
    change TrivSqZeroExt.inl (F 0 * G 0) +
      TrivSqZeroExt.inr (deriv (fun z => F z * G z) 0) =
        (TrivSqZeroExt.inl (F 0) + TrivSqZeroExt.inr (deriv F 0)) *
          (TrivSqZeroExt.inl (G 0) + TrivSqZeroExt.inr (deriv G 0))
    rw [deriv_fun_mul hF.differentiableAt hG.differentiableAt]
    ext <;> simp [DualNumber.snd_mul, add_comm]

/-- On an analytic representative the jet is exactly value plus derivative times ε.
Source: Hartshorne, Algebraic Geometry, II.8, dual-number tangent vectors. -/
@[simp] theorem s2e_u1_analyticGermJet_representative
    (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0) :
    s2e_u1_analyticGermJet (s2e_u1_analyticGerm F hF) =
      TrivSqZeroExt.inl (F 0) + TrivSqZeroExt.inr (deriv F 0) := rfl

end HodgeLean.Foundations.Program
