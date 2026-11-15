import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bTransitions

noncomputable section
open scoped Topology ContDiff Manifold

namespace HodgeLean.Foundations.Program

def b6a_valueShift (t : Fin 10 → ℂ) (j : Fin 13) : ℂ :=
  if h : j.val < 10 then t ⟨j.val, h⟩ else if j.val = 11 then 1 else 0

theorem b6a_value_finite (t : Fin 10 → ℂ) (j : Fin 13) (hj : j.val ≠ 12) (w : ℂ) :
    b6a_value t j w = ((b6a_valueShift t j + w : ℂ) : OnePoint ℂ) := by
  unfold b6a_value b6a_valueShift
  split_ifs <;> simp_all [add_comm]
  omega

theorem b6a_value_infinite (t : Fin 10 → ℂ) (j : Fin 13) (hj : j.val = 12) (w : ℂ) :
    b6a_value t j w = b4cov_sphInv (w : OnePoint ℂ) := by
  simp [b6a_value, hj]

end HodgeLean.Foundations.Program
