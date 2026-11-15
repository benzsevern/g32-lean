import HodgeLean.Foundations.Program.RigidStartingSystemHomAction
import HodgeLean.Foundations.Program.RigidStartingSystemTraceDual

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

theorem b65r_dual_fixed_intertwiner {n r : ℕ}
    (T S : Fin r → (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (Y : Matrix (Fin n) (Fin n) ℂ)
    (hf : ∀ i, (b65r_traceDual n Y).comp (b65r_homAction (S i) (T i)) =
      b65r_traceDual n Y) :
    ∀ i, (T i).val*Y = Y*(S i).val := by
  intro i
  have hi : ((T i)⁻¹).val*Y*(S i).val = Y := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro X
    have he := congrArg (fun f : Module.Dual ℂ (Matrix (Fin n) (Fin n) ℂ) ↦ f X) (hf i)
    change trace (Y*((S i).val*X*((T i)⁻¹).val)) = trace (Y*X) at he
    calc
      trace ((((T i)⁻¹).val*Y*(S i).val)*X) =
          trace (((T i)⁻¹).val*(Y*((S i).val*X))) := by congr 1; noncomm_ring
      _ = trace ((Y*((S i).val*X))*((T i)⁻¹).val) := trace_mul_comm _ _
      _ = trace (Y*((S i).val*X*((T i)⁻¹).val)) := by congr 1; noncomm_ring
      _ = trace (Y*X) := he
  calc
    (T i).val*Y = (T i).val*(((T i)⁻¹).val*Y*(S i).val) := by rw [hi]
    _ = Y*(S i).val := by simp [mul_assoc]

end HodgeLean.Foundations.Program
