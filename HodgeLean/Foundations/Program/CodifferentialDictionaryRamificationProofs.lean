import HodgeLean.Ported.TauCeti.TauCeti.Analysis.Contour.Residue.Basic

noncomputable section
open Filter Topology
namespace HodgeLean.Foundations.Program

theorem b66d_residue_power_simple {H : ℂ → ℂ} {s : ℂ} {e : ℕ}
    (he : 0 < e) (hH : AnalyticAt ℂ H s) :
    TauCeti.Contour.residue
      (fun z : ℂ => (e : ℂ) * z ^ (e - 1) * H (s + z ^ e) / z ^ e) 0 =
      (e : ℂ) * H s := by
  have hform : (fun z : ℂ => (e : ℂ) * z ^ (e - 1) * H (s + z ^ e) / z ^ e) =
      (fun z : ℂ => ((e : ℂ) * H (s + z ^ e)) / (z - 0) ^ (0 + 1)) := by
    funext z
    by_cases hz : z = 0
    · simp [hz, zero_pow (Nat.ne_of_gt he)]
    · have hp : z ^ e = z ^ (e - 1) * z := by
        rw [← pow_succ]
        congr 1
        omega
      simp only [sub_zero, zero_add, pow_one]
      rw [hp]
      field_simp
  have hcomp : AnalyticAt ℂ (fun z : ℂ => H (s + z ^ e)) 0 := by
    apply AnalyticAt.comp (by simpa only [zero_pow (Nat.ne_of_gt he), add_zero] using hH)
    fun_prop
  have han : AnalyticAt ℂ (fun z : ℂ => (e : ℂ) * H (s + z ^ e)) 0 :=
    analyticAt_const.mul hcomp
  rw [hform]
  simpa only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    zero_pow (Nat.ne_of_gt he), add_zero] using
      TauCeti.Contour.residue_div_sub_pow_of_analyticAt han 0

end HodgeLean.Foundations.Program
