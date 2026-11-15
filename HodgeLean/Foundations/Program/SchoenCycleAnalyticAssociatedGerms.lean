import HodgeLean.Foundations.Program.SchoenCycleAnalyticGermPullback

/-! # Analytic representatives of associated germ equations -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Foundations.Program

/-- Associated actual analytic germs have an analytic unit representative comparing their original equations.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, II.B and III.A. -/
theorem s2e_associated_analyticGerms_unit {n : ℕ} {p : Fin n → ℂ}
    (F G : (Fin n → ℂ) → ℂ) (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (h : Associated (⟨Filter.Germ.ofFun F, F, hF, rfl⟩ : AnalyticGermAt n p)
      (⟨Filter.Germ.ofFun G, G, hG, rfl⟩ : AnalyticGermAt n p)) :
    ∃ η : (Fin n → ℂ) → ℂ, AnalyticAt ℂ η p ∧ η p ≠ 0 ∧
      F =ᶠ[𝓝 p] fun z => η z * G z := by
  obtain ⟨w, hw⟩ := h.symm
  obtain ⟨η, hη, hηw⟩ := (w : AnalyticGermAt n p).2
  refine ⟨η, hη, ?_, ?_⟩
  · have hv := (w.isUnit.map (analyticGermAtValue n p)).ne_zero
    change (w : AnalyticGermAt n p).val.value ≠ 0 at hv
    rwa [← hηw, Filter.Germ.value_ofFun] at hv
  · apply Filter.Germ.coe_eq.mp
    calc
      Filter.Germ.ofFun F =
          ((⟨Filter.Germ.ofFun G, G, hG, rfl⟩ : AnalyticGermAt n p) * w).val :=
        (congrArg Subtype.val hw).symm
      _ = Filter.Germ.ofFun G * (w : AnalyticGermAt n p).val := rfl
      _ = Filter.Germ.ofFun G * Filter.Germ.ofFun η := congrArg₂ (· * ·) rfl hηw.symm
      _ = Filter.Germ.ofFun (fun z => η z * G z) := by rw [mul_comm]; rfl

end HodgeLean.Foundations.Program
