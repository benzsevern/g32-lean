import HodgeLean.Foundations.Program.HolomorphicODELinearLimit

noncomputable section
open Set Metric Filter Topology
namespace HodgeLean.Foundations.Program

def b65_linearTerm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) (c : ℂ) (v : E) : ℕ → ℂ → E
  | 0 => fun _ ↦ v
  | n + 1 => b65_segmentPrimitive (fun x ↦ A x (b65_linearTerm A c v n x)) c

theorem b65_linearTerm_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {A : ℂ → E →L[ℂ] E} {c : ℂ} {R : ℝ} (v : E)
    (hA : AnalyticOnNhd ℂ A (ball c R)) :
    ∀ n, AnalyticOnNhd ℂ (b65_linearTerm A c v n) (ball c R) := by
  intro n
  induction n with
  | zero => exact fun x hx ↦ analyticAt_const
  | succ n ih =>
    have hd := hA.differentiableOn.clm_apply ih.differentiableOn
    apply DifferentiableOn.analyticOnNhd _ isOpen_ball
    intro x hx
    exact (b65_segmentPrimitive_hasDerivAt hd hx).differentiableAt.differentiableWithinAt

theorem b65_linearTerm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : ℂ → E →L[ℂ] E} {c : ℂ} {r C : ℝ} (hC : 0 ≤ C) (v : E)
    (hb : ∀ x ∈ ball c r, ‖A x‖ ≤ C) :
    ∀ n x, x ∈ ball c r → ‖b65_linearTerm A c v n x‖ ≤ ‖v‖ * C ^ n * ‖x - c‖ ^ n / n.factorial := by
  intro n
  induction n with
  | zero => intro x hx; simp [b65_linearTerm]
  | succ n ih =>
    intro x hx
    have hf : ∀ z ∈ ball c r, ‖A z (b65_linearTerm A c v n z)‖ ≤
        (‖v‖ * C ^ (n + 1) / n.factorial) * ‖z - c‖ ^ n := by
      intro z hz
      calc
        ‖A z (b65_linearTerm A c v n z)‖ ≤ ‖A z‖ * ‖b65_linearTerm A c v n z‖ := (A z).le_opNorm _
        _ ≤ C * (‖v‖ * C ^ n * ‖z - c‖ ^ n / n.factorial) :=
          mul_le_mul (hb z hz) (ih z hz) (norm_nonneg _) hC
        _ = (‖v‖ * C ^ (n + 1) / n.factorial) * ‖z - c‖ ^ n := by rw [pow_succ]; ring
    have hh := b65_segmentPrimitive_power_bound (by positivity : 0 ≤ ‖v‖ * C ^ (n + 1) / n.factorial) n hx hf
    change ‖b65_segmentPrimitive (fun z ↦ A z (b65_linearTerm A c v n z)) c x‖ ≤ _
    convert hh using 1
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_mul_eq_div_div]
    ring

theorem b65_linearPartial_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {A : ℂ → E →L[ℂ] E} {c : ℂ} {R : ℝ} (v : E)
    (hA : AnalyticOnNhd ℂ A (ball c R)) :
    ∀ n x, x ∈ ball c R → HasDerivAt
      (fun t ↦ ∑ i ∈ Finset.range (n + 1), b65_linearTerm A c v i t)
      (A x (∑ i ∈ Finset.range n, b65_linearTerm A c v i x)) x := by
  intro n
  induction n with
  | zero =>
    intro x hx
    simpa [b65_linearTerm] using hasDerivAt_const x v
  | succ n ih =>
    intro x hx
    have hh := b65_segmentPrimitive_hasDerivAt
      (hA.differentiableOn.clm_apply (b65_linearTerm_analytic v hA n).differentiableOn) hx
    have ht : HasDerivAt (b65_linearTerm A c v (n + 1))
        (A x (b65_linearTerm A c v n x)) x := hh
    convert (ih x hx).add ht using 1
    · funext t
      simp only [Pi.add_apply, Finset.sum_range_succ]
    · simp only [Finset.sum_range_succ, map_add]

end HodgeLean.Foundations.Program
