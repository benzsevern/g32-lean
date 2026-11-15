import HodgeLean.Foundations.Program.HolomorphicODEPrimitive
import HodgeLean.Foundations.Program.HolomorphicODELimit
import HodgeLean.Foundations.Program.HolomorphicODEEstimates

noncomputable section
open Set Metric Filter Topology
open scoped Interval
namespace HodgeLean.Foundations.Program

def b65_picardStep {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : P × (ℂ × E) → E) (c : ℂ) (F : P × (ℂ × E) → E)
    (q : P × (ℂ × E)) : E :=
  q.2.2 + b65_segmentPrimitive (fun x ↦ A (q.1, (x, F (q.1, (x, q.2.2))))) c q.2.1

def b65_picardIter {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : P × (ℂ × E) → E) (c : ℂ) : ℕ → P × (ℂ × E) → E
  | 0 => fun q ↦ q.2.2
  | n + 1 => b65_picardStep A c (b65_picardIter A c n)

theorem b65_picardStep_analytic {P E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    {A : P × (ℂ × E) → E} {c : ℂ} {r : ℝ} {U : Set P} {V W : Set E}
    (hU : IsOpen U) (hV : IsOpen V)
    (hA : AnalyticOnNhd ℂ A (U ×ˢ (ball c r ×ˢ W)))
    {F : P × (ℂ × E) → E}
    (hF : AnalyticOnNhd ℂ F (U ×ˢ (ball c r ×ˢ V)))
    (hFW : ∀ q ∈ U ×ˢ (ball c r ×ˢ V), F q ∈ W) :
    AnalyticOnNhd ℂ (b65_picardStep A c F) (U ×ˢ (ball c r ×ˢ V)) := by
  let B : (P × E) × ℂ → E := fun q ↦ A (q.1.1, (q.2, F (q.1.1, (q.2, q.1.2))))
  have hB : AnalyticOnNhd ℂ B ((U ×ˢ V) ×ˢ ball c r) := by
    intro q hq
    have hm : (q.1.1, (q.2, q.1.2)) ∈ U ×ˢ (ball c r ×ˢ V) :=
      ⟨hq.1.1, hq.2, hq.1.2⟩
    have hre : AnalyticAt ℂ (fun q : (P × E) × ℂ ↦ (q.1.1, (q.2, q.1.2))) q := by
      exact (analyticAt_fst.comp analyticAt_fst).prod
        (analyticAt_snd.prod (analyticAt_snd.comp analyticAt_fst))
    have hFc := (hF _ hm).comp (f := fun q : (P × E) × ℂ ↦ (q.1.1, (q.2, q.1.2))) hre
    apply (hA _ ⟨hq.1.1, hq.2, hFW _ hm⟩).comp
      (f := fun q : (P × E) × ℂ ↦ (q.1.1, (q.2, F (q.1.1, (q.2, q.1.2)))))
    exact ((analyticAt_fst.comp analyticAt_fst).prod (analyticAt_snd.prod hFc))
  have hprim := b65_segmentPrimitive_analytic_parameters (hU.prod hV) hB
  intro q hq
  have hm : ((q.1, q.2.2), q.2.1) ∈ (U ×ˢ V) ×ˢ ball c r := ⟨⟨hq.1, hq.2.2⟩, hq.2.1⟩
  have hre : AnalyticAt ℂ (fun q : P × (ℂ × E) ↦ ((q.1, q.2.2), q.2.1)) q := by
    exact (analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)).prod
      (analyticAt_fst.comp analyticAt_snd)
  exact (analyticAt_snd.comp analyticAt_snd).add
    ((hprim _ hm).comp (f := fun q : P × (ℂ × E) ↦ ((q.1, q.2.2), q.2.1)) hre)

theorem b65_picardStep_displacement {P E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : P × (ℂ × E) → E} {c : ℂ} {r M : ℝ} {U : Set P} {V W : Set E}
    (hM : 0 ≤ M) (hb : ∀ q ∈ U ×ˢ (ball c r ×ˢ W), ‖A q‖ ≤ M)
    {F : P × (ℂ × E) → E}
    (hFW : ∀ q ∈ U ×ˢ (ball c r ×ˢ V), F q ∈ W)
    {q : P × (ℂ × E)} (hq : q ∈ U ×ˢ (ball c r ×ˢ V)) :
    ‖b65_picardStep A c F q - q.2.2‖ ≤ r * M := by
  rw [b65_picardStep, add_sub_cancel_left]
  apply (b65_segmentPrimitive_norm_le hq.2.1 ?_).trans
    (mul_le_mul_of_nonneg_right (mem_ball_iff_norm.mp hq.2.1).le hM)
  intro x hx
  exact hb _ ⟨hq.1, hx, hFW _ ⟨hq.1, hx, hq.2.2⟩⟩

theorem b65_displacement_inner_ball {E : Type*} [NormedAddCommGroup E]
    {a v y : E} {S d : ℝ} (hd : d < S / 4) (hv : v ∈ ball y (S / 2))
    (ha : ‖a - v‖ ≤ d) : a ∈ ball y (3 * S / 4) := by
  rw [mem_ball, dist_eq_norm]
  have ht : ‖a - y‖ ≤ ‖a - v‖ + ‖v - y‖ := norm_sub_le_norm_sub_add_norm_sub a v y
  have hv' := mem_ball_iff_norm.mp hv
  linarith

theorem b65_picardIter_bounds {P E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    {A : P × (ℂ × E) → E} {c : ℂ} {y : E} {r S M : ℝ} {U : Set P}
    (hU : IsOpen U) (hr : 0 < r) (hS : 0 < S) (hM : 0 ≤ M) (hd : r * M < S / 4)
    (hA : AnalyticOnNhd ℂ A (U ×ˢ (ball c r ×ˢ ball y S)))
    (hb : ∀ q ∈ U ×ˢ (ball c r ×ˢ ball y S), ‖A q‖ ≤ M) (n : ℕ) :
    AnalyticOnNhd ℂ (b65_picardIter A c n) (U ×ˢ (ball c r ×ˢ ball y (S / 2))) ∧
      ∀ q ∈ U ×ˢ (ball c r ×ˢ ball y (S / 2)), ‖b65_picardIter A c n q - q.2.2‖ ≤ r * M := by
  induction n with
  | zero =>
    constructor
    · intro q hq
      exact analyticAt_snd.comp analyticAt_snd
    · intro q hq
      simpa [b65_picardIter] using mul_nonneg hr.le hM
  | succ n ih =>
    have hm : ∀ q ∈ U ×ˢ (ball c r ×ˢ ball y (S / 2)), b65_picardIter A c n q ∈ ball y S := by
      intro q hq
      exact ball_subset_ball (by linarith : 3 * S / 4 ≤ S)
        (b65_displacement_inner_ball hd hq.2.2 (ih.2 q hq))
    exact ⟨b65_picardStep_analytic hU isOpen_ball hA ih.1 hm,
      fun q hq ↦ b65_picardStep_displacement hM hb hm hq⟩

theorem b65_picardField_analytic {P E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    {A : P × (ℂ × E) → E} {c : ℂ} {r : ℝ} {U : Set P} {V W : Set E}
    (hA : AnalyticOnNhd ℂ A (U ×ˢ (ball c r ×ˢ W)))
    {F : P × (ℂ × E) → E}
    (hF : AnalyticOnNhd ℂ F (U ×ˢ (ball c r ×ˢ V)))
    (hFW : ∀ q ∈ U ×ˢ (ball c r ×ˢ V), F q ∈ W)
    {p : P} (hp : p ∈ U) {v : E} (hv : v ∈ V) :
    AnalyticOnNhd ℂ (fun x ↦ A (p, (x, F (p, (x, v))))) (ball c r) := by
  intro x hx
  have hm : (p, (x, v)) ∈ U ×ˢ (ball c r ×ˢ V) := ⟨hp, hx, hv⟩
  have hre : AnalyticAt ℂ (fun x : ℂ ↦ (p, (x, v))) x :=
    analyticAt_const.prod (analyticAt_id.prod analyticAt_const)
  have hFc := (hF _ hm).comp (f := fun x : ℂ ↦ (p, (x, v))) hre
  apply (hA _ ⟨hp, hx, hFW _ hm⟩).comp
    (f := fun x : ℂ ↦ (p, (x, F (p, (x, v)))))
  exact analyticAt_const.prod (analyticAt_id.prod hFc)

theorem b65_picardStep_hasDerivAt {P E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    {A : P × (ℂ × E) → E} {c : ℂ} {r : ℝ} {U : Set P} {V W : Set E}
    (hA : AnalyticOnNhd ℂ A (U ×ˢ (ball c r ×ˢ W)))
    {F : P × (ℂ × E) → E}
    (hF : AnalyticOnNhd ℂ F (U ×ˢ (ball c r ×ˢ V)))
    (hFW : ∀ q ∈ U ×ˢ (ball c r ×ˢ V), F q ∈ W)
    {p : P} (hp : p ∈ U) {v : E} (hv : v ∈ V) {x : ℂ} (hx : x ∈ ball c r) :
    HasDerivAt (fun t ↦ b65_picardStep A c F (p, (t, v)))
      (A (p, (x, F (p, (x, v))))) x := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hh := b65_segmentPrimitive_hasDerivAt
    (b65_picardField_analytic hA hF hFW hp hv).differentiableOn hx
  simpa [b65_picardStep] using hh.const_add v

end HodgeLean.Foundations.Program
