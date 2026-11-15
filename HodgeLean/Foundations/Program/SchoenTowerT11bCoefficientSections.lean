import HodgeLean.Foundations.Program.SchoenTowerT11bCoefficientRootBounds
import Mathlib.Data.Fintype.EquivFin

/-! Finite local enumeration over Banach parameter spaces without a degree drop.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open Filter
open scoped Topology

/-- A simple fiber without a degree drop has finitely many distinct smooth real root sections nearby.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, higher-dimensional local enumeration step. -/
theorem s2v_t11b_smooth_coefficient_simple_fiber_sections {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (P : Polynomial (V → ℝ)) (hP : ∀ i, ContDiff ℝ (⊤ : WithTop ℕ∞) (P.coeff i))
    (a : V) (hlead : P.leadingCoeff a ≠ 0)
    (hsimple : ∀ x : ℝ, P.eval₂ (Pi.evalRingHom (fun _ : V => ℝ) a) x = 0 →
      (P.map (Pi.evalRingHom (fun _ : V => ℝ) a)).derivative.eval x ≠ 0) :
    ∃ m : ℕ, ∃ ε : ℝ, ∃ d : Fin m → ℝ, ∃ ψ : Fin m → V → ℝ,
      0 < ε ∧ Function.Injective d ∧
      (∀ i, ψ i a = d i ∧ ContDiffOn ℝ 1 (ψ i) (Metric.ball a ε)) ∧
      (∀ t ∈ Metric.ball a ε, Function.Injective (fun i => ψ i t)) ∧
      ∀ t ∈ Metric.ball a ε, ∀ x : ℝ,
        P.eval₂ (Pi.evalRingHom (fun _ : V => ℝ) t) x = 0 ↔ ∃ i, x = ψ i t := by
  classical
  let q := P.map (Pi.evalRingHom (fun _ : V => ℝ) a)
  let R := {x : ℝ // x ∈ q.roots.toFinset}
  let m := Fintype.card R
  let E : Fin m ≃ R := (Fintype.equivFin R).symm
  let d : Fin m → ℝ := fun i => (E i).val
  have hq : q ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp (by
    change (P.map (Pi.evalRingHom (fun _ : V => ℝ) a)).leadingCoeff ≠ 0
    rw [P.leadingCoeff_map_of_leadingCoeff_ne_zero (Pi.evalRingHom (fun _ : V => ℝ) a) hlead]
    exact hlead)
  have hd : Function.Injective d := Subtype.val_injective.comp E.injective
  have hroot : ∀ i, P.eval₂ (Pi.evalRingHom (fun _ : V => ℝ) a) (d i) = 0 := by
    intro i
    have hi := (Polynomial.mem_roots hq).mp (Multiset.mem_toFinset.mp (E i).property)
    simpa only [Polynomial.IsRoot.def, q, ← Polynomial.eval₂_eq_eval_map] using hi
  have hsections := fun i : Fin m =>
    s2v_t11b_smooth_coefficient_simple_root_section P hP a (d i) (hroot i) (hsimple (d i) (hroot i))
  choose ψ hψa hψ heq hzero using hsections
  have hrects : ∀ i, ∃ r : ℝ, 0 < r ∧
      ∀ t ∈ Metric.ball a r, ∀ x ∈ Metric.ball (d i) r,
        P.eval₂ (Pi.evalRingHom (fun _ : V => ℝ) t) x = 0 ↔ ψ i t = x := by
    intro i
    obtain ⟨r, hr, hrect⟩ := Metric.eventually_nhds_iff.mp (heq i)
    refine ⟨r, hr, ?_⟩
    intro t ht x hx
    apply hrect (y := (t, x))
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨Metric.mem_ball.mp ht, Metric.mem_ball.mp hx⟩
  choose r hr hrect using hrects
  let U : Set ℝ := ⋃ i : Fin m, Metric.ball (d i) (r i)
  have hU : IsOpen U := isOpen_iUnion (fun i => Metric.isOpen_ball)
  have hcover : ∀ x : ℝ, P.eval₂ (Pi.evalRingHom (fun _ : V => ℝ) a) x = 0 → x ∈ U := by
    intro x hx
    have hqx : q.IsRoot x := by
      simpa only [Polynomial.IsRoot.def, q, ← Polynomial.eval₂_eq_eval_map] using hx
    let z : R := ⟨x, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr hqx)⟩
    let i := E.symm z
    have hdi : d i = x := congrArg Subtype.val (E.apply_symm_apply z)
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [← hdi]
    exact Metric.mem_ball_self (hr i)
  obtain ⟨ε₀, hε₀, hstay⟩ := Metric.eventually_nhds_iff.mp
    (s2v_t11b_continuous_coefficient_roots_stay_in P (fun i => (hP i).continuous) a hlead U hU hcover)
  have hregular : ∀ᶠ t in 𝓝 a, ∀ i : Fin m,
      ContDiffAt ℝ 1 (ψ i) t ∧ P.eval₂ (Pi.evalRingHom (fun _ : V => ℝ) t) (ψ i t) = 0 ∧
        t ∈ Metric.ball a (r i) := by
    apply eventually_all.mpr
    intro i
    exact ((hψ i).eventually (by norm_num)).and
      ((hzero i).and (Metric.ball_mem_nhds a (hr i)))
  have hdistinct : ∀ᶠ t in 𝓝 a, Function.Injective (fun i => ψ i t) := by
    have hpair : ∀ᶠ t in 𝓝 a, ∀ i j : Fin m, i ≠ j → ψ i t ≠ ψ j t := by
      apply eventually_all.mpr
      intro i
      apply eventually_all.mpr
      intro j
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
      · have hn : ψ i a ≠ ψ j a := by simpa only [hψa i, hψa j] using hd.ne hij
        exact (((hψ i).continuousAt.ne_iff_eventually_ne (hψ j).continuousAt).mp hn).mono
          (fun _ h _ => h)
    filter_upwards [hpair] with t ht
    intro i j hij
    by_contra hne
    exact ht i j hne hij
  obtain ⟨s, hs, hsmall⟩ := Metric.eventually_nhds_iff.mp (hregular.and hdistinct)
  refine ⟨m, min ε₀ s, d, ψ, lt_min hε₀ hs, hd, ?_, ?_, ?_⟩
  · intro i
    refine ⟨hψa i, ?_⟩
    intro t ht
    exact ((hsmall ((Metric.mem_ball.mp ht).trans_le (min_le_right ε₀ s))).1 i).1.contDiffWithinAt
  · intro t ht
    exact (hsmall ((Metric.mem_ball.mp ht).trans_le (min_le_right ε₀ s))).2
  · intro t ht x
    have hreg := (hsmall ((Metric.mem_ball.mp ht).trans_le (min_le_right ε₀ s))).1
    constructor
    · intro hx
      have hxU := hstay (y := t) ((Metric.mem_ball.mp ht).trans_le (min_le_left ε₀ s)) x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
      exact ⟨i, ((hrect i t (hreg i).2.2 x hi).mp hx).symm⟩
    · rintro ⟨i, rfl⟩
      exact (hreg i).2.1

end HodgeLean.Foundations.Program
