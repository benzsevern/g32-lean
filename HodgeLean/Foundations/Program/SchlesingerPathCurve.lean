import HodgeLean.Foundations.Program.SchlesingerPathDefs
import HodgeLean.Foundations.Program.PullbackMonodromyProofs
import HodgeLean.Foundations.Program.HurwitzTransport

noncomputable section
open Set Metric Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65p_curve_analyticAt (p : Fin 12 → ℂ) (hne : ∀ j, p j ≠ 0)
    (hab : p 10 ≠ p 11) : AnalyticAt ℂ (b65p_curve p) 0 := by
  have hm (j : Fin 12) : AnalyticAt ℂ
      (fun θ : ℂ ↦ p j + θ * b65p_V (b65p_fibre j) (p j)) 0 :=
    analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  unfold b65p_curve b65p_chartPoint b65s_normalize b65p_moving b65p_poles
  apply analyticAt_pi_iff.mpr
  intro i
  simp only [Sum.elim_inr]
  apply (((hm _).sub (hm 10)).mul (hm 11)).div ((hm _).mul ((hm 11).sub (hm 10)))
  simpa only [Pi.mul_apply, Pi.sub_apply, zero_mul, add_zero] using
    mul_ne_zero (hne (Fin.castLE (by norm_num) i)) (sub_ne_zero.mpr hab.symm)

theorem b65p_chartPoint_mem (p : Fin 12 → ℂ) (hinj : Function.Injective p)
    (hne : ∀ j, p j ≠ 0) : b65p_chartPoint p ∈ b6_chart := by
  have hab : p 11 - p 10 ≠ 0 := sub_ne_zero.mpr (fun h ↦ by
    have := hinj h; norm_num at this)
  apply b65s_chart_of
  · intro i j hij
    have h := b65s_normalize_injective (hne 10) (hne 11) hab (hne _) (hne _) hij
    have hh := congrArg (fun j : Fin 12 ↦ j.val) (hinj h)
    exact Fin.ext hh
  · intro i
    exact b65s_normalize_ne_zero (hne 11) hab (hne _) (fun h ↦ by
      have hh := congrArg Fin.val (hinj h)
      have hi := i.isLt
      simp only [Fin.val_castLE] at hh
      omega)
  · intro i
    exact b65s_normalize_ne_one (hne 10) hab (hne _) (fun h ↦ by
      have hh := congrArg Fin.val (hinj h)
      have hi := i.isLt
      simp only [Fin.val_castLE] at hh
      omega)

theorem b65p_curve_local (p : Fin 12 → ℂ) (hinj : Function.Injective p)
    (hne : ∀ j, p j ≠ 0) :
    AnalyticAt ℂ (b65p_curve p) 0 ∧ ContinuousAt (b65p_curve p) 0 ∧
    b65p_curve p 0 ∈ b6t_polydisc (b65p_curve p 0) ∧
    ∀ᶠ θ in 𝓝 (0 : ℂ), b65p_curve p θ ∈ b6t_polydisc (b65p_curve p 0) ∧
      b65p_curve p θ ∈ b6_chart := by
  have ha := b65p_curve_analyticAt p hne (fun h ↦ by have := hinj h; norm_num at this)
  have hzero : b65p_curve p 0 = b65p_chartPoint p := by
    simp only [b65p_curve]
    congr 1
    funext j
    simp [b65p_moving, b65p_poles]
  have hchart : b65p_curve p 0 ∈ b6_chart := hzero ▸ b65p_chartPoint_mem p hinj hne
  obtain ⟨hmem, _, hopen, hsub⟩ := b6t_polydisc_neighbourhood _ hchart
  exact ⟨ha, ha.continuousAt, hmem,
    (ha.continuousAt.eventually (hopen.mem_nhds hmem)).mono (fun θ hθ ↦ ⟨hθ, hsub hθ⟩)⟩

theorem b65p_normalize_hasDerivAt (a b z u v w : ℂ)
    (hz : z ≠ 0) (hab : b - a ≠ 0) :
    HasDerivAt (fun θ : ℂ ↦ b65s_normalize (a + θ * u) (b + θ * v) (z + θ * w))
      ((((w - u) * b + (z - a) * v) * (z * (b - a)) -
        ((z - a) * b) * (w * (b - a) + z * (v - u))) / (z * (b - a)) ^ 2) 0 := by
  have h (x y : ℂ) : HasDerivAt (fun θ : ℂ ↦ x + θ * y) y 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const y).const_add x
  convert
    ((((h z w).sub (h a u)).mul (h b v)).div
      ((h z w).mul ((h b v).sub (h a u))) (by simpa using mul_ne_zero hz hab)) using 1 <;>
    simp [b65s_normalize]
  rfl

theorem b65p_normalize_stationary_velocity (a b z u v w : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hz : z ≠ 0) (hab : b - a ≠ 0)
    (hzero : deriv (fun θ : ℂ ↦
      b65s_normalize (a + θ * u) (b + θ * v) (z + θ * w)) 0 = 0) :
    w = (u / a - (v / b - u / a) / (b - a) * a) * z +
      ((v / b - u / a) / (b - a)) * z ^ 2 := by
  have hn := (div_eq_zero_iff.mp
    ((b65p_normalize_hasDerivAt a b z u v w hz hab).deriv.symm.trans hzero)).resolve_right
      (pow_ne_zero 2 (mul_ne_zero hz hab))
  have hid :
      ((w - u) * b + (z - a) * v) * (z * (b - a)) -
        ((z - a) * b) * (w * (b - a) + z * (v - u)) =
      a * b * (b - a) *
        (w - ((u / a - (v / b - u / a) / (b - a) * a) * z +
          ((v / b - u / a) / (b - a)) * z ^ 2)) := by
    field_simp
    ring
  rw [hid] at hn
  exact sub_eq_zero.mp ((mul_eq_zero.mp hn).resolve_left
    (mul_ne_zero (mul_ne_zero ha hb) hab))

theorem b65p_V5_not_quadratic_on_six (q : Fin 6 → ℂ)
    (hq : Function.Injective q) (β γ : ℂ) :
    ¬ (∀ i, b65p_V5 (q i) = β * q i + γ * q i ^ 2) := by
  intro he
  let P : ℂ[X] := Polynomial.C (-3/7) * Polynomial.X ^ 5 +
    Polynomial.C (3/7) * Polynomial.X ^ 4 + Polynomial.C (3/7) * Polynomial.X ^ 3 +
    Polynomial.C (3/7) * Polynomial.X ^ 2 + Polynomial.C (1/7) * Polynomial.X -
    Polynomial.C (2/7) - Polynomial.C β * Polynomial.X - Polynomial.C γ * Polynomial.X ^ 2
  have hd : P.natDegree = 5 := by
    dsimp [P]
    compute_degree!
  have heval (i : Fin 6) : P.eval (q i) = 0 := by
    simp only [P, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    have hi := he i
    unfold b65p_V5 at hi
    linear_combination hi
  have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hq heval
    (by rw [hd]; norm_num)
  rw [hP, Polynomial.natDegree_zero] at hd
  norm_num at hd

theorem b65p_curve_deriv_ne_zero (p : Fin 12 → ℂ)
    (hinj : Function.Injective p) (hne : ∀ j, p j ≠ 0) :
    deriv (b65p_curve p) 0 ≠ 0 := by
  intro hzero
  have hab : p 11 - p 10 ≠ 0 := sub_ne_zero.mpr (fun h ↦ by
    have := hinj h
    norm_num at this)
  let γ := (b65p_V (b65p_fibre 11) (p 11) / p 11 -
    b65p_V (b65p_fibre 10) (p 10) / p 10) / (p 11 - p 10)
  let β := b65p_V (b65p_fibre 10) (p 10) / p 10 - γ * p 10
  have hv (j : Fin 12) : b65p_V (b65p_fibre j) (p j) = β * p j + γ * p j ^ 2 := by
    by_cases hj : j.val < 10
    · let i : Fin 10 := ⟨j.val, hj⟩
      have hd := hasDerivAt_pi.mp
        (b65p_curve_analyticAt p hne (fun h ↦ hab (sub_eq_zero.mpr h.symm))).differentiableAt.hasDerivAt i
      rw [hzero] at hd
      have hd0 : deriv (fun θ ↦ b65s_normalize
          (p 10 + θ * b65p_V (b65p_fibre 10) (p 10))
          (p 11 + θ * b65p_V (b65p_fibre 11) (p 11))
          (p j + θ * b65p_V (b65p_fibre j) (p j))) 0 = 0 := by
        simpa [b65p_curve, b65p_chartPoint, b65p_moving, b65p_poles, i] using hd.deriv
      exact b65p_normalize_stationary_velocity _ _ _ _ _ _ (hne 10) (hne 11) (hne j) hab hd0
    · have hj' : j = 10 ∨ j = 11 := by
        have := j.isLt
        omega
      rcases hj' with rfl | rfl <;> dsimp [β, γ] <;>
        field_simp [hne 10, hne 11, hab] <;> ring
  let labels : Fin 6 → Fin 12 := ![1, 3, 5, 6, 9, 10]
  have hlabels : Function.Injective labels := by decide
  have hfibre : ∀ i, b65p_fibre (labels i) = 5 := by decide
  apply b65p_V5_not_quadratic_on_six (fun i ↦ p (labels i)) (hinj.comp hlabels) β γ
  intro i
  simpa [hfibre i, b65p_V] using hv (labels i)

theorem b65p_moving_eventually_separated (p : Fin 12 → ℂ)
    (hinj : Function.Injective p) (hne : ∀ j, p j ≠ 0) :
    ∀ᶠ θ in 𝓝 (0 : ℂ), Function.Injective (b65p_moving p θ) ∧
      ∀ j, b65p_moving p θ j ≠ 0 := by
  have hc (j : Fin 12) : ContinuousAt (fun θ : ℂ ↦ b65p_moving p θ j) 0 := by
    exact continuousAt_const.add (continuousAt_id.mul continuousAt_const)
  have h0 (j : Fin 12) : b65p_moving p 0 j = p j := by
    simp [b65p_moving, b65p_poles]
  have hn : ∀ᶠ θ in 𝓝 (0 : ℂ), ∀ j, b65p_moving p θ j ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro j
    exact (hc j).eventually_ne (by rw [h0]; exact hne j)
  have hi : ∀ᶠ θ in 𝓝 (0 : ℂ), ∀ i j, i ≠ j →
      b65p_moving p θ i - b65p_moving p θ j ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ h ↦ (h hij).elim)
    · exact (((hc i).sub (hc j)).eventually_ne
        (by simpa only [Pi.sub_apply, h0] using
          sub_ne_zero.mpr (fun h ↦ hij (hinj h)))).mono
          (fun _ h _ ↦ h)
  filter_upwards [hi, hn] with θ hi hn
  refine ⟨?_, hn⟩
  intro i j hij
  by_contra hneij
  exact hi i j hneij (sub_eq_zero.mpr hij)

end HodgeLean.Foundations.Program
