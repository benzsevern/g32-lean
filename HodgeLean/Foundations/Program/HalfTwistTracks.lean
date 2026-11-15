import HodgeLean.Foundations.Program.HalfTwistDefs

/-! # Elementary half-turn tracks
Continuity, endpoints and absence of collisions for `b66h_track`.
HC no distance; AV milestone no distance.
-/
noncomputable section
open Complex Set Topology
namespace HodgeLean.Foundations.Program

/-- Integer real coordinates of the twelve finite marks. -/
def b66h_markZ : Fin 12 → ℤ := ![-12, -11, -10, -9, -8, -7, -6, -5, -4, -3, 0, 1]

theorem b66h_marks_eq (k : Fin 12) : mr_marks k = ((b66h_markZ k : ℝ) : ℂ) := by
  fin_cases k <;> norm_num [b66h_markZ, mr_marks, mr_base, Fin.append, Fin.addCases]

theorem b66h_markZ_injective : Function.Injective b66h_markZ := by
  decide

theorem b66h_markZ_outside : ∀ (j : Fin 11) (m : Fin 12), m ≠ j.castSucc → m ≠ j.succ →
    0 < (b66h_markZ m - b66h_markZ j.castSucc) * (b66h_markZ m - b66h_markZ j.succ) := by
  decide

theorem b66h_track_moving (j : Fin 11) (ε t : ℝ) (k : Fin 12)
    (hk : k = j.castSucc ∨ k = j.succ) :
    b66h_track j ε t k = (mr_marks j.castSucc + mr_marks j.succ) / 2 +
      (mr_marks k - (mr_marks j.castSucc + mr_marks j.succ) / 2) *
        Complex.exp (ε * Real.pi * Complex.I * (t : ℂ)) := by
  simp only [b66h_track, ite_eq_left hk]

theorem b66h_track_fixed (j : Fin 11) (ε t : ℝ) (k : Fin 12)
    (hk : ¬ (k = j.castSucc ∨ k = j.succ)) : b66h_track j ε t k = mr_marks k := by
  simp only [b66h_track, ite_eq_right hk]

theorem b66h_norm_exp (ε t : ℝ) : ‖Complex.exp (ε * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
  rw [show (ε : ℂ) * Real.pi * Complex.I * (t : ℂ) = ((ε * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem b66h_track_continuous_body (j : Fin 11) (ε : ℝ) :
    Continuous (fun q : ℝ × Fin 12 ↦ b66h_track j ε q.1 q.2) := by
  rw [continuous_prod_of_discrete_right]
  intro k
  by_cases hk : k = j.castSucc ∨ k = j.succ
  · simp only [b66h_track_moving j ε _ k hk]
    fun_prop
  · simp only [b66h_track_fixed j ε _ k hk]
    exact continuous_const

theorem b66h_track_endpoints_body (j : Fin 11) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    b66h_track j ε 0 = mr_marks ∧
      b66h_track j ε 1 = mr_marks ∘ Equiv.swap j.castSucc j.succ := by
  have hne : j.castSucc ≠ j.succ := Fin.castSucc_lt_succ.ne
  have hexp : Complex.exp (ε * Real.pi * Complex.I * ((1 : ℝ) : ℂ)) = -1 := by
    rcases hε with rfl | rfl
    · simp
    · rw [show ((-1 : ℝ) : ℂ) * Real.pi * Complex.I * ((1 : ℝ) : ℂ) =
        -(Real.pi * Complex.I) by push_cast; ring, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
  constructor
  · funext k
    by_cases hk : k = j.castSucc ∨ k = j.succ
    · rw [b66h_track_moving j ε 0 k hk]
      simp
    · rw [b66h_track_fixed j ε 0 k hk]
  · funext k
    by_cases hk : k = j.castSucc ∨ k = j.succ
    · rw [b66h_track_moving j ε 1 k hk, hexp]
      rcases hk with rfl | rfl
      · simp only [Function.comp_apply, Equiv.swap_apply_left]; ring
      · simp only [Function.comp_apply, Equiv.swap_apply_right]; ring
    · rw [b66h_track_fixed j ε 1 k hk]
      push Not at hk
      simp [Equiv.swap_apply_of_ne_of_ne hk.1 hk.2]

theorem b66h_track_injective_body (j : Fin 11) (ε t : ℝ) :
    Function.Injective (b66h_track j ε t) := by
  have hne : j.castSucc ≠ j.succ := Fin.castSucc_lt_succ.ne
  set a := b66h_markZ j.castSucc
  set b := b66h_markZ j.succ
  have hab : a ≠ b := fun h ↦ hne (b66h_markZ_injective h)
  set c : ℂ := (mr_marks j.castSucc + mr_marks j.succ) / 2
  set e := Complex.exp (ε * Real.pi * Complex.I * (t : ℂ))
  have he : ‖e‖ = 1 := b66h_norm_exp ε t
  have he0 : e ≠ 0 := Complex.exp_ne_zero _
  -- a moving point never meets a fixed mark
  have hmf : ∀ k m, (k = j.castSucc ∨ k = j.succ) → ¬ (m = j.castSucc ∨ m = j.succ) →
      c + (mr_marks k - c) * e ≠ mr_marks m := by
    intro k m hk hm h
    push Not at hm
    have hpos := b66h_markZ_outside j m hm.1 hm.2
    have hn : ‖mr_marks m - c‖ = ‖mr_marks k - c‖ := by
      rw [← h, add_sub_cancel_left, norm_mul, he, mul_one]
    have hr : ∀ y : ℝ, ‖((y : ℝ) : ℂ)‖ ^ 2 = y ^ 2 := fun y ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hc : c = (((a + b : ℤ) : ℝ) / 2 : ℝ) := by
      simp only [c, b66h_marks_eq, a, b]; push_cast; ring
    have key : ∀ n : Fin 12, mr_marks n - c = (((b66h_markZ n : ℝ) - ((a + b : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by
      intro n; rw [b66h_marks_eq, hc]; push_cast; ring
    have hn2 := congrArg (· ^ 2) hn
    simp only [key, hr] at hn2
    have hpos' : (0 : ℝ) < ((b66h_markZ m : ℝ) - a) * ((b66h_markZ m : ℝ) - b) := by
      exact_mod_cast hpos
    rcases hk with rfl | rfl
    · change ((b66h_markZ m : ℝ) - ((a + b : ℤ) : ℝ) / 2) ^ 2 =
        ((a : ℝ) - ((a + b : ℤ) : ℝ) / 2) ^ 2 at hn2
      push_cast at hn2; nlinarith
    · change ((b66h_markZ m : ℝ) - ((a + b : ℤ) : ℝ) / 2) ^ 2 =
        ((b : ℝ) - ((a + b : ℤ) : ℝ) / 2) ^ 2 at hn2
      push_cast at hn2; nlinarith
  have hmarks : Function.Injective mr_marks := by
    intro x y h
    rw [b66h_marks_eq, b66h_marks_eq] at h
    exact b66h_markZ_injective (by exact_mod_cast Complex.ofReal_injective h)
  intro k k' h
  by_cases hk : k = j.castSucc ∨ k = j.succ <;>
    by_cases hk' : k' = j.castSucc ∨ k' = j.succ
  · rw [b66h_track_moving j ε t k hk, b66h_track_moving j ε t k' hk'] at h
    have h2 : mr_marks k = mr_marks k' := by
      have := mul_right_cancel₀ he0 (add_left_cancel h)
      simpa using this
    exact hmarks h2
  · rw [b66h_track_moving j ε t k hk, b66h_track_fixed j ε t k' hk'] at h
    exact absurd h (hmf k k' hk hk')
  · rw [b66h_track_fixed j ε t k hk, b66h_track_moving j ε t k' hk'] at h
    exact absurd h.symm (hmf k' k hk' hk)
  · rw [b66h_track_fixed j ε t k hk, b66h_track_fixed j ε t k' hk'] at h
    exact hmarks h

end HodgeLean.Foundations.Program
