import HodgeLean.Foundations.MeyerRationalS8
import HodgeLean.Foundations.MeyerRational

/-! Meyer isotropy for finite-dimensional regular indefinite rational forms. -/

noncomputable section
namespace HodgeLean.Foundations.MeyerRational

theorem real_diagonal_zero_of_signs {n : ℕ} (a : Fin n → ℝ)
    (hp : ∃ i, 0 < a i) (hn : ∃ j, a j < 0) :
    ∃ x : Fin n → ℝ, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  classical
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hn
  have hij : i ≠ j := by rintro rfl; linarith
  let x : Fin n → ℝ := fun k => if k = i then Real.sqrt (-a j)
    else if k = j then Real.sqrt (a i) else 0
  refine ⟨x, ?_, ?_⟩
  · intro h
    have hxi := congrFun h i
    have hnz := Real.sqrt_pos.mpr (neg_pos.mpr hj)
    simp [x] at hxi
    linarith
  · have he (k : Fin n) : a k * x k ^ 2 =
        (if k = i then a i * (-a j) else 0) +
        (if k = j then a j * a i else 0) := by
      by_cases hki : k = i
      · subst k
        simp [x, hij, Real.sq_sqrt (neg_pos.mpr hj).le]
      · by_cases hkj : k = j
        · subst k
          simp [x, hki, Real.sq_sqrt hi.le]
        · simp [x, hki, hkj]
    simp_rw [he, Finset.sum_add_distrib]
    simp
    ring

end HodgeLean.Foundations.MeyerRational

namespace HodgeLean.Foundations.HermitianClass

open HodgeLean.Foundations.MeyerRational

/-- A regular indefinite rational form of dimension at least five has a nonzero zero.
Source: Serre, A Course in Arithmetic, Chapter IV, §3.2, Corollary 2. -/
theorem meyer_isotropic (V : Type*) [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (q : QuadraticForm ℚ V)
    (hq : q.associated.SeparatingLeft) (hdim : 5 ≤ Module.finrank ℚ V)
    (hp : ∃ x, 0 < q x) (hn : ∃ x, q x < 0) :
    ∃ x, x ≠ 0 ∧ q x = 0 := by
  obtain ⟨w, ⟨E⟩⟩ := q.equivalent_weightedSumSquares_units_of_nondegenerate' hq
  obtain ⟨vp, hvp⟩ := hp
  obtain ⟨vn, hvn⟩ := hn
  have hs := (diagonal_signs _ (fun i => (w i : ℚ))).mp
    ⟨⟨E vp, by
        change 0 < QuadraticMap.weightedSumSquares ℚ w (E vp)
        rw [E.map_app]
        exact hvp⟩,
      ⟨E vn, by
        change QuadraticMap.weightedSumSquares ℚ w (E vn) < 0
        rw [E.map_app]
        exact hvn⟩⟩
  obtain ⟨D, a, hD, _, ha, hap, han, hmodel⟩ :=
    integral_model _ (fun i => (w i : ℚ)) (fun i => (w i).ne_zero) hs.1 hs.2
  obtain ⟨e, T, hT, _, _, hep, hen, hrestrict⟩ :=
    five_restriction _ hdim a ha hap han
  let b : Fin 5 → ℚ := fun i => a (e i)
  have hb : ∀ i, b i ≠ 0 := fun i => Int.cast_ne_zero.mpr (ha (e i))
  have hpR : ∃ i, (0 : ℝ) < (b i : ℝ) := by
    obtain ⟨i, hi⟩ := hep
    exact ⟨i, by dsimp [b]; exact_mod_cast hi⟩
  have hnR : ∃ i, (b i : ℝ) < 0 := by
    obtain ⟨i, hi⟩ := hen
    exact ⟨i, by dsimp [b]; exact_mod_cast hi⟩
  obtain ⟨x, hx, hzero⟩ := five_local_global b hb
    (by simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two] using
      real_diagonal_zero_of_signs (fun i => (b i : ℝ)) hpR hnR)
    (fun p _ => local_five_isotropic p (fun i => (b i : ℚ_[p]))
      (fun i => Rat.cast_ne_zero.mpr (hb i)))
  have hTx : T x ≠ 0 := by
    intro h
    apply hx
    apply hT
    simpa using h
  let v := E.toLinearEquiv.symm (T x)
  refine ⟨v, ?_, ?_⟩
  · intro h
    apply hTx
    have hE := congrArg E.toLinearEquiv h
    simpa [v] using hE
  · have hInt : integralDiagonal _ a (T x) = 0 := by
      rw [hrestrict]
      exact hzero
    have heq := hmodel (T x)
    have hEv : E v = T x := E.toLinearEquiv.apply_symm_apply _
    have hqv : QuadraticMap.weightedSumSquares ℚ (fun i => (w i : ℚ)) (T x) = q v := by
      change QuadraticMap.weightedSumSquares ℚ w (T x) = q v
      rw [← hEv, E.map_app]
    rw [hqv, hInt] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD))

end HodgeLean.Foundations.HermitianClass
