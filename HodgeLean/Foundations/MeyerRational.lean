import HodgeLean.Foundations.MeyerRationalProofs

/-! # First stage toward Meyer over the rationals

Implication from diagonal coefficient signs to integral normalization and a five-coordinate
restriction. The arithmetic isotropy theorem is deferred. No geometric conclusion is claimed.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.MeyerRational

/-- Both rational signs occur precisely when both coefficient signs occur.
Source: Serre, *A Course in Arithmetic*, Chapter IV, §1.1 (diagonal forms). -/
theorem diagonal_signs (n : ℕ) (w : Fin n → ℚ) :
    ((∃ x, 0 < QuadraticMap.weightedSumSquares ℚ w x) ∧
      (∃ x, QuadraticMap.weightedSumSquares ℚ w x < 0)) ↔
    ((∃ i, 0 < w i) ∧ (∃ i, w i < 0)) :=
  diagonal_signs_aux n w

example (n : ℕ) (w : Fin n → ℚ) :
    ((∃ x, 0 < QuadraticMap.weightedSumSquares ℚ w x) ∧
      (∃ x, QuadraticMap.weightedSumSquares ℚ w x < 0)) ↔
    ((∃ i, 0 < w i) ∧ (∃ i, w i < 0)) :=
  diagonal_signs n w

/-- A positive common denominator gives an integral diagonal model with unchanged signs.
Source: Serre, *A Course in Arithmetic*, Chapter IV, §3.2 (rational diagonal reduction). -/
theorem integral_model (n : ℕ) (w : Fin n → ℚ)
    (hw : ∀ i, w i ≠ 0) (hp : ∃ i, 0 < w i) (hm : ∃ i, w i < 0) :
    ∃ (D : ℕ) (a : Fin n → ℤ), 0 < D ∧
      (∀ i, (a i : ℚ) = D * w i) ∧ (∀ i, a i ≠ 0) ∧
      (∃ i, 0 < a i) ∧ (∃ i, a i < 0) ∧
      ∀ x, integralDiagonal n a x = (D : ℚ) * QuadraticMap.weightedSumSquares ℚ w x :=
  integral_model_aux n w hw hp hm

example (n : ℕ) (w : Fin n → ℚ)
    (hw : ∀ i, w i ≠ 0) (hp : ∃ i, 0 < w i) (hm : ∃ i, w i < 0) :
    ∃ (D : ℕ) (a : Fin n → ℤ), 0 < D ∧
      (∀ i, (a i : ℚ) = D * w i) ∧ (∀ i, a i ≠ 0) ∧
      (∃ i, 0 < a i) ∧ (∃ i, a i < 0) ∧
      ∀ x, integralDiagonal n a x = (D : ℚ) * QuadraticMap.weightedSumSquares ℚ w x :=
  integral_model n w hw hp hm

/-- Five coordinates can retain both signs, with an injective zero-extension map.
Source: Serre, *A Course in Arithmetic*, Chapter IV, §3.2, Corollary 2 (dimension reduction). -/
theorem five_restriction (n : ℕ) (hn : 5 ≤ n) (a : Fin n → ℤ)
    (ha : ∀ i, a i ≠ 0) (hp : ∃ i, 0 < a i) (hm : ∃ i, a i < 0) :
    ∃ (e : Fin 5 ↪ Fin n) (T : (Fin 5 → ℚ) →ₗ[ℚ] (Fin n → ℚ)),
      Function.Injective T ∧ (∀ x i, T x (e i) = x i) ∧
      (∀ x j, j ∉ Set.range e → T x j = 0) ∧
      (∃ i, 0 < a (e i)) ∧ (∃ i, a (e i) < 0) ∧
      ∀ x, integralDiagonal n a (T x) = integralDiagonal 5 (a ∘ e) x :=
  five_restriction_aux n hn a ha hp hm

example (n : ℕ) (hn : 5 ≤ n) (a : Fin n → ℤ)
    (ha : ∀ i, a i ≠ 0) (hp : ∃ i, 0 < a i) (hm : ∃ i, a i < 0) :
    ∃ (e : Fin 5 ↪ Fin n) (T : (Fin 5 → ℚ) →ₗ[ℚ] (Fin n → ℚ)),
      Function.Injective T ∧ (∀ x i, T x (e i) = x i) ∧
      (∀ x j, j ∉ Set.range e → T x j = 0) ∧
      (∃ i, 0 < a (e i)) ∧ (∃ i, a (e i) < 0) ∧
      ∀ x, integralDiagonal n a (T x) = integralDiagonal 5 (a ∘ e) x :=
  five_restriction n hn a ha hp hm

-- Concrete inputs are checked without selecting any output of an open theorem.
example : (∀ i : Fin 5, (![1, -1, 1, 1, 1] : Fin 5 → ℤ) i ≠ 0) ∧
    (∃ i : Fin 5, 0 < (![1, -1, 1, 1, 1] : Fin 5 → ℤ) i) ∧
    (∃ i : Fin 5, (![1, -1, 1, 1, 1] : Fin 5 → ℤ) i < 0) := by
  refine ⟨?_, ⟨0, by norm_num⟩, ⟨1, by norm_num⟩⟩
  intro i
  fin_cases i <;> norm_num

example : (∀ i : Fin 5, (![1, -1, 1, 1, 1] : Fin 5 → ℚ) i ≠ 0) ∧
    (∃ i : Fin 5, 0 < (![1, -1, 1, 1, 1] : Fin 5 → ℚ) i) ∧
    (∃ i : Fin 5, (![1, -1, 1, 1, 1] : Fin 5 → ℚ) i < 0) := by
  refine ⟨?_, ⟨0, by norm_num⟩, ⟨1, by norm_num⟩⟩
  intro i
  fin_cases i <;> norm_num

example : integralDiagonal 5 ![1, -1, 1, 1, 1] ![1, 0, 0, 0, 0] = 1 ∧
    integralDiagonal 5 ![1, -1, 1, 1, 1] ![0, 1, 0, 0, 0] = -1 := by
  norm_num [integralDiagonal, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_succ]

-- The dimensions used by the trace route meet the restriction's size input.
example : 5 ≤ 12 ∧ 5 ≤ 8 ∧ 5 ≤ 5 := by norm_num

-- Chain check: regular rational forms reach the integral signed diagonal interface.
example (V : Type*) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (q : QuadraticForm ℚ V) (hq : q.associated.SeparatingLeft)
    (hp : ∃ v, 0 < q v) (hm : ∃ v, q v < 0) :
    ∃ (D : ℕ) (a : Fin (Module.finrank ℚ V) → ℤ)
      (E : V ≃ₗ[ℚ] (Fin (Module.finrank ℚ V) → ℚ)),
      0 < D ∧ (∀ i, a i ≠ 0) ∧ (∃ i, 0 < a i) ∧ (∃ i, a i < 0) ∧
      ∀ v, integralDiagonal _ a (E v) = (D : ℚ) * q v := by
  obtain ⟨w, ⟨E⟩⟩ := q.equivalent_weightedSumSquares_units_of_nondegenerate' hq
  obtain ⟨v, hv⟩ := hp
  obtain ⟨u, hu⟩ := hm
  have hs := (diagonal_signs _ (fun i => (w i : ℚ))).mp
    ⟨⟨E v, by
       change 0 < QuadraticMap.weightedSumSquares ℚ w (E v)
       rw [E.map_app]
       exact hv⟩,
     ⟨E u, by
       change QuadraticMap.weightedSumSquares ℚ w (E u) < 0
       rw [E.map_app]
       exact hu⟩⟩
  obtain ⟨D, a, hD, _, ha, hap, ham, heq⟩ :=
    integral_model _ (fun i => (w i : ℚ)) (fun i => (w i).ne_zero) hs.1 hs.2
  exact ⟨D, a, E.toLinearEquiv, hD, ha, hap, ham,
    fun v => (heq (E v)).trans (congrArg ((D : ℚ) * ·) (E.map_app v))⟩

-- Chain check: a five-variable arithmetic result can use this actual embedding.
example (n : ℕ) (hn : 5 ≤ n) (a : Fin n → ℤ)
    (ha : ∀ i, a i ≠ 0) (hp : ∃ i, 0 < a i) (hm : ∃ i, a i < 0) :
    ∃ (b : Fin 5 → ℤ) (T : (Fin 5 → ℚ) →ₗ[ℚ] (Fin n → ℚ)),
      (∀ i, b i ≠ 0) ∧ (∃ i, 0 < b i) ∧ (∃ i, b i < 0) ∧
      Function.Injective T ∧ ∀ x, integralDiagonal n a (T x) = integralDiagonal 5 b x := by
  obtain ⟨e, T, hT, _, _, hep, hem, heq⟩ := five_restriction n hn a ha hp hm
  exact ⟨a ∘ e, T, fun i => ha (e i), hep, hem, hT, heq⟩

end HodgeLean.Foundations.MeyerRational
