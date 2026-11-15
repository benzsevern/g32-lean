import HodgeLean.Foundations.Program.MilneTensorAlternatingPolynomials
import HodgeLean.Foundations.Program.MilneTensorPivot

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι ζ : Type*} [LinearOrder ι] [Fintype ι]

set_option maxHeartbeats 400000 in
theorem m1b_alternating_two_chart_polynomial
    (p₀ p₁ : {p : ι × ι // p.1 < p.2}) (hp : p₀ ≠ p₁)
    (C : Matrix ι ι ℂ) (hC : ∀ i j, C j i = -C i j)
    (hdiagC : ∀ i, C i i = 0) (hdC : C.det ≠ 0)
    (a b : MvPolynomial ((ι × ι) ⊕ ζ) ℂ) (k l : ℕ)
    (F : Matrix ι ι ℂ → (ζ → ℂ) → ℂ)
    (ha : ∀ Q : Matrix ι ι ℂ, (∀ i j, Q j i = -Q i j) → (∀ i, Q i i = 0) →
      Q.det ≠ 0 → Q p₀.val.1 p₀.val.2 ≠ 0 → ∀ v,
        MvPolynomial.eval (Sum.elim (fun ij => Q ij.1 ij.2) v) a =
          Q p₀.val.1 p₀.val.2 ^ k * F Q v)
    (hb : ∀ Q : Matrix ι ι ℂ, (∀ i j, Q j i = -Q i j) → (∀ i, Q i i = 0) →
      Q.det ≠ 0 → Q p₁.val.1 p₁.val.2 ≠ 0 → ∀ v,
        MvPolynomial.eval (Sum.elim (fun ij => Q ij.1 ij.2) v) b =
          Q p₁.val.1 p₁.val.2 ^ l * F Q v) :
    ∃ q : MvPolynomial ((ι × ι) ⊕ ζ) ℂ,
      ∀ Q : Matrix ι ι ℂ, (∀ i j, Q j i = -Q i j) → (∀ i, Q i i = 0) →
        Q.det ≠ 0 → (Q p₀.val.1 p₀.val.2 ≠ 0 ∨ Q p₁.val.1 p₁.val.2 ≠ 0) →
        ∀ v, MvPolynomial.eval (Sum.elim (fun ij => Q ij.1 ij.2) v) q = F Q v := by
  let σ := {p : ι × ι // p.1 < p.2} ⊕ ζ
  let T := m1b_alternatingCoordinateMatrix (ι := ι) ζ
  let E (x : σ → ℂ) := (MvPolynomial.eval x).mapMatrix T
  have hskew (x : σ → ℂ) (i j : ι) : E x j i = -E x i j := by
    have h := congrArg (fun M => MvPolynomial.eval x (M i j))
      (m1b_alternatingCoordinateMatrix_transpose (ι := ι) ζ)
    simpa only [E, T, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.transpose_apply, Matrix.neg_apply, map_neg] using h
  have hdiag (x : σ → ℂ) (i : ι) : E x i i = 0 := by
    change MvPolynomial.eval x (m1b_alternatingCoordinateMatrix ζ i i) = 0
    rw [m1b_alternatingCoordinateMatrix_diagonal, map_zero]
  have hentry (x : σ → ℂ) (p : {p : ι × ι // p.1 < p.2}) :
      E x p.val.1 p.val.2 = x (Sum.inl p) := by
    change MvPolynomial.eval x (m1b_alternatingCoordinateMatrix ζ p.val.1 p.val.2) = _
    simp only [m1b_alternatingCoordinateMatrix, dite_eq_left p.property, MvPolynomial.eval_X]
  let x₀ : σ → ℂ := Sum.elim (fun p => C p.val.1 p.val.2) (fun _ => 0)
  have hEC : E x₀ = C := m1b_alternatingCoordinateMatrix_eval C hC hdiagC (fun _ => 0)
  have hd : T.det ≠ 0 := by
    intro hz
    have he := congrArg (MvPolynomial.eval x₀) hz
    rw [map_zero, (MvPolynomial.eval x₀).map_det T] at he
    change (E x₀).det = 0 at he
    rw [hEC] at he
    exact hdC he
  obtain ⟨c, hc⟩ := m1b_two_pivot_polynomial (Sum.inl p₀ : σ) (Sum.inl p₁)
    (fun h => hp (Sum.inl.inj h))
    (m1b_rawAlternatingPolynomial a) (m1b_rawAlternatingPolynomial b) T.det hd k l
    (fun x => F (E x) (fun z => x (Sum.inr z))) (by
      intro x hx hi
      rw [m1b_rawAlternatingPolynomial_eval]
      have hdE : (E x).det ≠ 0 := by
        rw [← (MvPolynomial.eval x).map_det T]
        exact hx
      have he := ha (E x) (hskew x) (hdiag x) hdE
        (by rw [hentry]; exact hi) (fun z => x (Sum.inr z))
      rw [hentry x p₀] at he
      simpa only [E, T, RingHom.mapMatrix_apply, Matrix.map_apply] using he) (by
      intro x hx hi
      rw [m1b_rawAlternatingPolynomial_eval]
      have hdE : (E x).det ≠ 0 := by
        rw [← (MvPolynomial.eval x).map_det T]
        exact hx
      have he := hb (E x) (hskew x) (hdiag x) hdE
        (by rw [hentry]; exact hi) (fun z => x (Sum.inr z))
      rw [hentry x p₁] at he
      simpa only [E, T, RingHom.mapMatrix_apply, Matrix.map_apply] using he)
  refine ⟨m1b_alternatingRawPolynomial c, ?_⟩
  intro Q hQ hdiagQ hdQ hpQ v
  rw [m1b_alternatingRawPolynomial_eval]
  let x : σ → ℂ := Sum.elim (fun p => Q p.val.1 p.val.2) v
  have hEQ : E x = Q := m1b_alternatingCoordinateMatrix_eval Q hQ hdiagQ v
  have hdX : MvPolynomial.eval x T.det ≠ 0 := by
    rw [(MvPolynomial.eval x).map_det T]
    change (E x).det ≠ 0
    rw [hEQ]
    exact hdQ
  have he := hc x hdX hpQ
  change MvPolynomial.eval x c = F Q v
  simpa only [hEQ, x, Sum.elim_inr] using he

end HodgeLean.Foundations.Program
