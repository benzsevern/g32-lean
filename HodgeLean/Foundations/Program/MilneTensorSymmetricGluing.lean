import HodgeLean.Foundations.Program.MilneTensorSymmetricCoordinates
import HodgeLean.Foundations.Program.MilneTensorPivot

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι ζ : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 400000 in
theorem m1b_symmetric_two_chart_polynomial (i j : ι) (hij : i ≠ j)
    (a b : MvPolynomial ((ι × ι) ⊕ ζ) ℂ) (k l : ℕ)
    (F : Matrix ι ι ℂ → (ζ → ℂ) → ℂ)
    (ha : ∀ (B : Matrix ι ι ℂ), (∀ s t, B s t = B t s) → B.det ≠ 0 → B i i ≠ 0 →
      ∀ v, MvPolynomial.eval (Sum.elim (fun st => B st.1 st.2) v) a = B i i ^ k * F B v)
    (hb : ∀ (B : Matrix ι ι ℂ), (∀ s t, B s t = B t s) → B.det ≠ 0 → B j j ≠ 0 →
      ∀ v, MvPolynomial.eval (Sum.elim (fun st => B st.1 st.2) v) b = B j j ^ l * F B v) :
    ∃ p : MvPolynomial ((ι × ι) ⊕ ζ) ℂ,
      ∀ (B : Matrix ι ι ℂ), (∀ s t, B s t = B t s) → B.det ≠ 0 →
        (B i i ≠ 0 ∨ B j j ≠ 0) → ∀ v,
          MvPolynomial.eval (Sum.elim (fun st => B st.1 st.2) v) p = F B v := by
  let σ := Sym2 ι ⊕ ζ
  let T : Matrix ι ι (MvPolynomial σ ℂ) :=
    fun s t => MvPolynomial.X (Sum.inl (Sym2.mk s t))
  let R : ((ι × ι) ⊕ ζ) → σ := Sum.map (fun st => Sym2.mk st.1 st.2) id
  let E (x : σ → ℂ) : Matrix ι ι ℂ := fun s t => x (Sum.inl (Sym2.mk s t))
  have hE (x : σ → ℂ) : (MvPolynomial.eval x).mapMatrix T = E x := by
    ext s t
    exact MvPolynomial.eval_X _
  have hsE (x : σ → ℂ) (s t : ι) : E x s t = E x t s := by
    dsimp only [E]
    rw [Sym2.eq_swap]
  let x₀ : σ → ℂ := Sum.elim
    (Sym2.lift ⟨(1 : Matrix ι ι ℂ), fun s t => by simp [Matrix.one_apply, eq_comm]⟩)
    (fun _ => 0)
  have hE₀ : E x₀ = 1 := by ext s t; rfl
  have hd : T.det ≠ 0 := by
    intro hz
    have he := congrArg (MvPolynomial.eval x₀) hz
    rw [map_zero, (MvPolynomial.eval x₀).map_det T, hE, hE₀, Matrix.det_one] at he
    exact one_ne_zero he
  have hvars : (Sum.inl (Sym2.mk i i) : σ) ≠ Sum.inl (Sym2.mk j j) := by
    intro he
    have he' := Sum.inl.inj he
    rcases Sym2.eq_iff.mp he' with h | h <;> exact hij h.1
  obtain ⟨c, hc⟩ := m1b_two_pivot_polynomial
    (Sum.inl (Sym2.mk i i) : σ) (Sum.inl (Sym2.mk j j)) hvars
    (MvPolynomial.rename R a) (MvPolynomial.rename R b) T.det hd k l
    (fun x => F (E x) (fun z => x (Sum.inr z))) (by
      intro x hx hi
      rw [m1b_rawSymmetricPolynomial_eval]
      have hdet : (E x).det ≠ 0 := by
        rw [← hE, ← (MvPolynomial.eval x).map_det T]
        exact hx
      exact ha (E x) (hsE x) hdet hi (fun z => x (Sum.inr z))) (by
      intro x hx hj
      rw [m1b_rawSymmetricPolynomial_eval]
      have hdet : (E x).det ≠ 0 := by
        rw [← hE, ← (MvPolynomial.eval x).map_det T]
        exact hx
      exact hb (E x) (hsE x) hdet hj (fun z => x (Sum.inr z)))
  refine ⟨m1b_symmetricRawPolynomial c, ?_⟩
  intro B hs hdet hp v
  rw [m1b_symmetricRawPolynomial_eval c B hs v]
  let x : σ → ℂ := Sum.elim (Sym2.lift ⟨B, hs⟩) v
  have hEB : E x = B := by ext s t; rfl
  have hdx : MvPolynomial.eval x T.det ≠ 0 := by
    rw [(MvPolynomial.eval x).map_det T, hE, hEB]
    exact hdet
  have he := hc x hdx hp
  change MvPolynomial.eval x c = F B v
  simpa only [hEB, x, Sum.elim_inr] using he

end HodgeLean.Foundations.Program
