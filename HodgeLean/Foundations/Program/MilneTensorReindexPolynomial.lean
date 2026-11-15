import HodgeLean.Foundations.Program.MilneTensorSymmetricGluing

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι τ ρ : Type*}

def m1b_reindexFormVectorPolynomial (e : ι ≃ ι)
    (p : MvPolynomial ((ι × ι) ⊕ (τ × (ρ × ι))) ℂ) :
    MvPolynomial ((ι × ι) ⊕ (τ × (ρ × ι))) ℂ :=
  MvPolynomial.rename (Sum.map (Prod.map e e) (Prod.map id (Prod.map id e))) p

theorem m1b_reindexFormVectorPolynomial_eval (e : ι ≃ ι)
    (p : MvPolynomial ((ι × ι) ⊕ (τ × (ρ × ι))) ℂ)
    (B : Matrix ι ι ℂ) (v : τ → ρ → ι → ℂ) :
    MvPolynomial.eval (Sum.elim (fun ij => B ij.1 ij.2) (fun ti => v ti.1 ti.2.1 ti.2.2))
      (m1b_reindexFormVectorPolynomial e p) =
        MvPolynomial.eval (Sum.elim (fun ij => B (e ij.1) (e ij.2))
          (fun ti => v ti.1 ti.2.1 (e ti.2.2))) p := by
  rw [m1b_reindexFormVectorPolynomial, MvPolynomial.eval_rename]
  congr 2
  funext s
  cases s <;> rfl

theorem m1b_symmetric_reindexed_numerator [Fintype ι] [DecidableEq ι]
    (e : ι ≃ ι) (i : ι) (a : MvPolynomial ((ι × ι) ⊕ (τ × (ρ × ι))) ℂ) (k : ℕ)
    (F : Matrix ι ι ℂ → (τ → ρ → ι → ℂ) → ℂ)
    (ha : ∀ (B : Matrix ι ι ℂ), (∀ s t, B s t = B t s) → B.det ≠ 0 → B i i ≠ 0 →
      ∀ v, MvPolynomial.eval (Sum.elim (fun st => B st.1 st.2)
        (fun ti => v ti.1 ti.2.1 ti.2.2)) a = B i i ^ k * F B v)
    (hF : ∀ (B : Matrix ι ι ℂ), (∀ s t, B s t = B t s) → B.det ≠ 0 →
      ∀ v, F (fun s t => B (e s) (e t)) (fun t c s => v t c (e s)) = F B v) :
    ∀ (B : Matrix ι ι ℂ), (∀ s t, B s t = B t s) → B.det ≠ 0 → B (e i) (e i) ≠ 0 →
      ∀ v, MvPolynomial.eval (Sum.elim (fun st => B st.1 st.2)
        (fun ti => v ti.1 ti.2.1 ti.2.2)) (m1b_reindexFormVectorPolynomial e a) =
          B (e i) (e i) ^ k * F B v := by
  intro B hs hd hi v
  rw [m1b_reindexFormVectorPolynomial_eval]
  have hdet : Matrix.det (fun s t => B (e s) (e t)) ≠ 0 := by
    change (Matrix.reindex e.symm e.symm B).det ≠ 0
    rw [Matrix.det_reindex_self]
    exact hd
  have h := ha (fun s t => B (e s) (e t)) (fun s t => hs (e s) (e t)) hdet hi
    (fun t c s => v t c (e s))
  rw [hF B hs hd v] at h
  exact h

end HodgeLean.Foundations.Program
