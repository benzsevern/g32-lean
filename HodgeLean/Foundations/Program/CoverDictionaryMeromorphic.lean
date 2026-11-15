import HodgeLean.Foundations.Program.CoverDictionaryOrders

/-! Meromorphic matrix operations for coefficient descent. -/

noncomputable section
open Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- The determinant of a matrix of meromorphic germs is meromorphic. -/
theorem caf_meromorphic_matrix_det {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℂ → Matrix n n ℂ) (z₀ : ℂ)
    (hA : ∀ i j, MeromorphicAt (fun z ↦ A z i j) z₀) :
    MeromorphicAt (fun z ↦ (A z).det) z₀ := by
  simp only [Matrix.det_apply']
  exact MeromorphicAt.fun_sum fun σ _ ↦
    (MeromorphicAt.const _ _).mul (MeromorphicAt.fun_prod fun i _ ↦ hA _ _)

/-- Adjugate entries are meromorphic whenever the matrix entries are meromorphic. -/
theorem caf_meromorphic_matrix_adjugate {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℂ → Matrix n n ℂ) (z₀ : ℂ)
    (hA : ∀ i j, MeromorphicAt (fun z ↦ A z i j) z₀) (i j : n) :
    MeromorphicAt (fun z ↦ (A z).adjugate i j) z₀ := by
  simp only [Matrix.adjugate_apply]
  apply caf_meromorphic_matrix_det
  intro k l
  by_cases hk : k = j
  · subst k
    simpa only [Matrix.updateRow_self] using (MeromorphicAt.const ((Pi.single i (1 : ℂ) : n → ℂ) l) z₀)
  · simpa only [Matrix.updateRow_ne hk] using hA k l

/-- Inverse entries are meromorphic, including at zeros of the determinant. -/
theorem caf_meromorphic_matrix_inv {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℂ → Matrix n n ℂ) (z₀ : ℂ)
    (hA : ∀ i j, MeromorphicAt (fun z ↦ A z i j) z₀) (i j : n) :
    MeromorphicAt (fun z ↦ (A z)⁻¹ i j) z₀ := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact (caf_meromorphic_matrix_det A z₀ hA).inv.mul
    (caf_meromorphic_matrix_adjugate A z₀ hA i j)

end HodgeLean.Foundations.Program
