import HodgeLean.Foundations.Program.KernelFramesFamilyFlow

/-! # B6-5 stage 5d, family part: entrywise analyticity of matrix formulas

Entrywise analyticity of matrix-valued functions, stable under sums, products, polynomial
evaluation, determinants, adjugates and inverses where the determinant does not vanish; the
residue matrices of a 5c record are entrywise analytic on its disc.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- Entrywise analyticity of a matrix-valued function on a set. -/
def b65q_MatAn {m n : Type*} (s : Set ℂ) (M : ℂ → Matrix m n ℂ) : Prop :=
  ∀ i j, AnalyticOnNhd ℂ (fun θ ↦ M θ i j) s

theorem b65q_an_sum {ι : Type*} (S : Finset ι) {s : Set ℂ} {f : ι → ℂ → ℂ}
    (h : ∀ a ∈ S, AnalyticOnNhd ℂ (f a) s) : AnalyticOnNhd ℂ (fun θ ↦ ∑ a ∈ S, f a θ) s := by
  have := Finset.analyticOnNhd_sum S h
  simpa [Finset.sum_fn] using this

theorem b65q_an_prod {ι : Type*} (S : Finset ι) {s : Set ℂ} {f : ι → ℂ → ℂ}
    (h : ∀ a ∈ S, AnalyticOnNhd ℂ (f a) s) : AnalyticOnNhd ℂ (fun θ ↦ ∏ a ∈ S, f a θ) s :=
  Finset.analyticOnNhd_fun_prod S h

section
variable {m n l : Type*} {s : Set ℂ}

theorem b65q_MatAn.const (M₀ : Matrix m n ℂ) : b65q_MatAn s fun _ ↦ M₀ :=
  fun _ _ ↦ analyticOnNhd_const

theorem b65q_MatAn.add {M N : ℂ → Matrix m n ℂ} (hM : b65q_MatAn s M) (hN : b65q_MatAn s N) :
    b65q_MatAn s fun θ ↦ M θ + N θ := fun i j ↦ (hM i j).add (hN i j)

theorem b65q_MatAn.sub {M N : ℂ → Matrix m n ℂ} (hM : b65q_MatAn s M) (hN : b65q_MatAn s N) :
    b65q_MatAn s fun θ ↦ M θ - N θ := fun i j ↦ (hM i j).sub (hN i j)

theorem b65q_MatAn.neg {M : ℂ → Matrix m n ℂ} (hM : b65q_MatAn s M) :
    b65q_MatAn s fun θ ↦ -M θ := fun i j ↦ (hM i j).neg

theorem b65q_MatAn.smul {c : ℂ → ℂ} {M : ℂ → Matrix m n ℂ} (hc : AnalyticOnNhd ℂ c s)
    (hM : b65q_MatAn s M) : b65q_MatAn s fun θ ↦ c θ • M θ := fun i j ↦ by
  simpa using hc.mul (hM i j)

theorem b65q_MatAn.mul [Fintype n] {M : ℂ → Matrix m n ℂ} {N : ℂ → Matrix n l ℂ} (hM : b65q_MatAn s M)
    (hN : b65q_MatAn s N) : b65q_MatAn s fun θ ↦ M θ * N θ := fun i j ↦ by
  simp only [Matrix.mul_apply]
  exact b65q_an_sum _ fun k _ ↦ (hM i k).mul (hN k j)

theorem b65q_MatAn.sum {ι : Type*} (S : Finset ι) {M : ι → ℂ → Matrix m n ℂ}
    (hM : ∀ a ∈ S, b65q_MatAn s (M a)) : b65q_MatAn s fun θ ↦ ∑ a ∈ S, M a θ := fun i j ↦ by
  simp only [Matrix.sum_apply]
  exact b65q_an_sum _ fun a ha ↦ hM a ha i j

theorem b65q_MatAn.transpose {M : ℂ → Matrix m n ℂ} (hM : b65q_MatAn s M) :
    b65q_MatAn s fun θ ↦ (M θ)ᵀ := fun i j ↦ hM j i

theorem b65q_MatAn.submatrix {m' n' : Type*} {M : ℂ → Matrix m n ℂ} (hM : b65q_MatAn s M)
    (r : m' → m) (c : n' → n) : b65q_MatAn s fun θ ↦ (M θ).submatrix r c := fun i j ↦ hM (r i) (c j)

end

section
variable {n : Type*} [Fintype n] [DecidableEq n] {s : Set ℂ}

theorem b65q_MatAn.one : b65q_MatAn s fun _ ↦ (1 : Matrix n n ℂ) := b65q_MatAn.const 1

theorem b65q_MatAn.pow {M : ℂ → Matrix n n ℂ} (hM : b65q_MatAn s M) (k : ℕ) :
    b65q_MatAn s fun θ ↦ M θ ^ k := by
  induction k with
  | zero => simpa using b65q_MatAn.one
  | succ k ih => simpa [pow_succ] using ih.mul hM

theorem b65q_MatAn.aeval {M : ℂ → Matrix n n ℂ} (hM : b65q_MatAn s M) (f : ℂ[X]) :
    b65q_MatAn s fun θ ↦ aeval (M θ) f := by
  simp only [aeval_eq_sum_range]
  exact b65q_MatAn.sum _ fun i _ ↦ (hM.pow i).smul analyticOnNhd_const

theorem b65q_MatAn.det {M : ℂ → Matrix n n ℂ} (hM : b65q_MatAn s M) :
    AnalyticOnNhd ℂ (fun θ ↦ (M θ).det) s := by
  simp only [Matrix.det_apply']
  exact b65q_an_sum _ fun σ _ ↦ analyticOnNhd_const.mul
    (b65q_an_prod _ fun i _ ↦ hM (σ i) i)

theorem b65q_MatAn.adjugate {M : ℂ → Matrix n n ℂ} (hM : b65q_MatAn s M) :
    b65q_MatAn s fun θ ↦ (M θ).adjugate := fun i j ↦ by
  simp only [Matrix.adjugate_apply]
  refine b65q_MatAn.det (M := fun θ ↦ (M θ).updateRow j (Pi.single i 1)) ?_
  intro a b
  by_cases h : a = j
  · subst h; simpa using analyticOnNhd_const
  · simpa [Matrix.updateRow_ne h] using hM a b

theorem b65q_MatAn.inv {M : ℂ → Matrix n n ℂ} (hM : b65q_MatAn s M)
    (hd : ∀ θ ∈ s, (M θ).det ≠ 0) : b65q_MatAn s fun θ ↦ (M θ)⁻¹ := by
  have : (fun θ ↦ (M θ)⁻¹) = fun θ ↦ ((M θ).det)⁻¹ • (M θ).adjugate := by
    funext θ; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact b65q_MatAn.smul (hM.det.inv hd) hM.adjugate

end

theorem b65q_MatAn.res {p : Fin 12 → ℂ} (O : b65p_Outputs p) (q : Fin 4 ⊕ Fin 12) :
    b65q_MatAn (ball 0 O.radius) fun θ ↦ b65q_res O.residue θ q := fun i j ↦ by
  have := (b65q_entryCLM i j).comp_analyticOnNhd (O.residue_analytic q)
  simpa [Function.comp_def, b65q_entryCLM_apply, b65q_res] using this

theorem b65q_MatAn.mono {m n : Type*} {s t : Set ℂ} {M : ℂ → Matrix m n ℂ} (hM : b65q_MatAn s M)
    (hts : t ⊆ s) : b65q_MatAn t M := fun i j ↦ (hM i j).mono hts

end HodgeLean.Foundations.Program
