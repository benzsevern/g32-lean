import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section
namespace HodgeLean.Foundations.Program

/-- A positive half-dimensional subspace of a split Hermitian space is a strict
contraction graph over its positive summand. -/
theorem b60c_positive_subspace_graph {n : ℕ}
    (F : Submodule ℂ ((Fin n → ℂ) × (Fin n → ℂ)))
    (hdim : Module.finrank ℂ F = n)
    (hpos : ∀ v ∈ F, v ≠ 0 →
      ∑ i, Complex.normSq (v.2 i) < ∑ i, Complex.normSq (v.1 i)) :
    ∃ T : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ), F = T.graph ∧
      ∀ x, x ≠ 0 → ∑ i, Complex.normSq (T x i) < ∑ i, Complex.normSq (x i) := by
  let p : F →ₗ[ℂ] (Fin n → ℂ) := (LinearMap.fst ℂ _ _).comp F.subtype
  have hinj : Function.Injective p := by
    apply (LinearMap.ker_eq_bot).mp
    apply eq_bot_iff.mpr
    intro v hv
    change v = 0
    have hvfst : (v : (Fin n → ℂ) × (Fin n → ℂ)).1 = 0 := hv
    by_contra hv0
    have hvne : (v : (Fin n → ℂ) × (Fin n → ℂ)) ≠ 0 := by
      intro h
      exact hv0 (Subtype.ext h)
    have h := hpos v v.property hvne
    rw [hvfst] at h
    simp only [Pi.zero_apply, Complex.normSq_zero, Finset.sum_const_zero] at h
    exact (not_lt_of_ge (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)) h
  have hsurj : Function.Surjective p :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa using hdim)).mp hinj
  obtain ⟨T, hT⟩ := F.exists_eq_graph ⟨hinj, hsurj⟩
  refine ⟨T, hT, ?_⟩
  intro x hx
  apply hpos (x, T x)
  · rw [hT]
    exact rfl
  · intro h
    exact hx (congrArg Prod.fst h)

#print axioms b60c_positive_subspace_graph

open scoped Matrix ComplexOrder

/-- The strict contraction inequality is the defining matrix positivity of the
bounded period chart. -/
theorem b60c_contraction_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ x, x ≠ 0 →
      ∑ i, Complex.normSq ((A *ᵥ x) i) < ∑ i, Complex.normSq (x i)) :
    (1 - Aᴴ * A).PosDef := by
  have hnorm (x : Fin n → ℂ) : star x ⬝ᵥ x = (∑ i, Complex.normSq (x i) : ℝ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum,
      Complex.normSq_eq_conj_mul_self]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self A))
  intro x hx
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hnorm, hnorm]
  exact_mod_cast sub_pos.mpr (hA x hx)

#print axioms b60c_contraction_posDef

/-- Positive planes have matrix graph coordinates in the bounded chart. -/
theorem b60c_positive_subspace_matrix {n : ℕ}
    (F : Submodule ℂ ((Fin n → ℂ) × (Fin n → ℂ)))
    (hdim : Module.finrank ℂ F = n)
    (hpos : ∀ v ∈ F, v ≠ 0 →
      ∑ i, Complex.normSq (v.2 i) < ∑ i, Complex.normSq (v.1 i)) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ,
      F = (Matrix.toLin' A).graph ∧ (1 - Aᴴ * A).PosDef := by
  obtain ⟨T, hT, hnorm⟩ := b60c_positive_subspace_graph F hdim hpos
  refine ⟨LinearMap.toMatrix' T, ?_, b60c_contraction_posDef _ ?_⟩
  · simpa only [Matrix.toLin'_toMatrix'] using hT
  · intro x hx
    simpa only [LinearMap.toMatrix'_mulVec] using hnorm x hx

#print axioms b60c_positive_subspace_matrix

/-- Isotropy of opposite graph frames forces the transpose relation. -/
theorem b60c_graph_isotropy_transpose {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ x y : Fin n → ℂ, x ⬝ᵥ (B *ᵥ y) = (A *ᵥ x) ⬝ᵥ y) :
    B = A.transpose := by
  ext i j
  simpa [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Pi.single_apply] using
    h (Pi.single i 1) (Pi.single j 1)

#print axioms b60c_graph_isotropy_transpose

end HodgeLean.Foundations.Program
