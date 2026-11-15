import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveMatrixQuotient
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveMatrixEquations

/-! # Literal finite equation model of actual complex projective matrices -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual Hermitian, unit diagonal-sum, and two-by-two minor equations reconstruct a nonzero homogeneous vector whose original normalized matrix is the supplied matrix.
Source: Mathlib, Complex.mul_conj and finite sums; the rank-one Hermitian projection construction.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_exists_of_equations {ι : Type} [Fintype ι]
    (M : Matrix ι ι ℂ)
    (hherm : ∀ i j, star (M i j) = M j i)
    (htrace : ∑ i, M i i = 1)
    (hminor : ∀ i j k l, M i j * M k l = M i l * M k j) :
    ∃ v : ι → ℂ, v ≠ 0 ∧ properCycle_projective_matrix v = M := by
  have hsum : ∑ i, (M i i).re = 1 := by
    simpa only [Complex.re_sum, Complex.one_re] using congrArg Complex.re htrace
  have hp : ∃ i, 0 < (M i i).re := by
    by_contra! h
    have hh : ∑ i, (M i i).re ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith
  obtain ⟨i, hi⟩ := hp
  have hii : M i i ≠ 0 := fun h => (ne_of_gt hi) (congrArg Complex.re h)
  let v : ι → ℂ := fun j => M j i
  have hv : v ≠ 0 := fun h => hii (congrFun h i)
  have hmass : (properCycle_projective_matrix_mass v : ℂ) = M i i := by
    change ((∑ j, Complex.normSq (M j i) : ℝ) : ℂ) = M i i
    rw [Complex.ofReal_sum]
    calc
      (∑ j, (Complex.normSq (M j i) : ℂ)) = ∑ j, M j j * M i i := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Complex.mul_conj (M j i)]
        change M j i * star (M j i) = M j j * M i i
        rw [hherm j i]
        exact (hminor j j i i).symm
      _ = (∑ j, M j j) * M i i := (Finset.sum_mul _ _ _).symm
      _ = M i i := by rw [htrace, one_mul]
  refine ⟨v, hv, ?_⟩
  ext j k
  change M j i * star (M k i) / (properCycle_projective_matrix_mass v : ℂ) = M j k
  rw [hherm k i, hmass]
  exact (div_eq_iff hii).mpr (hminor j k i i).symm

/-- The actual projective matrix range is exactly the displayed finite Hermitian, unit diagonal-sum and minor equation locus.
Source: Mathlib, Projectivization.mk_rep; properCycle_projective_matrix_exists_of_equations.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_coordinates_range {ι : Type} [Fintype ι] :
    Set.range (properCycle_projective_matrix_coordinates (ι := ι)) =
      {M : Matrix ι ι ℂ | (∀ i j, star (M i j) = M j i) ∧
        (∑ i, M i i) = 1 ∧ ∀ i j k l, M i j * M k l = M i l * M k j} := by
  ext M
  constructor
  · rintro ⟨p, rfl⟩
    have he : properCycle_projective_matrix_coordinates p = properCycle_projective_matrix p.rep := by
      exact (congrArg properCycle_projective_matrix_coordinates (Projectivization.mk_rep p)).symm.trans
        (properCycle_projective_matrix_coordinates_mk p.rep p.rep_nonzero)
    rw [he]
    exact ⟨properCycle_projective_matrix_conjugate p.rep,
      properCycle_projective_matrix_diagonal_sum p.rep p.rep_nonzero,
      properCycle_projective_matrix_minor p.rep⟩
  · intro h
    obtain ⟨v, hv, he⟩ := properCycle_projective_matrix_exists_of_equations M h.1 h.2.1 h.2.2
    exact ⟨Projectivization.mk ℂ v hv, (properCycle_projective_matrix_coordinates_mk v hv).trans he⟩

end HodgeLean.Foundations.QuotientDuality
