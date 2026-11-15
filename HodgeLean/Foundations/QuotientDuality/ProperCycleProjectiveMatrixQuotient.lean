import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveMatrixRecovery

/-! # Actual matrix coordinates on complex linear projectivization -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual normalized outer product descends to complex projective points using its checked homogeneous rescaling law.
Source: Mathlib, Projectivization.lift; properCycle_projective_matrix_smul.
HC no distance; AV milestone no distance. -/
def properCycle_projective_matrix_coordinates {ι : Type} [Fintype ι] :
    Projectivization ℂ (ι → ℂ) → Matrix ι ι ℂ :=
  Projectivization.lift (fun v => properCycle_projective_matrix v.val) (by
    intro a b c h
    have hc : c ≠ 0 := by
      intro hz
      apply a.property
      exact h.trans (by rw [hz, zero_smul])
    rw [h]
    exact properCycle_projective_matrix_smul c hc b.val)

/-- The actual quotient matrix on a homogeneous point is its original normalized coordinate outer product.
Source: Mathlib, Projectivization.lift_mk.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_coordinates_mk {ι : Type} [Fintype ι]
    (v : ι → ℂ) (hv : v ≠ 0) :
    properCycle_projective_matrix_coordinates (Projectivization.mk ℂ v hv) =
      properCycle_projective_matrix v := rfl

/-- The actual matrix coordinate map is continuous for the original quotient topology on finite complex projective space.
Source: Mathlib, Continuous.quotient_lift; ComplexProjectiveSpace.instTopologicalSpace.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_coordinates_continuous (n : ℕ) :
    Continuous (properCycle_projective_matrix_coordinates (ι := Fin (n + 1))) := by
  unfold properCycle_projective_matrix_coordinates
  apply Continuous.quotient_lift
  exact properCycle_projective_matrix_continuous

/-- The actual finite matrix coordinates separate the original complex projective points.
Source: Mathlib, Projectivization.mk_rep; properCycle_projective_points_eq_of_matrix_eq.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_coordinates_injective {ι : Type} [Fintype ι] :
    Function.Injective (properCycle_projective_matrix_coordinates (ι := ι)) := by
  intro x y h
  have h' := h
  rw [← Projectivization.mk_rep x, ← Projectivization.mk_rep y,
    properCycle_projective_matrix_coordinates_mk, properCycle_projective_matrix_coordinates_mk] at h'
  have he := properCycle_projective_points_eq_of_matrix_eq x.rep y.rep x.rep_nonzero y.rep_nonzero h'
  simpa only [Projectivization.mk_rep] using he

/-- The original compact complex projective space is embedded as an actual closed subset of the finite matrix coordinate space.
Source: Mathlib, Continuous.isClosedEmbedding; ComplexProjectiveSpace compactness from the unit-sphere quotient.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_coordinates_closed_embedding (n : ℕ) :
    Topology.IsClosedEmbedding (properCycle_projective_matrix_coordinates (ι := Fin (n + 1))) :=
  (properCycle_projective_matrix_coordinates_continuous n).isClosedEmbedding
    properCycle_projective_matrix_coordinates_injective

end HodgeLean.Foundations.QuotientDuality
