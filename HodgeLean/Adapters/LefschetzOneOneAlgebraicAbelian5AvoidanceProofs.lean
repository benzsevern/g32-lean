import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5GeometryProofs

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations Set Metric
open scoped ENNReal
namespace HodgeLean.Adapters

/-- The four affine boundary edges avoid a proper analytic set after one translation.
Source: analytic-set dimension, compact segment dimension growth, and finite-union dimension. -/
theorem bh5_analytic_set_avoidance_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (Z : Set (Fin (dim X.left) → ℂ))
    (hZ : IsClosedAnalytic (Fin (dim X.left) → ℂ) Z) (hproper : Z ≠ univ)
    (l m : abelianPeriodLattice X) :
    ∃ z : Fin (dim X.left) → ℂ, ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      bh4_squareEdge X l m z i t ∉ Z := by
  classical
  by_cases hn : dim X.left = 0
  · haveI : Subsingleton (Fin (dim X.left) → ℂ) := by
      rw [hn]; infer_instance
    have hz : ∀ z, z ∉ Z := by
      intro z hz
      apply hproper
      exact Set.eq_univ_of_forall fun w ↦ (Subsingleton.elim z w) ▸ hz
    exact ⟨0, fun _ _ _ ↦ hz _⟩
  · have hnpos : 0 < dim X.left := Nat.pos_of_ne_zero hn
    let a : Fin 4 → (Fin (dim X.left) → ℂ) := ![0, l, l + m, m]
    let v : Fin 4 → (Fin (dim X.left) → ℂ) := ![l, m, -l, -m]
    let S := fun i ↦ bh5_segmentIncidence (dim X.left) Z (a i) (v i)
    have hd : ((2 * dim X.left - 2 : ℕ) : ℝ≥0∞) + 1 <
        Module.finrank ℝ (Fin (dim X.left) → ℂ) := by
      rw [Module.finrank_pi_fintype]
      simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
      norm_cast
      omega
    obtain ⟨z, hz⟩ := bh5_four_sets_noncover (dim X.left) S _ hd (fun i ↦
      (bh5_segment_dim_aux (dim X.left) Z (a i) (v i)).trans
        (add_le_add (bh5_analytic_dim_aux (dim X.left) hnpos Z hZ hproper) le_rfl))
    refine ⟨z, fun i t ht hi ↦ hz i ⟨t, ht, ?_⟩⟩
    have he : z + a i + t • v i = bh4_squareEdge X l m z i t := by
      fin_cases i <;> simp [a, v, bh4_squareEdge, sub_smul] <;> abel
    exact he.symm ▸ hi

end HodgeLean.Adapters
