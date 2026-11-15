import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveMatrix

/-! # Recovering actual homogeneous coordinate ratios from projective matrices -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

/-- A nonzero homogeneous coordinate is recovered by the literal matrix column ratio in its original projective chart.
Source: Mathlib, field division and Complex.normSq_pos; the normalized outer-product formula.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_coordinate_ratio {ι : Type} [Fintype ι]
    (v : ι → ℂ) (hv : v ≠ 0) (i : ι) (hi : v i ≠ 0) (j : ι) :
    properCycle_projective_matrix v j i / properCycle_projective_matrix v i i = v j / v i := by
  have hn : (properCycle_projective_matrix_mass v : ℂ) ≠ 0 := by
    exact_mod_cast (properCycle_projective_matrix_mass_pos v hv).ne'
  have hs : star (v i) ≠ 0 := star_ne_zero.mpr hi
  simp only [properCycle_projective_matrix, Matrix.of_apply]
  field_simp

/-- Equality of the actual normalized matrices recovers equality of the original complex projective points.
Source: Mathlib, Projectivization.mk_eq_mk_iff'; properCycle_projective_matrix_coordinate_ratio.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_points_eq_of_matrix_eq {ι : Type} [Fintype ι]
    (v w : ι → ℂ) (hv : v ≠ 0) (hw : w ≠ 0)
    (he : properCycle_projective_matrix v = properCycle_projective_matrix w) :
    Projectivization.mk ℂ v hv = Projectivization.mk ℂ w hw := by
  have hi : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hi
  have hn : (properCycle_projective_matrix_mass v : ℂ) ≠ 0 := by
    exact_mod_cast (properCycle_projective_matrix_mass_pos v hv).ne'
  have hd : properCycle_projective_matrix v i i ≠ 0 :=
    div_ne_zero (mul_ne_zero hi (star_ne_zero.mpr hi)) hn
  have hwi : w i ≠ 0 := by
    intro hz
    apply hd
    rw [he]
    change w i * star (w i) / (properCycle_projective_matrix_mass w : ℂ) = 0
    rw [hz, zero_mul, zero_div]
  apply (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).mpr
  refine ⟨v i / w i, ?_⟩
  funext j
  change (v i / w i) * w j = v j
  have hj := congrArg (fun A : Matrix ι ι ℂ => A j i / A i i) he
  rw [properCycle_projective_matrix_coordinate_ratio v hv i hi j,
    properCycle_projective_matrix_coordinate_ratio w hw i hwi j] at hj
  have hc := (div_eq_div_iff hi hwi).mp hj
  calc
    (v i / w i) * w j = (w j * v i) / w i := by ring
    _ = v j := (div_eq_iff hwi).mpr hc.symm

end HodgeLean.Foundations.QuotientDuality
