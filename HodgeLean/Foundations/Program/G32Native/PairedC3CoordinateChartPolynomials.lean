import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateChartMap

/-! # The polynomial presentation of the original projective chart map -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The original affine comparison is a complex algebra homomorphism. -/
def pairedC3CoordinateChartAlgHom {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    Away (homogeneousSubmodule (Fin (n + 1)) ℂ) (X (e i)) →ₐ[ℂ]
      Away (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i) where
  __ := pairedC3CoordinateChartMap e i
  commutes' := paired_c3_coordinate_chart_map_algebraMap e i

/-- On a retained affine chart, retain precisely the non-denominator
source coordinates among the non-denominator target coordinates. -/
def pairedC3ChartCoordinateEmbedding {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    {j : Fin (k + 1) // j ≠ i} ↪ {j : Fin (n + 1) // j ≠ e i} where
  toFun j := ⟨e j.val, fun h => j.property (e.injective h)⟩
  inj' a b h := Subtype.ext (e.injective
    (congrArg (fun z : {j : Fin (n + 1) // j ≠ e i} => z.val) h))

/-- The original homogeneous retained indices also determine the
retained affine indices; the denominator contributes no new index. -/
theorem paired_c3_chart_coordinate_mem_range {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1))
    (j : {j : Fin (n + 1) // j ≠ e i}) :
    j ∈ Set.range (pairedC3ChartCoordinateEmbedding e i) ↔ j.val ∈ Set.range e := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.val, congrArg (fun z : {j : Fin (n + 1) // j ≠ e i} => z.val) ha⟩
  · rintro ⟨a, ha⟩
    have hai : a ≠ i := by
      intro h
      apply j.property
      rw [← ha, h]
    exact ⟨⟨a, hai⟩, Subtype.ext ha⟩

/-- The actual projective chart comparison is exactly polynomial
coordinate elimination, through the specified chart equivalences. -/
theorem paired_c3_coordinate_chart_polynomial_map {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    ((pairedC3PolynomialChartAlgEquiv k i).toAlgHom.comp
      (pairedC3CoordinateChartAlgHom e i)).comp
        (pairedC3PolynomialChartAlgEquiv n (e i)).symm.toAlgHom =
      MvPolynomial.killCompl (R := ℂ) (pairedC3ChartCoordinateEmbedding e i).injective := by
  classical
  apply MvPolynomial.algHom_ext
  intro j
  change pairedC3PolynomialChartAlgEquiv k i
    (pairedC3CoordinateChartMap e i ((pairedC3PolynomialChartAlgEquiv n (e i)).symm (X j))) = _
  rw [paired_c3_polynomial_chart_inverse_variable]
  by_cases hj : j.val ∈ Set.range e
  · obtain ⟨a, ha⟩ := hj
    have hai : a ≠ i := by
      intro h
      apply j.property
      rw [← ha, h]
    let a' : {j : Fin (k + 1) // j ≠ i} := ⟨a, hai⟩
    have hja : pairedC3ChartCoordinateEmbedding e i a' = j := Subtype.ext ha
    rw [← hja]
    change pairedC3PolynomialChartAlgEquiv k i
      (pairedC3CoordinateChartMap e i (ProjSpace.ratio ℂ n (e i) (e a))) =
      MvPolynomial.killCompl (R := ℂ) (pairedC3ChartCoordinateEmbedding e i).injective
        (X (pairedC3ChartCoordinateEmbedding e i a'))
    rw [paired_c3_coordinate_chart_map_retained_ratio]
    change pairedC3PolynomialChartCoordinates k i (ProjSpace.ratio ℂ k i a) = _
    rw [paired_c3_polynomial_chart_coordinates_ratio, dite_eq_right hai]
    have hp := MvPolynomial.killCompl_rename_app (R := ℂ)
      (pairedC3ChartCoordinateEmbedding e i).injective (X a')
    rw [MvPolynomial.rename_X] at hp
    exact hp.symm
  · have hj' : j ∉ Set.range (pairedC3ChartCoordinateEmbedding e i) :=
      fun h => hj ((paired_c3_chart_coordinate_mem_range e i j).mp h)
    rw [paired_c3_coordinate_chart_map_discarded_ratio e i j.val hj, map_zero]
    symm
    simp only [MvPolynomial.killCompl, MvPolynomial.aeval_X, dite_eq_right hj']

end HodgeLean.Foundations.Program.G32Native
