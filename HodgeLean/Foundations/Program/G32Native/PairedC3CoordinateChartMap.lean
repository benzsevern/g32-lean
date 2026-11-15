import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateInclusionCharts
import HodgeLean.Foundations.Program.G32Native.PairedC3PolynomialChartCoordinates

/-! # The actual coordinate-elimination map on normalized projective charts -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- Normalize only the source denominator of the original affine chart
map, retaining its original homogeneous-localization morphism. -/
def pairedC3CoordinateChartMap {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    Away (homogeneousSubmodule (Fin (n + 1)) ℂ) (X (e i)) →+*
      Away (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i) :=
  (RingEquiv.cast (R := fun z => Away (homogeneousSubmodule (Fin (k + 1)) ℂ) z)
    (paired_c3_coordinate_projection_variable (A := ℂ) e i)).toRingHom.comp
      (Away.map (pairedC3GradedCoordinateProjection (A := ℂ) e) (X (e i)))

/-- Retained coordinate ratios are unchanged by the actual affine comparison. -/
theorem paired_c3_coordinate_chart_map_retained_ratio {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i j : Fin (k + 1)) :
    pairedC3CoordinateChartMap e i (ProjSpace.ratio ℂ n (e i) (e j)) =
      ProjSpace.ratio ℂ k i j := by
  unfold pairedC3CoordinateChartMap ProjSpace.ratio
  change RingEquiv.cast (R := fun z => Away (homogeneousSubmodule (Fin (k + 1)) ℂ) z)
    (paired_c3_coordinate_projection_variable (A := ℂ) e i) (Away.map (pairedC3GradedCoordinateProjection (A := ℂ) e)
    (X (e i)) (Away.mk _ _ 1 (X (e j)) _)) = _
  rw [Away.map_mk, paired_c3_away_cast_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, paired_c3_coordinate_projection_variable]

/-- Every discarded-coordinate ratio is zero in the actual source chart. -/
theorem paired_c3_coordinate_chart_map_discarded_ratio {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) (j : Fin (n + 1))
    (hj : j ∉ Set.range e) :
    pairedC3CoordinateChartMap e i (ProjSpace.ratio ℂ n (e i) j) = 0 := by
  change RingEquiv.cast (R := fun z => Away (homogeneousSubmodule (Fin (k + 1)) ℂ) z)
    (paired_c3_coordinate_projection_variable (A := ℂ) e i) (Away.map (pairedC3GradedCoordinateProjection (A := ℂ) e)
    (X (e i)) (pairedC3CoordinateNormalRatio e i j)) = 0
  rw [paired_c3_coordinate_normal_ratio_vanishes e i j hj, map_zero]

/-- The affine comparison is surjective after normalizing the denominator. -/
theorem paired_c3_coordinate_chart_map_surjective {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    Function.Surjective (pairedC3CoordinateChartMap e i) :=
  (RingEquiv.cast (R := fun z => Away (homogeneousSubmodule (Fin (k + 1)) ℂ) z)
    (paired_c3_coordinate_projection_variable (A := ℂ) e i)).surjective.comp
      (paired_c3_coordinate_inclusion_chart_surjective e i)

/-- Coordinate elimination fixes every complex polynomial coefficient. -/
theorem paired_c3_coordinate_projection_constant {ι κ : Type} (e : κ ↪ ι) (c : ℂ) :
    pairedC3GradedCoordinateProjection (A := ℂ) e (C c) = C c :=
  MvPolynomial.killCompl_C e.injective c

/-- The actual affine comparison retains its original complex scalar action. -/
theorem paired_c3_coordinate_chart_map_algebraMap {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) (c : ℂ) :
    pairedC3CoordinateChartMap e i
      (algebraMap ℂ (Away (homogeneousSubmodule (Fin (n + 1)) ℂ) (X (e i))) c) =
    algebraMap ℂ (Away (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)) c := by
  have hc : algebraMap ℂ (Away (homogeneousSubmodule (Fin (n + 1)) ℂ) (X (e i))) c =
      Away.mk _ (isHomogeneous_X ℂ (e i)) 0 (C c)
        (by simpa using isHomogeneous_C (Fin (n + 1)) c) := by
    apply HomogeneousLocalization.val_injective
    simp only [ProjSpace.val_algebraMap, Away.val_mk, pow_zero]
    rfl
  rw [hc]
  change RingEquiv.cast (R := fun z => Away (homogeneousSubmodule (Fin (k + 1)) ℂ) z)
    (paired_c3_coordinate_projection_variable (A := ℂ) e i) (Away.map (pairedC3GradedCoordinateProjection (A := ℂ) e)
    (X (e i)) (Away.mk _ (isHomogeneous_X ℂ (e i)) 0 (C c)
      (by simpa using isHomogeneous_C (Fin (n + 1)) c))) = _
  rw [Away.map_mk, paired_c3_away_cast_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, paired_c3_coordinate_projection_constant,
    ProjSpace.val_algebraMap, pow_zero]
  rfl

end HodgeLean.Foundations.Program.G32Native
