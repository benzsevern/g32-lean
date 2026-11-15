import HodgeLean.Foundations.Program.SchoenTowerN2bPullbackChartOverlaps
import HodgeLean.Foundations.Program.SchoenTowerN2bGeometricDenominators
import HodgeLean.Foundations.Program.SchoenTowerN2bCoordinateRatios

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- The actual normalized projective coordinate viewed in the integral source function field.
Source: Hartshorne, Algebraic Geometry, II.2.5 and II.3. -/
def n2b_pullbackRationalCoord {X : Scheme.{0}} [IsIntegral X] {n : ℕ}
    (ψ : X ⟶ g3c_P n) (i j : Fin (n + 1)) [Nonempty (n2b_pullbackChart ψ j)] :
    X.functionField :=
  n2b_openChartRationalMap (n2b_pullbackChartι ψ j) (n2b_pullbackChartCoord ψ j i)

theorem n2b_pullbackRationalCoord_self {X : Scheme.{0}} [IsIntegral X] {n : ℕ}
    (ψ : X ⟶ g3c_P n) (i : Fin (n + 1)) [Nonempty (n2b_pullbackChart ψ i)] :
    n2b_pullbackRationalCoord ψ i i = 1 := by
  unfold n2b_pullbackRationalCoord
  rw [n2b_pullbackChartCoord_self, map_one]

/-- Actual normalized rational coordinates obey the multiplicative transition equation. -/
theorem n2b_pullbackRationalCoord_transition {X : Scheme.{0}} [IsIntegral X] {n : ℕ}
    (ψ : X ⟶ g3c_P n) (i j k : Fin (n + 1))
    [Nonempty (n2b_pullbackChart ψ i)] [Nonempty (n2b_pullbackChart ψ j)] :
    n2b_pullbackRationalCoord ψ k j =
      n2b_pullbackRationalCoord ψ i j * n2b_pullbackRationalCoord ψ k i := by
  let p := pullback.fst (n2b_pullbackChartι ψ i) (n2b_pullbackChartι ψ j)
  let q := pullback.snd (n2b_pullbackChartι ψ i) (n2b_pullbackChartι ψ j)
  let P : Scheme.{0} := pullback (n2b_pullbackChartι ψ i) (n2b_pullbackChartι ψ j)
  letI : Nonempty P :=
    n2b_openChart_overlap_nonempty (n2b_pullbackChartι ψ i) (n2b_pullbackChartι ψ j)
  letI : IsIntegral P := isIntegral_of_isOpenImmersion q
  let φ := n2b_openChartRationalMap (q ≫ n2b_pullbackChartι ψ j)
  have hv : φ (p.appTop.hom (n2b_pullbackChartCoord ψ i k)) =
      n2b_openChartRationalMap (n2b_pullbackChartι ψ i) (n2b_pullbackChartCoord ψ i k) := by
    simpa only [φ, p, q, pullback.condition] using
      (n2b_openChartRationalMap_restrict p (n2b_pullbackChartι ψ i)
        (n2b_pullbackChartCoord ψ i k))
  have h := congrArg φ (n2b_pullbackChart_overlap_coord ψ i j k)
  change φ (q.appTop.hom (n2b_pullbackChartCoord ψ j k)) =
    φ (q.appTop.hom (n2b_pullbackChartCoord ψ j i) *
      p.appTop.hom (n2b_pullbackChartCoord ψ i k)) at h
  simp only [map_mul, hv] at h
  dsimp only [φ] at h
  simpa only [n2b_openChartRationalMap_restrict, n2b_pullbackRationalCoord] using h

end HodgeLean.Foundations.Program
