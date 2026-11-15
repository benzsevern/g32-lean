import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveChartSectionValue
import HodgeLean.Foundations.Program.G32Native.PairedC3NormalizedCoordinateChart
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineChartIdealValue
import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalChartClass
import HodgeLean.Foundations.Program.G32Native.PairedC3OriginalChartKernelBasis
import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalStandardGenerators
import HodgeLean.Foundations.AlgebraicGeometry.ConormalBaseChange

/-! # Canonical normal generators on the original affine chart diagram -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
open AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry.Scheme.Modules.FramePullback
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev pairedC3ChartRing (n : ℕ) (i : Fin (n + 1)) : CommRingCat :=
  CommRingCat.of (Away (homogeneousSubmodule (Fin (n + 1)) ℂ) (X i))

def pairedC3ChartInclusion (n : ℕ) (i : Fin (n + 1)) :
    Spec (pairedC3ChartRing n i) ⟶ pairedC3Proj n :=
  Proj.awayι (homogeneousSubmodule (Fin (n + 1)) ℂ) (X i) (isHomogeneous_X ℂ i) zero_lt_one

def pairedC3ChartProjection {n k : ℕ} (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    pairedC3ChartRing n (e i) ⟶ pairedC3ChartRing k i :=
  CommRingCat.ofHom (pairedC3CoordinateChartMap e i)

instance pairedC3ChartInclusion_isOpenImmersion (n : ℕ) (i : Fin (n + 1)) :
    IsOpenImmersion (pairedC3ChartInclusion n i) := by
  dsimp only [pairedC3ChartInclusion]
  infer_instance

/-- The named source chart has the original retained standard open as its full preimage. -/
theorem paired_c3_chart_inclusion_preimage (n : ℕ) (i : Fin (n + 1)) :
    pairedC3ChartInclusion n i ⁻¹ᵁ ProjSpace.standardOpen ℂ n i = ⊤ :=
  paired_c3_projective_chart_preimage n i

/-- The named chart diagram commutes in its original scheme maps. -/
theorem paired_c3_chart_diagram_commutes {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    pairedC3ChartInclusion k i ≫ pairedC3PolynomialCoordinateInclusion (A := ℂ) e =
      Spec.map (pairedC3ChartProjection e i) ≫ pairedC3ChartInclusion n (e i) :=
  paired_c3_normalized_coordinate_chart_commutes e i

/-- The named projection retains the original source standard open. -/
theorem paired_c3_chart_projection_preimage {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    pairedC3PolynomialCoordinateInclusion (A := ℂ) e ⁻¹ᵁ ProjSpace.standardOpen ℂ n (e i) =
      ProjSpace.standardOpen ℂ k i :=
  paired_c3_coordinate_inclusion_preimage_basicOpen (A := ℂ) e i

/-- The composite chart parameterization lies entirely in the original ambient chart. -/
theorem paired_c3_chart_composite_preimage {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    (pairedC3ChartInclusion k i ≫ pairedC3PolynomialCoordinateInclusion (A := ℂ) e) ⁻¹ᵁ
      ProjSpace.standardOpen ℂ n (e i) = ⊤ := by
  change pairedC3ChartInclusion k i ⁻¹ᵁ
    (pairedC3PolynomialCoordinateInclusion (A := ℂ) e ⁻¹ᵁ ProjSpace.standardOpen ℂ n (e i)) = ⊤
  rw [paired_c3_coordinate_inclusion_preimage_basicOpen]
  exact paired_c3_chart_inclusion_preimage k i

/-- The original projective ideal generator, transported to the entire affine chart ideal. -/
def pairedC3CanonicalAffineIdealGenerator {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1))
    (j : {j : Fin (n + 1) // j ∉ Set.range e}) :
    Γ(Conormal.idealModule (Spec.map (pairedC3ChartProjection e i)), ⊤) :=
  pairedC3AffineChartIdealSection (pairedC3PolynomialCoordinateInclusion (A := ℂ) e)
    (pairedC3ChartRing n (e i)) (pairedC3ChartRing k i) (pairedC3ChartProjection e i)
    (pairedC3ChartInclusion n (e i)) (pairedC3ChartInclusion k i)
    (paired_c3_chart_diagram_commutes e i)
    (ProjSpace.standardOpen ℂ n (e i)) (paired_c3_chart_inclusion_preimage n (e i))
    (pairedC3ProjectiveIdealGenerator e i j.val j.property)

/-- The original conormal generator pulled to the full affine source chart. -/
def pairedC3CanonicalChartConormalGenerator {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1))
    (j : {j : Fin (n + 1) // j ∉ Set.range e}) :
    Γ((Scheme.Modules.pullback (pairedC3ChartInclusion k i)).obj
      (s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e)), ⊤) :=
  pairedC3ConormalChartSourceClass (pairedC3PolynomialCoordinateInclusion (A := ℂ) e)
    (pairedC3ChartInclusion k i) (ProjSpace.standardOpen ℂ n (e i)) (ProjSpace.standardOpen ℂ k i)
    (paired_c3_chart_projection_preimage e i)
    (paired_c3_chart_inclusion_preimage k i) (pairedC3ProjectiveIdealGenerator e i j.val j.property)

end HodgeLean.Foundations.Program.G32Native
