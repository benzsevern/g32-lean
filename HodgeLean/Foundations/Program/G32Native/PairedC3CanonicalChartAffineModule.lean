import HodgeLean.Foundations.Program.G32Native.PairedC3CanonicalChartIso
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineConormalTensor

noncomputable section
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The pulled original conormal on the full affine chart is an associated module. -/
theorem paired_c3_canonical_chart_module_affine {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    IsIso ((Scheme.Modules.pullback (pairedC3ChartInclusion k i)).obj
      (s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e))).fromTildeΓ := by
  let R := pairedC3ChartRing n (e i)
  let S := pairedC3ChartRing k i
  let q := pairedC3ChartProjection e i
  let T := (ModuleCat.extendScalars q.hom).obj (ModuleCat.of R (RingHom.ker q.hom))
  exact isIso_fromTildeΓ_iff.mpr
    ⟨T, ⟨(pairedC3CanonicalChartConormalIso e i ≪≫ pairedC3AffineConormalTensorIso R S q).symm⟩⟩

#print axioms paired_c3_canonical_chart_module_affine
end HodgeLean.Foundations.Program.G32Native
