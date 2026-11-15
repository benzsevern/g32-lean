import HodgeLean.Foundations.Program.G32Native.PairedC3CanonicalAffineGenerators
import HodgeLean.Foundations.Program.G32Native.PairedC3CanonicalChartIso
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineConormalBasis

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable MvPolynomial.gradedAlgebra

/-- The affine conormal basis indexed by the original discarded coordinates. -/
def pairedC3CanonicalAffineConormalBasis {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1)) :
    Module.Basis {j : Fin (n + 1) // j ∉ Set.range e} (pairedC3ChartRing k i)
      ((moduleSpecΓFunctor (R := pairedC3ChartRing k i)).obj
        (Conormal.sheaf (Spec.map (pairedC3ChartProjection e i)))) :=
  pairedC3AffineConormalBasis (pairedC3ChartRing n (e i)) (pairedC3ChartRing k i)
    (pairedC3ChartProjection e i) (paired_c3_coordinate_chart_map_surjective e i)
    (pairedC3OriginalChartKernelBasis e i)

/-- The affine basis vectors are the original transported ideal classes. -/
theorem paired_c3_canonical_affine_basis_class {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1))
    (j : {j : Fin (n + 1) // j ∉ Set.range e}) :
    pairedC3CanonicalAffineConormalBasis e i j =
      pairedC3PullbackSection (Spec.map (pairedC3ChartProjection e i))
        (Conormal.idealModule (Spec.map (pairedC3ChartProjection e i))) ⊤
        (pairedC3CanonicalAffineIdealGenerator e i j) := by
  exact paired_c3_affine_conormal_basis_apply
    (pairedC3ChartRing n (e i)) (pairedC3ChartRing k i) (pairedC3ChartProjection e i)
    (paired_c3_coordinate_chart_map_surjective e i) (pairedC3OriginalChartKernelBasis e i)
    (fun a => ⟨ProjSpace.ratio ℂ n (e i) a.val,
      paired_c3_coordinate_chart_map_discarded_ratio e i a.val a.property⟩)
    (paired_c3_original_chart_kernel_basis_apply e i)
    (pairedC3CanonicalAffineIdealGenerator e i)
    (paired_c3_canonical_affine_ideal_generator_value e i) j

#print axioms paired_c3_canonical_affine_basis_class
end HodgeLean.Foundations.Program.G32Native
