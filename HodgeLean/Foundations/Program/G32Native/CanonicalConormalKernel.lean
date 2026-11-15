import HodgeLean.Foundations.Program.G32Native.CanonicalConormalFibreEquiv
import HodgeLean.Foundations.Program.G32Native.SplitKernelExact

/-! # The exact tangent kernel of the actual conormal derivative -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual conormal derivative has exactly the original immersion tangent
image as kernel. -/
theorem canonicalConormalDerivative_ker (G : CanonicalAbelGeometry) (x : ComplexPoint G.Q) :
    LinearMap.ker (canonicalConormalDerivative G x) = LinearMap.range
      (fderiv ℂ (inclusionInComplexCharts G.W G.Q G.ι G.k (G.k + G.k) x)
        (localChart G.Q G.k x x)).toLinearMap := by
  let A := canonicalConormalDerivative G x
  let t := (fderiv ℂ (inclusionInComplexCharts G.W G.Q G.ι G.k (G.k + G.k) x)
    (localChart G.Q G.k x x)).toLinearMap
  let P := (closedImmersionDerivativeProjection G.W G.Q G.ι G.k (G.k + G.k) x).toLinearMap
  letI := smoothNormalPoint_finiteDimensional G.Q G.W G.k G.k G.ι x
  have hpt : P.comp t = LinearMap.id := congrArg ContinuousLinearMap.toLinearMap
    (closedImmersionDerivativeProjection_leftInverse G.W G.Q G.ι G.k (G.k + G.k) x)
  have hat : A.comp t = 0 := by
    unfold A canonicalConormalDerivative
    exact conormalPointDerivativeMap_tangent G.k (G.k + G.k) G.ι x _ _ _
  have hrank : Module.finrank ℂ P.ker = Module.finrank ℂ (canonicalNormalFibre G x) :=
    (g32n_normal_rank G.W G.Q G.ι G.k x).trans
      (smoothNormalPoint_finrank G.Q G.W G.k G.k G.ι x).symm
  apply ker_eq_range_of_split_pairing A t P hpt hat
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr
    (splitKernelPairing_surjective A t P hpt hat (canonicalConormalDerivative_surjective G x))

#print axioms canonicalConormalDerivative_ker

/-- Every linear map vanishing on the original tangent image takes the same
value on a vector and its specified conormal-normal representative. -/
theorem canonicalConormalDerivative_factor (G : CanonicalAbelGeometry)
    (x : ComplexPoint G.Q) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : (Fin (G.k + G.k) → ℂ) →ₗ[ℂ] V)
    (hD : LinearMap.range
      (fderiv ℂ (inclusionInComplexCharts G.W G.Q G.ι G.k (G.k + G.k) x)
        (localChart G.Q G.k x x)).toLinearMap ≤ LinearMap.ker D)
    (w : Fin (G.k + G.k) → ℂ) :
    D (canonicalConormalFibreEquiv G x (canonicalConormalDerivative G x w)).val = D w := by
  have hv : w - (canonicalConormalFibreEquiv G x (canonicalConormalDerivative G x w)).val ∈
      LinearMap.ker (canonicalConormalDerivative G x) := by
    change canonicalConormalDerivative G x
      (w - (canonicalConormalFibreEquiv G x (canonicalConormalDerivative G x w)).val) = 0
    rw [map_sub, canonicalConormalFibreEquiv_pairing, sub_self]
  rw [canonicalConormalDerivative_ker] at hv
  have hz := hD hv
  change D (w - (canonicalConormalFibreEquiv G x (canonicalConormalDerivative G x w)).val) = 0 at hz
  exact (sub_eq_zero.mp (by simpa only [map_sub] using hz)).symm

#print axioms canonicalConormalDerivative_factor

end HodgeLean.Foundations.Program.G32Native
