import HodgeLean.Foundations.Program.G32Native.CanonicalConormalDerivative
import HodgeLean.Foundations.Program.G32Native.ConormalPointDerivativeTangent
import HodgeLean.Foundations.Program.G32Native.SmoothConormalPointFrame
import HodgeLean.Foundations.Program.G32Native.SplitKernelPairing
import HodgeLean.Foundations.Program.G32Native.ConormalPointDerivativeNormalization

/-! # Actual conormal duals and the specified canonical normal complement -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual conormal derivative identifies the retained dual conormal
fibre with the kernel of the specified original tangent retraction. -/
def canonicalConormalFibreEquiv (G : CanonicalAbelGeometry) (x : ComplexPoint G.Q) :
    canonicalNormalFibre G x ≃ₗ[ℂ] canonicalNormalComplement G x := by
  let A := canonicalConormalDerivative G x
  let t := (fderiv ℂ (inclusionInComplexCharts G.W G.Q G.ι G.k (G.k + G.k) x)
    (localChart G.Q G.k x x)).toLinearMap
  let P := (closedImmersionDerivativeProjection G.W G.Q G.ι G.k (G.k + G.k) x).toLinearMap
  letI := smoothNormalPoint_finiteDimensional G.Q G.W G.k G.k G.ι x
  have hpt : P.comp t = LinearMap.id := by
    exact congrArg ContinuousLinearMap.toLinearMap
      (closedImmersionDerivativeProjection_leftInverse G.W G.Q G.ι G.k (G.k + G.k) x)
  have hat : A.comp t = 0 := by
    unfold A canonicalConormalDerivative
    exact conormalPointDerivativeMap_tangent G.k (G.k + G.k) G.ι x _ _ _
  have hrank : Module.finrank ℂ P.ker = Module.finrank ℂ (canonicalNormalFibre G x) :=
    (g32n_normal_rank G.W G.Q G.ι G.k x).trans
      (smoothNormalPoint_finrank G.Q G.W G.k G.k G.ι x).symm
  exact splitKernelPairingEquiv A t P hpt hat (canonicalConormalDerivative_surjective G x) hrank

/-- The retained original normal representative has exactly the original
conormal pairing value. -/
theorem canonicalConormalFibreEquiv_pairing (G : CanonicalAbelGeometry)
    (x : ComplexPoint G.Q) (ν : canonicalNormalFibre G x) :
    canonicalConormalDerivative G x (canonicalConormalFibreEquiv G x ν).val = ν := by
  exact (canonicalConormalFibreEquiv G x).symm_apply_apply ν

/-- On the retained original coordinate open, the specified canonical
normal representative retains the derivative of every original ideal equation. -/
theorem canonicalConormalFibreEquiv_chosen_localSection (G : CanonicalAbelGeometry)
    (x : ComplexPoint G.Q) (ν : canonicalNormalFibre G x)
    (s : SheafOfModules.unit
        (localEtaleCoordinates G.W (G.k + G.k) (Point.map G.ι x)).ambientCoordinateOpen.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback
        (localEtaleCoordinates G.W (G.k + G.k) (Point.map G.ι x)).ambientCoordinateOpen.ι).obj
        (Conormal.idealModule G.ι.left))
    (hx : Point.map G.ι x ∈ Point.overOpen
      (localEtaleCoordinates G.W (G.k + G.k) (Point.map G.ι x)).ambientCoordinateOpen) :
    ν (conormalLocalClass G.ι
      (localEtaleCoordinates G.W (G.k + G.k) (Point.map G.ι x)).ambientCoordinateOpen s x hx) =
    conormalLocalDerivative G.ι (G.k + G.k)
      (localEtaleCoordinates G.W (G.k + G.k) (Point.map G.ι x)).ambientCoordinateOpen s x
      (canonicalConormalFibreEquiv G x ν).val := by
  let D := localEtaleCoordinates G.W (G.k + G.k) (Point.map G.ι x)
  have hU : IsAffineOpen D.ambientCoordinateOpen := by
    simpa only [LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top]
      using D.isAffine
  have h := congrArg (fun f : canonicalNormalFibre G x =>
    f (conormalLocalClass G.ι D.ambientCoordinateOpen s x hx))
      (canonicalConormalFibreEquiv_pairing G x ν)
  exact h.symm.trans (conormalPointDerivativeMap_localSection G.ι (G.k + G.k) x
    D.ambientCoordinateOpen hU hx (canonicalConormalFibreEquiv G x ν).val s)

#print axioms canonicalConormalFibreEquiv_chosen_localSection
#print axioms canonicalConormalFibreEquiv_pairing
#print axioms canonicalConormalFibreEquiv
end HodgeLean.Foundations.Program.G32Native
