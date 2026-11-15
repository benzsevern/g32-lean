import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.PeriodFormDuality
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.AnalyticFormPullback

/-! # Normalized analytic form equivalence on the retained theta model

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [Module.Finite ℤ (b3_periodLattice E C)]
  [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]

/-- The original curve forms identified with all analytic one-forms on the actual theta model.
Source: Birkenhake–Lange, §§1.1–1.2; Forster, §21; b3A_torus_formEquiv.
HC no distance; AV milestone no distance. -/
def thetaAnalyticFormEquiv (h : Module.finrank ℂ E = 1) :
    b3_HolForm E C ≃ₗ[ℂ]
      b3_HolForm (Fin (TopologicalSpace.dim (model (C := C) h).left) → ℂ)
        (ComplexPoint (model (C := C) h)) := by
  letI := b3_periodLattice_free (E := E) (C := C)
  letI := b2_torus_compactSpace _ (b3_isWeightOne (C := C) h)
  letI : ConnectedSpace (b3_Jacobian E C) :=
    (b3Rest2_covHom_spec (E := E) (C := C)).2.connectedSpace
      (b3Rest2_covHom_spec (E := E) (C := C)).1.continuous
  letI : IsManifold 𝓘(ℂ, b3Rest2_VJ E C) ω (b3_Jacobian E C) := b2_torus_isManifold _
  exact (((periodFormEquiv h).trans LinearMap.toContinuousLinearMap.symm).trans
    (b3A_torus_formEquiv (b3_periodF E C)).symm).trans
      (analyticFormTransport (theta (C := C) h) (theta_contMDiff h) (theta_symm_contMDiff h))

/-- The equivalence selects the invariant form with the original period covector exactly.
Source: Birkenhake–Lange, §§1.1–1.2; periodFormEquiv_apply.
HC no distance; AV milestone no distance. -/
theorem thetaAnalyticFormEquiv_apply (h : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) :
    thetaAnalyticFormEquiv h θ = thetaAnalyticForm h θ := by
  letI := b3_periodLattice_free (E := E) (C := C)
  letI := b2_torus_compactSpace _ (b3_isWeightOne (C := C) h)
  letI : ConnectedSpace (b3_Jacobian E C) :=
    (b3Rest2_covHom_spec (E := E) (C := C)).2.connectedSpace
      (b3Rest2_covHom_spec (E := E) (C := C)).1.continuous
  letI : IsManifold 𝓘(ℂ, b3Rest2_VJ E C) ω (b3_Jacobian E C) := b2_torus_isManifold _
  apply Subtype.ext
  change b3_pullback (Fin (TopologicalSpace.dim (model (C := C) h).left) → ℂ)
    (b3Rest2_VJ E C) (theta (C := C) h).symm
    (b3A_invForm (b3_periodF E C)
      (LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.symm (periodFormEquiv h θ)))) = _
  let e : Module.Dual ℂ (b3Rest2_VJ E C) ≃ₗ[ℂ] (b3Rest2_VJ E C →L[ℂ] ℂ) :=
    LinearMap.toContinuousLinearMap
  have he : e (e.symm (periodFormEquiv h θ)) = periodLinear θ :=
    (e.apply_symm_apply _).trans (periodFormEquiv_apply h θ)
  exact congrArg (fun ℓ : b3Rest2_VJ E C →L[ℂ] ℂ ↦
    b3_pullback (Fin (TopologicalSpace.dim (model (C := C) h).left) → ℂ)
      (b3Rest2_VJ E C) (theta (C := C) h).symm (b3A_invForm (b3_periodF E C) ℓ)) he

#print axioms thetaAnalyticFormEquiv
#print axioms thetaAnalyticFormEquiv_apply

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
