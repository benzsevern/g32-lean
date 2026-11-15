import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.ThetaSchemeForms
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.CoverDifferential
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.FormCoverComposition

/-! # Literal cover values of the selected invariant scheme forms

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

/-- The specified complex manifold structure on a lattice quotient.
HC no distance; AV milestone no distance. -/
local instance coverPullbackTorusManifold {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) [DiscreteTopology (b2_latticeMap Λ F).range] :
    IsManifold 𝓘(ℂ, b3A_TM F) ω (b2_torus Λ F) := b2_torus_isManifold F

/-- Pullback of a constant invariant torus form along the original cover.
Source: Birkenhake–Lange, §1.1; torusCover_mfderiv.
HC no distance; AV milestone no distance. -/
theorem invariantForm_coverPullback {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) [DiscreteTopology (b2_latticeMap Λ F).range]
    (ℓ : b3A_TM F →L[ℂ] ℂ) :
    b3_pullback (b3A_TM F) (b3A_TM F) (b2_torusCover Λ F) (b3A_invForm F ℓ) =
      (fun w : TangentBundle 𝓘(ℂ, b3A_TM F) (b3A_TM F) ↦ ℓ w.2) := by
  funext w
  change ℓ (mfderiv 𝓘(ℂ, b3A_TM F) 𝓘(ℂ, b3A_TM F) (b2_torusCover Λ F) w.1 w.2) = _
  rw [torusCover_mfderiv]
  rfl

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]

section CoverPullback
variable [Module.Finite ℤ (b3_periodLattice E C)]
  [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]

/-- The specified complex manifold structure on the curve period quotient.
HC no distance; AV milestone no distance. -/
local instance coverPullbackJacobianManifold :
    IsManifold 𝓘(ℂ, b3Rest2_VJ E C) ω (b3_Jacobian E C) := b2_torus_isManifold _

/-- The analytic invariant form pulls back to its constant covector on the original cover.
Source: Birkenhake–Lange, §§1.1–1.2; formPullback_comp.
HC no distance; AV milestone no distance. -/
theorem thetaAnalyticForm_coverPullback (h : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) :
    b3_pullback (b3Rest2_VJ E C) _
      (theta (C := C) h ∘ b3Rest2_covHom (E := E) (C := C))
      (thetaAnalyticForm h θ).val =
      (fun w : TangentBundle 𝓘(ℂ, b3Rest2_VJ E C) (b3Rest2_VJ E C) ↦ periodLinear θ w.2) := by
  have hc := (b2_torusCover_contMDiff (b3_periodF E C)).mdifferentiable (by simp)
  have ht := (theta_contMDiff (C := C) h).mdifferentiable (by simp)
  exact formCoverComposition (b3Rest2_covHom (E := E) (C := C)) hc
    (fun z ↦ torusCover_mfderiv (b3_periodF E C) z)
    (theta (C := C) h) ht (thetaAnalyticForm h θ).val (periodLinear θ)
    (thetaAnalyticForm_pullback h θ)

/-- Scheme-form pullback retains the same constant covector on the original cover.
Source: Birkenhake–Lange, §§1.1–1.2; thetaSchemeFormEquiv_values.
HC no distance; AV milestone no distance. -/
theorem thetaSchemeForm_coverPullback (h : Module.finrank ℂ E = 1) (θ : b3_HolForm E C) :
    b3_pullback (b3Rest2_VJ E C) _
      (theta (C := C) h ∘ b3Rest2_covHom (E := E) (C := C))
      (schemeForm (model (C := C) h) (thetaSchemeFormEquiv h θ)) =
      (fun w : TangentBundle 𝓘(ℂ, b3Rest2_VJ E C) (b3Rest2_VJ E C) ↦ periodLinear θ w.2) := by
  exact (congrArg (b3_pullback (b3Rest2_VJ E C) _
    (theta (C := C) h ∘ b3Rest2_covHom (E := E) (C := C)))
      (thetaSchemeFormEquiv_values h θ)).trans (thetaAnalyticForm_coverPullback h θ)
end CoverPullback

/-- The selected global scheme forms have exactly the original covectors on the literal theta cover.
Source: Birkenhake–Lange, §§1.1–1.2; Forster, §21; mfderiv_comp_apply.
HC no distance; AV milestone no distance. -/
theorem thetaSchemeFormEquiv_cover
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] (h : Module.finrank ℂ E = 1) :
    letI := b3_periodLattice_finite (C := C) h
    letI := b3_periodLattice_free (E := E) (C := C)
    letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := C) h)
    ∀ (θ : b3_HolForm E C) (z v : b3Rest2_VJ E C),
      globalOneFormCovector (model (C := C) h) _ (thetaSchemeFormEquiv h θ)
        (theta (C := C) h (b3Rest2_covHom (E := E) (C := C) z))
        (mfderiv 𝓘(ℂ, b3Rest2_VJ E C)
          𝓘(ℂ, Fin (TopologicalSpace.dim (model (C := C) h).left) → ℂ)
          (theta (C := C) h ∘ b3Rest2_covHom (E := E) (C := C)) z v) = periodCovector h θ v := by
  letI := b3_periodLattice_finite (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := C) h)
  intro θ z v
  exact (congrFun (thetaSchemeForm_coverPullback h θ) ⟨z, v⟩).trans
    (periodLinear_apply h θ v)

#print axioms thetaAnalyticForm_coverPullback
#print axioms thetaSchemeForm_coverPullback
#print axioms thetaSchemeFormEquiv_cover

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
