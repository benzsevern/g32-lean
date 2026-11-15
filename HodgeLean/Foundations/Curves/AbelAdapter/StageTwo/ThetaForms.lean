import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.IntegralSource

/-! # Analytic forms on the retained theta model

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

section Pullback
variable {U V W : Type} [NormedAddCommGroup U] [NormedSpace ℂ U]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {S T R : Type} [TopologicalSpace S] [ChartedSpace U S]
  [TopologicalSpace T] [ChartedSpace V T] [TopologicalSpace R] [ChartedSpace W R]

/-- Pullback of tangent functions respects the chain rule.
Source: Griffiths–Harris, chapter 0 §2; mfderiv_comp_apply.
HC no distance; AV milestone no distance. -/
theorem formPullback_comp (f : S → T) (hf : MDifferentiable 𝓘(ℂ, U) 𝓘(ℂ, V) f)
    (g : T → R) (hg : MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, W) g)
    (form : TangentBundle 𝓘(ℂ, W) R → ℂ) :
    b3_pullback U W (g ∘ f) form = b3_pullback U V f (b3_pullback V W g form) := by
  funext p
  exact congrArg (fun w ↦ form ⟨g (f p.1), w⟩)
    (mfderiv_comp_apply p.1 (hg (f p.1)) (hf p.1) p.2)

/-- Pullback along an analytic homeomorphism cancels pullback along its inverse.
Source: Griffiths–Harris, chapter 0 §2; mfderiv_comp_apply.
HC no distance; AV milestone no distance. -/
theorem formPullback_inverse (f : S ≃ₜ T)
    (hf : MDifferentiable 𝓘(ℂ, U) 𝓘(ℂ, V) f)
    (hg : MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, U) f.symm)
    (form : TangentBundle 𝓘(ℂ, U) S → ℂ) :
    b3_pullback U V f (b3_pullback V U f.symm form) = form := by
  rw [← formPullback_comp f hf f.symm hg form]
  have hi : f.symm ∘ f = id := funext f.symm_apply_apply
  rw [hi]
  funext p
  change form ⟨p.1, mfderiv 𝓘(ℂ, U) 𝓘(ℂ, U) id p.1 p.2⟩ = form p
  rw [mfderiv_id]
  rfl
end Pullback

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  (h : Module.finrank ℂ E = 1)

variable [Module.Finite ℤ (b3_periodLattice E C)]
  [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
/-- The original Jacobian manifold structure.
HC no distance; AV milestone no distance. -/
local instance thetaJacobianManifold : IsManifold 𝓘(ℂ, b3Rest2_VJ E C) ω (b3_Jacobian E C) :=
  b2_torus_isManifold _

/-- The original period covector as a continuous complex linear map.
Source: Forster, §21; b3Rest2_ellV.
HC no distance; AV milestone no distance. -/
def periodLinear (θ : b3_HolForm E C) : b3Rest2_VJ E C →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj θ).comp
      (((b3_periodF E C).liftQ (b3_cplxPeriod E C) le_rfl).comp
        (b2_coord (b3Rest2_QJ E C)).symm.toLinearMap))

/-- The continuous covector has exactly the retained period values.
Source: Forster, §21; b3Rest2_ellV.
HC no distance; AV milestone no distance. -/
theorem periodLinear_apply (θ : b3_HolForm E C) (v : b3Rest2_VJ E C) :
    periodLinear θ v = periodCovector h θ v := rfl

/-- Holomorphicity of theta in the retained charts.
Source: Birkenhake–Lange, Theorem 4.5.1; b5_theta_holomorphicFunctions.
HC no distance; AV milestone no distance. -/
theorem theta_contMDiff :
    ContMDiff 𝓘(ℂ, b3Rest2_VJ E C)
      𝓘(ℂ, Fin (TopologicalSpace.dim (model (C := C) h).left) → ℂ) ω (theta (C := C) h) :=
  (b5_theta_holomorphicFunctions _ _ (b3_isWeightOne (C := C) h) (polarization (C := C) h)
    (b3_intersectionForm_isRiemannForm h _ (b3_exists_intersectionForm (C := C) h).choose_spec)).1

/-- Holomorphicity of theta's inverse in the retained charts.
Source: Birkenhake–Lange, Theorem 4.5.1; b5_theta_holomorphicFunctions.
HC no distance; AV milestone no distance. -/
theorem theta_symm_contMDiff :
    ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim (model (C := C) h).left) → ℂ)
      𝓘(ℂ, b3Rest2_VJ E C) ω (theta (C := C) h).symm :=
  (b5_theta_holomorphicFunctions _ _ (b3_isWeightOne (C := C) h) (polarization (C := C) h)
    (b3_intersectionForm_isRiemannForm h _ (b3_exists_intersectionForm (C := C) h).choose_spec)).2.1

/-- The analytic invariant form transported to the actual theta model.
Source: Birkenhake–Lange, §§1.1–1.2; b3A_invForm_mem.
HC no distance; AV milestone no distance. -/
def thetaAnalyticForm (θ : b3_HolForm E C) :
    b3_HolForm (Fin (TopologicalSpace.dim (model (C := C) h).left) → ℂ)
      (ComplexPoint (model (C := C) h)) :=
  ⟨b3_pullback _ _ (theta (C := C) h).symm (b3A_invForm (b3_periodF E C) (periodLinear θ)),
    b3_pullback_mem_holForm _ (theta_symm_contMDiff h) _
      (b3A_invForm_mem _ (periodLinear θ))⟩

/-- Pullback along theta recovers the original analytic invariant covector.
Source: Birkenhake–Lange, §§1.1–1.2; mfderiv_comp_apply.
HC no distance; AV milestone no distance. -/
theorem thetaAnalyticForm_pullback (θ : b3_HolForm E C) :
    b3_pullback (b3Rest2_VJ E C) _ (theta (C := C) h) (thetaAnalyticForm h θ).val =
      b3A_invForm (b3_periodF E C) (periodLinear θ) :=
  formPullback_inverse (theta (C := C) h)
    ((theta_contMDiff h).mdifferentiable (by simp))
    ((theta_symm_contMDiff h).mdifferentiable (by simp)) _

/-- The model Abel pullback agrees with the original analytic Abel pullback.
Source: Forster, §21; mfderiv_comp_apply.
HC no distance; AV milestone no distance. -/
theorem thetaAnalyticForm_abel (p : C) (θ : b3_HolForm E C) :
    b3_pullback E _ (modelAbel h p) (thetaAnalyticForm h θ).val =
      b3_pullback E (b3Rest2_VJ E C) (analyticAbel h p)
        (b3A_invForm (b3_periodF E C) (periodLinear θ)) := by
  have ha : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, b3Rest2_VJ E C) (analyticAbel h p) :=
    (b3_abelJacobi_holomorphic (C := C) h p (analyticAbel h p)
      (b3_exists_abelJacobi h p).choose_spec).mdifferentiable (by simp)
  have ht := (theta_contMDiff (C := C) h).mdifferentiable (by simp)
  exact (formPullback_comp (analyticAbel h p) ha (theta (C := C) h) ht
    (thetaAnalyticForm h θ).val).trans
      (congrArg (b3_pullback E (b3Rest2_VJ E C) (analyticAbel h p))
        (thetaAnalyticForm_pullback h θ))

#print axioms periodLinear
#print axioms thetaAnalyticForm
#print axioms thetaAnalyticForm_pullback
#print axioms thetaAnalyticForm_abel

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
