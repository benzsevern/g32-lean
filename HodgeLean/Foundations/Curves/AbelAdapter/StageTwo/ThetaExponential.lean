import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.Defs
import HodgeLean.Foundations.Program.TorusAlgebraizationB56Period

/-! # The literal theta cover and the original exponential map

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open HodgeLean.Foundations HodgeLean.Foundations.Program
open scoped TensorProduct Manifold ContDiff CategoryTheory.MonObj
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- The original theta derivative, with its specified exponential coordinates.
Source: Birkenhake–Lange, §1.1; b5_periodDerivative.
HC no distance; AV milestone no distance. -/
def thetaCoverLinear (h : Module.finrank ℂ E = 1) :
    b3Rest2_VJ E C →L[ℂ] (Fin (TopologicalSpace.dim (model (C := C) h).left) → ℂ) := by
  letI := b3_periodLattice_finite (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  exact LinearMap.toContinuousLinearMap (b5_periodDerivative _ _
    (b3_isWeightOne (C := C) h) (polarization (C := C) h)
    (b3_intersectionForm_isRiemannForm h _ (b3_exists_intersectionForm (C := C) h).choose_spec))

/-- The literal theta cover is the exponential of its original derivative.
Source: Birkenhake–Lange, §1.1; b56_thetaCover_eq_exp.
HC no distance; AV milestone no distance. -/
theorem thetaCoverLinear_exp (h : Module.finrank ℂ E = 1) :
    letI := b3_periodLattice_finite (C := C) h
    letI := b3_periodLattice_free (E := E) (C := C)
    letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := C) h)
    ∀ z : b3Rest2_VJ E C,
      theta (C := C) h (b3Rest2_covHom (E := E) (C := C) z) =
        (complexExponential (model (C := C) h) _ (thetaCoverLinear h z)).toMul := by
  letI := b3_periodLattice_finite (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := C) h)
  let Λ := b3_periodLattice E C
  let F := b3_periodF E C
  let hF := b3_isWeightOne (C := C) h
  let Q := polarization (C := C) h
  have hQ := b3_intersectionForm_isRiemannForm h Q
    (b3_exists_intersectionForm (C := C) h).choose_spec
  letI := b5_groupObj Λ F hF Q hQ
  letI := b5_commutative Λ F hF Q hQ
  letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral Λ F hF Q hQ
  letI := b5_smooth Λ F hF Q hQ
  letI := b5_projective Λ F hF Q hQ
  intro z
  have hc := b56_cover_of _ _ (b5_theta_descent Λ F hF Q hQ)
  exact (hc z).trans (b56_thetaCover_eq_exp
    (b5_evaluation_irrelevant_aux Λ F hF Q hQ) (b5_thetaCover Λ F hF Q hQ)
    (fun _ ↦ rfl) (b56_bpf_of (b5_Lcube_basepointFree_aux Λ F hF Q hQ))
    (b5_theta Λ F hF Q hQ) hc (TopologicalSpace.dim (b5_model Λ F hF Q).left) (b5_group Λ F hF Q hQ).1
    (b5_group Λ F hF Q hQ).2.1 z)

#print axioms thetaCoverLinear
#print axioms thetaCoverLinear_exp

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
