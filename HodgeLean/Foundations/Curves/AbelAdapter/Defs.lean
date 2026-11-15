import HodgeLean.Foundations.Program.CurveJacobian
import HodgeLean.Foundations.Program.TorusAlgebraization
import HodgeLean.Adapters.GagaMaps

/-! # Normalized period-model Abel construction

The lattice, filtration, theta model and path normalization are retained literally.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
open scoped TensorProduct Manifold ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- The selected integral intersection polarization on the original B3 period lattice.
Source: Farkas–Kra, Riemann Surfaces, III; `b3_exists_intersectionForm`. -/
def polarization (hE : Module.finrank ℂ E = 1) :
    LinearMap.BilinForm ℤ (b3_periodLattice E C) :=
  (b3_exists_intersectionForm (C := C) hE).choose

example (hE : Module.finrank ℂ E = 1) (l : b3_periodLattice E C) :
    polarization hE l (0 : b3_periodLattice E C) = 0 := map_zero _

private theorem polarization_spec (hE : Module.finrank ℂ E = 1) :
    b3_IsIntersectionForm E (polarization (C := C) hE) :=
  (b3_exists_intersectionForm (C := C) hE).choose_spec

variable (hE : Module.finrank ℂ E = 1)

/-- The selected path-integral map into the unaltered B3 quotient.
Source: Forster, Lectures on Riemann Surfaces, §21; `b3_exists_abelJacobi`. -/
def analyticAbel (p : C) : C → b3_Jacobian E C :=
  (b3_exists_abelJacobi hE p).choose

example (p : C) : analyticAbel hE p p = 0 :=
  (b3_exists_abelJacobi hE p).choose_spec.1

/-- The actual third-Veronese Proj, with B3's integral lattice and selected polarization.
Source: Birkenhake–Lange, Complex Abelian Varieties, Theorem 4.5.1 and Ch. 11. -/
def model : Over (Spec ↧ℂ) := by
  letI := b3_periodLattice_finite (C := C) hE
  letI := b3_periodLattice_free (E := E) (C := C)
  exact b5_model (b3_periodLattice E C) (b3_periodF E C)
    (b3_isWeightOne hE) (polarization hE)

example : IsProjective (model (C := C) hE).hom := by
  letI := b3_periodLattice_finite (C := C) hE
  letI := b3_periodLattice_free (E := E) (C := C)
  exact b5_projective _ _ _ _
    (b3_intersectionForm_isRiemannForm hE _ (polarization_spec hE))

/-- The theta homeomorphism on the retained B3 quotient, without a rescaling.
Source: Birkenhake–Lange, Theorem 4.5.1; `b5_thetaEquiv`. -/
def theta : b3_Jacobian E C ≃ₜ ComplexPoint (model (C := C) hE) := by
  letI := b3_periodLattice_finite (C := C) hE
  letI := b3_periodLattice_free (E := E) (C := C)
  exact b5_thetaEquiv _ _ (b3_isWeightOne hE) (polarization hE)
    (b3_intersectionForm_isRiemannForm hE _ (polarization_spec hE))

example (t : b3_Jacobian E C) : (theta hE).symm (theta hE t) = t :=
  (theta hE).symm_apply_apply t

/-- The analytic Abel map with values in the actual projective model.
Source: Forster, §21; Birkenhake–Lange, Ch. 11. -/
def modelAbel (p : C) : C → ComplexPoint (model (C := C) hE) :=
  theta hE ∘ analyticAbel hE p

example (p : C) : modelAbel hE p p = theta hE 0 := by
  exact congrArg (theta hE) (b3_exists_abelJacobi hE p).choose_spec.1

end HodgeLean.Foundations.Curves.AbelAdapter
