import HodgeLean.Foundations.ChowAbelianSurfaceProofs
import HodgeLean.Adapters.LefschetzOneOneChowBridge

/-! # First primitives for set-level Chow on E²

Implications from finiteness to the canonical closed-point carrier on E², and
from polynomial homogeneity to the complex points of a fixed Zariski closure.
The latter is the scheme-carrier segment of the cone route. Analytic embedding
comparison and extension across the vertex remain deferred, as does Chow on E².
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Curves
namespace HodgeLean.Foundations

/-- Finite sets of complex points have their literal image as a closed scheme carrier.
Source: Mathlib `pointEquivClosedPoint`, `ext_of_apply_closedPoint_eq`;
the finite-set argument in `gaga24_curve_chow_aux`. -/
theorem chowEE_finite_algebraic (Z : Set (ComplexPoint (g3_power E 2)))
    (hZ : Z.Finite) :
    IsClosed ((Point.underlying : ComplexPoint (g3_power E 2) → (g3_power E 2).left) '' Z) ∧
      Z = (Point.underlying : ComplexPoint (g3_power E 2) → (g3_power E 2).left) ⁻¹'
        ((Point.underlying : ComplexPoint (g3_power E 2) → (g3_power E 2).left) '' Z) :=
  chowEE_finite_algebraic_aux Z hZ

/-- Homogeneity prevents Zariski closure from adding complex zero-test failures.
Source: Hartshorne, Algebraic Geometry, Chapter I §2, projective zero loci;
Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3, Chow's theorem. -/
theorem chowEE_projectiveCarrier_mem (n m : ℕ) (d : Fin m → ℕ)
    (P : Fin m → MvPolynomial (Fin (n + 1)) ℂ)
    (hP : ∀ j, (P j).IsHomogeneous (d j))
    (z : Fin (n + 1) → ℂ) (hz : z ≠ 0) :
    (ComplexProjectiveSpace.vectorToComplexPoint z hz).underlying ∈
        chowEE_projectiveCarrier n m P ↔ ∀ j, MvPolynomial.eval z (P j) = 0 :=
  chowEE_projectiveCarrier_mem_aux n m d P hP z hz

/-- W1: the identity point of the actual surface supplies every finite-set premise.
Source: abelian exponential at zero and finite singletons. -/
example : IsClosed ({(abelianExp (g3_power E 2) 0).underlying} :
    Set (g3_power E 2).left) ∧
    ({abelianExp (g3_power E 2) 0} : Set (ComplexPoint (g3_power E 2))) =
      Point.underlying ⁻¹' {(abelianExp (g3_power E 2) 0).underlying} := by
  simpa only [image_singleton] using
    chowEE_finite_algebraic {abelianExp (g3_power E 2) 0} (finite_singleton _)

/-- W2: the empty finite set has its exact empty carrier.
Source: finite empty sets. -/
example : IsClosed ((Point.underlying : ComplexPoint (g3_power E 2) →
    (g3_power E 2).left) '' ∅) ∧
    (∅ : Set (ComplexPoint (g3_power E 2))) = Point.underlying ⁻¹'
      ((Point.underlying : ComplexPoint (g3_power E 2) → (g3_power E 2).left) '' ∅) :=
  chowEE_finite_algebraic ∅ finite_empty

/-- W3: a nonempty proper projective hyperplane contains [0:1].
Source: Hartshorne, Algebraic Geometry, Chapter I §2. -/
example : (ComplexProjectiveSpace.vectorToComplexPoint (![0, 1] : Fin 2 → ℂ)
      (by intro h; have := congrFun h 1; norm_num at this)).underlying ∈
    chowEE_projectiveCarrier 1 1 (fun _ ↦ MvPolynomial.X 0) := by
  apply (chowEE_projectiveCarrier_mem 1 1 (fun _ ↦ 1)
    (fun _ ↦ MvPolynomial.X 0) (fun _ ↦ MvPolynomial.isHomogeneous_X ℂ 0) _ _).2
  intro j
  simp

/-- W4: the same hyperplane excludes [1:0].
Source: Hartshorne, Algebraic Geometry, Chapter I §2. -/
example : (ComplexProjectiveSpace.vectorToComplexPoint (![1, 0] : Fin 2 → ℂ)
      (by intro h; have := congrFun h 0; norm_num at this)).underlying ∉
    chowEE_projectiveCarrier 1 1 (fun _ ↦ MvPolynomial.X 0) := by
  rw [chowEE_projectiveCarrier_mem 1 1 (fun _ ↦ 1)
    (fun _ ↦ MvPolynomial.X 0) (fun _ ↦ MvPolynomial.isHomogeneous_X ℂ 0)]
  simp

/-- W5: a degree-zero unit excludes the point of projective zero-space.
Source: Hartshorne, Algebraic Geometry, Chapter I §2. -/
example : (ComplexProjectiveSpace.vectorToComplexPoint (fun _ : Fin 1 ↦ (1 : ℂ))
      (by intro h; have := congrFun h 0; norm_num at this)).underlying ∉
    chowEE_projectiveCarrier 0 1 (fun _ ↦ 1) := by
  rw [chowEE_projectiveCarrier_mem 0 1 (fun _ ↦ 0) (fun _ ↦ 1)
    (fun _ ↦ MvPolynomial.isHomogeneous_one (Fin 1) ℂ)]
  simp

/-- The requested consumer check supplies no additional geometric instances.
This is a type check under the displayed Chow binder, not a new Chow theorem.
Source: `bhg_lefschetzOneOne_of_chow` and `ccm10_hdg_le_span_EE`. -/
example (hChow : ∀ Z : Set (ComplexPoint (g3_power E 2)),
    IsClosedAnalytic (Fin (dim (g3_power E 2).left) → ℂ) Z →
      ∃ C : Set (g3_power E 2).left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint (g3_power E 2) → (g3_power E 2).left) ⁻¹' C) :
    ∀ p : ℕ, Hdg^p(g3_power E 2; ℚ) ≤ algebraicCycleClassSpan (g3_power E 2) p :=
  ccm10_hdg_le_span_EE (bhg_lefschetzOneOne_of_chow (g3_power E 2) hChow)

end HodgeLean.Foundations
