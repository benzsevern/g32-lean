import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8Defs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8OrientationProofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8CurvatureProofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian6ComponentProofs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian6DegreeProofs

/-! # Constructed geometric inputs for stage eight

The cubic and its square use the explicit shifted theta series and the checked stage-six
coordinates. A nonzero value provides degenerate avoiding boundaries without invoking
analytic stratification. The divisors themselves are nonempty.
This module holds only the witnesses, so later stages can use them without importing the
stage-eight leaves.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.Curves HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open Filter Set Topology
open scoped CategoryTheory.MonObj
namespace HodgeLean.Adapters

/-- Simultaneous concrete input data for testing component comparisons.
These data contain an equation and a nonzero value, but no cohomology comparison.
Source: the explicit theta and algebraic component constructions in stage six. -/
structure bh8_ComponentWitness (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] where
  x : X.left
  codim : Order.coheight x = 1
  support_nonempty : (bh4_componentSupport X x).Nonempty
  f : (Fin (dim X.left) → ℂ) → ℂ
  analytic : AnalyticOnNhd ℂ f univ
  reduced : ∀ p, Squarefree (⟨Germ.ofFun f, f, analytic p (mem_univ p), rfl⟩ :
    AnalyticGermAt (dim X.left) p)
  support : ∀ p, f p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X x
  point : Fin (dim X.left) → ℂ
  nonzero : f point ≠ 0

local instance bh8_cubic_comm : IsCommMonObj E :=
  isCommMonObj_of_complexSelfProductIntegral E (complexSelfProductIntegral_of_isIntegral E)

/-- The identity divisor of the cubic with its explicit elliptic theta equation.
Source: `bh6_point_component_aux`, `bh6_theta_kernel` and `bh6_reduced_linear_pullback_aux`. -/
def bh8_cubicWitness : bh8_ComponentWitness E := Classical.choice (by
  obtain ⟨τ, q, a, b, hτ, hs, hc⟩ := bh6_elliptic_coordinates_aux
  obtain ⟨x, hx, hxS⟩ := bh6_point_component_aux
  obtain ⟨hf, hred⟩ := bh6_reduced_linear_pullback_aux (dim E.left) q.toLinearMap
    q.surjective (bh6_theta τ) (bh6_theta_zeros τ hτ).1 (bh6_theta_simple_aux τ hτ)
  obtain ⟨w, hw⟩ := bh6_theta_nonzero τ hτ
  refine ⟨⟨x, hx, ?_, bh6_theta τ ∘ q, hf, hred, ?_, q.symm w, ?_⟩⟩
  · rw [hxS]; exact Set.singleton_nonempty _
  · intro v
    rw [hxS, Set.mem_singleton_iff]
    exact bh6_theta_kernel τ hτ q a b hs hc v
  · simpa using hw)

/-- The first-projection fiber on the square of the cubic, with its pulled-back theta equation.
Source: `bh6_product_coordinates_aux` and `bh6_product_component_aux`. -/
def bh8_productWitness : bh8_ComponentWitness (g3_power E 2) := Classical.choice (by
  obtain ⟨τ, q, a, b, hτ, hs, hc⟩ := bh6_elliptic_coordinates_aux
  obtain ⟨Q, t, ht, hQ⟩ := bh6_product_coordinates_aux
  obtain ⟨x, hx, hxne, hxS⟩ := bh6_product_component_aux
  let r : (Fin (dim (g3_power E 2).left) → ℂ) →ₗ[ℂ] ℂ :=
    q.toLinearMap.comp ((LinearMap.proj (0 : Fin 2)).comp Q.toLinearMap)
  have hr : Function.Surjective r := by
    intro w
    refine ⟨Q.symm (fun _ ↦ q.symm w), ?_⟩
    simp [r]
  obtain ⟨hf, hred⟩ := bh6_reduced_linear_pullback_aux _ r hr (bh6_theta τ)
    (bh6_theta_zeros τ hτ).1 (bh6_theta_simple_aux τ hτ)
  obtain ⟨w, hw⟩ := bh6_theta_nonzero τ hτ
  obtain ⟨v, hv⟩ := hr w
  refine ⟨⟨x, hx, hxne, bh6_theta τ ∘ r, hf, hred, ?_, v, ?_⟩⟩
  · intro v
    rw [hxS]
    change bh6_theta τ (q (Q v 0)) = 0 ↔ _ = 1
    rw [hQ]
    exact bh6_theta_kernel τ hτ q a b hs hc (Q v 0)
  · simpa [Function.comp_apply, hv] using hw)

example : (bh4_componentSupport E bh8_cubicWitness.x).Nonempty :=
  bh8_cubicWitness.support_nonempty
example : (bh4_componentSupport (g3_power E 2) bh8_productWitness.x).Nonempty :=
  bh8_productWitness.support_nonempty

/-- A nonzero value constructs all boundary hypotheses when both periods are zero.
Source: the formula for the four period-square edges. -/
theorem bh8_witness_boundary
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (W : bh8_ComponentWitness X) :
    (∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, W.f (bh4_squareEdge X 0 0 W.point i t) ≠ 0) ∧
    (∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1,
      abelianExp X (bh4_squareEdge X 0 0 W.point i t) ∉ cycleComponentSupport X W.x) := by
  have h (i : Fin 4) (t : ℝ) : bh4_squareEdge X 0 0 W.point i t = W.point := by
    fin_cases i <;> simp [bh4_squareEdge]
  refine ⟨fun i t _ ↦ by rw [h]; exact W.nonzero, ?_⟩
  intro i t _ hs
  rw [h] at hs
  exact W.nonzero ((W.support W.point).mpr hs)

end HodgeLean.Adapters
