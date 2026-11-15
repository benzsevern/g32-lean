import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs

/-! # Evaluation of rational cycles on actual component classes

HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Evaluate a cycle by its actual rational coefficients on a supplied family of component classes.
Source: Fulton, Intersection Theory, sections 1.5 and 19.1, rational linearity in prime components.
HC no distance; AV milestone no distance. -/
def properCycle_component_evaluation
    {X : Scheme.{0}} {W : Type*} [AddCommGroup W] [Module ℚ W]
    (C : X → W) (γ : AlgebraicCycle X ℚ) : W := ∑ᶠ ξ, γ ξ • C ξ

private lemma evaluation_support_finite
    {X : Scheme.{0}} [CompactSpace X] {W : Type*} [AddCommGroup W] [Module ℚ W]
    (C : X → W) (γ : AlgebraicCycle X ℚ) :
    Function.HasFiniteSupport (fun ξ => γ ξ • C ξ) := by
  apply (a3b2_support_finite γ).subset
  intro ξ hξ
  change γ ξ ≠ 0
  intro hz
  apply hξ
  change γ ξ • C ξ = 0
  rw [hz, zero_smul]

/-- The evaluation on a literal prime retains its coefficient and its selected component class.
Source: Fulton, Intersection Theory, section 1.5.
HC no distance; AV milestone no distance. -/
theorem properCycle_component_evaluation_single
    {X : Scheme.{0}} [DecidableEq X] {W : Type*} [AddCommGroup W] [Module ℚ W]
    (C : X → W) (ξ : X) (q : ℚ) :
    properCycle_component_evaluation C (Function.locallyFinsuppWithin.single ξ q) = q • C ξ := by
  classical
  unfold properCycle_component_evaluation
  rw [finsum_eq_single _ ξ]
  · simp
  · intro η hη
    simp [hη]

example {X : Scheme.{0}} (ξ : X) :
    properCycle_component_evaluation (fun _ : X => (3 : ℚ)) (properPrime ξ) = 3 := by
  classical
  rw [properPrime, properCycle_component_evaluation_single]
  norm_num

/-- Evaluation respects addition of actual rational cycles.
Source: Fulton, Intersection Theory, section 1.5.
HC no distance; AV milestone no distance. -/
theorem properCycle_component_evaluation_add
    {X : Scheme.{0}} [CompactSpace X] {W : Type*} [AddCommGroup W] [Module ℚ W]
    (C : X → W) (γ δ : AlgebraicCycle X ℚ) :
    properCycle_component_evaluation C (γ + δ) =
      properCycle_component_evaluation C γ + properCycle_component_evaluation C δ := by
  unfold properCycle_component_evaluation
  simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, add_smul]
  exact finsum_add_distrib (evaluation_support_finite C γ) (evaluation_support_finite C δ)

example {X : Scheme.{0}} [CompactSpace X] (ξ : X) :
    properCycle_component_evaluation (fun _ : X => (3 : ℚ)) (properPrime ξ + properPrime ξ) = 6 := by
  classical
  rw [properCycle_component_evaluation_add]
  simp only [properPrime, properCycle_component_evaluation_single, one_smul]
  norm_num

/-- Actual coefficient scaling becomes scalar multiplication of the component sum.
Source: Fulton, Intersection Theory, section 19.1.
HC no distance; AV milestone no distance. -/
theorem properCycle_component_evaluation_scale
    {X : Scheme.{0}} {W : Type*} [AddCommGroup W] [Module ℚ W]
    (C : X → W) (γ : AlgebraicCycle X ℚ) (q : ℚ) :
    properCycle_component_evaluation C (γ.mapRange (q * ·) (mul_zero _)) =
      q • properCycle_component_evaluation C γ := by
  unfold properCycle_component_evaluation
  simp only [Function.locallyFinsuppWithin.mapRange_apply, mul_smul, smul_finsum]

example {X : Scheme.{0}} (ξ : X) :
    properCycle_component_evaluation (fun _ : X => (3 : ℚ))
      ((properPrime ξ).mapRange ((-2 : ℚ) * ·) (mul_zero _)) = -6 := by
  classical
  rw [properCycle_component_evaluation_scale]
  simp only [properPrime, properCycle_component_evaluation_single, one_smul]
  norm_num

end HodgeLean.Foundations.QuotientDuality
