import HodgeLean.Foundations.AnalyticDivisorAlgebraic23
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothClosedLift

/-! # Algebraic divisor realization data

The output is a data structure, with the fields of the bh4 consumer.
No proposition abbreviates a proof obligation. HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic24
open Filter Set Topology
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic21
open HodgeLean.Foundations.AnalyticDivisorAlgebraic22
open scoped Manifold CategoryTheory.MonObj

open HodgeLean.Foundations.AnalyticDivisorAlgebraic23
/-- Effective algebraic component data with reduced analytic local equations.
Source: Serre, GAGA, Théorème 3; Griffiths--Harris, Chapter 1 §1 (divisors). -/
structure gaga24_Algebraization (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    (V : J → Set (Fin (dim X.left) → ℂ)) (f : J → (Fin (dim X.left) → ℂ) → ℂ) where
  n : ℕ
  x : Fin n → X.left
  distinct : Function.Injective x
  codim : ∀ i, Order.coheight (x i) = 1
  mult : Fin n → ℕ
  positive : ∀ i, 0 < mult i
  support : abelianExp X '' localDivisorSupport V f =
    ⋃ i, gaga23_componentSupport X (x i)
  local_equations : ∀ j p, p ∈ V j →
    ∃ (g : Fin n → (Fin (dim X.left) → ℂ) → ℂ)
      (hg : ∀ i, AnalyticAt ℂ (g i) p),
      (∀ i, Squarefree (⟨Filter.Germ.ofFun (g i), g i, hg i, rfl⟩ :
        AnalyticGermAt (dim X.left) p)) ∧
      (∀ i, ∀ᶠ z in 𝓝 p, g i z = 0 ↔ abelianExp X z ∈
        gaga23_componentSupport X (x i)) ∧
      AreAssociatedAt (f j) (fun z ↦ ∏ i, g i z ^ mult i) p

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] :
    gaga24_Algebraization X (fun _ : Unit ↦ univ) (fun _ _ ↦ 1) := by
  refine ⟨0, Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0,
    Fin.elim0, fun i ↦ i.elim0, ?_, ?_⟩
  · simp [localDivisorSupport]
  · intro j p hp
    refine ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, ?_⟩
    exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
      Eventually.of_forall fun z ↦ by simp⟩

end HodgeLean.Foundations.AnalyticDivisorAlgebraic24
