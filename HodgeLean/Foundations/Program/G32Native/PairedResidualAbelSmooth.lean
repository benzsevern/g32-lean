import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelNativeRank
import Mathlib.AlgebraicGeometry.Noetherian
import HodgeLean.Foundations.Program.G32Native.PairedResidualNativeTorusRank
import HodgeLean.Foundations.Program.G32Native.PairedResidualNativeDerivative
import HodgeLean.Foundations.Program.G32Native.PairedResidualNativeDerivative

/-! # Scheme smoothness of the original algebraic Abel morphism -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open scoped TensorProduct BigOperators Topology Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
  [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)
/-- The original algebraic Abel morphism is smooth in high degree, retaining
its supplied symmetric quotient and specified theta realization.
Source: Forster, Lectures on Riemann Surfaces, §21; Schoen, Compositio
Mathematica 65 (1988), Lemma 2.6. -/
theorem residual_algebraic_abel_smooth
    (B : Over (Spec ↧ℂ)) [IsIntegral B.left] (n : ℕ)
    [SmoothOfRelativeDimension n B.hom]
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hpoint : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (a : B ⟶ model (C := ComplexPoint Z) hOne) (p : ComplexPoint Z)
    (hsum : ∀ u, (theta (C := ComplexPoint Z) hOne).symm (Point.map a (Point.map γ u)) =
      ∑ i, analyticAbel hOne p (Point.map (g3_proj Z n i) u))
    (hd : 2 * (Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2 < (n : ℤ))
    : Smooth a.left := by
  let J := model (C := ComplexPoint Z) hOne
  let m := TopologicalSpace.dim J.left
  letI : Smooth B.hom := SmoothOfRelativeDimension.smooth n B.hom
  letI : LocallyOfFiniteType (a.left ≫ J.hom) := by
    rw [Over.w a]
    infer_instance
  letI : LocallyOfFiniteType a.left := locallyOfFiniteType_of_comp a.left J.hom
  letI : LocallyOfFinitePresentation a.left := inferInstance
  apply residual_smooth_of_mfderiv_surjective B J n m a
  intro b
  exact residual_algebraic_abel_native_mfderiv_surjective Z B n γ hγ hpoint hquot
    a p hsum hd b

#print axioms residual_algebraic_abel_smooth
end HodgeLean.Foundations.Program.G32Native
