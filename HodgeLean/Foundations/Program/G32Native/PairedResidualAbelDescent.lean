import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelAlgebraization
import HodgeLean.Foundations.Program.TorusAlgebraizationB55Graph
import HodgeLean.Foundations.Program.SchoenCycleStep1

/-! # Abel sums on the retained symmetric quotient -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open scoped BigOperators Topology Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
  [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)

/-- The ordered algebraic Abel map retains literal permutation invariance. -/
theorem residual_ordered_abel_invariant (n : ℕ) (p : ComplexPoint Z)
    (v : g3_power Z n ⟶ model (C := ComplexPoint Z) hOne)
    (hv : Point.map v = fun u => theta (C := ComplexPoint Z) hOne
      (∑ i, analyticAbel (C := ComplexPoint Z) hOne p (Point.map (g3_proj Z n i) u))) :
    ∀ σ, s2_permute Z n σ ≫ v = v := by
  intro σ
  apply b55_hom_ext
  funext u
  rw [Point.map_comp_apply, hv]
  apply congrArg (theta (C := ComplexPoint Z) hOne)
  calc
    (∑ i, analyticAbel (C := ComplexPoint Z) hOne p (Point.map (g3_proj Z n i)
        (Point.map (s2_permute Z n σ) u))) =
      ∑ i, analyticAbel (C := ComplexPoint Z) hOne p (Point.map (g3_proj Z n (σ.symm i)) u) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        change (u ≫ s2_permute Z n σ) ≫ g3_proj Z n i = u ≫ g3_proj Z n (σ.symm i)
        rw [Category.assoc]
        exact congrArg (fun f => u ≫ f)
          (s2_check_lift_proj n (fun j => g3_proj Z n (σ.symm j)) i)
    _ = ∑ i, analyticAbel (C := ComplexPoint Z) hOne p (Point.map (g3_proj Z n i) u) :=
      σ.symm.sum_comp (fun i : Fin n => analyticAbel (C := ComplexPoint Z) hOne p (Point.map (g3_proj Z n i) u))

#print axioms residual_ordered_abel_invariant
/-- The supplied categorical symmetric quotient carries the actual algebraic Abel sum. -/
theorem residual_symmetric_abel_algebraization (n : ℕ) (p : ComplexPoint Z)
    (B : Over (Spec ↧ℂ)) (γ : g3_power Z n ⟶ B)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v) :
    ∃ a : B ⟶ model (C := ComplexPoint Z) hOne,
      Point.map (γ ≫ a) = fun u => theta (C := ComplexPoint Z) hOne
        (∑ i, analyticAbel (C := ComplexPoint Z) hOne p (Point.map (g3_proj Z n i) u)) := by
  obtain ⟨v, hv⟩ := residual_ordered_abel_algebraization Z n p
  have hvinv : ∀ σ, s2_permute Z n σ ≫ v = v :=
    residual_ordered_abel_invariant Z n p v hv
  obtain ⟨a, ha, _⟩ := hquot (model (C := ComplexPoint Z) hOne) v hvinv
  have hh : Point.map (γ ≫ a) = Point.map v :=
    congrArg (fun w : g3_power Z n ⟶ model (C := ComplexPoint Z) hOne => Point.map w) ha
  exact ⟨a, hh.trans hv⟩

#print axioms residual_symmetric_abel_algebraization
end HodgeLean.Foundations.Program.G32Native
