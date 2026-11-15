import HodgeLean.Foundations.Program.SchoenCycleGeometryChecks
import HodgeLean.Foundations.Program.TorusAlgebraizationB55Graph

/-! # Pointwise normalized algebraic descent through the retained quotient -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- An algebraic invariant point trace descends uniquely with its point formula retained. -/
theorem residual_quotient_trace_descends
    {Z B T : Over (Spec ↧ℂ)} (n : ℕ)
    [IsReduced (g3_power Z n).left] [LocallyOfFiniteType (g3_power Z n).hom]
    [IsSeparated T.hom] [LocallyOfFiniteType T.hom]
    (γ : g3_power Z n ⟶ B)
    (hquot : ∀ (U : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ U),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ U, γ ≫ u = v)
    (f : ComplexPoint (g3_power Z n) → ComplexPoint T)
    (hf : ∀ σ u, f (Point.map (s2_permute Z n σ) u) = f u)
    (v : g3_power Z n ⟶ T) (hv : Point.map v = f) :
    ∃! a : B ⟶ T, ∀ u, Point.map a (Point.map γ u) = f u := by
  have hinv : ∀ σ, s2_permute Z n σ ≫ v = v := by
    intro σ
    apply b55_hom_ext
    funext u
    exact (Point.map_comp_apply _ _ u).trans
      ((congrFun hv _).trans ((hf σ u).trans (congrFun hv u).symm))
  obtain ⟨a, ha, hu⟩ := hquot T v hinv
  refine ⟨a, fun u => ?_, fun b hb => ?_⟩
  · exact (Point.map_comp_apply γ a u).symm.trans
      ((congrArg (fun w => Point.map w u) ha).trans (congrFun hv u))
  · apply hu b
    apply b55_hom_ext
    funext u
    exact (Point.map_comp_apply γ b u).trans ((hb u).trans (congrFun hv u).symm)

#print axioms residual_quotient_trace_descends
end HodgeLean.Foundations.Program.G32Native
