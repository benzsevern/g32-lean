import HodgeLean.Foundations.Program.G32Native.PairedResidualOrderedAbel
import HodgeLean.Foundations.Program.G32Native.PairedResidualPointTrace
import HodgeLean.Foundations.Program.G32Native.PairedResidualQuotientTrace

/-! # The algebraic Abel trace on the supplied symmetric quotient -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter
open scoped BigOperators Topology Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- The supplied quotient has a unique algebraic Abel trace with the original ordered point formula.
Source: Serre, GAGA (1956), §3 Proposition 13; Forster, Lectures on Riemann Surfaces, §21. -/
theorem residual_symmetric_abel_algebraic
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (γ : g3_power Z n ⟶ B)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (p : ComplexPoint Z) :
    letI := AlgebraicGeometry.ComplexPoint.connectedSpace Z
    let h := Module.finrank_fin_fun (n := 1) ℂ
    ∃! a : B ⟶ model (C := ComplexPoint Z) h,
      ∀ u, Point.map a (Point.map γ u) = theta h
        (∑ i, analyticAbel h p (Point.map (g3_proj Z n i) u)) := by
  letI := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  let h := Module.finrank_fin_fun (n := 1) ℂ
  obtain ⟨v, hv⟩ := residual_ordered_abel_algebraic Z n p
  let J := model (C := ComplexPoint Z) h
  letI := b3_periodLattice_finite (C := ComplexPoint Z) h
  letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint Z)
  letI : IsProjective J.hom := (projectiveGroup (C := ComplexPoint Z) h).2.1
  exact residual_quotient_trace_descends (Z := Z) (B := B) (T := J) n γ hquot
    (fun u => theta h (∑ i, analyticAbel h p (Point.map (g3_proj Z n i) u)))
    (fun σ u => congrArg (theta h)
      (residual_ordered_point_trace_permute Z n (analyticAbel h p) σ u)) v hv

#print axioms residual_symmetric_abel_algebraic
end HodgeLean.Foundations.Program.G32Native
