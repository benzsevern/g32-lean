import HodgeLean.Foundations.Program.G32Native.CanonicalAbelAlgebraization
import HodgeLean.Foundations.Program.G32Native.CanonicalQuotientPointDescent

/-! # The algebraic symmetric Abel map on the specified quotient -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
namespace HodgeLean.Foundations.Program.G32Native

/-- The retained theta comparison of the symmetric Abel sum is algebraic. -/
theorem canonical_symmetric_abel_algebraic (G : CanonicalAbelGeometry)
    (p : ComplexPoint G.Z) :
    ∃ vB : G.B ⟶ model (C := ComplexPoint G.Z) (Module.finrank_fin_fun (n := 1) ℂ),
      Point.map vB = fun b => theta (Module.finrank_fin_fun (n := 1) ℂ)
        (canonicalSymmetricAbel G p b) := by
  obtain ⟨v, hv⟩ := canonical_ordered_abel_algebraization G p
  exact canonical_quotient_descend_pointMap G _ _ v hv

#print axioms canonical_symmetric_abel_algebraic
end HodgeLean.Foundations.Program.G32Native
