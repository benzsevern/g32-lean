import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Cancellation of actual ideal pullback along a scheme isomorphism -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Pulling actual ideal sheaves back along a scheme isomorphism detects their equality. -/
theorem residual_ideal_comap_iso_injective {X Y : Scheme} (e : X ≅ Y) :
    Function.Injective (fun I : Y.IdealSheafData => I.comap e.hom) := by
  intro I J h
  have h' := congrArg (fun K : X.IdealSheafData => K.comap e.inv) h
  simpa only [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id,
    Scheme.IdealSheafData.comap_id] using h'

#print axioms residual_ideal_comap_iso_injective
end HodgeLean.Foundations.Program.G32Native
