import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Actual affine neighborhoods inside two original ambient opens -/
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- An original point in two actual ambient opens has an actual affine
neighborhood contained in both original opens. -/
theorem exists_affine_open_intersection (W : Scheme.{0}) (U V : W.Opens) (p : W)
    (hpU : p ∈ U) (hpV : p ∈ V) :
    ∃ T : W.Opens, IsAffineOpen T ∧ p ∈ T ∧ T ≤ U ∧ T ≤ V := by
  obtain ⟨_, ⟨T, hT, rfl⟩, hpT, hTU⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (show p ∈ (U : Set W) ∩ V from ⟨hpU, hpV⟩)
      (U.2.inter V.2)
  exact ⟨T, hT, hpT, fun q hq => (hTU hq).1, fun q hq => (hTU hq).2⟩

#print axioms exists_affine_open_intersection
end HodgeLean.Foundations.Program.G32Native
