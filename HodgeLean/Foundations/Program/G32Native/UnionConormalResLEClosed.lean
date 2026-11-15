import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Immersions restricted to an explicitly specified inverse image open -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Restricting an immersion to the full inverse image open retains its property. -/
lemma unionConormal_resLE_isClosedImmersion
    {Q W : Scheme.{0}} (i : Q ⟶ W) [IsClosedImmersion i]
    (U : W.Opens) (V : Q.Opens) (hle : V ≤ i ⁻¹ᵁ U) (he : V = i ⁻¹ᵁ U) :
    IsClosedImmersion (i.resLE U V hle) := by
  subst V
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

end HodgeLean.Foundations.Program.G32Native
