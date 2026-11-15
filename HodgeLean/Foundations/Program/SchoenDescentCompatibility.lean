import HodgeLean.Foundations.Program.SchoenOpenRestrictionEpimorphisms

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Local descents along a surjective stalk injection agree on intersections. -/
theorem s2_localDescent_compatible {X Y T : Scheme.{0}} (q : X ⟶ Y) [Surjective q]
    (hq : ∀ x : X, Function.Injective (q.stalkMap x)) (f : X ⟶ T)
    (U V : Y.Opens) (dU : U.toScheme ⟶ T) (dV : V.toScheme ⟶ T)
    (hU : (q ∣_ U) ≫ dU = (q ⁻¹ᵁ U).ι ≫ f)
    (hV : (q ∣_ V) ≫ dV = (q ⁻¹ᵁ V).ι ≫ f) :
    Y.homOfLE (show U ⊓ V ≤ U from inf_le_left) ≫ dU =
      Y.homOfLE (show U ⊓ V ≤ V from inf_le_right) ≫ dV := by
  haveI := s2_morphismRestrict_epi q hq (U ⊓ V)
  apply (cancel_epi (q ∣_ (U ⊓ V))).mp
  rw [← Category.assoc, morphismRestrict_homOfLE q (U ⊓ V) U inf_le_left,
    Category.assoc, hU, ← Category.assoc, Scheme.homOfLE_ι]
  rw [← Category.assoc, morphismRestrict_homOfLE q (U ⊓ V) V inf_le_right,
    Category.assoc, hV, ← Category.assoc, Scheme.homOfLE_ι]

end HodgeLean.Foundations.Program
