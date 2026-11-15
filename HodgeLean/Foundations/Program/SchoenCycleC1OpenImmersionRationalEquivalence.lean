import HodgeLean.Foundations.Program.SchoenCycleC1GenericLocalFieldSquare
import HodgeLean.Foundations.Program.SchoenGenericPointMorphisms

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- An actual open immersion identifies the original function fields by its
generic stalk map, retaining every original local stalk square. -/
theorem s2e_c1_open_immersion_rational_equivalence
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsOpenImmersion f] :
    ∃ E : Y.functionField ≃+* X.functionField,
      ∀ (p : X) (r : Y.presheaf.stalk (f p)),
        E (algebraMap (Y.presheaf.stalk (f p)) Y.functionField r) =
          algebraMap (X.presheaf.stalk p) X.functionField ((f.stalkMap p).hom r) := by
  have hg := genericPoint_eq_of_isOpenImmersion f
  let u : Y.functionField ⟶ X.functionField :=
    eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫ f.stalkMap (genericPoint X)
  let E := (asIso u).commRingCatIsoToRingEquiv
  refine ⟨E, ?_⟩
  intro p r
  exact s2e_c1_generic_stalk_map_local_square f hg p r

end HodgeLean.Foundations.Program
