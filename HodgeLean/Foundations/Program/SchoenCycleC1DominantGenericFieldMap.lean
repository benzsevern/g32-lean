import HodgeLean.Foundations.Program.SchoenCycleC1DominantGenericPoint
import HodgeLean.Foundations.Program.SchoenCycleC1GenericLocalFieldSquare

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The actual dominant projection constructs an injective rational pullback
retaining every original local stalk pullback under its canonical embedding. -/
theorem s2e_c1_dominant_generic_field_map
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    ∃ φ : Y.functionField →+* X.functionField, Function.Injective φ ∧
      ∀ (p : X) (r : Y.presheaf.stalk (f p)),
        φ (algebraMap (Y.presheaf.stalk (f p)) Y.functionField r) =
          algebraMap (X.presheaf.stalk p) X.functionField ((f.stalkMap p).hom r) := by
  have hg := s2e_c1_dominant_generic_point f
  let φ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫ f.stalkMap (genericPoint X)).hom
  exact ⟨φ, φ.injective, s2e_c1_generic_stalk_map_local_square f hg⟩

end HodgeLean.Foundations.Program
