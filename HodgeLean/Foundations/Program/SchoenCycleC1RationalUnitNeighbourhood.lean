import HodgeLean.Foundations.Program.SchoenCycleC1AffineUnitGerm
import Mathlib.AlgebraicGeometry.FunctionField

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A specified rational stalk unit extends to an actual affine unit on
an arbitrarily small neighbourhood with the same rational value. -/
theorem s2e_c1_rational_unit_neighbourhood
    (X : Scheme) [IsIntegral X] (p : X) (U : X.Opens) (hp : p ∈ U)
    (t : X.functionField) (u : (X.presheaf.stalk p)ˣ)
    (hu : algebraMap (X.presheaf.stalk p) X.functionField (u : _) = t) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : V ≤ U) (hV : p ∈ V)
      (v : Γ(X, V)ˣ),
      letI : Nonempty V := ⟨⟨p, hV⟩⟩
      X.germToFunctionField V (v : Γ(X, V)) = t := by
  obtain ⟨V, hV, hVU, hpV, v, hv⟩ := s2e_c1_affine_unit_germ_representative X p U hp u
  refine ⟨V, hV, hVU, hpV, v, ?_⟩
  letI : Nonempty V := ⟨⟨p, hpV⟩⟩
  rw [← hv, X.algebraMap_germ_eq_germToFunctionField] at hu
  exact hu

end HodgeLean.Foundations.Program
