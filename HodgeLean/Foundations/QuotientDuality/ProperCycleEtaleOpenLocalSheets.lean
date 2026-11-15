import HodgeLean.Foundations.QuotientDuality.ProperCycleTargetOpenLocalSheets
import HodgeLean.Foundations.QuotientDuality.ProperCycleRestrictedFibreEquiv

/-! # Actual local sheets of the original morphism on finite etale target opens -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The original complex-point map has actual local sheets over a target open where its actual restriction is finite etale.
Source: SGA 1, Expose XII, Proposition 3.1, analytic local inverses of etale morphisms.
HC no distance; AV milestone no distance. -/
lemma properCycle_local_sheets_over_finite_etale_open
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (U : Y.left.Opens) [IsFinite (f.left ∣_ U)] [Etale (f.left ∣_ U)] :
    IsLocalHomeomorphOn (Point.map f) ((Point.map f) ⁻¹' Point.overOpen U) := by
  let XU := openScheme X (f.left ⁻¹ᵁ U)
  let YU := openScheme Y U
  let g := s2e_c11_restricted_over_morphism X Y f U
  letI : LocallyOfFiniteType XU.hom :=
    inferInstanceAs (LocallyOfFiniteType ((f.left ⁻¹ᵁ U).ι ≫ X.hom))
  letI : LocallyOfFiniteType YU.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ Y.hom))
  letI : IsFinite g.left := inferInstanceAs (IsFinite (f.left ∣_ U))
  letI : Etale g.left := inferInstanceAs (Etale (f.left ∣_ U))
  have hg := s2e_c11_etale_local_homeomorph XU YU g
  have hr := s2e_c11_restricted_point_local_homeomorph X Y f U hg
  exact properCycle_local_sheets_of_open_target_restriction (Point.map f)
    (Point.continuousMap f).continuous (Point.overOpen U) (Point.isOpen_overOpen U) hr

end HodgeLean.Foundations.QuotientDuality
