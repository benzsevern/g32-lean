import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates

/-! # Scheme properties of the native analytic coordinate maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The scheme coordinate morphism underlying the native analytic chart is étale.
Source: Hartshorne, Algebraic Geometry, II.8; HodgeConjecture,
AlgebraicGeometry.LocalEtaleCoordinates.coordinateRingHomOnOpen_etale. -/
theorem s2e_native_coordinate_map_etale
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x : X.left) (D : LocalEtaleCoordinates X d x) : Etale D.toAffineSpace := by
  letI : IsAffine D.neighborhood.toScheme := D.isAffine
  letI : Etale (Spec.map (CommRingCat.ofHom D.coordinateRingHomOnOpen)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact D.coordinateRingHomOnOpen_etale
  dsimp only [LocalEtaleCoordinates.toAffineSpace]
  infer_instance

end HodgeLean.Foundations.Program
