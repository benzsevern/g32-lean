import HodgeLean.Foundations.Program.SchoenCycleU1Diagonal
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite unramified maps separated by complex points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- A finite formally unramified complex morphism that separates complex points
is a scheme immersion with proper image.
Source: Mathlib, `FormallyUnramified.isOpenImmersion_diagonal`,
`isIso_iff_isOpenImmersion_and_surjective`, `IsClosedImmersion.iff_isFinite_and_mono`. -/
theorem s2e_u1_finite_unramified_point_separation_immersion
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [FormallyUnramified f.left]
    (hinj : Function.Injective (Point.map f)) : IsClosedImmersion f.left := by
  letI := s2e_u1_finite_diagonal_surjective X Y f hinj
  letI : IsIso (pullback.diagonal f.left) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  letI : Mono f.left := (pullback.isIso_diagonal_iff f.left).mp inferInstance
  exact (IsClosedImmersion.iff_isFinite_and_mono f.left).mpr ⟨inferInstance, inferInstance⟩

end HodgeLean.Foundations.Program
