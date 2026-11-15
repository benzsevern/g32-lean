import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-! # Finite unramified maps with universally injective fibres -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A finite universally injective formally unramified map is an immersion with proper image.
Source: Mathlib, AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono and
AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal. -/
theorem s2e_finite_radicial_unramified_immersion
    {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] [UniversallyInjective f]
    [FormallyUnramified f] : IsClosedImmersion f := by
  letI : Surjective (pullback.diagonal f) :=
    (UniversallyInjective.iff_diagonal f).mp inferInstance
  letI : Epi (pullback.diagonal f).base := by
    rw [TopCat.epi_iff_surjective]
    exact Scheme.Hom.surjective _
  letI : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_epi_base _).mpr ⟨inferInstance, inferInstance⟩
  letI : Mono f := (pullback.isIso_diagonal_iff f).mp inferInstance
  exact (IsClosedImmersion.iff_isFinite_and_mono f).mpr ⟨inferInstance, inferInstance⟩

end HodgeLean.Foundations.Program
