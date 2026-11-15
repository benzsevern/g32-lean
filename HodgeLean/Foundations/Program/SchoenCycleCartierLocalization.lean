import HodgeLean.Foundations.Program.SchoenCycleCartierAlgebra
import Mathlib.RingTheory.Localization.Defs

/-! # Refining affine Cartier charts
Localizing a free ideal preserves its rank-one ideal-module description.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A regular principal parameter gives a free rank-one ideal module. -/
theorem s2e_regular_principal_ideal_free
    {R : Type*} [CommRing R] (z : R)
    (hregular : Function.Injective (fun a : R => a * z)) :
    Nonempty ((Ideal.span {z}) ≃ₗ[R] R) := by
  have hrange : (LinearMap.mulRight R z).range = (Ideal.span {z} : Submodule R R) := by
    ext x
    change (∃ a : R, a * z = x) ↔ x ∈ Ideal.span {z}
    exact Ideal.mem_span_singleton'.symm
  exact ⟨((LinearEquiv.ofInjective (LinearMap.mulRight R z) hregular) ≪≫ₗ
    (LinearEquiv.ofEq _ _ hrange)).symm⟩

/-- Localization preserves an ideal-module equivalence with the ring. -/
theorem s2e_free_ideal_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I : Ideal R)
    (hfree : Nonempty (I ≃ₗ[R] R)) :
    Nonempty ((Ideal.map (algebraMap R S) I) ≃ₗ[S] S) := by
  obtain ⟨e⟩ := hfree
  obtain ⟨z, hz, hregular⟩ := s2e_free_ideal_regular_generator I e
  rw [hz, Ideal.map_span, Set.image_singleton]
  apply s2e_regular_principal_ideal_free
  have hzreg : IsRegular z := isRightRegular_iff_isRegular.mp hregular
  have hzmem : z ∈ nonZeroDivisors R := isRegular_iff_mem_nonZeroDivisors.mp hzreg
  have hzmem' : algebraMap R S z ∈ nonZeroDivisors S :=
    IsLocalization.nonZeroDivisors_le_comap M S hzmem
  exact isRightRegular_iff_isRegular.mpr (isRegular_iff_mem_nonZeroDivisors.mpr hzmem')

end HodgeLean.Foundations.Program
