import Mathlib.RingTheory.Localization.Ideal

/-! # Localization of a kernel detected in an injective target -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- In a commuting localization square, an injective target map detects the localized kernel exactly.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3. -/
theorem s2e_localized_kernel_of_injective_target
    {R S A T : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing T]
    [Algebra R A] (M : Submonoid R) [IsLocalization M A]
    (φ : R →+* S) (ψ : S →+* T) (hψ : Function.Injective ψ)
    (α : A →+* T) (h : α.comp (algebraMap R A) = ψ.comp φ) :
    Ideal.map (algebraMap R A) (RingHom.ker φ) = RingHom.ker α := by
  have hcomm (r : R) : α (algebraMap R A r) = ψ (φ r) :=
    congrArg (fun f : R →+* T => f r) h
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change α (algebraMap R A r) = 0
    rw [hcomm r, show φ r = 0 from hr, map_zero]
  · intro r hr
    change α r = 0 at hr
    obtain ⟨a, t, ha⟩ := IsLocalization.exists_mk'_eq M r
    have he : algebraMap R A a = r * algebraMap R A t := by
      rw [← ha, IsLocalization.mk'_spec]
    have hz : φ a = 0 := hψ (by
      rw [← hcomm a, he, map_mul, hr, zero_mul, map_zero])
    rw [← ha]
    apply (IsLocalization.mk'_mem_iff (M := M) (S := A)).mpr
    exact Ideal.mem_map_of_mem (algebraMap R A) hz

end HodgeLean.Foundations.Program
