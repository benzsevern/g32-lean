import HodgeLean.Foundations.Program.TorusAlgebraizationB54Normalize
import HodgeLean.Foundations.Program.TorusAlgebraizationB54NormalDescent

noncomputable section
open HomogeneousLocalization
namespace HodgeLean.Foundations.Program

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G] {r : A} (hr : r ∈ G 1)

def b54_awayRetraction : Localization.Away r →+* Away G r :=
  Localization.awayLift (b54_awayNormalize G hr) r
    (by rw [b54_awayNormalize_self]; exact isUnit_one)

theorem b54_awayRetraction_val (x : Away G r) :
    b54_awayRetraction G hr (HomogeneousLocalization.val x) = x := by
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective G hr x
  rw [Away.val_mk]
  unfold b54_awayRetraction
  rw [Localization.awayLift_mk (b54_awayNormalize G hr) r a 1
    (by rw [b54_awayNormalize_self, one_mul])]
  rw [one_pow, mul_one]
  exact b54_awayNormalize_homogeneous G hr k a (by simpa using ha)

include hr in
theorem b54_away_integrallyClosed [IsDomain A] [IsIntegrallyClosed A] (hne : r ≠ 0) :
    IsIntegrallyClosed (Away G r) := by
  have hs : Submonoid.powers r ≤ nonZeroDivisors A :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hne)
  letI := IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away r) hs
  letI := isIntegrallyClosed_of_isLocalization (Localization.Away r) (Submonoid.powers r) hs
  letI : IsDomain (Away G r) :=
    Function.Injective.isDomain (algebraMap (Away G r) (Localization.Away r))
      (HomogeneousLocalization.val_injective (.powers r))
  exact b54_normal_of_ring_retraction (algebraMap (Away G r) (Localization.Away r))
    (b54_awayRetraction G hr) (b54_awayRetraction_val G hr)

theorem b54_away_isDomain [IsDomain A] (hne : r ≠ 0) : IsDomain (Away G r) := by
  have hs : Submonoid.powers r ≤ nonZeroDivisors A :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hne)
  letI := IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away r) hs
  exact Function.Injective.isDomain (algebraMap (Away G r) (Localization.Away r))
    (HomogeneousLocalization.val_injective (.powers r))

end HodgeLean.Foundations.Program
