import HodgeLean.Foundations.IntegralHomology.StageTwo.IntegralDual
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.PID

/-! Retractions obtained from projective images and quotients.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

theorem kernel_retraction {R M N : Type} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) [Module.Projective R (LinearMap.range f)] :
    ∃ p : M →ₗ[R] LinearMap.ker f, ∀ z : LinearMap.ker f, p z = z := by
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let p : M →ₗ[R] LinearMap.ker f :=
    (LinearMap.id - s.comp f.rangeRestrict).codRestrict (LinearMap.ker f) (by
      intro x
      change f (x - s (f.rangeRestrict x)) = 0
      have hx := congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict x))
      change f (s (f.rangeRestrict x)) = f x at hx
      rw [map_sub, hx, sub_self])
  refine ⟨p, ?_⟩
  intro z
  apply Subtype.ext
  change z.val - s (f.rangeRestrict z.val) = z.val
  have hz : f.rangeRestrict z.val = 0 := Subtype.ext z.property
  rw [hz, map_zero, sub_zero]

theorem submodule_retraction {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] (N : Submodule R M)
    [Module.Projective R (M ⧸ N)] :
    ∃ r : M →ₗ[R] N, ∀ z : N, r z = z := by
  obtain ⟨s, hs⟩ := N.mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective N))
  let r : M →ₗ[R] N := (LinearMap.id - s.comp N.mkQ).codRestrict N (by
    intro x
    apply (Submodule.Quotient.mk_eq_zero N).mp
    change N.mkQ (x - s (N.mkQ x)) = 0
    rw [map_sub, show N.mkQ (s (N.mkQ x)) = N.mkQ x from
      LinearMap.congr_fun hs (N.mkQ x), sub_self])
  refine ⟨r, ?_⟩
  intro z
  apply Subtype.ext
  change z.val - s (N.mkQ z.val) = z.val
  rw [show N.mkQ z.val = 0 from (Submodule.Quotient.mk_eq_zero N).mpr z.property,
    map_zero, sub_zero]
end HodgeLean.Foundations.IntegralHomology.StageTwo
