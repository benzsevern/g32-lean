import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Algebra.Equiv

/-! # Fixed residue characters of local algebra automorphisms -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every scalar-preserving automorphism of a local algebra preserves its
ground-field residue augmentation. -/
theorem s2e_c1_local_residue_fixed_by_algebraEquiv
    {k R : Type*} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
    (φ : R →ₐ[k] k) (τ : R ≃ₐ[k] R) (r : R) : φ (τ r) = φ r := by
  haveI : IsLocalHom τ.toRingHom := ⟨fun a ha => by
    have h := ha.map τ.symm.toRingHom
    change IsUnit (τ.symm (τ a)) at h
    simpa only [AlgEquiv.symm_apply_apply] using h⟩
  have hs : Function.Surjective φ := fun c =>
    ⟨algebraMap k R c, by simpa only [Algebra.algebraMap_self_apply] using φ.commutes c⟩
  have hk : RingHom.ker φ = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ hs)
  have hr : r - algebraMap k R (φ r) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hk]
    change φ (r - algebraMap k R (φ r)) = 0
    simp only [map_sub, φ.commutes, Algebra.algebraMap_self_apply, sub_self]
  have ht : τ (r - algebraMap k R (φ r)) ∈ IsLocalRing.maximalIdeal R :=
    IsLocalRing.map_maximalIdeal_le τ.toRingHom (Ideal.mem_map_of_mem τ.toRingHom hr)
  rw [← hk] at ht
  change φ (τ (r - algebraMap k R (φ r))) = 0 at ht
  simpa only [map_sub, τ.commutes, φ.commutes, Algebra.algebraMap_self_apply, sub_eq_zero] using ht

end HodgeLean.Foundations.Program
