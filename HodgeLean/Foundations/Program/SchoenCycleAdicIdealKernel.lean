import HodgeLean.Foundations.Program.SchoenCycleAdicEqualizer
import HodgeLean.Foundations.Program.SchoenCycleAdicScalarExtension
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Ideal.Maps

/-! # Ideal images and kernels under adic extension -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open TensorProduct
universe u
namespace HodgeLean.Foundations.Program

/-- The image of the adic module of a finite ideal is its extension to the
adic ring.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
Proposition 10.13; Mathlib, AdicCompletion.ofTensorProduct_surjective_of_finite. -/
theorem s2e_adic_ideal_subtype_range
    {R : Type*} [CommRing R] (I J : Ideal R) [Module.Finite R J] :
    LinearMap.range (AdicCompletion.map I J.subtype) =
      J.map (algebraMap R (AdicCompletion I R)) := by
  apply le_antisymm
  · rintro z ⟨y, rfl⟩
    obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I J y
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r j =>
      rw [AdicCompletion.ofTensorProduct_tmul, map_smul, AdicCompletion.map_of]
      exact (J.map (algebraMap R (AdicCompletion I R))).smul_mem r
        (Ideal.mem_map_of_mem _ j.property)
    | add x y hx hy =>
      simpa only [map_add] using (J.map (algebraMap R (AdicCompletion I R))).add_mem hx hy
  · apply Ideal.map_le_iff_le_comap.mpr
    intro j hj
    exact ⟨AdicCompletion.of I J ⟨j, hj⟩, AdicCompletion.map_of I J.subtype ⟨j, hj⟩⟩

#print axioms s2e_adic_ideal_subtype_range
/-- Adic extension of the kernel of a linear map from a Noetherian ring to
a finite module equals the kernel of the induced adic map.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
Propositions 10.12–10.13. -/
theorem s2e_adic_linear_kernel
    {R M : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (f : R →ₗ[R] M) :
    LinearMap.ker (AdicCompletion.map I f) =
      Ideal.map (algebraMap R (AdicCompletion I R)) (LinearMap.ker f) := by
  have he : Function.Exact (LinearMap.ker f).subtype f := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact x.property
  have h := s2e_adic_map_exact_of_injective I (LinearMap.ker f).subtype f
    (Submodule.injective_subtype _) he
  rw [← s2e_adic_ideal_subtype_range I (LinearMap.ker f)]
  ext z
  exact h z

#print axioms s2e_adic_linear_kernel
/-- For a finite algebra, the canonical adic ring map has the extended
algebra-map kernel.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
Propositions 10.12–10.13. -/
theorem s2e_adic_algebraMap_kernel
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R]
    [Algebra R S] [Module.Finite R S] (I : Ideal R) :
    RingHom.ker (s2e_adic_ring_map I (I.map (algebraMap R S))
      (algebraMap R S) le_rfl) =
      (RingHom.ker (algebraMap R S)).map (algebraMap R (AdicCompletion I R)) := by
  have hk := s2e_adic_linear_kernel I (Algebra.linearMap R S)
  ext z
  change s2e_adic_ring_map I (I.map (algebraMap R S))
    (algebraMap R S) le_rfl z = 0 ↔ _
  rw [← s2e_adic_scalar_extension_algebraMap]
  rw [map_eq_zero_iff _ (s2e_adic_scalar_extension_equiv (S := S) I).injective]
  change z ∈ LinearMap.ker (AdicCompletion.map I (Algebra.linearMap R S)) ↔ _
  rw [hk]
  rfl

#print axioms s2e_adic_algebraMap_kernel
end HodgeLean.Foundations.Program
