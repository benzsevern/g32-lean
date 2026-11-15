import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Restricting an actual pairing to a specified split normal complement -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native

/-- A surjective pairing annihilating the specified tangent image remains
surjective on the kernel of the specified tangent retraction. -/
theorem splitKernelPairing_surjective
    {K E T N : Type*} [Field K]
    [AddCommGroup E] [Module K E] [AddCommGroup T] [Module K T]
    [AddCommGroup N] [Module K N]
    (A : E →ₗ[K] N) (t : T →ₗ[K] E) (p : E →ₗ[K] T)
    (hpt : p.comp t = LinearMap.id) (hat : A.comp t = 0)
    (hA : Function.Surjective A) :
    Function.Surjective (A.comp p.ker.subtype) := by
  intro n
  obtain ⟨v, hv⟩ := hA n
  have ht : p (t (p v)) = p v := DFunLike.congr_fun hpt (p v)
  have ha : A (t (p v)) = 0 := DFunLike.congr_fun hat (p v)
  refine ⟨⟨v - t (p v), ?_⟩, ?_⟩
  · change p (v - t (p v)) = 0
    rw [map_sub, ht, sub_self]
  · change A (v - t (p v)) = n
    rw [map_sub, ha, sub_zero]
    exact hv

/-- A surjective pairing of the expected rank gives the actual inverse
identification with the specified split normal complement. -/
def splitKernelPairingEquiv
    {K E T N : Type*} [Field K]
    [AddCommGroup E] [Module K E] [AddCommGroup T] [Module K T]
    [AddCommGroup N] [Module K N] [FiniteDimensional K E] [FiniteDimensional K N]
    (A : E →ₗ[K] N) (t : T →ₗ[K] E) (p : E →ₗ[K] T)
    (hpt : p.comp t = LinearMap.id) (hat : A.comp t = 0)
    (hA : Function.Surjective A) (hrank : Module.finrank K p.ker = Module.finrank K N) :
    N ≃ₗ[K] p.ker := by
  have hs := splitKernelPairing_surjective A t p hpt hat hA
  exact (LinearEquiv.ofBijective (A.comp p.ker.subtype)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr hs, hs⟩).symm

/-- The specified normal representative retains its original pairing value. -/
theorem splitKernelPairingEquiv_pairing
    {K E T N : Type*} [Field K]
    [AddCommGroup E] [Module K E] [AddCommGroup T] [Module K T]
    [AddCommGroup N] [Module K N] [FiniteDimensional K E] [FiniteDimensional K N]
    (A : E →ₗ[K] N) (t : T →ₗ[K] E) (p : E →ₗ[K] T)
    (hpt : p.comp t = LinearMap.id) (hat : A.comp t = 0)
    (hA : Function.Surjective A) (hrank : Module.finrank K p.ker = Module.finrank K N)
    (n : N) : A (splitKernelPairingEquiv A t p hpt hat hA hrank n).val = n := by
  exact (splitKernelPairingEquiv A t p hpt hat hA hrank).symm_apply_apply n

#print axioms splitKernelPairingEquiv
#print axioms splitKernelPairingEquiv_pairing
#print axioms splitKernelPairing_surjective
end HodgeLean.Foundations.Program.G32Native
