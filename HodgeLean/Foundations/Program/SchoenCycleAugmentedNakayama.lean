import HodgeLean.Foundations.Program.SchoenCycleAugmentationFibreBasis
import Mathlib.RingTheory.LocalRing.Module

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Vanishing of the scalar augmentation fibre forces a finite module over the actual local algebra to vanish.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 2.8. -/
theorem s2e_augmented_nakayama
    (k R M : Type*) [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite R M]
    (ε : R →ₐ[k] k) :
    letI : Algebra R k := ε.toAlgebra
    Subsingleton (TensorProduct R k M) → Subsingleton M := by
  letI : Algebra R k := ε.toAlgebra
  intro h
  letI := h
  let b : Module.Basis Empty k (TensorProduct R k M) := .empty _
  obtain ⟨B, _⟩ := s2e_augmentation_fibre_basis k R M Empty ε
    (fun e => nomatch e) b (fun e => nomatch e)
  letI : Subsingleton (TensorProduct R (IsLocalRing.ResidueField R) M) :=
    B.repr.injective.subsingleton
  exact (IsLocalRing.subsingleton_tensorProduct (R := R) (M := M)).mp inferInstance

#print axioms s2e_augmented_nakayama
end HodgeLean.Foundations.Program
