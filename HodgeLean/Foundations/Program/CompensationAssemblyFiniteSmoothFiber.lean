import HodgeLean.Foundations.Program.CompensationAssemblyFiniteSmoothEtale
import Mathlib.RingTheory.TotallySplit

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem cq_finite_smooth_complex_fiber_degree (R B : Type)
    [CommRing R] [IsDomain R] [CharZero R] [CommRing B] [IsDomain B]
    [Algebra R B] [Algebra R ℂ] [Module.Finite R B] [Algebra.Smooth R B]
    (hinj : Function.Injective (algebraMap R B)) :
    a1p_degree (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (⟨⊥, inferInstance⟩ : Spec (CommRingCat.of B)) =
      Nat.card (PrimeSpectrum (ℂ ⊗[R] B)) := by
  letI : Algebra.Etale R B := cq_finite_smooth_domain_etale R B hinj
  exact cq_finiteEtale_complex_fiber_degree R B hinj

theorem cq_finite_smooth_complex_points_degree (R B : Type)
    [CommRing R] [IsDomain R] [CharZero R] [CommRing B] [IsDomain B]
    [Algebra R B] [Algebra R ℂ] [Module.Finite R B] [Algebra.Smooth R B]
    (hinj : Function.Injective (algebraMap R B)) :
    a1p_degree (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (⟨⊥, inferInstance⟩ : Spec (CommRingCat.of B)) =
      Nat.card (B →ₐ[R] ℂ) := by
  letI : Algebra.Etale R B := cq_finite_smooth_domain_etale R B hinj
  rw [cq_finite_smooth_complex_fiber_degree R B hinj]
  exact (Nat.card_congr ((Algebra.TensorProduct.liftEquivRight R ℂ B ℂ).trans
    (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum ℂ (ℂ ⊗[R] B)))).symm

end HodgeLean.Foundations.Program
