import HodgeLean.Adapters.NormalConeB4aGysinFiniteFibreLift
import HodgeLean.Adapters.NormalConeB4aGysinEvaluationKernel

noncomputable section
namespace HodgeLean.Adapters

/-- A selected prime above a local finite fibre fixes the original source
projection of its complex model evaluation. -/
theorem a3b4a_gysin_exists_finite_model_source_evaluation
    {B S T : Type} [CommRing B] [CommRing S] [CommRing T]
    [Algebra ℂ B] [Algebra ℂ S] [Algebra ℂ T]
    [Algebra B T] [IsScalarTower ℂ B T] [Module.Finite B T]
    [Algebra S T] [IsScalarTower ℂ S T]
    (p : Ideal B) [p.IsPrime] [IsLocalRing (p.Fiber T)]
    (u : B →ₐ[ℂ] ℂ) (hu : RingHom.ker u = p)
    (w : S →ₐ[ℂ] ℂ) (r : Ideal T) [r.IsPrime] [r.LiesOver p]
    (hr : r.comap (algebraMap S T) = RingHom.ker w) :
    ∃ v : T →ₐ[ℂ] ℂ, v.comp (IsScalarTower.toAlgHom ℂ B T) = u ∧
      v.comp (IsScalarTower.toAlgHom ℂ S T) = w := by
  obtain ⟨v, hv⟩ := a3b4a_gysin_exists_finite_local_fibre_evaluation (T := T) p u hu
  letI : (RingHom.ker v).IsPrime := RingHom.ker_isPrime v
  letI : (RingHom.ker v).LiesOver p := by
    constructor
    change p = (RingHom.ker v.toRingHom).comap (algebraMap B T)
    rw [RingHom.comap_ker]
    exact hu.symm.trans
      (congrArg (fun f : B →ₐ[ℂ] ℂ => RingHom.ker f.toRingHom) hv).symm
  have hk := a3b4a_gysin_unique_prime_over_local_fibre p (RingHom.ker v) r
  refine ⟨v, hv, a3b4a_gysin_evaluation_eq_of_ker_eq _ _ ?_⟩
  change RingHom.ker (v.toRingHom.comp (algebraMap S T)) = RingHom.ker w
  rw [← RingHom.comap_ker]
  exact (congrArg (Ideal.comap (algebraMap S T)) hk).trans hr

end HodgeLean.Adapters
