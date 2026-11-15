import HodgeLean.Adapters.NormalConeB4aGysinFinitePointProper
import HodgeLean.Adapters.NormalConeB4aGysinFiniteLocalBase

noncomputable section
namespace HodgeLean.Adapters

/-- A local fibre of a finite complex algebra has only one complex
evaluation extending a fixed evaluation of its base. -/
theorem a3b4a_gysin_finite_local_fibre_evaluation_unique
    {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra B T] [IsScalarTower ℂ B T] [Module.Finite B T]
    (p : Ideal B) [p.IsPrime] [IsLocalRing (p.Fiber T)]
    (u : B →ₐ[ℂ] ℂ) (hu : RingHom.ker u = p)
    (w w' : T →ₐ[ℂ] ℂ)
    (hw : w.comp (IsScalarTower.toAlgHom ℂ B T) = u)
    (hw' : w'.comp (IsScalarTower.toAlgHom ℂ B T) = u) : w = w' := by
  letI : (RingHom.ker w).IsPrime := RingHom.ker_isPrime w
  letI : (RingHom.ker w').IsPrime := RingHom.ker_isPrime w'
  have hover (v : T →ₐ[ℂ] ℂ) (hv : v.comp (IsScalarTower.toAlgHom ℂ B T) = u) :
      (RingHom.ker v).LiesOver p := by
    constructor
    change p = (RingHom.ker v.toRingHom).comap (algebraMap B T)
    rw [RingHom.comap_ker]
    exact hu.symm.trans
      (congrArg (fun f : B →ₐ[ℂ] ℂ => RingHom.ker f.toRingHom) hv).symm
  letI := hover w hw
  letI := hover w' hw'
  have hk := a3b4a_gysin_unique_prime_over_local_fibre p (RingHom.ker w) (RingHom.ker w')
  apply AlgHom.ext
  intro t
  have ht : w (t - algebraMap ℂ T (w' t)) = 0 := by
    change t - algebraMap ℂ T (w' t) ∈ RingHom.ker w
    rw [hk]
    change w' (t - algebraMap ℂ T (w' t)) = 0
    simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  rw [map_sub, w.commutes, Algebra.algebraMap_self_apply] at ht
  exact sub_eq_zero.mp ht

end HodgeLean.Adapters
