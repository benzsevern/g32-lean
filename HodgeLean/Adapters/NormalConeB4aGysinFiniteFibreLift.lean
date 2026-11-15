import HodgeLean.Adapters.NormalConeB4aGysinFinitePointTrapping
import HodgeLean.Adapters.NormalConeB4aGysinModelPoint

noncomputable section
namespace HodgeLean.Adapters

/-- A nontrivial local fibre of a finite complex algebra supplies the
complex evaluation above a rational base evaluation. -/
theorem a3b4a_gysin_exists_finite_local_fibre_evaluation
    {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra B T] [IsScalarTower ℂ B T] [Module.Finite B T]
    (p : Ideal B) [p.IsPrime] [IsLocalRing (p.Fiber T)]
    (u : B →ₐ[ℂ] ℂ) (hu : RingHom.ker u = p) :
    ∃ w : T →ₐ[ℂ] ℂ, w.comp (IsScalarTower.toAlgHom ℂ B T) = u := by
  obtain ⟨e, he⟩ := a3b4a_gysin_exists_rational_residue_equiv p u hu
  let F := p.Fiber T
  letI : Module.Finite ℂ p.ResidueField :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  letI : Module.Finite ℂ F := Module.Finite.trans p.ResidueField F
  let v : F →ₐ[ℂ] ℂ := (a3b4a_gysin_algHomEquivPrimeSpectrum ℂ F).symm
    ⟨IsLocalRing.maximalIdeal F, inferInstance⟩
  have hv (x : p.ResidueField) : v (algebraMap p.ResidueField F x) = e x := by
    have hx : x = algebraMap ℂ p.ResidueField (e x) := by
      apply e.injective
      rw [e.commutes, Algebra.algebraMap_self_apply]
    nth_rw 1 [hx]
    rw [← IsScalarTower.algebraMap_apply ℂ p.ResidueField F, v.commutes,
      Algebra.algebraMap_self_apply]
  let w := v.comp ((Algebra.TensorProduct.includeRight : T →ₐ[B] F).restrictScalars ℂ)
  refine ⟨w, ?_⟩
  apply AlgHom.ext
  intro b
  change v ((Algebra.TensorProduct.includeRight : T →ₐ[B] F) (algebraMap B T b)) = u b
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B p.ResidueField F, hv, he]

end HodgeLean.Adapters
