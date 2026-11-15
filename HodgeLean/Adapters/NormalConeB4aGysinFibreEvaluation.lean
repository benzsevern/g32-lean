import HodgeLean.Adapters.NormalConeB4aGysinFiniteFibreLift
import HodgeLean.Adapters.NormalConeB4aGysinBaseChangeInjective
import HodgeLean.Adapters.NormalConeB4aGysinEvaluationKernel

noncomputable section
namespace HodgeLean.Adapters
open scoped TensorProduct

/-- Evaluations over a rational base point identify the points of the
full finite fibre, retaining the prime of every source evaluation. -/
theorem a3b4a_gysin_fibre_evaluation_equiv
    {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra B T] [IsScalarTower ℂ B T] [Module.Finite B T]
    (p : Ideal B) [p.IsPrime] (u : B →ₐ[ℂ] ℂ) (hu : RingHom.ker u = p) :
    ∃ E : {w : T →ₐ[ℂ] ℂ // w.comp (IsScalarTower.toAlgHom ℂ B T) = u} ≃
        PrimeSpectrum (p.Fiber T),
      ∀ w, (E w).asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = RingHom.ker w.val := by
  classical
  let H := PrimeSpectrum.preimageEquivFiber B T ⟨p, inferInstance⟩
  let X := {w : T →ₐ[ℂ] ℂ // w.comp (IsScalarTower.toAlgHom ℂ B T) = u}
  let k : X → PrimeSpectrum.comap (algebraMap B T) ⁻¹' {⟨p, inferInstance⟩} :=
    fun w => ⟨⟨RingHom.ker w.val,
    RingHom.ker_isPrime w.val⟩, by
      apply PrimeSpectrum.ext
      change (RingHom.ker w.val.toRingHom).comap (algebraMap B T) = p
      rw [RingHom.comap_ker]
      exact (congrArg (fun v : B →ₐ[ℂ] ℂ => RingHom.ker v.toRingHom) w.property).trans hu⟩
  let f : X → PrimeSpectrum (p.Fiber T) := fun w => H (k w)
  have hf (w : X) : (f w).asIdeal.comap
      Algebra.TensorProduct.includeRight.toRingHom = RingHom.ker w.val := by
    have hh := H.symm_apply_apply (k w)
    exact congrArg (fun x => x.val.asIdeal) hh
  have hinj : Function.Injective f := by
    intro w w' h
    apply Subtype.ext
    apply a3b4a_gysin_evaluation_eq_of_ker_eq
    rw [← hf w, ← hf w', h]
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨e, he⟩ := a3b4a_gysin_exists_rational_residue_equiv p u hu
    let F := p.Fiber T
    letI : Module.Finite ℂ p.ResidueField :=
      Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
    letI : Module.Finite ℂ F := Module.Finite.trans p.ResidueField F
    let v : F →ₐ[ℂ] ℂ := (a3b4a_gysin_algHomEquivPrimeSpectrum ℂ F).symm z
    have hv (x : p.ResidueField) : v (algebraMap p.ResidueField F x) = e x := by
      have hx : x = algebraMap ℂ p.ResidueField (e x) := by
        apply e.injective
        rw [e.commutes, Algebra.algebraMap_self_apply]
      nth_rw 1 [hx]
      rw [← IsScalarTower.algebraMap_apply ℂ p.ResidueField F, v.commutes,
        Algebra.algebraMap_self_apply]
    let w := v.comp ((Algebra.TensorProduct.includeRight : T →ₐ[B] F).restrictScalars ℂ)
    have hw : w.comp (IsScalarTower.toAlgHom ℂ B T) = u := by
      apply AlgHom.ext
      intro b
      change v ((Algebra.TensorProduct.includeRight : T →ₐ[B] F) (algebraMap B T b)) = u b
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B p.ResidueField F, hv, he]
    refine ⟨⟨w, hw⟩, ?_⟩
    apply H.symm.injective
    apply Subtype.ext
    apply PrimeSpectrum.ext
    change (f ⟨w, hw⟩).asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom =
      z.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom
    rw [hf]
    have hz : RingHom.ker v = z.asIdeal := congrArg PrimeSpectrum.asIdeal
      ((a3b4a_gysin_algHomEquivPrimeSpectrum ℂ F).apply_symm_apply z)
    rw [← hz]
    exact (RingHom.comap_ker _ _).symm
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end HodgeLean.Adapters
