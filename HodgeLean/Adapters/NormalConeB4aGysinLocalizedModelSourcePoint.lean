import HodgeLean.Adapters.NormalConeB4aGysinFiniteModelSourcePoint
import HodgeLean.Adapters.NormalConeB4aGysinTensorPoint

noncomputable section
namespace HodgeLean.Adapters
open scoped TensorProduct

/-- A nonvanishing selected tensor prime constructs the complex point of
the finite localized factor with its prescribed base and source projections. -/
theorem a3b4a_gysin_exists_localized_model_source_evaluation
    {D T S : Type} [CommRing D] [CommRing T] [CommRing S]
    [Algebra ℂ D] [Algebra ℂ T] [Algebra ℂ S]
    [Algebra D T] [Algebra D S] [IsScalarTower ℂ D T] [IsScalarTower ℂ D S]
    (e : TensorProduct D T S) [Module.Finite T (Localization.Away e)]
    (p : Ideal T) [p.IsPrime] [IsLocalRing (p.Fiber (Localization.Away e))]
    (u : T →ₐ[ℂ] ℂ) (hu : RingHom.ker u = p)
    (w : S →ₐ[ℂ] ℂ)
    (Q : Ideal (TensorProduct D T S)) [Q.IsPrime] [Q.LiesOver p]
    (hQ : Q.comap Algebra.TensorProduct.includeRight.toRingHom = RingHom.ker w)
    (he : e ∉ Q) :
    letI : Algebra S (TensorProduct D T S) := Algebra.TensorProduct.rightAlgebra
    letI : IsScalarTower ℂ S (TensorProduct D T S) := IsScalarTower.of_algebraMap_eq'
      ((Algebra.TensorProduct.includeRight : S →ₐ[D] TensorProduct D T S).restrictScalars ℂ).comp_algebraMap.symm
    letI : IsScalarTower ℂ S (Localization.Away e) :=
      IsScalarTower.to₁₂₄ ℂ S (TensorProduct D T S) (Localization.Away e)
    ∃ v : Localization.Away e →ₐ[ℂ] ℂ,
      v.comp (IsScalarTower.toAlgHom ℂ T (Localization.Away e)) = u ∧
      v.comp (IsScalarTower.toAlgHom ℂ S (Localization.Away e)) = w := by
  let A := TensorProduct D T S
  let J := Localization.Away e
  letI : Algebra S A := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower ℂ S A := IsScalarTower.of_algebraMap_eq'
    ((Algebra.TensorProduct.includeRight : S →ₐ[D] A).restrictScalars ℂ).comp_algebraMap.symm
  letI : IsScalarTower ℂ S J := IsScalarTower.to₁₂₄ ℂ S A J
  let r := Q.map (algebraMap A J)
  have hd : Disjoint (Submonoid.powers e : Set A) (Q : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime e).mpr he
  letI : r.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers e) J Q inferInstance hd
  letI : r.LiesOver Q :=
    IsLocalization.liesOver_map_of_isPrime_disjoint (Submonoid.powers e) J hd
  letI : r.LiesOver p := Ideal.LiesOver.trans r Q p
  have hr : r.comap (algebraMap S J) = RingHom.ker w := by
    calc
      r.comap (algebraMap S J) =
          (r.comap (algebraMap A J)).comap (algebraMap S A) := by
        rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      _ = Q.comap (algebraMap S A) :=
        congrArg (Ideal.comap (algebraMap S A)) (r.over_def Q).symm
      _ = RingHom.ker w := hQ
  exact a3b4a_gysin_exists_finite_model_source_evaluation p u hu w r hr

end HodgeLean.Adapters
