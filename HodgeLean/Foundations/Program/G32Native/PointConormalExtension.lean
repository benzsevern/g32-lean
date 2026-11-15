import HodgeLean.Foundations.Program.G32Native.DualConormalSequence

/-! # Extension of point-valued conormal functionals to ambient derivations -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- A functional on the actual conormal module of a smooth quotient extends
to an ambient derivation, retaining its values on the original ideal classes. -/
theorem pointConormalFunctional_extends
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Extension A B) [Algebra.FormallySmooth A P.Ring]
    [Algebra.FormallySmooth A B]
    {M : Type*} [AddCommGroup M] [Module B M] [Module A M] [Module P.Ring M]
    [IsScalarTower A B M] [IsScalarTower P.Ring B M] [IsScalarTower A P.Ring M]
    (f : P.Cotangent →ₗ[B] M) :
    ∃ D : Derivation A P.Ring M, ∀ r : P.ker, D r.val = f (.mk r) := by
  obtain ⟨l, hl⟩ := P.formallySmooth_iff_split_injection.mp inferInstance
  let u : Ω[P.Ring⁄A] →ₗ[P.Ring] P.CotangentSpace :=
    TensorProduct.mk P.Ring B Ω[P.Ring⁄A] (1 : B)
  let D := (((f.comp l).restrictScalars P.Ring).comp u).compDer
    (KaehlerDifferential.D A P.Ring)
  refine ⟨D, ?_⟩
  intro r
  change f (l ((1 : B) ⊗ₜ[P.Ring] KaehlerDifferential.D A P.Ring r.val)) = f (.mk r)
  rw [← P.cotangentComplex_mk r]
  exact congrArg f (DFunLike.congr_fun hl (.mk r))

/-- A point-valued functional on the original kernel ideal extends to an
ambient derivation when the quotient is smooth; its original ideal values are retained. -/
theorem pointIdealFunctional_extends
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Extension A B) [Algebra.FormallySmooth A P.Ring]
    [Algebra.FormallySmooth A B]
    {M : Type*} [AddCommGroup M] [Module B M] [Module A M] [Module P.Ring M]
    [IsScalarTower A B M] [IsScalarTower P.Ring B M] [IsScalarTower A P.Ring M]
    (f : P.ker →ₗ[P.Ring] M) :
    ∃ D : Derivation A P.Ring M, ∀ r : P.ker, D r.val = f r := by
  have hk (r : P.ker) (m : M) : (r : P.Ring) • m = 0 := by
    calc
      (r : P.Ring) • m = algebraMap P.Ring B r • m :=
        (IsScalarTower.algebraMap_smul B r.val m).symm
      _ = 0 := by rw [show algebraMap P.Ring B r = 0 from r.property, zero_smul]
  let q : P.ker.Cotangent →ₗ[P.Ring] M := Ideal.Cotangent.lift f (by
    intro r s
    change f ((r : P.Ring) • s) = 0
    rw [map_smul]
    exact hk r (f s))
  let e : P.Cotangent ≃ₗ[P.Ring] P.ker.Cotangent := {
    __ := AddEquiv.refl _
    map_smul' := Algebra.Extension.Cotangent.val_smul' }
  let F : P.Cotangent →ₗ[B] M :=
    (q.comp e.toLinearMap).extendScalarsOfSurjective P.algebraMap_surjective
  obtain ⟨D, hD⟩ := pointConormalFunctional_extends P F
  exact ⟨D, hD⟩

#print axioms pointIdealFunctional_extends
#print axioms pointConormalFunctional_extends
end HodgeLean.Foundations.Program.G32Native
