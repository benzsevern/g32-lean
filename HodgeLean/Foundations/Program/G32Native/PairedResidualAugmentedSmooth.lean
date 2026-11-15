import HodgeLean.Foundations.Program.G32Native.PairedResidualAugmentedInjection
import HodgeLean.Foundations.Program.G32Native.PairedResidualDifferentialBaseChange
import HodgeLean.Foundations.Program.G32Native.PairedResidualLocalSmooth

/-! # Relative formal smoothness at the original scalar augmentation -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- Injectivity of the original augmented cotangent fibre gives relative
formal smoothness of the same local algebra.
Source: Stacks Project, Tags 00S2 and 00TI; Hartshorne, Algebraic Geometry, II.8. -/
theorem residual_formallySmooth_of_augmented_differential
    (k S T : Type*) [Field k] [CommRing S] [CommRing T] [IsLocalRing T]
    [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    [Algebra.FormallySmooth k T]
    [Module.Finite S Ω[S⁄k]] [Module.Finite T Ω[T⁄k]]
    (ε : T →ₐ[k] k) :
    letI : Algebra T k := ε.toAlgebra
    letI : Algebra S k := (ε.comp (IsScalarTower.toAlgHom k S T)).toAlgebra
    letI : IsScalarTower S T k := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower k T k :=
      IsScalarTower.of_algebraMap_eq fun c => (ε.commutes c).symm
    letI : IsScalarTower k S k :=
      IsScalarTower.of_algebraMap_eq fun c =>
        ((ε.comp (IsScalarTower.toAlgHom k S T)).commutes c).symm
    Function.Injective (residualDifferentialFibreMap k S T k) →
      Algebra.FormallySmooth S T := by
  letI : Algebra T k := ε.toAlgebra
  letI : Algebra S k := (ε.comp (IsScalarTower.toAlgHom k S T)).toAlgebra
  letI : IsScalarTower S T k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower k T k :=
    IsScalarTower.of_algebraMap_eq fun c => (ε.commutes c).symm
  letI : IsScalarTower k S k :=
    IsScalarTower.of_algebraMap_eq fun c =>
      ((ε.comp (IsScalarTower.toAlgHom k S T)).commutes c).symm
  intro h
  have hb : Function.Injective ((KaehlerDifferential.mapBaseChange k S T).baseChange k) := by
    rw [residual_differential_fibre_baseChange]
    exact h.comp (AlgebraTensorModule.cancelBaseChange S T k k Ω[S⁄k]).injective
  have hr := residual_residue_injective_of_augmentation k T
    (T ⊗[S] Ω[S⁄k]) Ω[T⁄k] ε (KaehlerDifferential.mapBaseChange k S T) hb
  apply residual_local_formallySmooth_of_residue_differential k S T
  simpa only [LinearMap.baseChange_eq_lTensor] using hr

#print axioms residual_formallySmooth_of_augmented_differential
end HodgeLean.Foundations.Program.G32Native
