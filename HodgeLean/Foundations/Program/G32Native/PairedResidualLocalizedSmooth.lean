import HodgeLean.Foundations.Program.G32Native.PairedResidualEtaleFibreNaturality
import HodgeLean.Foundations.Program.G32Native.PairedResidualAugmentedSmooth

/-! # Relative smoothness after the actual source localization -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open KaehlerDifferential TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The original augmented differential injection gives relative formal
smoothness after formally etale localization at the same specified point.
Source: Stacks Project, Tags 00S2 and 00TI; Hartshorne, Algebraic Geometry, II.8. -/
theorem residual_formallySmooth_after_etale_localization
    (k S A L : Type*) [Field k] [CommRing S] [CommRing A] [CommRing L] [IsLocalRing L]
    [Algebra k S] [Algebra k A] [Algebra k L]
    [Algebra S A] [Algebra S L] [Algebra A L]
    [IsScalarTower k S A] [IsScalarTower k S L] [IsScalarTower k A L]
    [IsScalarTower S A L] [Algebra.FormallySmooth k A] [Algebra.FormallyEtale A L]
    [Module.Finite S Ω[S⁄k]] [Module.Finite A Ω[A⁄k]] (ε : L →ₐ[k] k) :
    letI : Algebra L k := ε.toAlgebra
    let εA := ε.comp (IsScalarTower.toAlgHom k A L)
    let εS := ε.comp (IsScalarTower.toAlgHom k S L)
    letI : Algebra A k := εA.toAlgebra
    letI : Algebra S k := εS.toAlgebra
    letI : IsScalarTower A L k := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower S L k := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower S A k := IsScalarTower.of_algebraMap_eq (by
      intro s
      change ε (algebraMap S L s) = ε (algebraMap A L (algebraMap S A s))
      rw [IsScalarTower.algebraMap_apply S A L])
    letI : IsScalarTower k L k :=
      IsScalarTower.of_algebraMap_eq fun c => (ε.commutes c).symm
    letI : IsScalarTower k A k :=
      IsScalarTower.of_algebraMap_eq fun c => (εA.commutes c).symm
    letI : IsScalarTower k S k :=
      IsScalarTower.of_algebraMap_eq fun c => (εS.commutes c).symm
    Function.Injective (residualDifferentialFibreMap k S A k) →
      Algebra.FormallySmooth S L := by
  dsimp only
  letI : Algebra L k := ε.toAlgebra
  let εA := ε.comp (IsScalarTower.toAlgHom k A L)
  let εS := ε.comp (IsScalarTower.toAlgHom k S L)
  letI : Algebra A k := εA.toAlgebra
  letI : Algebra S k := εS.toAlgebra
  letI : IsScalarTower A L k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower S L k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower S A k := IsScalarTower.of_algebraMap_eq (by
    intro s
    change ε (algebraMap S L s) = ε (algebraMap A L (algebraMap S A s))
    rw [IsScalarTower.algebraMap_apply S A L])
  letI : IsScalarTower k L k :=
    IsScalarTower.of_algebraMap_eq fun c => (ε.commutes c).symm
  letI : IsScalarTower k A k :=
    IsScalarTower.of_algebraMap_eq fun c => (εA.commutes c).symm
  letI : IsScalarTower k S k :=
    IsScalarTower.of_algebraMap_eq fun c => (εS.commutes c).symm
  intro h
  letI : Algebra.FormallySmooth k L := Algebra.FormallySmooth.comp k A L
  letI : Module.Finite L Ω[L⁄k] := Module.Finite.of_surjective
    (tensorKaehlerEquivOfFormallyEtale k A L).toLinearMap
    (tensorKaehlerEquivOfFormallyEtale k A L).surjective
  have hL : Function.Injective (residualDifferentialFibreMap k S L k) := by
    have hi : Function.Injective
        ((residualEtaleDifferentialFibreEquiv k A L k).toLinearMap.comp
          (residualDifferentialFibreMap k S L k)) := by
      rw [residual_etale_differential_fibre_naturality]
      exact h
    intro x y hxy
    exact hi (congrArg (residualEtaleDifferentialFibreEquiv k A L k) hxy)
  exact residual_formallySmooth_of_augmented_differential k S L ε hL

#print axioms residual_formallySmooth_after_etale_localization
end HodgeLean.Foundations.Program.G32Native
