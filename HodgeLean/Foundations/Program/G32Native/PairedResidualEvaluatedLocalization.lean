import HodgeLean.Foundations.Program.G32Native.PairedResidualLocalizedSmooth

/-! # Source localization with the original supplied point evaluations -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open KaehlerDifferential TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The localization criterion retains independently supplied evaluations
when their original section and germ maps commute.
Source: Stacks Project, Tags 00S2 and 00TI; Hartshorne, Algebraic Geometry, II.8. -/
theorem residual_formallySmooth_localization_with_evaluations
    (k S A L : Type*) [Field k] [CommRing S] [CommRing A] [CommRing L] [IsLocalRing L]
    [Algebra k S] [Algebra k A] [Algebra k L]
    [Algebra S A] [Algebra S L] [Algebra A L]
    [IsScalarTower k S A] [IsScalarTower k S L] [IsScalarTower k A L]
    [IsScalarTower S A L] [Algebra.FormallySmooth k A] [Algebra.FormallyEtale A L]
    [Module.Finite S Ω[S⁄k]] [Module.Finite A Ω[A⁄k]]
    (εL : L →ₐ[k] k) (εA : A →ₐ[k] k) (εS : S →ₐ[k] k)
    (hA : εL.comp (IsScalarTower.toAlgHom k A L) = εA)
    (hS : εA.comp (IsScalarTower.toAlgHom k S A) = εS) :
    letI : Algebra L k := εL.toAlgebra
    letI : Algebra A k := εA.toAlgebra
    letI : Algebra S k := εS.toAlgebra
    letI : IsScalarTower S A k := IsScalarTower.of_algebraMap_eq fun a =>
      (DFunLike.congr_fun (congrArg AlgHom.toRingHom hS) a).symm
    letI : IsScalarTower k A k :=
      IsScalarTower.of_algebraMap_eq fun c => (εA.commutes c).symm
    letI : IsScalarTower k S k :=
      IsScalarTower.of_algebraMap_eq fun c => (εS.commutes c).symm
    Function.Injective (residualDifferentialFibreMap k S A k) →
      Algebra.FormallySmooth S L := by
  have hS' : εL.comp (IsScalarTower.toAlgHom k S L) = εS := by
    rw [← hS, ← hA]
    ext s
    change εL (algebraMap S L s) = εL (algebraMap A L (algebraMap S A s))
    rw [IsScalarTower.algebraMap_apply S A L]
  subst εA
  subst εS
  exact residual_formallySmooth_after_etale_localization k S A L εL

#print axioms residual_formallySmooth_localization_with_evaluations
end HodgeLean.Foundations.Program.G32Native
