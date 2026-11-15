import HodgeLean.Foundations.QuotientDuality.PersistenceRelativeCoefficients
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! Transport of the actual rational relative-chain equivalences to rational algebras. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HomologicalComplex
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_relative_chain_quasiIso_change_coefficients
    (K : Type) [CommRing K] [Algebra ℚ K] {P Q : TopPair.{0}} (f : P ⟶ Q)
    (hf : QuasiIso ((relativeChainFunctor ℚ).map f)) :
    QuasiIso ((relativeChainFunctor K).map f) := by
  haveI (n : ℕ) : Projective (((relativeChainFunctor ℚ).obj P).X n) := by infer_instance
  haveI (n : ℕ) : Projective (((relativeChainFunctor ℚ).obj Q).X n) := by infer_instance
  obtain ⟨e, he⟩ := (ChainComplex.quasiIso_iff_of_projective
    ((relativeChainFunctor ℚ).map f)).mp hf
  let eK : HomotopyEquiv ((relativeChainFunctor K).obj P) ((relativeChainFunctor K).obj Q) :=
    (HomotopyEquiv.ofIso ((persistenceRelativeCoefficientIso K).app P).symm).trans
      (((ModuleCat.extendScalars (algebraMap ℚ K)).mapHomotopyEquiv e).trans
        (HomotopyEquiv.ofIso ((persistenceRelativeCoefficientIso K).app Q)))
  have hhom : eK.hom = (relativeChainFunctor K).map f := by
    change ((persistenceRelativeCoefficientIso K).app P).inv ≫
      (persistenceScalarExtensionChainFunctor K).map e.hom ≫
        ((persistenceRelativeCoefficientIso K).app Q).hom = _
    have hn : (persistenceScalarExtensionChainFunctor K).map ((relativeChainFunctor ℚ).map f) ≫
        ((persistenceRelativeCoefficientIso K).app Q).hom =
      ((persistenceRelativeCoefficientIso K).app P).hom ≫ (relativeChainFunctor K).map f :=
      (persistenceRelativeCoefficientIso K).hom.naturality f
    rw [he, hn, Iso.inv_hom_id_assoc]
  have h := eK.quasiIso_hom
  rw [hhom] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
