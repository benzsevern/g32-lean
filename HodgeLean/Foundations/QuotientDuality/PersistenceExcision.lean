import HodgeLean.Foundations.QuotientDuality.PersistenceCoefficientQuasiIso
import HodgeLean.Foundations.QuotientDuality.PersistencePairChainComparison
import HodgeLean.RealDefs.ComplexFundamentalClassParts.D_ClosedExcision

/-! Excision on the actual relative chains with rational-algebra coefficients. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HomologicalComplex
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal inclusion of a support neighbourhood into the ambient support pair. -/
def persistenceSupportExcisionMap
    {X : Type} [TopologicalSpace X] (U A : Set X) :
    TopPair.ofSubset (X := TopCat.of U) {u | u.val ∉ A} ⟶
      TopPair.ofSubset (X := TopCat.of X) Aᶜ :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of U ⟶ TopCat.of X)
    (fun _ ha => ha)

lemma persistence_support_excision_relative_chain_quasiIso
    (K : Type) [CommRing K] [Algebra ℚ K] {X : Type} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen U) (hA : IsClosed A) (hAU : A ⊆ U) :
    QuasiIso ((relativeChainFunctor K).map (persistenceSupportExcisionMap U A)) := by
  exact persistence_relative_chain_quasiIso_change_coefficients K _
    (HodgeLean.RealDefs.ClosedExcision.relativeChainMap_quasiIso hU hA hAU)

lemma persistence_support_excision_relative_cohomology_bijective
    (K : Type) [Field K] [Algebra ℚ K] {X : Type} [TopologicalSpace X]
    {U A : Set X} (hU : IsOpen U) (hA : IsClosed A) (hAU : A ⊆ U) (n : ℕ) :
    Function.Bijective (relativeCohomologyMap K n (persistenceSupportExcisionMap U A)) := by
  exact persistence_relative_cohomology_bijective_of_relative_chain_quasiIso K _
    (persistence_support_excision_relative_chain_quasiIso K hU hA hAU) n

end HodgeLean.Foundations.QuotientDuality
