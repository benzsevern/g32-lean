import HodgeLean.Foundations.QuotientDuality.RetainedCycleCompactSectionHomology
import HodgeLean.Foundations.QuotientDuality.RetainedCycleBoundedSupportForgetting
import HodgeLean.Foundations.QuotientDuality.RetainedCycleTruncationWindow

/-! # The actual bounded global finite-chain comparison -/

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology.Singular
open HodgeLean.Foundations.RationalHomologyManifold
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The original global chain-section map with the literal regrading and bounded projection.
Source: properCycle_chain_sheaf_section_map; properCycle_section_functor_extend_iso; CochainComplex.πTruncGE.
-/
def retainedBoundedGlobalChainMap (X : TopCat.{0}) (N : ℕ) :=
  extendMap (properCycle_chain_sheaf_section_map X ⊤) ComplexShape.embeddingDownNat ≫
    (properCycle_section_functor_extend_iso (subdivisionGlobalSectionsFunctor X)
      (singularChainSheafComplex ℚ X)).hom ≫
    ((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℤ)).map
      ((singularChainSheafCochainComplex ℚ X).πTruncGE (-(N : ℤ)))

/-- The bounded global finite-chain comparison preserves homology in the untouched window. -/
lemma retained_bounded_global_chain_quasiIsoAt (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (N : ℕ) (i : ℤ) (hi : -(N : ℤ)+1 < i) :
    QuasiIsoAt (retainedBoundedGlobalChainMap X N) i := by
  haveI : IsIso (properCycle_chain_sheaf_section_map X ⊤) :=
    retained_global_chain_sheaf_section_isIso X
  haveI : IsIso (extendMap (properCycle_chain_sheaf_section_map X ⊤)
      ComplexShape.embeddingDownNat) :=
    by
      change IsIso ((ComplexShape.embeddingDownNat.extendFunctor AddCommGrpCat).map
        (properCycle_chain_sheaf_section_map X ⊤))
      infer_instance
  haveI := retained_functor_truncation_quasiIsoAt (subdivisionGlobalSectionsFunctor X)
    (singularChainSheafCochainComplex ℚ X) (-(N : ℤ)) i hi
  unfold retainedBoundedGlobalChainMap
  infer_instance

end HodgeLean.Foundations.QuotientDuality
