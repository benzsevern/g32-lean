import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeTriadProjection
import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportedCapProjection

/-! # Original relative cap projected to arbitrary triad targets
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original relative cap followed by projection modulo any second subspace is the original triad cap of the literal quotient chain.
Source: relativeChainProjection_relativeCapHom; triadRelativeChainProjection_triadCapHom.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_triad_cap_chain_square
    (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p) :
    relativeCapHom ℚ (TopPair.ofSubset (X := X) A) p q φ ≫
        (relativeChainProjection ℚ (TopPair.ofSubset (X := X) B)).f q =
      (properCycle_relative_to_triad_chain_map X A B).f (p+q) ≫
        triadCapHom ℚ X A B p q φ := by
  have hp := congrArg (fun f => f.f (p+q)) (properCycle_relative_to_triad_projection X A B)
  rw [HomologicalComplex.comp_f] at hp
  apply Cofork.IsColimit.hom_ext
    (relativeChainProjectionComponentIsCokernelForCap ℚ (TopPair.ofSubset (X := X) A) (p+q))
  change (relativeChainProjection ℚ (TopPair.ofSubset (X := X) A)).f (p+q) ≫
    (relativeCapHom ℚ (TopPair.ofSubset (X := X) A) p q φ ≫ _) =
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) A)).f (p+q) ≫
      ((properCycle_relative_to_triad_chain_map X A B).f (p+q) ≫ _)
  rw [← Category.assoc, relativeChainProjection_relativeCapHom,
    ← Category.assoc, hp, triadRelativeChainProjection_triadCapHom]
  rfl

end HodgeLean.Foundations.QuotientDuality
