import HodgeLean.Foundations.QuotientDuality.ProperCycleUnionCapComparison
import Mathlib.Algebra.Homology.Embedding.Restriction

/-! # The original even-degree relative cap as a chain map on actual degree tails -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Reindex the actual chain degrees by adding the fixed cap degree on the left.
Source: Mathlib, Algebra/Homology/Embedding/Restriction.lean, restriction along embeddings of complex shapes.
HC no distance; AV milestone no distance. -/
def properCycle_cap_tail_embedding (p : ℕ) :
    (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) where
  f q := p + q
  injective_f := fun _ _ h => Nat.add_left_cancel h
  rel := by
    intro i j h
    change j + 1 = i at h
    change (p + j) + 1 = p + i
    omega

instance properCycle_cap_tail_embedding_rel_iff (p : ℕ) :
    (properCycle_cap_tail_embedding p).IsRelIff where
  rel' i j h := by
    change (p + j) + 1 = p + i at h
    change j + 1 = i
    omega

/-- For an even relative cocycle degree, the original triad cap is an actual chain map from the degree-reindexed sum-relative complex to the original target relative complex.
Source: Hatcher, Algebraic Topology, section 3.3, the signed cap boundary formula.
HC no distance; AV milestone no distance. -/
def properCycle_even_triad_cap_chain_map
    (X : TopCat.{0}) (A B : Set X) (p : ℕ) (hp : Even p)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := X) A) p φ = 0) :
    (triadRelativeChainComplex ℚ X A B).restriction (properCycle_cap_tail_embedding p) ⟶
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) B) where
  f q := triadCapHom ℚ X A B p q φ
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    subst i
    apply ModuleCat.hom_ext
    change (relativeBoundary ℚ (TopPair.ofSubset (X := X) B) j).comp
        (triadCap ℚ X A B p (j + 1) φ) =
      (triadCap ℚ X A B p j φ).comp (triadRelativeBoundary ℚ X A B (p + j))
    have h := boundary_triadCap_eq_of_cocycle ℚ X A B p j φ hφ
    rw [hp.neg_one_pow, one_smul] at h
    exact h

end HodgeLean.Foundations.QuotientDuality
