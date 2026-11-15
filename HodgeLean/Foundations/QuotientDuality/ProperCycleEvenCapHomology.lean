import HodgeLean.Foundations.QuotientDuality.ProperCycleEvenCapChainMap

/-! # Original homology maps of the reindexed even-degree cap complex -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original chain complex and its degree tail have identical three-term models in every positive tail degree.
Source: Mathlib, Algebra/Homology/ShortComplex/HomologicalComplex.lean, isoSc'.
HC no distance; AV milestone no distance. -/
def properCycle_cap_tail_sc_iso
    (K : ChainComplex (ModuleCat ℚ) ℕ) (p q : ℕ) :
    K.sc (p + (q + 1)) ≅
      (K.restriction (properCycle_cap_tail_embedding p)).sc (q + 1) :=
  K.isoSc' (p + ((q + 1) + 1)) (p + (q + 1)) (p + q)
    (by rw [ChainComplex.prev]; omega)
    (by rw [show p + (q + 1) = (p + q) + 1 by omega, ChainComplex.next_nat_succ]) ≪≫
  ((K.restriction (properCycle_cap_tail_embedding p)).isoSc'
    ((q + 1) + 1) (q + 1) q (by rw [ChainComplex.prev]) (ChainComplex.next_nat_succ q)).symm

/-- The literal three-term comparison identifies original positive-degree homology with the homology of the corresponding degree tail.
Source: Mathlib, Algebra/Homology/ShortComplex/HomologicalComplex.lean, homology of three-term models.
HC no distance; AV milestone no distance. -/
def properCycle_cap_tail_homology_iso
    (K : ChainComplex (ModuleCat ℚ) ℕ) (p q : ℕ) :
    K.homology (p + (q + 1)) ≅
      (K.restriction (properCycle_cap_tail_embedding p)).homology (q + 1) :=
  ShortComplex.homologyMapIso (properCycle_cap_tail_sc_iso K p q)

/-- The original homology map of the even cap chain map equals the repository's actual triad cap map after the literal degree-tail comparison.
Source: Hatcher, Algebraic Topology, section 3.3; Mathlib, homology maps of three-term chain models.
HC no distance; AV milestone no distance. -/
lemma properCycle_even_triad_cap_homology_comparison
    (X : TopCat.{0}) (A B : Set X) (p q : ℕ) (hp : Even p)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := X) A) p φ = 0) :
    (properCycle_cap_tail_homology_iso (triadRelativeChainComplex ℚ X A B) p q).hom ≫
      HomologicalComplex.homologyMap (properCycle_even_triad_cap_chain_map X A B p hp φ hφ)
        (q + 1) =
      ModuleCat.ofHom (triadCapHomologyMap ℚ X A B p (q + 1) φ hφ) := by
  let E := properCycle_cap_tail_sc_iso (triadRelativeChainComplex ℚ X A B) p q
  let F := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)
    (q + 1)).map (properCycle_even_triad_cap_chain_map X A B p hp φ hφ)
  have h : ShortComplex.homologyMap (E.hom ≫ F) =
      ShortComplex.homologyMap (triadCapShortComplexHom ℚ X A B p (q + 1) φ hφ) := by
    apply AlgebraicTopology.Simplicial.homologyMap_eq_of_τ₂_eq
    change E.hom.τ₂ ≫ triadCapHom ℚ X A B p (q + 1) φ = _
    rw [triadCapShortComplexHom_τ₂]
    have hmid : E.hom.τ₂ = 𝟙 _ := by
      apply ModuleCat.hom_ext
      ext z
      rfl
    rw [hmid, Category.id_comp]
  rw [ShortComplex.homologyMap_comp] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
