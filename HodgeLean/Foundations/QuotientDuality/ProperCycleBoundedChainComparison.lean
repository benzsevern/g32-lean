import HodgeLean.Foundations.QuotientDuality.ProperCycleBoundedChainSheaf

/-! # Original chain sheaves retain homology under actual bounded truncation
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Local homology concentration makes the actual projection to the bounded chain sheaf complex a quasi-isomorphism; no choice of an ambient orientation enters this projection.
Source: properCycle_chain_cohomology_concentrated; CochainComplex.quasiIso_πTruncGE_iff.
HC no distance; AV milestone no distance. -/
lemma properCycle_bounded_chain_sheaf_quasiIso (X : TopCat.{0}) [T2Space X] (N : ℕ)
    (hvan : ∀ m : ℕ, m ≠ N → ∀ x : X,
      Subsingleton (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) m)) :
    QuasiIso
      ((singularChainSheafCochainComplex ℚ X).πTruncGE (-(N : ℤ))) := by
  rw [CochainComplex.quasiIso_πTruncGE_iff, CochainComplex.isGE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact properCycle_chain_cohomology_concentrated X N hvan i (by omega)

end HodgeLean.Foundations.QuotientDuality
