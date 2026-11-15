import HodgeLean.Foundations.QuotientDuality.ProperCycleChainStalk

/-! # Local homology of the actual relative-chain sheaf complex -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Stalks of homology sheaves are the actual local relative rational homology groups.
Source: HodgeConjecture 2ead713, Other/AlgebraicTopology/Singular/Sheaf/ChainHomology.lean.
HC no distance; AV milestone no distance. -/
def properCycle_chain_homology_stalk_iso (X : TopCat.{0}) [T2Space X] (x : X) (n : ℕ) :
    (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).obj
      ((singularChainSheafComplex ℚ X).homology n) ≅
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj
      (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) n) :=
  (((singularChainSheafComplex ℚ X).sc n).mapHomologyIso
    (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x)).symm ≪≫
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.down ℕ) n).mapIso
    (properCycle_sheaf_complex_stalk_iso X x) ≪≫
  (((relativeChainFunctor ℚ).obj (TopPair.ofSubset ({x} : Set X)ᶜ)).sc n).mapHomologyIso
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0})

lemma properCycle_chain_homology_sheaf_vanishes (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (hlocal : ∀ x : X, Subsingleton (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) n)) :
    IsZero ((singularChainSheafComplex ℚ X).homology n) := by
  rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
  intro x
  apply (properCycle_chain_homology_stalk_iso X x n).isZero_iff.mpr
  have hz : IsZero (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) n) :=
    ModuleCat.isZero_iff_subsingleton.mpr (hlocal x)
  exact (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map_isZero hz

lemma properCycle_chain_cohomology_concentrated (X : TopCat.{0}) [T2Space X] (N : ℕ)
    (hlocal : ∀ m : ℕ, m ≠ N → ∀ x : X,
      Subsingleton (RelativeHomology ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) m)) :
    ∀ i : ℤ, i ≠ -(N : ℤ) →
      IsZero ((singularChainSheafCochainComplex ℚ X).homology i) := by
  intro i hi
  by_cases hpos : 0 < i
  · exact (singularChainSheafCochainComplex ℚ X).isZero_of_isLE 0 i hpos
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = -(m : ℤ) := ⟨(-i).toNat, by omega⟩
    have e : (singularChainSheafCochainComplex ℚ X).homology (-(m : ℤ)) ≅
        (singularChainSheafComplex ℚ X).homology m :=
      (singularChainSheafComplex ℚ X).extendHomologyIso ComplexShape.embeddingDownNat rfl
    exact e.isZero_iff.mpr
      (properCycle_chain_homology_sheaf_vanishes X m (hlocal m (by omega)))

end HodgeLean.Foundations.QuotientDuality
