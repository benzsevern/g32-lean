import HodgeLean.Foundations.QuotientDuality.ProperCycleProductTriadCap

/-! # Actual open-subspace relative excision in the subcomplex cap models -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Original open-triad excision identifies the actual union-subcomplex quotient homology with the literal relative homology of the union.
Source: Hatcher, Algebraic Topology, section 2.2, small-chain excision.
HC no distance; AV milestone no distance. -/
def properCycle_subset_union_quotient_homology_iso
    (X : TopCat.{0}) (A B : Set X) (hAo : IsOpen A) (hBo : IsOpen B) (n : ℕ) :
    (properCycle_subcomplex_quotient (subsetSingularSubcomplex X A ⊔ subsetSingularSubcomplex X B)).homology n ≅
      RelativeHomology ℚ (TopPair.ofSubset (X := X) (A ∪ B)) n := by
  letI : QuasiIso (triadToUnionRelativeChainMap ℚ X A B) :=
    triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hAo hBo
  exact (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso
      (properCycle_subset_union_subcomplex_triad_iso X A B) ≪≫
    asIso (HomologicalComplex.homologyMap (triadToUnionRelativeChainMap ℚ X A B) n)

/-- Actual union-relative vanishing gives vanishing of the original fixed-relative Mayer--Vietoris middle group.
Source: Hatcher, Algebraic Topology, section 2.2, open-triad excision and relative Mayer--Vietoris.
HC no distance; AV milestone no distance. -/
lemma properCycle_fixed_subcomplex_middle_isZero
    (X : TopCat.{0}) (A P Q : Set X) (hAo : IsOpen A) (hPo : IsOpen P) (hQo : IsOpen Q) (n : ℕ)
    (hP : IsZero (RelativeHomology ℚ (TopPair.ofSubset (X := X) (A ∪ P)) n))
    (hQ : IsZero (RelativeHomology ℚ (TopPair.ofSubset (X := X) (A ∪ Q)) n)) :
    IsZero ((properCycle_fixed_subcomplex_sequence
      (subsetSingularSubcomplex X A) (subsetSingularSubcomplex X P) (subsetSingularSubcomplex X Q)).X₂.homology n) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n
  letI : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
  let e := H.mapBiprod
      (properCycle_subcomplex_quotient (subsetSingularSubcomplex X A ⊔ subsetSingularSubcomplex X P))
      (properCycle_subcomplex_quotient (subsetSingularSubcomplex X A ⊔ subsetSingularSubcomplex X Q)) ≪≫
    biprod.mapIso (properCycle_subset_union_quotient_homology_iso X A P hAo hPo n)
      (properCycle_subset_union_quotient_homology_iso X A Q hAo hQo n)
  exact ((biprod_isZero_iff _ _).mpr ⟨hP, hQ⟩).of_iso e

/-- Original relative vanishing gives vanishing of the actual target Mayer--Vietoris middle group.
Source: Hatcher, Algebraic Topology, section 2.2, relative Mayer--Vietoris chain models.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_middle_isZero
    (X : TopCat.{0}) (P Q : Set X) (n : ℕ)
    (hP : IsZero (RelativeHomology ℚ (TopPair.ofSubset (X := X) P) n))
    (hQ : IsZero (RelativeHomology ℚ (TopPair.ofSubset (X := X) Q) n)) :
    IsZero ((properCycle_subcomplex_quotient_sequence
      (subsetSingularSubcomplex X P) (subsetSingularSubcomplex X Q)).X₂.homology n) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n
  letI : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
  let e := H.mapBiprod (properCycle_subcomplex_quotient (subsetSingularSubcomplex X P))
      (properCycle_subcomplex_quotient (subsetSingularSubcomplex X Q)) ≪≫
    biprod.mapIso (H.mapIso (properCycle_subset_subcomplex_relative_iso X P))
      (H.mapIso (properCycle_subset_subcomplex_relative_iso X Q))
  exact ((biprod_isZero_iff _ _).mpr ⟨hP, hQ⟩).of_iso e

end HodgeLean.Foundations.QuotientDuality
