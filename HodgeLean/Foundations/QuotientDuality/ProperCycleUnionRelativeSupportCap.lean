import HodgeLean.Foundations.QuotientDuality.ProperCycleCohomologyCapSupportRecurrence

/-! # The original normal cap in ordinary support-relative coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual open-triad excision followed by the literal support-complement union identification.
Source: triadToUnionRelativeChainMap_quasiIso_of_isOpen; properCycle_support_complement_union_iso.
HC no distance; AV milestone no distance. -/
def properCycle_support_cap_source_iso
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T) (n : ℕ) :
    TriadRelativeHomology ℚ Y Sᶜ Tᶜ n ≅
      RelativeHomology ℚ (TopPair.ofSubset (X := Y) (S ∩ T)ᶜ) n := by
  letI := triadToUnionRelativeChainMap_quasiIso_of_isOpen Y Sᶜ Tᶜ hS.isOpen_compl hT.isOpen_compl
  exact asIso (HomologicalComplex.homologyMap (triadToUnionRelativeChainMap ℚ Y Sᶜ Tᶜ) n) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).mapIso
      ((relativeChainFunctor ℚ).mapIso (properCycle_support_complement_union_iso Y S T))

/-- The original cohomology cap with its actual source excision, on ordinary intersection-support relative homology.
Source: properCycle_support_cap_source_iso; AlgebraicTopology.Singular.triadCapCohomologyLinear.
HC no distance; AV milestone no distance. -/
def properCycle_union_relative_support_cap
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T) (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) p) :
    RelativeHomology ℚ (TopPair.ofSubset (X := Y) (S ∩ T)ᶜ) (p+q) ⟶
      RelativeHomology ℚ (TopPair.ofSubset (X := Y) Tᶜ) q :=
  (properCycle_support_cap_source_iso Y S T hS hT (p+q)).inv ≫
    ModuleCat.ofHom (triadCapCohomologyLinear ℚ Y Sᶜ Tᶜ p q a)

/-- The intersection of the actual pulled-back normal support and the zero-slice support has its literal zero-slice intersection coordinates.
Source: Munkres, Topology, section 19, product subspaces.
HC no distance; AV milestone no distance. -/
def properCycle_real_support_intersection_pair_iso
    (Y : TopCat.{0}) (S T : Set Y) :
    TopPair.ofSubset (X := TopCat.of (ℝ × Y))
      ((Prod.snd ⁻¹' S) ∩ {z | z.1 = 0 ∧ z.2 ∈ T})ᶜ ≅
      TopPair.ofSubset (X := TopCat.of (ℝ × Y))
        {z | z.1 = 0 ∧ z.2 ∈ S ∩ T}ᶜ :=
  TopPair.isoOfSubset (Homeomorph.refl _) (by
    intro z
    change ¬ (z.1 = 0 ∧ z.2 ∈ S ∧ z.2 ∈ T) ↔ ¬ (z.2 ∈ S ∧ z.1 = 0 ∧ z.2 ∈ T)
    tauto)

/-- Ordinary support source excision followed by the literal intersection coordinates is the specified original upper union comparison.
Source: properCycle_support_cap_source_iso; properCycle_real_cap_upper_union_iso.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_cap_source_comparison
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T) (n : ℕ) :
    (properCycle_support_cap_source_iso (TopCat.of (ℝ × Y))
      (Prod.snd ⁻¹' S) {z | z.1 = 0 ∧ z.2 ∈ T}
      (hS.preimage continuous_snd)
      ((isClosed_eq continuous_fst continuous_const).inter (hT.preimage continuous_snd)) n).hom ≫
      HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (properCycle_real_support_intersection_pair_iso Y S T).hom) n =
      HomologicalComplex.homologyMap (triadToUnionRelativeChainMap ℚ (TopCat.of (ℝ × Y))
        (Prod.snd ⁻¹' Sᶜ) {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ) n ≫
      HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (properCycle_real_cap_upper_union_iso Y S T).hom) n := by
  have he : (properCycle_support_complement_union_iso (TopCat.of (ℝ × Y))
      (Prod.snd ⁻¹' S) {z | z.1 = 0 ∧ z.2 ∈ T}).hom ≫
      (properCycle_real_support_intersection_pair_iso Y S T).hom =
      (properCycle_real_cap_upper_union_iso Y S T).hom := by
    ext z : 2 <;> rfl
  dsimp only [properCycle_support_cap_source_iso, Iso.trans_hom, asIso_hom,
    CategoryTheory.Functor.mapIso_hom]
  dsimp only [HomologicalComplex.homologyFunctor]
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ← CategoryTheory.Functor.map_comp, he]
  rfl

end HodgeLean.Foundations.QuotientDuality
