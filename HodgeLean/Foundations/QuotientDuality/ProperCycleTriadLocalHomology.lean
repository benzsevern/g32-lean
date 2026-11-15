import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexProductCapDuality

/-! # Original triad excision and actual ambient local homology -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Original open-triad excision gives the actual ambient local homology whenever the specified subspaces have precisely the punctured ambient union.
Source: Hatcher, Algebraic Topology, section 2.2, excision for relative singular chains.
HC no distance; AV milestone no distance. -/
def properCycle_triad_local_homology_iso
    (X : TopCat.{0}) (A B : Set X) (hAo : IsOpen A) (hBo : IsOpen B)
    (x : X) (hU : A ∪ B = ({x} : Set X)ᶜ) (n : ℕ) :
    TriadRelativeHomology ℚ X A B n ≅ orientationGroup X n x := by
  letI : QuasiIso (triadToUnionRelativeChainMap ℚ X A B) :=
    triadToUnionRelativeChainMap_quasiIso_of_isOpen X A B hAo hBo
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n
  exact asIso (HomologicalComplex.homologyMap (triadToUnionRelativeChainMap ℚ X A B) n) ≪≫
    H.mapIso (eqToIso (congrArg
      (fun U : Set X => (relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) U)) hU))

/-- The original normal and tangential support-complement subspaces have exactly the ambient punctured product as their union.
Source: Hatcher, Algebraic Topology, section 3.3, local product cap models.
HC no distance; AV milestone no distance. -/
lemma properCycle_product_puncture_union (E F : Type) [Zero E] [Zero F] :
    (Prod.snd ⁻¹' ({0} : Set F)ᶜ : Set (E × F)) ∪ {z | z.1 = 0}ᶜ =
      ({(0, 0)} : Set (E × F))ᶜ := by
  ext z
  change (z.2 ≠ 0 ∨ z.1 ≠ 0) ↔ z ≠ (0, 0)
  constructor
  · rintro (h | h) hz
    · exact h (congrArg Prod.snd hz)
    · exact h (congrArg Prod.fst hz)
  · intro h
    by_cases hz : z.1 = 0
    · left
      intro hz'
      exact h (Prod.ext hz hz')
    · exact Or.inr hz

/-- In the original product triad the source homology is the actual local homology of the ambient product at its origin.
Source: Hatcher, Algebraic Topology, section 2.2, relative excision for a punctured product.
HC no distance; AV milestone no distance. -/
def properCycle_product_triad_local_homology_iso
    (E F : Type) [TopologicalSpace E] [T1Space E] [Zero E]
    [TopologicalSpace F] [T1Space F] [Zero F] (n : ℕ) :
    TriadRelativeHomology ℚ (TopCat.of (E × F))
      (Prod.snd ⁻¹' ({0} : Set F)ᶜ) {z | z.1 = 0}ᶜ n ≅
        orientationGroup (TopCat.of (E × F)) n (0, 0) :=
  properCycle_triad_local_homology_iso (TopCat.of (E × F)) _ _
    (isClosed_singleton.isOpen_compl.preimage continuous_snd)
    ((isClosed_singleton.preimage continuous_fst).isOpen_compl)
    (0, 0) (properCycle_product_puncture_union E F) n

end HodgeLean.Foundations.QuotientDuality
