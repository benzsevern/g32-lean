import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadLocalHomology

/-! # Actual intrinsic tangential local homology of the cap target -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Swapping the actual factors and contracting the normal factor identifies the original product cap target with intrinsic tangential local homology.
Source: Hatcher, Algebraic Topology, sections 2.1 and 2.2, homotopy invariance of relative homology.
HC no distance; AV milestone no distance. -/
def properCycle_product_tangent_local_homology_iso
    (E : Type) [TopologicalSpace E] [Zero E]
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) :
    RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of (E × F)) {z | z.1 = 0}ᶜ) n ≅
      orientationGroup (TopCat.of E) n 0 := by
  let e : TopPair.ofSubset (X := TopCat.of (E × F)) {z | z.1 = 0}ᶜ ≅
      TopPair.ofSubset (X := TopCat.of (F × E)) (Prod.snd ⁻¹' ({0} : Set E)ᶜ) :=
    TopPair.isoOfSubset (Homeomorph.prodComm E F) (fun _ => Iff.rfl)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n
  exact H.mapIso ((relativeChainFunctor ℚ).mapIso e) ≪≫
    properCycle_product_support_homology_iso F (TopCat.of E) {0} n

end HodgeLean.Foundations.QuotientDuality
