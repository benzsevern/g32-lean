import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartClassHomeomorph

/-! # Actual global orientation detection on a one-point space -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- On a one-point space the actual local orientation restriction detects every global homology class.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, the pair with empty complement.
HC no distance; AV milestone no distance. -/
lemma properCycle_subsingleton_local_orientation_injective
    (X : TopCat.{0}) [Subsingleton X] (x : X) (n : ℕ) :
    Function.Injective (fun c : Homology ℚ X n => localOrientation X n c x) := by
  have hempty : ({x} : Set X)ᶜ = ∅ := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact not_not.mpr (Subsingleton.elim y x)
  change Function.Injective (relativeHomologyProjection ℚ (pointComplementPair x) n).hom
  have hp : pointComplementPair x = emptySubspacePair X := by
    change TopPair.ofSubset (X := X) ({x} : Set X)ᶜ = TopPair.ofSubset (X := X) ∅
    rw [hempty]
  rw [hp]
  exact (homologyEmptySubspaceIso ℚ X n).toLinearEquiv.injective

/-- Actual local orientation restriction commutes with the singular map of a homeomorphism.
Source: Hatcher, Algebraic Topology, section 2.1, naturality of relative homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_local_orientation_homeomorph
    {X Y : TopCat.{0}} (H : X ≃ₜ Y) (x : X) (n : ℕ) (c : Homology ℚ X n) :
    relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H x)
      (localOrientation X n c x) =
      localOrientation Y n (homologyMap ℚ n (TopCat.ofHom ⟨H, H.continuous⟩) c) (H x) := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
      (pointComplementHomeomorphPairMap H x))
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h c

end HodgeLean.Foundations.QuotientDuality
