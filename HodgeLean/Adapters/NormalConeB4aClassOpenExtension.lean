import HodgeLean.Adapters.NormalConeB4aClassExtension
import HodgeLean.Adapters.NormalConeB4aClassDetection
import HodgeConjecture.Definitions.AlgebraicTopology.Support.NeighborhoodPairImage

/-! # Detecting classes after boundary removal on an open subset

Route: apply boundary extension in the open subspace and transport its
restriction map through the natural inclusions of neighborhood pairs.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace Topology

set_option backward.isDefEq.respectTransparency false in
/-- Boundary vanishing in the two extension degrees detects a relative class
on any ambient open from its restriction away from the boundary. -/
theorem a3b4a_classRelative_eq_zero_of_boundary_restriction
    (X : TopCat.{0}) [T2Space X] (S B : Closeds X) (hBS : B ≤ S)
    (W : Opens X) [∀ V : Opens W, ParacompactSpace V] (n : ℕ)
    (hzero : ∀ j ∈ ({n, n + 1} : Finset ℕ), IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (W : Set X) B) j))
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (W : Set X) S) n)
    (ha : relativeCohomologyMap ℚ n
      (neighborhoodSupportInclusionPairMap
        (show (W ⊓ B.compl : Opens X) ≤ W from inf_le_left) (S : Set X)) a = 0) : a = 0 := by
  let Y := TopCat.of W
  let f : Y → X := Subtype.val
  have hf : IsOpenEmbedding f := W.isOpen.isOpenEmbedding_subtypeVal
  let S' : Closeds Y := S.preimage hf.continuous
  let B' : Closeds Y := B.preimage hf.continuous
  have hzero' (j : ℕ) (hj : j ∈ ({n, n + 1} : Finset ℕ)) : IsZero
      (RelativeCohomology ℚ (neighborhoodSupportComplementPair (Set.univ : Set Y) B') j) := by
    have himage : f '' (Set.univ : Set Y) = (W : Set X) := by
      ext x
      simp [f, Y]
    have hi : IsZero (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (f '' (Set.univ : Set Y)) B) j) := by
      rw [himage]
      exact hzero j hj
    exact hi.of_iso (neighborhoodSupportPairImageCohomologyIso f hf.isEmbedding
      Set.univ B' B (fun _ _ => Iff.rfl) j).symm
  apply (a3b4a_classLocal_restrict_univ_bijective (S' : Set Y) n).1
  apply (a3b4a_classRelative_restriction_bijective_of_boundary_vanishing Y S' B'
    (fun x hx => hBS hx) n hzero').1
  rw [map_zero, map_zero, a3b4a_classLocal_restriction_comp]
  let F : neighborhoodSupportComplementPair (B'.compl : Set Y) S' ⟶
      neighborhoodSupportComplementPair ((W ⊓ B.compl : Opens X) : Set X) S :=
    TopPair.ofSubsetHom
      (TopCat.ofHom ⟨fun x => ⟨(x.1 : W).1, (x.1 : W).2, x.2⟩,
        (continuous_subtype_val.comp
          (show Continuous (fun x : B'.compl => (x.1 : W)) from continuous_subtype_val)).subtype_mk _⟩)
      (fun x hx => hx)
  have hp : F ≫ neighborhoodSupportInclusionPairMap
      (show (W ⊓ B.compl : Opens X) ≤ W from inf_le_left) (S : Set X) =
      a3b4_neighborhoodPairMap (B'.compl : Set Y) (S' : Set Y) := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext x
      rfl
    · ext x
      rfl
  rw [← hp, relativeCohomologyMap_comp, LinearMap.comp_apply]
  exact (congrArg (relativeCohomologyMap ℚ n F) ha).trans (map_zero _)

end HodgeLean.Adapters
