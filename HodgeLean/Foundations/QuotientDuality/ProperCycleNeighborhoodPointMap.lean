import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenEmbeddingLocalHomology
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodEmbedding
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ComplexNeighborhoodOrientation

/-! # Actual point-complement maps of embeddings with neighborhood image
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual embedding with neighborhood image induces a bijection through its literal point-complement pair map.
Source: Hatcher, Algebraic Topology, section 2.2, point excision through open image neighborhoods.
HC no distance; AV milestone no distance. -/
lemma properCycle_neighborhood_point_map_bijective
    {X Y : TopCat.{0}} [T1Space X] [T1Space Y] (f : X ⟶ Y) (hf : IsEmbedding f)
    (x : X) (hnb : Set.range f ∈ 𝓝 (f x)) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n (imagePointPairMap f hf.injective x)) := by
  let V : Opens Y := ⟨interior (Set.range f), isOpen_interior⟩
  have hxV : f x ∈ V := mem_interior_iff_mem_nhds.mpr hnb
  let U : Opens X := ⟨f ⁻¹' V, V.isOpen.preimage f.hom.continuous⟩
  let w : U := ⟨x, hxV⟩
  let e : U ≃ₜ V := hf.homeomorphOfSubsetRange
    (show (V : Set Y) ⊆ Set.range f from interior_subset)
  let i : TopCat.of U ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hi : IsOpenEmbedding i := U.isOpen.isOpenEmbedding_subtypeVal
  let g : TopCat.of U ⟶ Y := TopCat.ofHom ⟨fun u => f u.val,
    f.hom.continuous.comp continuous_subtype_val⟩
  have hg : IsOpenEmbedding g := V.isOpen.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  let a : pointComplementPair w ⟶ pointComplementPair x := imagePointPairMap i hi.injective w
  let b := imagePointPairMap f hf.injective x
  let d : pointComplementPair w ⟶ pointComplementPair (f x) := imagePointPairMap g hg.injective w
  have hd : a ≫ b = d := by ext z : 2 <;> rfl
  have ha : Function.Bijective (relativeHomologyMap ℚ n a) :=
    properCycle_open_embedding_local_homology_bijective i hi w n
  have hD : Function.Bijective (relativeHomologyMap ℚ n d) :=
    properCycle_open_embedding_local_homology_bijective g hg w n
  have hcomp : Function.Bijective ((relativeHomologyMap ℚ n b) ∘ (relativeHomologyMap ℚ n a)) := by
    change Function.Bijective ((relativeHomologyMap ℚ n b).comp (relativeHomologyMap ℚ n a))
    rw [← relativeHomologyMap_comp, hd]
    exact hD
  exact (Function.Bijective.of_comp_iff (relativeHomologyMap ℚ n b) ha).mp hcomp

end HodgeLean.Foundations.QuotientDuality
