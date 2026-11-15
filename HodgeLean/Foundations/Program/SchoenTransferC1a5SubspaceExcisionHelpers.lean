import HodgeLean.Foundations.Program.SchoenTransferC1a5SingularSubsetHelpers

/-! Relative open-cover excision for the actual integral chains of subspaces.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The singular set of a topological intersection identifies with the intersection of singular images.
Source: the actual subspace image isomorphism and singular image intersection formula. -/
def c1a5_singular_intersection_iso (X : TopCat.{0}) (U V : Set X) :
    TopCat.toSSet.obj (TopCat.of (U ∩ V : Set X)) ≅
      (SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X U)) ⊓
        SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X V))).toSSet :=
  c1a5_singular_subset_iso X (U ∩ V) ≪≫
    SSet.Subcomplex.eqToIso (c1a5_singular_subset_intersection X U V)

example (X : TopCat.{0}) (U V : Set X) := c1a5_singular_intersection_iso X U V

/-- The intersection isomorphism commutes with inclusion into the second subspace.
Source: the literal continuous subspace inclusions and the singular image identifications. -/
lemma c1a5_singular_intersection_iso_right (X : TopCat.{0}) (U V : Set X) :
    TopCat.toSSet.map (c1a5_subset_map X (Set.inter_subset_right : U ∩ V ⊆ V)) ≫
        (c1a5_singular_subset_iso X V).hom =
      (c1a5_singular_intersection_iso X U V).hom ≫
        SSet.Subcomplex.homOfLE (inf_le_right :
          SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X U)) ⊓
            SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X V)) ≤
          SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X V))) := by
  apply (cancel_mono (SSet.Subcomplex.range
    (TopCat.toSSet.map (topologicalSubsetInclusion X V))).ι).1
  simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι]
  ext n x
  rfl

/-- The intersection isomorphism commutes with inclusion into the first subspace.
Source: the literal continuous subspace inclusions and singular image identifications. -/
lemma c1a5_singular_intersection_iso_left (X : TopCat.{0}) (U V : Set X) :
    TopCat.toSSet.map (c1a5_subset_map X (Set.inter_subset_left : U ∩ V ⊆ U)) ≫
        (c1a5_singular_subset_iso X U).hom =
      (c1a5_singular_intersection_iso X U V).hom ≫
        SSet.Subcomplex.homOfLE (inf_le_left :
          SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X U)) ⊓
            SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X V)) ≤
          SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X U))) := by
  apply (cancel_mono (SSet.Subcomplex.range
    (TopCat.toSSet.map (topologicalSubsetInclusion X U))).ι).1
  simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι]
  ext n x
  rfl

/-- Binary open-cover excision for the literal singular chains of topological subspaces.
Source: Hatcher §2.1, Theorem 2.20, small-chain subdivision and quotient transport. -/
lemma c1a5_subspace_open_cover_excision (X : TopCat.{0}) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    QuasiIso (c1a5RelativeMap c1a5Chains
      (TopCat.toSSet.map (c1a5_subset_map X (Set.inter_subset_right : U ∩ V ⊆ V)))
      (TopCat.toSSet.map (topologicalSubsetInclusion X U))
      (TopCat.toSSet.map (c1a5_subset_map X (Set.inter_subset_left : U ∩ V ⊆ U)))
      (TopCat.toSSet.map (topologicalSubsetInclusion X V)) (by
        rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]; rfl)) := by
  let A := SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X U))
  let B := SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X V))
  let f := TopCat.toSSet.map (c1a5_subset_map X (Set.inter_subset_right : U ∩ V ⊆ V))
  let g := TopCat.toSSet.map (topologicalSubsetInclusion X U)
  let a := TopCat.toSSet.map (c1a5_subset_map X (Set.inter_subset_left : U ∩ V ⊆ U))
  let b := TopCat.toSSet.map (topologicalSubsetInclusion X V)
  let fi := SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)
  let ai := SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)
  let ei := (c1a5_singular_intersection_iso X U V).hom
  let eu := (c1a5_singular_subset_iso X U).hom
  let ev := (c1a5_singular_subset_iso X V).hom
  have hf : f ≫ ev = ei ≫ fi := c1a5_singular_intersection_iso_right X U V
  have ha : a ≫ eu = ei ≫ ai := c1a5_singular_intersection_iso_left X U V
  have hg : g ≫ 𝟙 _ = eu ≫ A.ι := by rfl
  have hb : b = ev ≫ B.ι := by rfl
  have w : f ≫ b = a ≫ g := by
    dsimp [f, a, g, b]
    rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]
    rfl
  let u := c1a5RelativeMap c1a5Chains f fi ei ev hf
  let v := c1a5RelativeMap c1a5Chains g A.ι eu (𝟙 _) hg
  let wi := c1a5RelativeMap c1a5Chains fi A.ι ai B.ι (by rfl)
  let w0 := c1a5RelativeMap c1a5Chains f g a b w
  have hm : Mono (c1a5_subset_map X (Set.inter_subset_right : U ∩ V ⊆ V)) :=
    (TopCat.mono_iff_injective _).2 (by
      intro x y h
      exact Subtype.ext (congrArg (fun z : TopCat.of V ↦ (z.val : X)) h))
  have hgm : Mono (topologicalSubsetInclusion X U) :=
    (TopCat.mono_iff_injective _).2 Subtype.val_injective
  have hu : QuasiIso u := by
    have := c1a5_chains_map_mono f
    have := c1a5_chains_map_mono fi
    exact c1a5_cokernel_comparison (c1a5Chains.map f) (c1a5Chains.map fi)
      (c1a5Chains.map ei) (c1a5Chains.map ev)
      (by rw [← c1a5Chains.map_comp, ← c1a5Chains.map_comp, hf]) inferInstance inferInstance
  have hv : QuasiIso v := by
    have := c1a5_chains_map_mono g
    have := c1a5_chains_map_mono A.ι
    exact c1a5_cokernel_comparison (c1a5Chains.map g) (c1a5Chains.map A.ι)
      (c1a5Chains.map eu) (c1a5Chains.map (𝟙 _))
      (by rw [← c1a5Chains.map_comp, ← c1a5Chains.map_comp, hg]) inferInstance inferInstance
  have hwi : QuasiIso wi := c1a5_binary_cover_relative_excision X U V hU hV hcover
  have he : u ≫ wi = w0 ≫ v := by
    apply (cancel_epi (cokernel.π (c1a5Chains.map f))).1
    simp only [u, wi, w0, v, c1a5RelativeMap, cokernel.map, cokernel.π_desc_assoc,
      cokernel.π_desc, Category.assoc, ← c1a5Chains.map_comp]
    rw [c1a5Chains.map_id, Category.id_comp, ← Category.assoc,
      ← c1a5Chains.map_comp, ← hb]
  have hc : QuasiIso (w0 ≫ v) := by
    rw [← he]
    have := hu
    have := hwi
    infer_instance
  have := hv
  have := hc
  exact quasiIso_of_comp_right w0 v

end HodgeLean.Foundations.Program
