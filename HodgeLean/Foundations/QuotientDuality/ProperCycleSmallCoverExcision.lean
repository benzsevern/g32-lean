import HodgeLean.Foundations.QuotientDuality.ProperCycleSmallCoverSubspace
import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexQuasiIso

/-! # Actual relative small-chain excision for arbitrary open covers -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal inclusion of the actual cover-small subcomplex into the singular subcomplex of its union induces homology isomorphisms.
Source: Hatcher, Algebraic Topology, section 2.2, open-cover subdivision.
HC no distance; AV milestone no distance. -/
lemma properCycle_small_cover_inclusion_quasiIso
    {I : Type} (X : TopCat.{0}) (U : I → Set X) (S : Set X)
    (hUo : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = S) :
    QuasiIso (SSet.chainComplexMap (SSet.Subcomplex.homOfLE
      (properCycle_small_cover_le_subset X U S
        (fun i => (Set.subset_iUnion U i).trans hcover.le))) (ModuleCat.of ℚ ℚ)) := by
  let hUS : ∀ i, U i ⊆ S := fun i => (Set.subset_iUnion U i).trans hcover.le
  let V : I → Set S := fun i => Subtype.val ⁻¹' U i
  let A := coverSmallSingularSubcomplex (TopCat.of S) V
  let B := coverSmallSingularSubcomplex X U
  let C := (SSet.chainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
  let eA := properCycle_small_cover_subspace_iso X U S hUS
  let eS := subsetSingularIso X S
  let j := SSet.Subcomplex.homOfLE (properCycle_small_cover_le_subset X U S hUS)
  have hs : eA.hom ≫ j = A.ι ≫ eS.hom := by
    apply (cancel_mono (subsetSingularSubcomplex X S).ι).mp
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι,
      properCycle_small_cover_subspace_iso_inclusion, Category.assoc]
    rfl
  have hVo : ∀ i, IsOpen (V i) := fun i => (hUo i).preimage continuous_subtype_val
  have hVc : ⋃ i, V i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x.val ∈ ⋃ i, U i := hcover.symm ▸ x.property
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  let e := coverSmallRationalChainHomotopyEquiv_of_openCover (TopCat.of S) V hVo hVc
  letI : QuasiIso (C.map A.ι) := by
    have he := e.quasiIso_hom
    rw [coverSmallRationalChainHomotopyEquiv_of_openCover_hom] at he
    exact he
  letI : QuasiIso (C.map eA.hom ≫ C.map j) := by
    rw [← C.map_comp, hs, C.map_comp]
    infer_instance
  exact quasiIso_of_comp_left (C.map eA.hom) (C.map j)

/-- Killing the actual cover-small chains computes the original ambient relative homology of their union.
Source: Hatcher, Algebraic Topology, section 2.2, relative open-cover subdivision.
HC no distance; AV milestone no distance. -/
lemma properCycle_small_cover_quotient_quasiIso
    {I : Type} (X : TopCat.{0}) (U : I → Set X) (S : Set X)
    (hUo : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = S) :
    QuasiIso (properCycle_subcomplex_quotient_map
      (properCycle_small_cover_le_subset X U S
        (fun i => (Set.subset_iUnion U i).trans hcover.le))) :=
  properCycle_subcomplex_quotient_quasiIso _
    (properCycle_small_cover_inclusion_quasiIso X U S hUo hcover)

/-- The actual open-cover quotient identifies with the original relative homology through the literal subspace chain comparison.
Source: Hatcher, Algebraic Topology, section 2.2, relative open-cover subdivision.
HC no distance; AV milestone no distance. -/
def properCycle_small_cover_relative_homology_iso
    {I : Type} (X : TopCat.{0}) (U : I → Set X) (S : Set X)
    (hUo : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = S) (n : ℕ) :
    (properCycle_subcomplex_quotient (coverSmallSingularSubcomplex X U)).homology n ≅
      RelativeHomology ℚ (TopPair.ofSubset (X := X) S) n := by
  let j := properCycle_subcomplex_quotient_map
    (properCycle_small_cover_le_subset X U S
      (fun i => (Set.subset_iUnion U i).trans hcover.le))
  letI : QuasiIso j := properCycle_small_cover_quotient_quasiIso X U S hUo hcover
  exact asIso (HomologicalComplex.homologyMap j n) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).mapIso
      (properCycle_subset_subcomplex_relative_iso X S)

/-- Refining actual open small-chain covers of the same subspace preserves their ambient relative homology through the literal quotient map.
Source: Hatcher, Algebraic Topology, section 2.2, subdivision under refinement.
HC no distance; AV milestone no distance. -/
lemma properCycle_small_cover_refinement_quotient_quasiIso
    {I J : Type} (X : TopCat.{0}) (U : I → Set X) (V : J → Set X) (S : Set X)
    (hUo : ∀ i, IsOpen (U i)) (hVo : ∀ j, IsOpen (V j))
    (hUc : ⋃ i, U i = S) (hVc : ⋃ j, V j = S)
    (hUV : coverSmallSingularSubcomplex X U ≤ coverSmallSingularSubcomplex X V) :
    QuasiIso (properCycle_subcomplex_quotient_map hUV) := by
  let hVS := properCycle_small_cover_le_subset X V S
    (fun j => (Set.subset_iUnion V j).trans hVc.le)
  letI : QuasiIso (properCycle_subcomplex_quotient_map hVS) :=
    properCycle_small_cover_quotient_quasiIso X V S hVo hVc
  letI : QuasiIso (properCycle_subcomplex_quotient_map hUV ≫
      properCycle_subcomplex_quotient_map hVS) := by
    rw [properCycle_subcomplex_quotient_map_comp]
    exact properCycle_small_cover_quotient_quasiIso X U S hUo hUc
  exact quasiIso_of_comp_right (properCycle_subcomplex_quotient_map hUV)
    (properCycle_subcomplex_quotient_map hVS)

/-- Adjoining a fixed actual open subspace to an open small-chain cover preserves its literal relative quotient comparison.
Source: Hatcher, Algebraic Topology, section 2.2, relative open-cover subdivision.
HC no distance; AV milestone no distance. -/
lemma properCycle_fixed_open_cover_quotient_quasiIso
    {I : Type} (X : TopCat.{0}) (A : Set X) (U : I → Set X) (S : Set X)
    (hAo : IsOpen A) (hUo : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = S) :
    QuasiIso (properCycle_subcomplex_quotient_map (sup_le_sup_left
      (properCycle_small_cover_le_subset X U S
        (fun i => (Set.subset_iUnion U i).trans hcover.le)) (subsetSingularSubcomplex X A))) := by
  let V : Option I → Set X := fun i => i.elim A U
  let W : Option Unit → Set X := fun i => i.elim A (fun _ => S)
  have hSo : IsOpen S := hcover ▸ isOpen_iUnion hUo
  have hVo : ∀ i, IsOpen (V i) := by
    rintro (_ | i)
    · exact hAo
    · exact hUo i
  have hWo : ∀ i, IsOpen (W i) := by
    rintro (_ | i)
    · exact hAo
    · exact hSo
  have hVc : ⋃ i, V i = A ∪ S := by
    simpa only [V, Set.iUnion_option, Option.elim_none, Option.elim_some] using
      congrArg (fun T : Set X => A ∪ T) hcover
  have hWc : ⋃ i, W i = A ∪ S := by
    rw [Set.iUnion_option]
    change A ∪ (⋃ _ : Unit, S) = A ∪ S
    congr 1
    ext x
    simp only [Set.mem_iUnion, exists_const]
  have hV : coverSmallSingularSubcomplex X V = subsetSingularSubcomplex X A ⊔
      coverSmallSingularSubcomplex X U := by
    simp [coverSmallSingularSubcomplex, V, iSup_option, subsetSingularSubcomplex]
  have hW : coverSmallSingularSubcomplex X W = subsetSingularSubcomplex X A ⊔
      subsetSingularSubcomplex X S := by
    simp [coverSmallSingularSubcomplex, W, iSup_option, subsetSingularSubcomplex]
  have hVW : coverSmallSingularSubcomplex X V ≤ coverSmallSingularSubcomplex X W := by
    rw [hV, hW]
    exact sup_le_sup_left (properCycle_small_cover_le_subset X U S
      (fun i => (Set.subset_iUnion U i).trans hcover.le)) _
  have h := properCycle_small_cover_refinement_quotient_quasiIso X V W (A ∪ S) hVo hWo hVc hWc hVW
  letI := h
  have hq : QuasiIso ((properCycle_subcomplex_quotient_iso_of_eq hV).inv ≫
      properCycle_subcomplex_quotient_map hVW ≫
      (properCycle_subcomplex_quotient_iso_of_eq hW).hom) := by infer_instance
  dsimp only [properCycle_subcomplex_quotient_iso_of_eq] at hq
  rw [properCycle_subcomplex_quotient_map_comp, properCycle_subcomplex_quotient_map_comp] at hq
  exact hq

end HodgeLean.Foundations.QuotientDuality
