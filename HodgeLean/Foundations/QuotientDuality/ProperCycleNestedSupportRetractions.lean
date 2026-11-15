import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarTrackNeighborhood

/-! # Actual retraction comparison for nested original supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Retractions for nested original supports commute with the literal support inclusion on a common original neighborhood, up to an actual homotopy.
Source: Hatcher, Algebraic Topology, section 0, neighborhood deformation retractions; the compact-parameter tube lemma.
HC no distance; AV milestone no distance. -/
lemma properCycle_nested_support_common_retractions
    {X : TopCat.{0}} {S T : Set X} (hST : S ⊆ T)
    (C : ProperCycleSupportCollar X S) (D : ProperCycleSupportCollar X T)
    (hfixed : ∀ (t : unitInterval) (s : TopCat.of S),
      C.deformation (t, C.inclusion s) = C.inclusion s) :
    ∃ V : Set X, IsOpen V ∧ S ⊆ V ∧
      ∃ (hVC : V ⊆ C.neighborhood) (hVD : V ⊆ D.neighborhood),
        Nonempty (TopCat.Homotopy
          ((TopPair.Hom.fst (neighborhoodSupportInclusionPairMap hVD T) :
            TopCat.of V ⟶ TopCat.of D.neighborhood) ≫ D.retraction)
          ((TopPair.Hom.fst (neighborhoodSupportInclusionPairMap hVC S) :
            TopCat.of V ⟶ TopCat.of C.neighborhood) ≫ C.retraction ≫
            (TopCat.ofHom (ContinuousMap.inclusion hST) : TopCat.of S ⟶ TopCat.of T))) := by
  obtain ⟨V, hV, hSV, hVC, htrack⟩ := properCycle_support_collar_track_neighborhood
    C hfixed D.neighborhood D.isOpen (hST.trans D.contains)
  have hVD : V ⊆ D.neighborhood := by
    intro v hv
    have ht := htrack v hv 0
    have he := congrArg (fun u : C.neighborhood => (u : X))
      (C.deformation.map_zero_left ⟨v, hVC hv⟩)
    change (C.deformation (0, ⟨v, hVC hv⟩) : X) = v at he
    rwa [he] at ht
  let f : TopCat.of V ⟶ TopCat.of C.neighborhood :=
    TopPair.Hom.fst (neighborhoodSupportInclusionPairMap hVC S)
  let g : TopCat.of V ⟶ TopCat.of D.neighborhood :=
    TopPair.Hom.fst (neighborhoodSupportInclusionPairMap hVD T)
  let st : TopCat.of S ⟶ TopCat.of T := TopCat.ofHom (ContinuousMap.inclusion hST)
  let J : TopCat.Homotopy (g ≫ D.retraction) (f ≫ C.retraction ≫ st) :=
    { toFun := fun tv => D.retraction
        ⟨(C.deformation (tv.1, ⟨tv.2.val, hVC tv.2.property⟩) : X),
          htrack tv.2.val tv.2.property tv.1⟩
      continuous_toFun := by
        apply Continuous.comp D.retraction.hom.continuous
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp (C.deformation.continuous.comp
          (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)))
      map_zero_left := by
        intro v
        apply congrArg D.retraction
        apply Subtype.ext
        exact congrArg (fun u : C.neighborhood => (u : X))
          (C.deformation.map_zero_left ⟨v.val, hVC v.property⟩)
      map_one_left := by
        intro v
        let s := C.retraction (f v)
        have he : (⟨(C.deformation (1, ⟨v.val, hVC v.property⟩) : X),
            htrack v.val v.property 1⟩ : D.neighborhood) = D.inclusion (st s) := by
          apply Subtype.ext
          calc
            _ = (C.inclusion s : X) := congrArg (fun u : C.neighborhood => (u : X))
              (C.deformation.map_one_left ⟨v.val, hVC v.property⟩)
            _ = (s : X) := ConcreteCategory.congr_hom C.inclusion_factor s
            _ = (D.inclusion (st s) : X) :=
              (ConcreteCategory.congr_hom D.inclusion_factor (st s)).symm
        change D.retraction _ = st s
        rw [he]
        exact ConcreteCategory.congr_hom D.inclusion_retraction (st s) }
  exact ⟨V, hV, hSV, hVC, hVD, ⟨J⟩⟩

end HodgeLean.Foundations.QuotientDuality
