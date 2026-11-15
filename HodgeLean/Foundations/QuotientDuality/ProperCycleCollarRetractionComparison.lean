import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarTrackNeighborhood

/-! # Actual retraction comparison on a common open support neighborhood
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Retractions from two actual collars are homotopic on a common original support neighborhood when one of their retained deformations fixes the support.
Source: Hatcher, Algebraic Topology, section 0, neighborhood deformation retractions; the compact-parameter tube lemma.
HC no distance; AV milestone no distance. -/
lemma properCycle_support_collar_common_retractions
    {X : TopCat.{0}} {S : Set X} (C D : ProperCycleSupportCollar X S)
    (hfixed : ∀ (t : unitInterval) (s : TopCat.of S),
      C.deformation (t, C.inclusion s) = C.inclusion s) :
    ∃ V : Set X, IsOpen V ∧ S ⊆ V ∧
      ∃ (hVC : V ⊆ C.neighborhood) (hVD : V ⊆ D.neighborhood),
        Nonempty (TopCat.Homotopy
          (TopPair.Hom.fst (neighborhoodSupportInclusionPairMap hVD S) ≫ D.retraction)
          (TopPair.Hom.fst (neighborhoodSupportInclusionPairMap hVC S) ≫ C.retraction)) := by
  obtain ⟨V, hV, hSV, hVC, htrack⟩ := properCycle_support_collar_track_neighborhood
    C hfixed D.neighborhood D.isOpen D.contains
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
    TopPair.Hom.fst (neighborhoodSupportInclusionPairMap hVD S)
  let J : TopCat.Homotopy (g ≫ D.retraction) (f ≫ C.retraction) :=
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
            htrack v.val v.property 1⟩ : D.neighborhood) = D.inclusion s := by
          apply Subtype.ext
          calc
            _ = (C.inclusion s : X) := congrArg (fun u : C.neighborhood => (u : X))
              (C.deformation.map_one_left ⟨v.val, hVC v.property⟩)
            _ = (s : X) := ConcreteCategory.congr_hom C.inclusion_factor s
            _ = (D.inclusion s : X) := (ConcreteCategory.congr_hom D.inclusion_factor s).symm
        change D.retraction _ = s
        rw [he]
        exact ConcreteCategory.congr_hom D.inclusion_retraction s }
  exact ⟨V, hV, hSV, hVC, hVD, ⟨J⟩⟩

end HodgeLean.Foundations.QuotientDuality
