import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidSpan
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceChainMax

/-! Centroids of a finite chain of nonempty faces form a genuine geometric simplex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_chain_independent {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] (v : ι → E) (hv : AffineIndependent ℝ v)
    (C : Finset (Finset ι)) (hne : ∀ T ∈ C, T.Nonempty)
    (hchain : ∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S) :
    AffineIndepOn ℝ (fun T : Finset ι => T.centroid ℝ v) (↑C : Set (Finset ι)) := by
  classical
  revert hne hchain
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    intro hne hchain
    by_cases hC : C.Nonempty
    · obtain ⟨S, hS, hmax⟩ := s2v_hardt6rb_face_chain_max C hC hchain
      let R := C.erase S
      by_cases hR : R.Nonempty
      · have hRsub : R ⊆ C := Finset.erase_subset S C
        have hneR : ∀ T ∈ R, T.Nonempty := fun T hT => hne T (hRsub hT)
        have hchainR : ∀ T ∈ R, ∀ U ∈ R, T ⊆ U ∨ U ⊆ T :=
          fun T hT U hU => hchain T (hRsub hT) U (hRsub hU)
        obtain ⟨U, hU, hmaxR⟩ := s2v_hardt6rb_face_chain_max R hR hchainR
        have hUS : U ⊆ S := hmax U (hRsub hU)
        have hUne : U ≠ S := (Finset.mem_erase.mp hU).1
        have hSU : ¬ S ⊆ U := fun h => hUne (Finset.Subset.antisymm hUS h)
        have hcenters : (fun T : Finset ι => T.centroid ℝ v) '' (↑R : Set (Finset ι)) ⊆
            affineSpan ℝ (v '' (↑U : Set ι)) := by
          rintro x ⟨T, hT, rfl⟩
          exact (s2v_hardt6rb_centroid_mem_affineSpan_iff v hv T U (hneR T hT)).mpr (hmaxR T hT)
        have hspan : affineSpan ℝ ((fun T : Finset ι => T.centroid ℝ v) '' (↑R : Set (Finset ι))) ≤
            affineSpan ℝ (v '' (↑U : Set ι)) := affineSpan_le.mpr hcenters
        have hnot : S.centroid ℝ v ∉
            affineSpan ℝ ((fun T : Finset ι => T.centroid ℝ v) '' (↑R : Set (Finset ι))) := by
          intro hx
          exact hSU ((s2v_hardt6rb_centroid_mem_affineSpan_iff v hv S U (hne S hS)).mp (hspan hx))
        have hind := ih R (Finset.erase_ssubset hS) hneR hchainR
        have hi := hind.insert hnot
        simpa only [← Finset.coe_insert, R, Finset.insert_erase hS] using hi
      · have hRempty : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
        have hEq : C = {S} := by
          rw [← Finset.insert_erase hS]
          change insert S R = {S}
          rw [hRempty]
          rfl
        simpa only [hEq, Finset.coe_singleton] using
          (AffineIndepOn.singleton ℝ (fun T : Finset ι => T.centroid ℝ v) S)
    · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
      simp only [he, Finset.coe_empty, affineIndepOn_empty]

end HodgeLean.Foundations.Program
