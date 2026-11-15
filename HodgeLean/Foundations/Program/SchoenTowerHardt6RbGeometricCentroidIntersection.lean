import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidChainReindex
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidRestriction

/-! Centroid-chain intersection identities in a geometric base simplex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_geometric_centroid_chain_intersection {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (S : Finset E) (hS : AffineIndependent ℝ (fun i : S => i.val))
    (C D : Finset (Finset E))
    (hsubC : ∀ T ∈ C, T ⊆ S) (hsubD : ∀ T ∈ D, T ⊆ S)
    (hneC : ∀ T ∈ C, T.Nonempty) (hneD : ∀ T ∈ D, T.Nonempty)
    (hC : ∀ T ∈ C, ∀ U ∈ C, T ⊆ U ∨ U ⊆ T)
    (hD : ∀ T ∈ D, ∀ U ∈ D, T ⊆ U ∨ U ⊆ T) :
    convexHull ℝ ((fun T : Finset E => T.centroid ℝ id) '' (↑C : Set (Finset E))) ∩
        convexHull ℝ ((fun T : Finset E => T.centroid ℝ id) '' (↑D : Set (Finset E))) =
      convexHull ℝ (((fun T : Finset E => T.centroid ℝ id) '' (↑C : Set (Finset E))) ∩
        ((fun T : Finset E => T.centroid ℝ id) '' (↑D : Set (Finset E)))) := by
  classical
  obtain ⟨hneF, hchainF, hF⟩ := s2v_hardt6rb_centroid_chain_reindex S C hsubC hneC hC
  obtain ⟨hneG, hchainG, hG⟩ := s2v_hardt6rb_centroid_chain_reindex S D hsubD hneD hD
  have hi := s2v_hardt6rb_centroid_chain_intersection (fun i : S => i.val) hS
    (C.image (fun T => Finset.univ.filter (fun i : S => i.val ∈ T)))
    (D.image (fun T => Finset.univ.filter (fun i : S => i.val ∈ T)))
    hneF hneG hchainF hchainG
  simpa only [hF, hG] using hi

end HodgeLean.Foundations.Program
