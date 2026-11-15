import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismRestriction
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismIndependence

/-! Restriction to a base face for every face of a staircase simplex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_prism_subface_restriction {E : Type*}
    [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (v : Fin (m + 1) → E) (hv : AffineIndependent ℝ v)
    (l u : Fin (m + 1) → ℝ) (j : Fin (m + 1))
    (I : Finset (Fin (m + 1))) (s : Finset (E × ℝ))
    (hs : (↑s : Set (E × ℝ)) ⊆
      (((fun i => (v i, l i)) '' {i | j ≤ i}) ∪
        ((fun i => (v i, u i)) '' {i | i ≤ j}))) :
    convexHull ℝ (↑s : Set (E × ℝ)) ∩
        Prod.fst ⁻¹' convexHull ℝ (v '' (↑I : Set _)) =
      convexHull ℝ ((↑s : Set (E × ℝ)) ∩
        Prod.fst ⁻¹' (v '' (↑I : Set _))) := by
  classical
  let S : Set (E × ℝ) :=
    (((fun i => (v i, l i)) '' {i | j ≤ i}) ∪
      ((fun i => (v i, u i)) '' {i | i ≤ j}))
  have hS : S.Finite :=
    ((Set.toFinite {i : Fin (m + 1) | j ≤ i}).image _).union
      ((Set.toFinite {i : Fin (m + 1) | i ≤ j}).image _)
  let T := hS.toFinset
  let R := s.filter (fun p => p.1 ∈ v '' (↑I : Set _))
  have hsT : s ⊆ T := fun p hp => hS.mem_toFinset.mpr (hs hp)
  have hind : AffineIndependent ℝ (fun p : T => (p : E × ℝ)) := by
    let e : T ↪ S :=
      ⟨fun p => ⟨p.val, hS.mem_toFinset.mp p.property⟩,
        fun a b h => Subtype.ext (congrArg (fun p : S => p.val) h)⟩
    exact (s2v_hardt6rb_prism_staircase_independent v hv l u j).comp_embedding e
  have hfull := s2v_hardt6rb_prism_face_restriction v hv l u j I
  have hR : (↑R : Set (E × ℝ)) =
      (↑s : Set (E × ℝ)) ∩ Prod.fst ⁻¹' (v '' (↑I : Set _)) := by
    ext p
    simp only [R, Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff,
      Set.mem_preimage]
  apply Set.Subset.antisymm
  · rintro p ⟨hps, hpI⟩
    have hpS : p ∈ convexHull ℝ S := convexHull_mono hs hps
    have hpR : p ∈ convexHull ℝ (S ∩ Prod.fst ⁻¹' (v '' (↑I : Set _))) := by
      rw [← hfull]
      exact ⟨hpS, hpI⟩
    let Q := T.filter (fun p => p.1 ∈ v '' (↑I : Set _))
    have hQ : (↑Q : Set (E × ℝ)) = S ∩ Prod.fst ⁻¹' (v '' (↑I : Set _)) := by
      ext q
      simp only [Q, T, Finset.mem_coe, Finset.mem_filter, hS.mem_toFinset,
        Set.mem_inter_iff, Set.mem_preimage]
    rw [← hQ] at hpR
    have hmem : p ∈ convexHull ℝ (↑s : Set (E × ℝ)) ∩
        convexHull ℝ (↑Q : Set (E × ℝ)) := ⟨hps, hpR⟩
    rw [← hind.convexHull_inter hsT (Finset.filter_subset _ _)] at hmem
    have he : s ∩ Q = R := by
      ext q
      simp only [Finset.mem_inter, Q, R, Finset.mem_filter]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hsT h.1, h.2⟩⟩
    change p ∈ convexHull ℝ ((↑s : Set (E × ℝ)) ∩ ↑Q) at hmem
    rw [← Finset.coe_inter, he, hR] at hmem
    exact hmem
  · apply Set.subset_inter (convexHull_mono Set.inter_subset_left)
    apply convexHull_min
    · rintro p ⟨_, hp⟩
      exact subset_convexHull ℝ _ hp
    · exact (convex_convexHull ℝ _).linear_preimage (LinearMap.fst ℝ E ℝ)

end HodgeLean.Foundations.Program
