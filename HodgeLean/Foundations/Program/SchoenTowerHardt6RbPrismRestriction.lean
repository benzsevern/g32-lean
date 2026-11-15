import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceWeights

/-! Restriction of an ordered prism simplex to an arbitrary base face. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_prism_face_restriction {E : Type*}
    [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (v : Fin (m + 1) → E) (hv : AffineIndependent ℝ v)
    (l u : Fin (m + 1) → ℝ) (j : Fin (m + 1))
    (I : Finset (Fin (m + 1))) :
    let S := ((fun i => (v i, l i)) '' {i | j ≤ i}) ∪
      ((fun i => (v i, u i)) '' {i | i ≤ j})
    convexHull ℝ S ∩ Prod.fst ⁻¹' convexHull ℝ (v '' (↑I : Set _)) =
      convexHull ℝ (S ∩ Prod.fst ⁻¹' (v '' (↑I : Set _))) := by
  classical
  intro S
  apply Set.Subset.antisymm
  · rintro p ⟨hp, hpI⟩
    obtain ⟨lo, up, hpos, hsum, hbase, hheight, hlo, hup⟩ :=
      s2v_hardt6rb_prism_point_weights v l u j p hp
    have hsupp := s2v_hardt6rb_face_weight_support v hv I
      (fun i => lo i + up i) hsum (hbase.symm ▸ hpI)
    have hloI (i) (hne : lo i ≠ 0) : i ∈ I := by
      by_contra hi
      have hz := hsupp i hi
      exact hne (by linarith [(hpos i).1, (hpos i).2])
    have hupI (i) (hne : up i ≠ 0) : i ∈ I := by
      by_contra hi
      have hz := hsupp i hi
      exact hne (by linarith [(hpos i).1, (hpos i).2])
    have hlo_mem (i) (hne : lo i ≠ 0) :
        (v i, l i) ∈ S ∩ Prod.fst ⁻¹' (v '' (↑I : Set _)) :=
      ⟨Or.inl ⟨i, le_of_not_gt (fun hi => hne (hlo i hi)), rfl⟩,
        ⟨i, hloI i hne, rfl⟩⟩
    have hup_mem (i) (hne : up i ≠ 0) :
        (v i, u i) ∈ S ∩ Prod.fst ⁻¹' (v '' (↑I : Set _)) :=
      ⟨Or.inr ⟨i, le_of_not_gt (fun hi => hne (hup i hi)), rfl⟩,
        ⟨i, hupI i hne, rfl⟩⟩
    obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (show (∑ i, (lo i + up i)) ≠ 0 by rw [hsum]; exact one_ne_zero)
    have hdefault : ∃ q, q ∈ S ∩ Prod.fst ⁻¹' (v '' (↑I : Set _)) := by
      by_cases hla : lo a = 0
      · exact ⟨(v a, u a), hup_mem a (by simpa only [hla, zero_add] using ha)⟩
      · exact ⟨(v a, l a), hlo_mem a hla⟩
    obtain ⟨q, hq⟩ := hdefault
    let zlo : Fin (m + 1) → E × ℝ := fun i => if lo i = 0 then q else (v i, l i)
    let zup : Fin (m + 1) → E × ℝ := fun i => if up i = 0 then q else (v i, u i)
    have hlo_eq (i) : lo i • zlo i = lo i • (v i, l i) := by
      by_cases hi : lo i = 0 <;> simp only [zlo, hi, ite_true, ite_false, zero_smul]
    have hup_eq (i) : up i • zup i = up i • (v i, u i) := by
      by_cases hi : up i = 0 <;> simp only [zup, hi, ite_true, ite_false, zero_smul]
    apply mem_convexHull_of_exists_fintype (Sum.elim lo up) (Sum.elim zlo zup)
    · intro i
      cases i with
      | inl i => exact (hpos i).1
      | inr i => exact (hpos i).2
    · rw [Fintype.sum_sum_type]
      simpa only [Sum.elim_inl, Sum.elim_inr, ← Finset.sum_add_distrib] using hsum
    · intro i
      cases i with
      | inl i =>
        dsimp only [Sum.elim_inl, zlo]
        split_ifs with hi
        · exact hq
        · exact hlo_mem i hi
      | inr i =>
        dsimp only [Sum.elim_inr, zup]
        split_ifs with hi
        · exact hq
        · exact hup_mem i hi
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, hlo_eq, hup_eq]
      apply Prod.ext
      · simp only [Prod.fst_add, Prod.fst_sum]
        change (∑ i, lo i • v i) + (∑ i, up i • v i) = p.1
        rw [← Finset.sum_add_distrib]
        simpa only [← add_smul] using hbase
      · simp only [Prod.snd_add, Prod.snd_sum]
        change (∑ i, lo i * l i) + (∑ i, up i * u i) = p.2
        simpa only [Finset.sum_add_distrib] using hheight
  · apply Set.subset_inter (convexHull_mono Set.inter_subset_left)
    apply convexHull_min
    · rintro p ⟨_, hp⟩
      exact subset_convexHull ℝ _ hp
    · exact (convex_convexHull ℝ _).linear_preimage (LinearMap.fst ℝ E ℝ)

end HodgeLean.Foundations.Program
