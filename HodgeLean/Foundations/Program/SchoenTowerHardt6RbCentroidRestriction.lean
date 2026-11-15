import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidChainIntersection

/-! Exact restriction of a centroid-chain simplex to an original base face. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_chain_restriction {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]
    (v : ι → E) (hv : AffineIndependent ℝ v) (C : Finset (Finset ι))
    (hne : ∀ T ∈ C, T.Nonempty)
    (hchain : ∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S) (I : Finset ι) :
    convexHull ℝ ((fun T => T.centroid ℝ v) '' (↑C : Set (Finset ι))) ∩
        convexHull ℝ (v '' (↑I : Set ι)) =
      convexHull ℝ ((fun T => T.centroid ℝ v) ''
        (↑(C.filter (fun T => T ⊆ I)) : Set (Finset ι))) := by
  classical
  apply Set.Subset.antisymm
  · rintro p ⟨hpC, hpI⟩
    rw [← Finset.coe_image] at hpC
    obtain ⟨a, ha, hasum, hap⟩ := Finset.mem_convexHull'.mp hpC
    have hi := (s2v_hardt6rb_centroid_chain_independent v hv C hne hchain).injOn
    rw [Finset.sum_image (fun S hS T hT he => hi hS hT he)] at hasum hap
    have haC : ∀ T ∈ C, 0 ≤ a (T.centroid ℝ v) :=
      fun T hT => ha _ (Finset.mem_image.mpr ⟨T, hT, rfl⟩)
    obtain ⟨_, hbsum, hbpoint⟩ := s2v_hardt6rb_centroid_mixture_weights v C hne
      (fun T => a (T.centroid ℝ v)) haC hasum
    let b : ι → ℝ := fun i =>
      ∑ T ∈ C, if i ∈ T then a (T.centroid ℝ v) * (T.card : ℝ)⁻¹ else 0
    have hbp : (∑ i, b i • v i) = p := hbpoint.trans hap
    have hbi : (∑ i, b i • v i) ∈ convexHull ℝ (v '' (↑I : Set ι)) := hbp.symm ▸ hpI
    have hzero := s2v_hardt6rb_face_weight_support v hv I b hbsum hbi
    have hsub (T : Finset ι) (hT : T ∈ C) (hapos : a (T.centroid ℝ v) ≠ 0) : T ⊆ I := by
      intro i hiT
      by_contra hiI
      have hcard : 0 < (T.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr (hne T hT)
      have hpos : 0 < a (T.centroid ℝ v) * (T.card : ℝ)⁻¹ :=
        mul_pos (lt_of_le_of_ne (haC T hT) hapos.symm) (inv_pos.mpr hcard)
      have hn (U : Finset ι) (hU : U ∈ C) :
          0 ≤ if i ∈ U then a (U.centroid ℝ v) * (U.card : ℝ)⁻¹ else 0 := by
        split_ifs
        · exact mul_nonneg (haC U hU) (inv_nonneg.mpr (Nat.cast_nonneg _))
        · exact le_rfl
      have hle : a (T.centroid ℝ v) * (T.card : ℝ)⁻¹ ≤ b i := by
        have h := Finset.single_le_sum hn hT
        simpa only [hiT, ite_true] using h
      rw [hzero i hiI] at hle
      linarith
    have hsum : (∑ T : C, a (T.val.centroid ℝ v)) = 1 := by
      rw [Finset.univ_eq_attach, Finset.sum_attach C (fun T : Finset ι => a (T.centroid ℝ v))]
      exact hasum
    let w : stdSimplex ℝ C := ⟨(fun T => a (T.val.centroid ℝ v)),
      (fun T => haC T.val T.property), hsum⟩
    have hpoint : (∑ T : C, w.val T • T.val.centroid ℝ v) = p := by
      change (∑ T : C, a (T.val.centroid ℝ v) • T.val.centroid ℝ v) = p
      rw [Finset.univ_eq_attach, Finset.sum_attach C
        (fun T : Finset ι => a (T.centroid ℝ v) • T.centroid ℝ v)]
      exact hap
    rw [← hpoint]
    apply s2v_hardt6rb_supported_convexHull (fun T : C => T.val.centroid ℝ v) w
    intro T hT
    exact ⟨T.val, Finset.mem_filter.mpr ⟨T.property, hsub T.val T.property hT⟩, rfl⟩
  · apply Set.subset_inter
    · apply convexHull_mono
      rintro x ⟨T, hT, rfl⟩
      exact ⟨T, (Finset.mem_filter.mp hT).1, rfl⟩
    · apply convexHull_min
      · rintro x ⟨T, hT, rfl⟩
        obtain ⟨hTC, hTI⟩ := Finset.mem_filter.mp hT
        exact (s2v_hardt6rb_centroid_mem_face_iff v hv T I (hne T hTC)).mpr hTI
      · exact convex_convexHull ℝ _

end HodgeLean.Foundations.Program
