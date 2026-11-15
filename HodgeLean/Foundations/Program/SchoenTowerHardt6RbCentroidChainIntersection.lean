import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidChain
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidMixture
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCommonChainSupport

/-! Common-face intersections of centroid-chain simplices over one independent base family. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_chain_intersection {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (v : ι → E) (hv : AffineIndependent ℝ v) (C D : Finset (Finset ι))
    (hneC : ∀ T ∈ C, T.Nonempty) (hneD : ∀ T ∈ D, T.Nonempty)
    (hC : ∀ S ∈ C, ∀ T ∈ C, S ⊆ T ∨ T ⊆ S)
    (hD : ∀ S ∈ D, ∀ T ∈ D, S ⊆ T ∨ T ⊆ S) :
    convexHull ℝ ((fun T => T.centroid ℝ v) '' (↑C : Set (Finset ι))) ∩
        convexHull ℝ ((fun T => T.centroid ℝ v) '' (↑D : Set (Finset ι))) =
      convexHull ℝ (((fun T => T.centroid ℝ v) '' (↑C : Set (Finset ι))) ∩
        ((fun T => T.centroid ℝ v) '' (↑D : Set (Finset ι)))) := by
  classical
  apply Set.Subset.antisymm ?_
    (Set.subset_inter (convexHull_mono Set.inter_subset_left) (convexHull_mono Set.inter_subset_right))
  rintro p ⟨hpC, hpD⟩
  rw [← Finset.coe_image] at hpC hpD
  obtain ⟨a, ha, hasum, hap⟩ := Finset.mem_convexHull'.mp hpC
  obtain ⟨b, hb, hbsum, hbp⟩ := Finset.mem_convexHull'.mp hpD
  have hiC := (s2v_hardt6rb_centroid_chain_independent v hv C hneC hC).injOn
  have hiD := (s2v_hardt6rb_centroid_chain_independent v hv D hneD hD).injOn
  rw [Finset.sum_image (fun S hS T hT he => hiC hS hT he)] at hasum hap
  rw [Finset.sum_image (fun S hS T hT he => hiD hS hT he)] at hbsum hbp
  have haC : ∀ T ∈ C, 0 ≤ a (T.centroid ℝ v) :=
    fun T hT => ha _ (Finset.mem_image.mpr ⟨T, hT, rfl⟩)
  have hbD : ∀ T ∈ D, 0 ≤ b (T.centroid ℝ v) :=
    fun T hT => hb _ (Finset.mem_image.mpr ⟨T, hT, rfl⟩)
  obtain ⟨_, hca, hcp⟩ := s2v_hardt6rb_centroid_mixture_weights v C hneC
    (fun T => a (T.centroid ℝ v)) haC hasum
  obtain ⟨_, hda, hdp⟩ := s2v_hardt6rb_centroid_mixture_weights v D hneD
    (fun T => b (T.centroid ℝ v)) hbD hbsum
  let a' : Finset ι → ℝ := fun T => a (T.centroid ℝ v) * (T.card : ℝ)⁻¹
  let b' : Finset ι → ℝ := fun T => b (T.centroid ℝ v) * (T.card : ℝ)⁻¹
  have ha' : ∀ T ∈ C, 0 ≤ a' T := fun T hT =>
    mul_nonneg (haC T hT) (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hb' : ∀ T ∈ D, 0 ≤ b' T := fun T hT =>
    mul_nonneg (hbD T hT) (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hbeta : ∀ i, (∑ T ∈ C, if i ∈ T then a' T else 0) =
      ∑ T ∈ D, if i ∈ T then b' T else 0 := by
    intro i
    exact hv.eq_of_sum_eq_sum (hca.trans hda.symm)
      ((hcp.trans hap).trans (hdp.trans hbp).symm) i (Finset.mem_univ i)
  have hshared (T : Finset ι) (hT : T ∈ C) (hpos : a (T.centroid ℝ v) ≠ 0) : T ∈ D := by
    have hcard : 0 < (T.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr (hneC T hT)
    have hapos : 0 < a (T.centroid ℝ v) := lt_of_le_of_ne (haC T hT) hpos.symm
    exact s2v_hardt6rb_common_chain_support C D hC hD a' b' ha' hb' hbeta T hT
      (hneC T hT) (mul_pos hapos (inv_pos.mpr hcard))
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
  exact ⟨⟨T.val, T.property, rfl⟩, ⟨T.val, hshared T.val T.property hT, rfl⟩⟩

end HodgeLean.Foundations.Program
