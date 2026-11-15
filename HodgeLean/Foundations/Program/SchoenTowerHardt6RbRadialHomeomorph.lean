import HodgeLean.Foundations.Program.SchoenTowerHardt6RbConeQuotient
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Quotient

/-! Boundary homeomorphisms extend to actual radial homeomorphisms of compact convex carriers. -/
noncomputable section
namespace HodgeLean.Foundations.Program
open Topology

theorem s2v_hardt6rb_radial_homeomorph {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (C : Set E) (D : Set F) (hC : IsCompact C) (hD : IsCompact D)
    (hc : Convex ℝ C) (hd : Convex ℝ D)
    (a : E) (b : F) (ha : a ∈ intrinsicInterior ℝ C) (hb : b ∈ intrinsicInterior ℝ D)
    (h : ↥(C \ intrinsicInterior ℝ C) ≃ₜ ↥(D \ intrinsicInterior ℝ D))
    (hne : (C \ intrinsicInterior ℝ C).Nonempty) :
    ∃ H : C ≃ₜ D, ∀ x : ↥(C \ intrinsicInterior ℝ C), ∀ t : Set.Icc (0 : ℝ) 1,
      (H ⟨AffineMap.lineMap a x.val t.val,
        hc.segment_subset (intrinsicInterior_subset ha) x.property.1
          (lineMap_mem_segment ℝ a x.val t.property)⟩).val =
        AffineMap.lineMap b (h x).val t.val := by
  have hneD : (D \ intrinsicInterior ℝ D).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨(h ⟨x, hx⟩).val, (h ⟨x, hx⟩).property⟩
  obtain ⟨p, hp, hpf, hpk⟩ := s2v_hardt6rb_cone_quotient C hC hc a ha hne
  obtain ⟨q, hq, hqf, hqk⟩ := s2v_hardt6rb_cone_quotient D hD hd b hb hneD
  let e := h.prodCongr (Homeomorph.refl (Set.Icc (0 : ℝ) 1))
  let pc : C(↥(C \ intrinsicInterior ℝ C) × Set.Icc (0 : ℝ) 1, C) := ⟨p, hp.continuous⟩
  let qc : C(↥(C \ intrinsicInterior ℝ C) × Set.Icc (0 : ℝ) 1, D) :=
    ⟨q ∘ e, hq.continuous.comp e.continuous⟩
  have hpc : IsQuotientMap pc := hp
  have hqc : IsQuotientMap qc := hq.comp e.isQuotientMap
  have hker : ∀ z w, Setoid.ker pc z w ↔ Setoid.ker qc z w := by
    intro z w
    change p z = p w ↔ q (e z) = q (e w)
    rw [hpk, hqk]
    change (z.2 = w.2 ∧ (z.2.val = 0 ∨ z.1 = w.1)) ↔
      (z.2 = w.2 ∧ (z.2.val = 0 ∨ h z.1 = h w.1))
    rw [h.injective.eq_iff]
  let H := (hpc.homeomorph.symm.trans (Homeomorph.Quotient.congrRight hker)).trans hqc.homeomorph
  have hH (z : ↥(C \ intrinsicInterior ℝ C) × Set.Icc (0 : ℝ) 1) : H (p z) = q (e z) := by
    have hpz : hpc.homeomorph (Quotient.mk _ z) = p z := rfl
    rw [← hpz]
    simp only [H, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    rfl
  refine ⟨H, ?_⟩
  intro x t
  have hpx : p (x, t) = ⟨AffineMap.lineMap a x.val t.val,
      hc.segment_subset (intrinsicInterior_subset ha) x.property.1
        (lineMap_mem_segment ℝ a x.val t.property)⟩ := Subtype.ext (hpf (x, t))
  rw [← hpx, hH]
  exact hqf (e (x, t))

end HodgeLean.Foundations.Program
