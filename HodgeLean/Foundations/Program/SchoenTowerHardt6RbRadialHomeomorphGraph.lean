import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRadialHomeomorph
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbConeMapGraph

/-! Actual Boolean graphs for radial extensions of prescribed boundary homeomorphisms. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_radial_homeomorph_graph {n m : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (D : Set (EuclideanSpace ℝ (Fin m)))
    (hC : IsCompact C) (hD : IsCompact D) (hc : Convex ℝ C) (hd : Convex ℝ D)
    (a : EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin m))
    (ha : a ∈ intrinsicInterior ℝ C) (hb : b ∈ intrinsicInterior ℝ D)
    (h : ↥(C \ intrinsicInterior ℝ C) ≃ₜ ↥(D \ intrinsicInterior ℝ D))
    (hne : (C \ intrinsicInterior ℝ C).Nonempty)
    (G : s2v_t11b_Formula (n + m))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : ↥(C \ intrinsicInterior ℝ C),
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (h x).val i)) :
    ∃ H : C ≃ₜ D, ∃ R : s2v_t11b_Formula (n + m),
      (∀ x : ↥(C \ intrinsicInterior ℝ C), ∀ t : Set.Icc (0 : ℝ) 1,
        (H ⟨AffineMap.lineMap a x.val t.val,
          hc.segment_subset (intrinsicInterior_subset ha) x.property.1
            (lineMap_mem_segment ℝ a x.val t.property)⟩).val =
          AffineMap.lineMap b (h x).val t.val) ∧
      (∀ z, z ∈ R.realize ↔ ∃ x : C,
        (∀ i, z (Fin.castAdd m i) = x.val i) ∧
        (∀ i, z (Fin.natAdd n i) = (H x).val i)) := by
  obtain ⟨H, hH⟩ := s2v_hardt6rb_radial_homeomorph C D hC hD hc hd a b ha hb h hne
  obtain ⟨p, hp, hpf, _⟩ := s2v_hardt6rb_cone_quotient C hC hc a ha hne
  have he : ∀ z, (H (p z)).val = AffineMap.lineMap b (h z.1).val z.2.val := by
    intro z
    have hz : p z = ⟨AffineMap.lineMap a z.1.val z.2.val,
        hc.segment_subset (intrinsicInterior_subset ha) z.1.property.1
          (lineMap_mem_segment ℝ a z.1.val z.2.property)⟩ := Subtype.ext (hpf z)
    rw [hz]
    exact hH z.1 z.2
  obtain ⟨R, hR⟩ := s2v_hardt6rb_cone_map_graph C (C \ intrinsicInterior ℝ C) D a b
    (fun x => (h x).val) H p hp.surjective hpf he G hG
  exact ⟨H, R, hH, hR⟩

end HodgeLean.Foundations.Program
