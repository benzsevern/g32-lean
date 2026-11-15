import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRootCollisionTransfer
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAmbientRescale
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBandEndpointTransfer

/-! Shared face labels construct actual continuous band models, including every collapsed fiber. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_coherent_root_band_models {n : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (r : L.faces → ℕ)
    (f g : (s : L.faces) → Fin (r s) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ s a, ContinuousOn (f s a) (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))))
    (hgc : ∀ s a, ContinuousOn (g s a) (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))))
    (hfm : ∀ s x, x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) → Monotone (fun a => f s a x))
    (hgm : ∀ s x, x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) → Monotone (fun a => g s a x))
    (hf : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
      StrictMono (fun a => f s a x))
    (hg : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
      StrictMono (fun a => g s a x))
    (ρ : ∀ s t : L.faces, t.val ⊆ s.val → Fin (r s) → Fin (r t))
    (hρf : ∀ s t hts a x, x ∈ convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) →
      f s a x = f t (ρ s t hts a) x)
    (hρg : ∀ s t hts a x, x ∈ convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) →
      g s a x = g t (ρ s t hts a) x)
    (s : L.faces) (a b : Fin (r s)) (hab : a ≤ b) :
    ∃ h : {p : EuclideanSpace ℝ (Fin n) × ℝ |
        p.1 ∈ convexHull ℝ (s.val : Set _) ∧ g s a p.1 ≤ p.2 ∧ p.2 ≤ g s b p.1} ≃ₜ
      {p : EuclideanSpace ℝ (Fin n) × ℝ |
        p.1 ∈ convexHull ℝ (s.val : Set _) ∧ f s a p.1 ≤ p.2 ∧ p.2 ≤ f s b p.1},
      (∀ p q, h p = q ↔ p.val.1 = q.val.1 ∧
        (p.val.2 - g s a p.val.1) * (f s b p.val.1 - f s a p.val.1) =
          (q.val.2 - f s a p.val.1) * (g s b p.val.1 - g s a p.val.1)) ∧
      (∀ p, (p.val.1 ∉ intrinsicInterior ℝ (convexHull ℝ (s.val : Set _)) ∨
          p.val.2 = g s a p.val.1 ∨ p.val.2 = g s b p.val.1) ↔
        ((h p).val.1 ∉ intrinsicInterior ℝ (convexHull ℝ (s.val : Set _)) ∨
          (h p).val.2 = f s a (h p).val.1 ∨ (h p).val.2 = f s b (h p).val.1)) := by
  let C := convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))
  letI : CompactSpace C := isCompact_iff_compactSpace.mp (s.val.finite_toSet.isCompact_convexHull ℝ)
  have hz (x : C) : g s a x.val = g s b x.val ↔ f s a x.val = f s b x.val :=
    (s2v_hardt6rb_root_collision_transfer L r f g hf hg ρ hρf hρg s a b x.val x.property).1
  obtain ⟨h, hh⟩ := s2v_hardt6rb_ambient_band_rescale C (g s a) (g s b) (f s a) (f s b)
    (continuousOn_iff_continuous_restrict.mp (hgc s a))
    (continuousOn_iff_continuous_restrict.mp (hgc s b))
    (continuousOn_iff_continuous_restrict.mp (hfc s a))
    (continuousOn_iff_continuous_restrict.mp (hfc s b))
    (fun x => hgm s x.val x.property hab) (fun x => hfm s x.val x.property hab) hz
  refine ⟨h, hh, ?_⟩
  intro p
  obtain ⟨hbase, he⟩ := (hh p (h p)).mp rfl
  have hq : f s a p.val.1 ≤ (h p).val.2 ∧ (h p).val.2 ≤ f s b p.val.1 := by
    rw [hbase]
    exact (h p).property.2
  have hend := s2v_hardt6rb_band_endpoint_transfer
    (g s a p.val.1) (g s b p.val.1) (f s a p.val.1) (f s b p.val.1)
    p.val.2 (h p).val.2 (hgm s _ p.property.1 hab) (hfm s _ p.property.1 hab)
    p.property.2 hq (hz ⟨p.val.1, p.property.1⟩) he
  rw [← hbase]
  exact or_congr Iff.rfl (or_congr hend.1 hend.2.1)

end HodgeLean.Foundations.Program
