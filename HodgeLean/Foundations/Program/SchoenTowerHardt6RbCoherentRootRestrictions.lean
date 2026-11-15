import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceRootRestriction
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceRootLabelUnique

/-! Actual root-label restrictions form a coherent system on all nested geometric base faces. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_coherent_face_root_restrictions {n : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (r : L.faces → ℕ)
    (f : (s : L.faces) → Fin (r s) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ s a, ContinuousOn (f s a) (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))))
    (hm : ∀ s x, x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) → Monotone (fun a => f s a x))
    (hs : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
      StrictMono (fun a => f s a x))
    (Q : Polynomial (MvPolynomial (Fin n) ℝ))
    (hroot : ∀ s a x, x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) →
      Q.eval₂ (MvPolynomial.eval (fun i => β x i)) (f s a x) = 0)
    (hcover : ∀ (s : L.faces) (x : EuclideanSpace ℝ (Fin n)),
      x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
      ∀ z, Q.eval₂ (MvPolynomial.eval (fun i => β x i)) z = 0 ↔ ∃ a, z = f s a x)
    : ∃ ρ : ∀ s t : L.faces, t.val ⊆ s.val → Fin (r s) → Fin (r t),
      (∀ s t hts, Monotone (ρ s t hts)) ∧
      (∀ s t hts a x, x ∈ convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) →
        f s a x = f t (ρ s t hts a) x) ∧
      (∀ s, ρ s s (Finset.Subset.refl s.val) = id) ∧
      (∀ (s t u : L.faces) (hts : t.val ⊆ s.val) (hut : u.val ⊆ t.val),
        ρ s u (hut.trans hts) = (ρ t u hut) ∘ (ρ s t hts)) := by
  classical
  choose ρ hmono he using fun (s t : L.faces) (hts : t.val ⊆ s.val) =>
    s2v_hardt6rb_face_root_restriction L β r f hf hm hs Q hroot hcover s t hts
  refine ⟨ρ, hmono, he, ?_, ?_⟩
  · intro s
    exact s2v_hardt6rb_face_root_label_unique L r f hs s s
      (ρ s s (Finset.Subset.refl s.val)) id
      (he s s (Finset.Subset.refl s.val)) (fun _ _ _ => rfl)
  · intro s t u hts hut
    apply s2v_hardt6rb_face_root_label_unique L r f hs s u
      (ρ s u (hut.trans hts)) ((ρ t u hut) ∘ (ρ s t hts))
      (he s u (hut.trans hts))
    intro a x hx
    exact (he s t hts a x (convexHull_mono (Finset.coe_subset.mpr hut) hx)).trans
      (he t u hut (ρ s t hts a) x hx)

end HodgeLean.Foundations.Program
