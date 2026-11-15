import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceRootIndexMap
import HodgeLean.Foundations.Program.SchoenTowerT11bDefs
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-! Whole-face polynomial root equations construct the actual root-label restriction on every subface. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_face_root_restriction {n : ℕ}
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
    (s t : L.faces) (hts : t.val ⊆ s.val) :
    ∃ ρ : Fin (r s) → Fin (r t), Monotone ρ ∧ ∀ a x,
      x ∈ convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) → f s a x = f t (ρ a) x := by
  have hsub : convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) ⊆
      convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) :=
    convexHull_mono (Finset.coe_subset.mpr hts)
  let F : Fin (r s) → convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) → ℝ :=
    fun a x => f s a x.val
  let G : Fin (r t) → convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) → ℝ :=
    fun a x => f t a x.val
  have hF (a : Fin (r s)) : Continuous (F a) :=
    continuousOn_iff_continuous_restrict.mp ((hf s a).mono hsub)
  have hG (a : Fin (r t)) : Continuous (G a) :=
    continuousOn_iff_continuous_restrict.mp (hf t a)
  have hcov : ∀ a (x : intrinsicInterior ℝ
      (convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))))), ∃ b,
      F a ⟨x.val, intrinsicInterior_subset x.property⟩ =
        G b ⟨x.val, intrinsicInterior_subset x.property⟩ := by
    intro a x
    exact (hcover t x.val x.property _).mp (hroot s a x.val (hsub (intrinsicInterior_subset x.property)))
  obtain ⟨ρ, hρ, he⟩ := s2v_hardt6rb_face_root_index_map t.val
    (L.nonempty_of_mem_faces t.property) F G hF hG
    (fun x => hm s x.val (hsub x.property))
    (fun x => hs t x.val x.property) hcov
  exact ⟨ρ, hρ, fun a x hx => he a ⟨x, hx⟩⟩

end HodgeLean.Foundations.Program
