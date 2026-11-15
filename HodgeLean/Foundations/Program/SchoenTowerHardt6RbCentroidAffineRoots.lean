import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidFaceParent
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceAffineRootModels
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAffineInteriorPositive

/-! Centroid refinement constructs coherent affine root models with strictly positive interior gaps. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_affine_roots {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hK : K.faces.Finite)
    (r : K.faces → ℕ)
    (f : (s : K.faces) → Fin (r s) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ∀ s x, x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) → Monotone (fun a => f s a x))
    (hs : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
      StrictMono (fun a => f s a x))
    (ρ : ∀ s t : K.faces, t.val ⊆ s.val → Fin (r s) → Fin (r t))
    (hρ : ∀ s t hts a x, x ∈ convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) →
      f s a x = f t (ρ s t hts a) x) :
    ∃ L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      L.faces.Finite ∧ L.space = K.space ∧ ∃ parent : L.faces → K.faces,
      (∀ s, (parent s).val.centroid ℝ id ∈ s.val) ∧
      (∀ s, convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) ⊆
        convexHull ℝ ((parent s).val : Set (EuclideanSpace ℝ (Fin n)))) ∧
      (∀ s, intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) ⊆
        intrinsicInterior ℝ (convexHull ℝ ((parent s).val : Set (EuclideanSpace ℝ (Fin n))))) ∧
      (∀ s t, t.val ⊆ s.val → (parent t).val ⊆ (parent s).val) ∧
      ∃ A : (s : L.faces) → Fin (r (parent s)) → (EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] ℝ),
      (∀ s a, Continuous (A s a)) ∧
      (∀ s a (x : s.val), A s a x.val = f (parent s) a x.val) ∧
      (∀ s x, x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) → Monotone (fun a => A s a x)) ∧
      (∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
        StrictMono (fun a => A s a x)) ∧
      (∀ s t, t.val ⊆ s.val → ∀ (hpt : (parent t).val ⊆ (parent s).val) a,
        Set.EqOn (A s a) (A t (ρ (parent s) (parent t) hpt a))
          (convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))))) := by
  classical
  obtain ⟨L, hL, hspace, parent, hv, hh, hi, hp⟩ := s2v_hardt6rb_centroid_face_parents K hK
  let R : ∀ s t : L.faces, t.val ⊆ s.val → Fin (r (parent s)) → Fin (r (parent t)) :=
    fun s t hts => ρ (parent s) (parent t) (hp s t hts)
  obtain ⟨A, hAc, hAv, hAm, hAe⟩ := s2v_hardt6rb_face_affine_root_models L
    (fun s => r (parent s)) (fun s => f (parent s))
    (fun s x hx => hm (parent s) x (hh s hx)) R
    (fun s t hts a x hx => hρ (parent s) (parent t) (hp s t hts) a x (hh t hx))
  refine ⟨L, hL, hspace, parent, hv, hh, hi, hp, A, hAc, hAv, hAm, ?_, ?_⟩
  · intro s x hx a b hab
    apply sub_pos.mp
    change 0 < ((A s b) - (A s a)) x
    apply s2v_hardt6rb_affine_interior_positive (convexHull ℝ (s.val : Set _))
      ((A s b) - (A s a)) ?_ ?_ hx
    · intro y hy
      exact sub_nonneg.mpr (hAm s y hy hab.le)
    · refine ⟨(parent s).val.centroid ℝ id, subset_convexHull ℝ _ (hv s), ?_⟩
      change 0 < A s b _ - A s a _
      rw [hAv s b ⟨_, hv s⟩, hAv s a ⟨_, hv s⟩]
      exact sub_pos.mpr (hs (parent s) _ (s2v_hardt6rb_centroid_intrinsic _
        (K.nonempty_of_mem_faces (parent s).property)) hab)
  · intro s t hts hpt a
    exact hAe s t hts a

end HodgeLean.Foundations.Program
