import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceFormula
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGraphSourceRestriction
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSectionPullback

/-! Actual root-section graphs pull back to intrinsic open faces of a base simplex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_open_face_section_graph {n m : ℕ}
    (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hs : AffineIndependent ℝ ((↑) : s → EuclideanSpace ℝ (Fin n)))
    (k : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))) → EuclideanSpace ℝ (Fin m))
    (C : Set (EuclideanSpace ℝ (Fin m))) (ψ : C → ℝ)
    (hmaps : ∀ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))),
      k ⟨x.val, intrinsicInterior_subset x.property⟩ ∈ C)
    (K : s2v_t11b_Formula (n + m))
    (hK : ∀ z, z ∈ K.realize ↔ ∃ x : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))),
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = k x i))
    (G : s2v_t11b_Formula (m + 1))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ y : C,
      (∀ i, z i.succ = y.val i) ∧ z 0 = ψ y) :
    ∃ R : s2v_t11b_Formula (n + 1), ∀ z, z ∈ R.realize ↔
      ∃ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))),
        (∀ i, z i.succ = x.val i) ∧
        z 0 = ψ ⟨k ⟨x.val, intrinsicInterior_subset x.property⟩, hmaps x⟩ := by
  obtain ⟨U, hU⟩ := s2v_hardt6rb_open_face_formula s hs
  have hsub : U.realize ⊆ convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))) := by
    rw [hU]
    exact intrinsicInterior_subset
  let kA : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))) →
      (Set.univ : Set (EuclideanSpace ℝ (Fin m))) := fun x => ⟨k x, trivial⟩
  obtain ⟨F, hF⟩ := s2v_hardt6rb_graph_source_restriction _ _ kA K hK U hsub
  let kU : U.realize → C := fun x =>
    ⟨k ⟨x.val, hsub x.property⟩, hmaps ⟨x.val, hU ▸ x.property⟩⟩
  have hFU : ∀ z, z ∈ F.realize ↔ ∃ x : U.realize,
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (kU x).val i) := hF
  obtain ⟨R, hR⟩ := s2v_hardt6rb_section_graph_pullback U.realize C kU ψ F G hFU hG
  refine ⟨R, ?_⟩
  intro z
  rw [hR]
  constructor
  · rintro ⟨x, hx, ht⟩
    exact ⟨⟨x.val, hU ▸ x.property⟩, hx, ht⟩
  · rintro ⟨x, hx, ht⟩
    exact ⟨⟨x.val, hU.symm ▸ x.property⟩, hx, ht⟩

end HodgeLean.Foundations.Program
