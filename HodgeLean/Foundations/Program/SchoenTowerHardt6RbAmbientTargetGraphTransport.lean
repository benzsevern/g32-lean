import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGraphCompose
import Mathlib.Topology.Homeomorph.Lemmas

/-! Actual graph transport through the given ambient target homeomorphism. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ambient_target_graph_transport {n m : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (A : Set (EuclideanSpace ℝ (Fin m)))
    (h : U ≃ₜ A) (G : s2v_t11b_Formula (n + m))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : U,
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = (h x).val i))
    (e : EuclideanSpace ℝ (Fin m) ≃ₜ EuclideanSpace ℝ (Fin m))
    (J : s2v_t11b_Formula (m + m))
    (hJ : ∀ z, z ∈ J.realize ↔ ∃ y : EuclideanSpace ℝ (Fin m),
      (∀ i, z (Fin.castAdd m i) = y i) ∧ (∀ i, z (Fin.natAdd m i) = e y i)) :
    ∃ k : U ≃ₜ (e '' A), ∃ R : s2v_t11b_Formula (n + m),
      (∀ x, (k x).val = e (h x).val) ∧
      (∀ z, z ∈ R.realize ↔ ∃ x : U,
        (∀ i, z (Fin.castAdd m i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = (k x).val i)) := by
  let k := h.trans (e.image A)
  let u : U → (Set.univ : Set (EuclideanSpace ℝ (Fin m))) := fun x => ⟨(h x).val, trivial⟩
  let v : ↥(Set.univ : Set (EuclideanSpace ℝ (Fin m))) → (Set.univ : Set (EuclideanSpace ℝ (Fin m))) :=
    fun y => ⟨e y.val, trivial⟩
  have hJ' : ∀ z, z ∈ J.realize ↔ ∃ y : (Set.univ : Set (EuclideanSpace ℝ (Fin m))),
      (∀ i, z (Fin.castAdd m i) = y.val i) ∧ (∀ i, z (Fin.natAdd m i) = (v y).val i) := by
    intro z
    rw [hJ]
    exact ⟨fun ⟨y, hy, he⟩ => ⟨⟨y, trivial⟩, hy, he⟩,
      fun ⟨y, hy, he⟩ => ⟨y.val, hy, he⟩⟩
  obtain ⟨R, hR⟩ := s2v_hardt6rb_actual_graph_compose U Set.univ Set.univ u v G J hG hJ'
  exact ⟨k, R, fun _ => rfl, hR⟩

end HodgeLean.Foundations.Program
