import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRelativeConvexCellMap
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAdjoinCellMapGraph

/-! A modeled cell is attached to the existing global homeomorphism using its prescribed shared boundary. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_adjoin_modeled_cell {n m : ℕ}
    (A C : Set (EuclideanSpace ℝ (Fin n))) (B T S : Set (EuclideanSpace ℝ (Fin m)))
    (hA : IsCompact A) (hC : IsCompact C) (hc : Convex ℝ C) (hneC : C.Nonempty)
    (hCA : C \ intrinsicInterior ℝ C ⊆ A) (hSB : S ⊆ B) (hST : S ⊆ T)
    (hAC : A ∩ C ⊆ C \ intrinsicInterior ℝ C) (hBT : B ∩ T ⊆ S)
    (e : A ≃ₜ B) (hmem : ∀ x : A, x.val ∈ C \ intrinsicInterior ℝ C ↔ (e x).val ∈ S)
    (model : C ≃ₜ T)
    (hmodel : ∀ x : C, x.val ∉ intrinsicInterior ℝ C ↔ (model x).val ∈ S)
    (F : s2v_t11b_Formula n) (hF : F.realize = C \ intrinsicInterior ℝ C)
    (G J : s2v_t11b_Formula (n + m))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : A,
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = (e x).val i))
    (hJ : ∀ z, z ∈ J.realize ↔ ∃ x : C,
      (∀ i, z (Fin.castAdd m i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = (model x).val i)) :
    ∃ H : ↥(A ∪ C) ≃ₜ ↥(B ∪ T), ∃ R : s2v_t11b_Formula (n + m),
      (∀ x : A, (H ⟨x.val, Or.inl x.property⟩).val = (e x).val) ∧
      (∃ k : C ≃ₜ T, ∀ x : C, (H ⟨x.val, Or.inr x.property⟩).val = (k x).val) ∧
      (∀ z, z ∈ R.realize ↔ ∃ x : ↥(A ∪ C),
        (∀ i, z (Fin.castAdd m i) = x.val i) ∧ (∀ i, z (Fin.natAdd n i) = (H x).val i)) := by
  obtain ⟨k, Q, hk, _, hQ⟩ := s2v_hardt6rb_relative_convex_cell_map A C B T S hC hc hneC
    hCA hSB hST e hmem model hmodel F hF G J hG hJ
  have hmemC (x : A) : x.val ∈ C ↔ (e x).val ∈ T := by
    constructor
    · intro hx
      exact hST ((hmem x).mp (hAC ⟨x.property, hx⟩))
    · intro hx
      exact ((hmem x).mpr (hBT ⟨(e x).property, hx⟩)).1
  have hagree (x : EuclideanSpace ℝ (Fin n)) (hxA : x ∈ A) (hxC : x ∈ C) :
      (k ⟨x, hxC⟩).val = (e ⟨x, hxA⟩).val := hk ⟨x, hAC ⟨hxA, hxC⟩⟩
  obtain ⟨H, R, hHe, hHk, hR⟩ := s2v_hardt6rb_adjoin_cell_map_graph A C B T hA hC e k
    hmemC hagree G Q hG hQ
  exact ⟨H, R, hHe, ⟨k, hHk⟩, hR⟩

end HodgeLean.Foundations.Program
