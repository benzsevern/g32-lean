import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactCellGraphGluing
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbRelativeCellInjectivity

/-! Relative cell extensions assemble with the existing map and its actual Boolean graph. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_adjoin_cell_map_graph {n m : ℕ}
    (A C : Set (EuclideanSpace ℝ (Fin n))) (B D : Set (EuclideanSpace ℝ (Fin m)))
    (hA : IsCompact A) (hC : IsCompact C) (e : A ≃ₜ B) (k : C ≃ₜ D)
    (hmem : ∀ x : A, x.val ∈ C ↔ (e x).val ∈ D)
    (hagree : ∀ (x : EuclideanSpace ℝ (Fin n)) (hxA : x ∈ A) (hxC : x ∈ C),
      (k ⟨x, hxC⟩).val = (e ⟨x, hxA⟩).val)
    (G J : s2v_t11b_Formula (n + m))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : A,
      (∀ j, z (Fin.castAdd m j) = x.val j) ∧ (∀ j, z (Fin.natAdd n j) = (e x).val j))
    (hJ : ∀ z, z ∈ J.realize ↔ ∃ x : C,
      (∀ j, z (Fin.castAdd m j) = x.val j) ∧ (∀ j, z (Fin.natAdd n j) = (k x).val j)) :
    ∃ H : ↥(A ∪ C) ≃ₜ ↥(B ∪ D), ∃ R : s2v_t11b_Formula (n + m),
      (∀ x : A, (H ⟨x.val, Or.inl x.property⟩).val = (e x).val) ∧
      (∀ x : C, (H ⟨x.val, Or.inr x.property⟩).val = (k x).val) ∧
      (∀ z, z ∈ R.realize ↔ ∃ x : ↥(A ∪ C),
        (∀ j, z (Fin.castAdd m j) = x.val j) ∧ (∀ j, z (Fin.natAdd n j) = (H x).val j)) := by
  classical
  let Cs : Bool → Set (EuclideanSpace ℝ (Fin n)) := fun b => if b then C else A
  let Ds : Bool → Set (EuclideanSpace ℝ (Fin m)) := fun b => if b then D else B
  let es : ∀ b, Cs b ≃ₜ Ds b := fun b => by cases b; exact e; exact k
  let Fs : Bool → s2v_t11b_Formula (n + m) := fun b => if b then J else G
  have hCs (b : Bool) : IsCompact (Cs b) := by cases b; exact hA; exact hC
  have hes : ∀ i j x (hi : x ∈ Cs i) (hj : x ∈ Cs j),
      (es i ⟨x, hi⟩).val = (es j ⟨x, hj⟩).val := by
    intro i j x hi hj
    cases i <;> cases j
    · rfl
    · exact (hagree x hi hj).symm
    · exact hagree x hj hi
    · rfl
  have hcross := s2v_hardt6rb_relative_cell_cross_injective A C B D e k hmem hagree
  have hei : ∀ i j (x : Cs i) (y : Cs j), (es i x).val = (es j y).val → x.val = y.val := by
    intro i j x y he
    cases i <;> cases j
    · exact congrArg Subtype.val (e.injective (Subtype.ext he))
    · exact hcross x y he
    · exact (hcross y x he.symm).symm
    · exact congrArg Subtype.val (k.injective (Subtype.ext he))
  have hFs : ∀ i z, z ∈ (Fs i).realize ↔ ∃ x : Cs i,
      (∀ j, z (Fin.castAdd m j) = x.val j) ∧ (∀ j, z (Fin.natAdd n j) = (es i x).val j) := by
    intro i
    cases i
    · exact hG
    · exact hJ
  obtain ⟨H₀, R, hH₀, hR⟩ := s2v_hardt6rb_compact_cell_graph_gluing Cs Ds hCs es hes hei Fs hFs
  have hSrc : (⋃ b, Cs b) = A ∪ C := by ext x; simp [Cs]
  have hTgt : (⋃ b, Ds b) = B ∪ D := by ext x; simp [Ds]
  let H := (Homeomorph.setCongr hSrc).symm.trans (H₀.trans (Homeomorph.setCongr hTgt))
  refine ⟨H, R, ?_, ?_, ?_⟩
  · intro x
    exact hH₀ false x
  · intro x
    exact hH₀ true x
  · intro z
    rw [hR]
    constructor
    · rintro ⟨x, hx, hy⟩
      exact ⟨⟨x.val, hSrc ▸ x.property⟩, hx, hy⟩
    · rintro ⟨x, hx, hy⟩
      exact ⟨⟨x.val, hSrc.symm ▸ x.property⟩, hx, hy⟩

end HodgeLean.Foundations.Program
