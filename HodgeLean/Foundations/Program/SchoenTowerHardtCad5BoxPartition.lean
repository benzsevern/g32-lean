import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Diagonal
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Bounds

/-! A concrete one-cell Boolean partition of the full open coordinate box. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_box_formula (d : ℕ) :
    ∃ B : s2v_t11b_Formula d,
      B.realize = {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1} := by
  obtain ⟨B, hB⟩ := s2v_hardt_cad3_finite_inter (fun i : Fin d =>
    s2v_t11b_Formula.inter (.compl (.nonneg (-MvPolynomial.X i - 1)))
      (.compl (.nonneg (MvPolynomial.X i - 1))))
  refine ⟨B, ?_⟩
  ext z
  rw [hB]
  change (∀ i, ¬ 0 ≤ MvPolynomial.eval (fun j => z j) (-MvPolynomial.X i - 1) ∧
    ¬ 0 ≤ MvPolynomial.eval (fun j => z j) (MvPolynomial.X i - 1)) ↔ _
  simp only [map_sub, map_neg, map_one, MvPolynomial.eval_X, not_le]
  apply forall_congr'
  intro i
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem s2v_hardt_cad5_box_partition (d : ℕ) :
    ∃ P : s2v_hardt_cad5_Partition
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1}, P.dimension = (d : ℤ) := by
  obtain ⟨B, hB⟩ := s2v_hardt_cad5_box_formula d
  obtain ⟨D, hD⟩ := s2v_hardt_cad5_diagonal_formula d
  let e := Homeomorph.setCongr hB
  have hn : B.realize.Nonempty := by
    refine ⟨0, ?_⟩
    rw [hB]
    intro v
    simp
  let P : s2v_hardt_cad5_Partition
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1} :=
    { count := 1
      cell := fun _ => B
      dim := fun _ => d
      chart := fun _ => e
      forward := fun _ => D
      inverse := fun _ => D
      nonempty := fun _ => hn
      disjoint := by intro i j h; exact (h (Subsingleton.elim i j)).elim
      cover := by
        ext z
        constructor
        · intro hz
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
          exact hB ▸ hi
        · intro hz
          exact Set.mem_iUnion.mpr ⟨0, hB.symm ▸ hz⟩
      bound := fun _ => le_rfl
      forward_eq := fun _ x z => hD x.val z
      inverse_eq := fun _ z x => hD z.val x }
  refine ⟨P, le_antisymm ?_ ?_⟩
  · exact s2v_hardt_cad5_max_le P.dim d (by omega) (fun _ => le_rfl)
  · exact s2v_hardt_cad5_le_max P.dim 0

end HodgeLean.Foundations.Program
