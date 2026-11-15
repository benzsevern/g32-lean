import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Bounds
import Mathlib.Order.Interval.Set.Infinite

/-! Dimension records for finite carriers. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_finite_cell_dim {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S)
    (hS : S.Finite) (i : Fin P.count) : P.dim i = 0 := by
  classical
  have hsub : (P.cell i).realize ⊆ S := by
    intro x hx
    rw [← P.cover]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  have hfin := hS.subset hsub
  letI : Finite (P.cell i).realize := hfin.to_subtype
  letI : Finite {z : EuclideanSpace ℝ (Fin (P.dim i)) |
      ∀ v, -1 < z v ∧ z v < 1} := Finite.of_equiv _ (P.chart i).toEquiv
  by_contra hdim
  let j : Fin (P.dim i) := ⟨0, Nat.pos_of_ne_zero hdim⟩
  let f : Set.Ioo (-1 : ℝ) 1 →
      {z : EuclideanSpace ℝ (Fin (P.dim i)) | ∀ v, -1 < z v ∧ z v < 1} :=
    fun t => ⟨WithLp.toLp 2 (fun _ => t.val), fun _ => t.property⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z => z.val j) h
  letI : Finite (Set.Ioo (-1 : ℝ) 1) := Finite.of_injective f hf
  letI : Infinite (Set.Ioo (-1 : ℝ) 1) := Set.Ioo.infinite (by norm_num)
  exact not_finite (Set.Ioo (-1 : ℝ) 1)

theorem s2v_hardt_cad5_finite_dimension {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S)
    (hS : S.Finite) (hn : S.Nonempty) : P.dimension = 0 := by
  apply le_antisymm
  · apply s2v_hardt_cad5_max_le
    · norm_num
    · intro i
      rw [s2v_hardt_cad5_finite_cell_dim P hS i]
      simp
  · exact s2v_hardt_cad5_dimension_nonneg P hn

theorem s2v_hardt_cad5_finite_of_dimension_le_zero {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S)
    (hP : P.dimension ≤ 0) : S.Finite := by
  classical
  rw [← P.cover]
  apply Set.finite_iUnion
  intro i
  have hd : P.dim i = 0 := by
    have hi : (P.dim i : ℤ) ≤ P.dimension := s2v_hardt_cad5_le_max P.dim i
    omega
  have ht : Subsingleton
      {z : EuclideanSpace ℝ (Fin (P.dim i)) | ∀ v, -1 < z v ∧ z v < 1} := by
    rw [hd]
    infer_instance
  letI := ht
  letI : Subsingleton (P.cell i).realize :=
    Function.Injective.subsingleton (P.chart i).injective
  exact Set.finite_coe_iff.mp (inferInstance : Finite (P.cell i).realize)

end HodgeLean.Foundations.Program
