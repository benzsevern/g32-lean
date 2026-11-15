import HodgeLean.Foundations.Program.SchoenTowerHardtCad6Tools

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

structure s2v_hardt_cad6_Entry (n : ℕ) where
  cell : s2v_t11b_Formula n
  dim : ℕ
  chart : cell.realize ≃ₜ
    {z : EuclideanSpace ℝ (Fin dim) | ∀ v, -1 < z v ∧ z v < 1}
  forward : s2v_t11b_Formula (n + dim)
  inverse : s2v_t11b_Formula (dim + n)
  nonempty : cell.realize.Nonempty
  bound : dim ≤ n
  forward_eq : ∀ (x : cell.realize) (z : EuclideanSpace ℝ (Fin dim)),
    WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ forward.realize ↔
      z = (chart x).val
  inverse_eq : ∀
    (z : {z : EuclideanSpace ℝ (Fin dim) | ∀ v, -1 < z v ∧ z v < 1})
    (x : EuclideanSpace ℝ (Fin n)),
    WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ inverse.realize ↔
      x = (chart.symm z).val

def s2v_hardt_cad6_entry {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (P : s2v_hardt_cad5_Partition S) (i : Fin P.count) : s2v_hardt_cad6_Entry n :=
  ⟨P.cell i, P.dim i, P.chart i, P.forward i, P.inverse i, P.nonempty i,
    P.bound i, P.forward_eq i, P.inverse_eq i⟩

def s2v_hardt_cad6_join {n : ℕ} {U T S : Set (EuclideanSpace ℝ (Fin n))}
    (P : s2v_hardt_cad5_Partition U) (R : s2v_hardt_cad5_Partition T)
    (hd : Disjoint U T) (hc : U ∪ T = S) : s2v_hardt_cad5_Partition S where
  count := P.count + R.count
  cell i := (Fin.addCases (s2v_hardt_cad6_entry P) (s2v_hardt_cad6_entry R) i : s2v_hardt_cad6_Entry n).cell
  dim i := (Fin.addCases (s2v_hardt_cad6_entry P) (s2v_hardt_cad6_entry R) i : s2v_hardt_cad6_Entry n).dim
  chart i := (Fin.addCases (s2v_hardt_cad6_entry P) (s2v_hardt_cad6_entry R) i : s2v_hardt_cad6_Entry n).chart
  forward i := (Fin.addCases (s2v_hardt_cad6_entry P) (s2v_hardt_cad6_entry R) i : s2v_hardt_cad6_Entry n).forward
  inverse i := (Fin.addCases (s2v_hardt_cad6_entry P) (s2v_hardt_cad6_entry R) i : s2v_hardt_cad6_Entry n).inverse
  nonempty i := (Fin.addCases (s2v_hardt_cad6_entry P) (s2v_hardt_cad6_entry R) i : s2v_hardt_cad6_Entry n).nonempty
  disjoint := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
      intro j <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
      intro hij <;> simp only [Fin.addCases_left, Fin.addCases_right, s2v_hardt_cad6_entry]
    · exact P.disjoint (fun h => hij (congrArg (Fin.castAdd R.count) h))
    · exact hd.mono (s2v_hardt_cad6_cell_subset P _) (s2v_hardt_cad6_cell_subset R _)
    · exact hd.symm.mono (s2v_hardt_cad6_cell_subset R _) (s2v_hardt_cad6_cell_subset P _)
    · exact R.disjoint (fun h => hij (congrArg (Fin.natAdd P.count) h))
  cover := by
    rw [← hc]
    conv_rhs => rw [← P.cover, ← R.cover]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      revert hi
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
        simp only [Fin.addCases_left, Fin.addCases_right, s2v_hardt_cad6_entry]
      · exact fun h => Or.inl ⟨a, h⟩
      · exact fun h => Or.inr ⟨a, h⟩
    · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
      · exact ⟨Fin.castAdd R.count a, by simpa [s2v_hardt_cad6_entry] using ha⟩
      · exact ⟨Fin.natAdd P.count a, by simpa [s2v_hardt_cad6_entry] using ha⟩
  bound i := (Fin.addCases (s2v_hardt_cad6_entry P) (s2v_hardt_cad6_entry R) i : s2v_hardt_cad6_Entry n).bound
  forward_eq i := (Fin.addCases (s2v_hardt_cad6_entry P) (s2v_hardt_cad6_entry R) i : s2v_hardt_cad6_Entry n).forward_eq
  inverse_eq i := (Fin.addCases (s2v_hardt_cad6_entry P) (s2v_hardt_cad6_entry R) i : s2v_hardt_cad6_Entry n).inverse_eq

end HodgeLean.Foundations.Program
