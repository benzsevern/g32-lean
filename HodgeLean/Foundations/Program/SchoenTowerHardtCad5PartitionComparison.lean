import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Comparison
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Diagonal

/-! Dimension comparison on common and nested carriers. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_partition_dimension_eq {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P Q : s2v_hardt_cad5_Partition S) :
    P.dimension = Q.dimension := by
  obtain ⟨D, hD⟩ := s2v_hardt_cad5_diagonal_formula n
  exact le_antisymm
    (s2v_hardt_cad5_dimension_le_of_graph_injective P Q
      (fun x => x) Function.injective_id D (fun x y => hD x.val y))
    (s2v_hardt_cad5_dimension_le_of_graph_injective Q P
      (fun x => x) Function.injective_id D (fun x y => hD x.val y))

theorem s2v_hardt_cad5_partition_dimension_mono {n : ℕ}
    {S T : Set (EuclideanSpace ℝ (Fin n))}
    (P : s2v_hardt_cad5_Partition S) (R : s2v_hardt_cad5_Partition T)
    (hST : S ⊆ T) : P.dimension ≤ R.dimension := by
  obtain ⟨D, hD⟩ := s2v_hardt_cad5_diagonal_formula n
  let f : S → T := fun x => ⟨x.val, hST x.property⟩
  apply s2v_hardt_cad5_dimension_le_of_graph_injective P R f ?_ D
    (fun x y => hD x.val y)
  intro x y h
  exact Subtype.ext (congrArg (fun z : T => z.val) h)

end HodgeLean.Foundations.Program
