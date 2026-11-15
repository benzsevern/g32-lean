import HodgeLean.Foundations.Program.SchoenTowerHardtCad5BoxBounds
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Bounds

/-! Ambient interior detected by the recorded chart dimension. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_dimension_eq_ambient_of_interior {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S)
    (hne : (interior S).Nonempty) : P.dimension = (n : ℤ) := by
  obtain ⟨i, hi⟩ := s2v_hardt_cad5_open_finite_relations_bound P.dim
    (fun i => {z | ∀ v, -1 < z v ∧ z v < 1}) P.inverse
    (interior S) isOpen_interior hne (by
      intro i z hz
      apply (Set.finite_singleton (((P.chart i).symm ⟨z, hz⟩).val)).subset
      intro x hx
      exact (P.inverse_eq i ⟨z, hz⟩ x).mp hx) (by
      intro x hx
      have hxS : x ∈ ⋃ i, (P.cell i).realize := by
        simpa only [P.cover] using (interior_subset hx : x ∈ S)
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxS
      let z := P.chart i ⟨x, hi⟩
      refine ⟨i, z.val, z.property, (P.inverse_eq i z x).mpr ?_⟩
      exact (congrArg Subtype.val ((P.chart i).symm_apply_apply ⟨x, hi⟩)).symm)
  exact le_antisymm (s2v_hardt_cad5_dimension_le_ambient P)
    (le_trans (by exact_mod_cast hi) (s2v_hardt_cad5_le_max P.dim i))

theorem s2v_hardt_cad5_interior_empty_of_dimension_lt {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (P : s2v_hardt_cad5_Partition S)
    (hP : P.dimension < (n : ℤ)) : interior S = ∅ := by
  by_contra h
  have heq := s2v_hardt_cad5_dimension_eq_ambient_of_interior P
    (Set.nonempty_iff_ne_empty.mpr h)
  omega

end HodgeLean.Foundations.Program
