import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Boolean
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5FiniteCarrier

/-! Finite-carrier comparisons and ambient limit dimensions. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_finite_invariance {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (P Q : s2v_hardt_cad5_Partition S) (hS : S.Finite) :
    P.dimension = Q.dimension := by
  rcases S.eq_empty_or_nonempty with h | h
  · rw [s2v_hardt_cad5_dimension_empty P h, s2v_hardt_cad5_dimension_empty Q h]
  · rw [s2v_hardt_cad5_finite_dimension P hS h,
      s2v_hardt_cad5_finite_dimension Q hS h]

theorem s2v_hardt_cad5_finite_bijection {n q : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} {T : Set (EuclideanSpace ℝ (Fin q))}
    (P : s2v_hardt_cad5_Partition S) (R : s2v_hardt_cad5_Partition T)
    (hS : S.Finite) (f : S ≃ T) : P.dimension = R.dimension := by
  letI : Finite S := hS.to_subtype
  letI : Finite T := Finite.of_equiv S f
  have hT : T.Finite := Set.finite_coe_iff.mp inferInstance
  rcases S.eq_empty_or_nonempty with h | h
  · have ht : T = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hs := (f.symm ⟨x, hx⟩).property
      simpa [h] using hs
    rw [s2v_hardt_cad5_dimension_empty P h, s2v_hardt_cad5_dimension_empty R ht]
  · obtain ⟨x, hx⟩ := h
    have ht : T.Nonempty := ⟨(f ⟨x, hx⟩).val, (f ⟨x, hx⟩).property⟩
    rw [s2v_hardt_cad5_finite_dimension P hS ⟨x, hx⟩,
      s2v_hardt_cad5_finite_dimension R hT ht]

theorem s2v_hardt_cad5_finite_closure {n : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) (hS : S.realize.Finite) :
    ∃ C : s2v_t11b_Formula n, ∃ Q : s2v_hardt_cad5_Partition C.realize,
      C.realize = closure S.realize ∧ Q.dimension = P.dimension := by
  exact ⟨S, P, hS.isClosed.closure_eq.symm, rfl⟩

theorem s2v_hardt_cad5_finite_boundary {n : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) (hS : S.realize.Finite) :
    ∃ B : s2v_t11b_Formula n, ∃ Q : s2v_hardt_cad5_Partition B.realize,
      B.realize = closure S.realize \ S.realize ∧
      (S.realize.Nonempty → Q.dimension < P.dimension) ∧
      (S.realize = ∅ → B.realize = ∅ ∧ Q.dimension = -1 ∧ P.dimension = -1) := by
  obtain ⟨B, Q, hB⟩ := s2v_hardt_cad5_boundary_partition S
  have he : B.realize = ∅ := by rw [hB, hS.isClosed.closure_eq, Set.diff_self]
  have hQ := s2v_hardt_cad5_dimension_empty Q he
  refine ⟨B, Q, hB, ?_, ?_⟩
  · intro hn
    rw [hQ, s2v_hardt_cad5_finite_dimension P hS hn]
    norm_num
  · intro h
    exact ⟨he, hQ, s2v_hardt_cad5_dimension_empty P h⟩

end HodgeLean.Foundations.Program
