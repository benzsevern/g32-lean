import HodgeLean.Foundations.Program.SchoenTowerHardtCad5ClosureProjection
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5MapAlgebraic

/-! Ambient limit dimension bounded by coordinate projection equations. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_closure_dimension_le {n : ℕ}
    (S : s2v_t11b_Formula n) (P : s2v_hardt_cad5_Partition S.realize)
    (C : s2v_t11b_Formula n) (Q : s2v_hardt_cad5_Partition C.realize)
    (hC : C.realize = closure S.realize) : Q.dimension ≤ P.dimension := by
  classical
  by_cases hS : S.realize = ∅
  · have hCE : C.realize = ∅ := by rw [hC, hS, closure_empty]
    rw [s2v_hardt_cad5_dimension_empty P hS, s2v_hardt_cad5_dimension_empty Q hCE]
  obtain ⟨p, hp⟩ := s2v_hardt_cad5_maximal_cell P (Set.nonempty_iff_ne_empty.mpr hS)
  let d := P.dim p
  have hd : (d : ℤ) = P.dimension := hp
  apply s2v_hardt_cad5_max_le Q.dim P.dimension
    (s2v_hardt_cad5_max_ge_neg_one P.dim)
  intro q
  by_contra hqe
  have hde : d < Q.dim q := by omega
  choose poly hpn hpl using fun r : Fin (d + 1) → Fin n =>
    s2v_hardt_cad5_projection_polynomial_limit S P (show P.dimension < ((d + 1 : ℕ) : ℤ) by omega) r
  obtain ⟨K₁, hK₁, hAlg⟩ := s2v_hardt_cad5_graph_map_algebraic (Q.cell q)
    (fun x => (Q.chart q x).val) (Q.forward q) (Q.forward_eq q)
  let s : Set ℝ := (K₁ : Set ℝ) ∪
    ⋃ r : Fin (d + 1) → Fin n, ((poly r).coeffs : Set ℝ)
  have hs : s.Countable := Set.Countable.union (by
    letI := hK₁
    exact Set.to_countable _) (Set.countable_iUnion (fun r => (poly r).coeffs.countable_toSet))
  let K : Subfield ℝ := Subfield.closure s
  letI : Countable K := s2v_hardt_cad5_countable_coefficient_field s hs
  have hK₁K : K₁ ≤ K := fun _ hc => Subfield.subset_closure (Or.inl hc)
  have hlift (r : Fin (d + 1) → Fin n) :
      ∃ pr : MvPolynomial (Fin (d + 1)) K, MvPolynomial.map K.subtype pr = poly r := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    exact ⟨⟨c, Subfield.subset_closure (Or.inr (Set.mem_iUnion.mpr ⟨r, hc⟩))⟩, rfl⟩
  obtain ⟨z, hz, hbox⟩ := s2v_hardt_cad5_independent_box_point K (Q.dim q)
  let x := (Q.chart q).symm ⟨z, hbox⟩
  have hxC : x.val ∈ C.realize := by
    have hxU : x.val ∈ ⋃ l, (Q.cell l).realize := Set.mem_iUnion.mpr ⟨q, x.property⟩
    simpa only [Q.cover] using hxU
  have hxCl : x.val ∈ closure S.realize := by simpa only [hC] using hxC
  let M := (IntermediateField.adjoin K (Set.range (fun i => x.val i))).toSubfield
  have hKM : K ≤ M := by
    intro c hc
    exact (IntermediateField.adjoin K (Set.range (fun i => x.val i))).algebraMap_mem ⟨c, hc⟩
  let a : Fin n → M := fun i => ⟨x.val i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hA : ∀ j, IsAlgebraic M ((Q.chart q x).val j) :=
    hAlg M (hK₁K.trans hKM) a x.property
  have hAz : ∀ j, IsAlgebraic M (z j) := by
    simpa only [x, Homeomorph.apply_symm_apply] using hA
  have hAlgz : ∀ j, IsAlgebraic (Algebra.adjoin K (Set.range (fun i => x.val i))) (z j) :=
    fun j => IntermediateField.isAlgebraic_adjoin_iff.mp (hAz j)
  obtain ⟨r, hr⟩ := s2v_hardt_cad5_independent_coordinate_projection K
    (fun i => x.val i) (fun i => z i) hz hAlgz hde
  obtain ⟨pr, hpr⟩ := hlift r
  have hqa : MvPolynomial.aeval (fun i => x.val (r i)) pr = 0 := by
    change MvPolynomial.eval₂ (algebraMap K ℝ) (fun i => x.val (r i)) pr = 0
    rw [MvPolynomial.eval₂_eq_eval_map]
    change MvPolynomial.eval (fun i => x.val (r i)) (MvPolynomial.map K.subtype pr) = 0
    rw [hpr]
    exact hpl r x.val hxCl
  have hpr0 := hr.eq_zero_of_aeval_eq_zero pr hqa
  apply hpn r
  rw [← hpr, hpr0, map_zero]

end HodgeLean.Foundations.Program
