import HodgeLean.Foundations.Program.SchoenTowerHardtCad5GenericFiberLimits
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5GraphLifts
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5RankProjection
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5MapAlgebraic

/-! Strict boundary dimension from generic finite fibers and actual CAD root sections. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_boundary_dimension_lt {n : ℕ}
    (S : s2v_t11b_Formula n) (P : s2v_hardt_cad5_Partition S.realize)
    (B : s2v_t11b_Formula n) (Q : s2v_hardt_cad5_Partition B.realize)
    (hB : B.realize = closure S.realize \ S.realize) (hS : S.realize.Nonempty) :
    Q.dimension < P.dimension := by
  classical
  obtain ⟨p, hp⟩ := s2v_hardt_cad5_maximal_cell P hS
  let d := P.dim p
  have hd : (d : ℤ) = P.dimension := hp
  by_contra hbad
  have hnQ : B.realize.Nonempty := by
    by_contra h
    have he := s2v_hardt_cad5_dimension_empty Q (Set.not_nonempty_iff_eq_empty.mp h)
    have hn := s2v_hardt_cad5_dimension_nonneg P hS
    omega
  obtain ⟨q, hq⟩ := s2v_hardt_cad5_maximal_cell Q hnQ
  have hde : d ≤ Q.dim q := by omega
  have hlocal (r : Fin d → Fin n) :
      ∃ Kr : Subfield ℝ, Countable Kr ∧
      ∀ L : Subfield ℝ, Kr ≤ L → ∀ x : EuclideanSpace ℝ (Fin n),
        AlgebraicIndependent L (fun i => x (r i)) → x ∈ closure S.realize → x ∈ S.realize := by
    obtain ⟨R, PR, hR, hdim, hcl⟩ := s2v_hardt_cad5_coordinate_graph_lift S P r
    obtain ⟨Kr, hKr, hlim⟩ := s2v_hardt_cad5_generic_bounded_fiber_limit R PR (by omega)
    refine ⟨Kr, hKr, ?_⟩
    intro L hKL x hgen hx
    have hmem := hlim L hKL (WithLp.toLp 2 (fun i => x (r i))) hgen x (hcl x hx)
    exact ((hR x _).mp hmem).1
  choose Kr hKr hlim using hlocal
  obtain ⟨Kg, hKg, hAlg⟩ := s2v_hardt_cad5_graph_map_algebraic (Q.cell q)
    (fun x => (Q.chart q x).val) (Q.forward q) (Q.forward_eq q)
  let s : Set ℝ := (Kg : Set ℝ) ∪ ⋃ r : Fin d → Fin n, (Kr r : Set ℝ)
  have hs : s.Countable := Set.Countable.union (by
    letI := hKg
    exact Set.to_countable _) (Set.countable_iUnion (fun r => by
      letI := hKr r
      exact Set.to_countable _))
  let K : Subfield ℝ := Subfield.closure s
  letI : Countable K := s2v_hardt_cad5_countable_coefficient_field s hs
  have hKgK : Kg ≤ K := fun _ hc => Subfield.subset_closure (Or.inl hc)
  have hKrK (r : Fin d → Fin n) : Kr r ≤ K := fun _ hc =>
    Subfield.subset_closure (Or.inr (Set.mem_iUnion.mpr ⟨r, hc⟩))
  obtain ⟨z, hz, hbox⟩ := s2v_hardt_cad5_independent_box_point K (Q.dim q)
  let x := (Q.chart q).symm ⟨z, hbox⟩
  have hxB : x.val ∈ B.realize := by
    have hxU : x.val ∈ ⋃ l, (Q.cell l).realize := Set.mem_iUnion.mpr ⟨q, x.property⟩
    simpa only [Q.cover] using hxU
  have hxD : x.val ∈ closure S.realize \ S.realize := by simpa only [hB] using hxB
  let M := (IntermediateField.adjoin K (Set.range (fun i => x.val i))).toSubfield
  have hKM : K ≤ M := by
    intro c hc
    exact (IntermediateField.adjoin K (Set.range (fun i => x.val i))).algebraMap_mem ⟨c, hc⟩
  let a : Fin n → M := fun i => ⟨x.val i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hA : ∀ j, IsAlgebraic M ((Q.chart q x).val j) :=
    hAlg M (hKgK.trans hKM) a x.property
  have hAz : ∀ j, IsAlgebraic M (z j) := by
    simpa only [x, Homeomorph.apply_symm_apply] using hA
  have hAlgz : ∀ j, IsAlgebraic (Algebra.adjoin K (Set.range (fun i => x.val i))) (z j) :=
    fun j => IntermediateField.isAlgebraic_adjoin_iff.mp (hAz j)
  obtain ⟨r, hr⟩ := s2v_hardt_cad5_independent_coordinate_projection_of_le K
    (fun i => x.val i) (fun i => z i) hz hAlgz hde
  exact hxD.2 (hlim r K (hKrK r) x.val hr hxD.1)

end HodgeLean.Foundations.Program
