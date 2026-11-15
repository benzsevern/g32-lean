import HodgeLean.Foundations.Program.SchoenTowerHardtCad5PartitionTopAssembly
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5FiniteExtraction
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5OpenChartRefinement
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5ChartTopRefinement
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5BoundaryDimension
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5ClosureDimension
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Boolean
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Unions
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Comparison
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Diagonal
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Defs

/-! Ordered dimension comparisons and extraction interfaces. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_invariance_aux {n q : ℕ} (S : s2v_t11b_Formula n) (T : s2v_t11b_Formula q)
    (P : s2v_hardt_cad5_Partition S.realize)
    (Q : s2v_hardt_cad5_Partition S.realize)
    (R : s2v_hardt_cad5_Partition T.realize) :
    P.dimension = Q.dimension ∧
    ∀ (f : S.realize ≃ T.realize) (G : s2v_t11b_Formula (n + q)),
      (∀ (x : S.realize) (y : EuclideanSpace ℝ (Fin q)),
        WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => y v)) ∈ G.realize ↔
          y = (f x).val) → P.dimension = R.dimension := by
  obtain ⟨D, hD⟩ := s2v_hardt_cad5_diagonal_formula n
  have hpq := s2v_hardt_cad5_dimension_le_of_graph_injective P Q
    (fun x => x) Function.injective_id D (fun x y => hD x.val y)
  have hqp := s2v_hardt_cad5_dimension_le_of_graph_injective Q P
    (fun x => x) Function.injective_id D (fun x y => hD x.val y)
  refine ⟨le_antisymm hpq hqp, ?_⟩
  intro f G hG
  have hpr := s2v_hardt_cad5_dimension_le_of_graph_injective P R f f.injective G hG
  obtain ⟨J, hJ⟩ := s2v_hardt_cad5_relation_restricted_reverse S G
  have hInv : ∀ (y : T.realize) (x : EuclideanSpace ℝ (Fin n)),
      WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => x v)) ∈ J.realize ↔
        x = (f.symm y).val := by
    intro y x
    rw [hJ x y.val]
    constructor
    · rintro ⟨hx, hxy⟩
      have hfx : f ⟨x, hx⟩ = y :=
        Subtype.ext ((hG ⟨x, hx⟩ y.val).mp hxy).symm
      have h := congrArg f.symm hfx
      exact congrArg Subtype.val ((f.symm_apply_apply ⟨x, hx⟩).symm.trans h)
    · intro hx
      subst x
      refine ⟨(f.symm y).property, (hG (f.symm y) y.val).mpr ?_⟩
      exact (congrArg Subtype.val (f.apply_symm_apply y)).symm
  exact le_antisymm hpr
    (s2v_hardt_cad5_dimension_le_of_graph_injective R P f.symm f.symm.injective J hInv)

theorem s2v_hardt_cad5_unions_aux {n k : ℕ} (B : Fin k → s2v_t11b_Formula n)
    (P : (i : Fin k) → s2v_hardt_cad5_Partition (B i).realize)
    (U : s2v_hardt_cad5_Partition (⋃ i, (B i).realize))
    (S T : s2v_t11b_Formula n)
    (Q : s2v_hardt_cad5_Partition S.realize)
    (R : s2v_hardt_cad5_Partition T.realize) :
    U.dimension =
      (Finset.univ.image (fun i => (P i).dimension) ∪ {-1}).max' (by simp) ∧
    (S.realize ⊆ T.realize → Q.dimension ≤ R.dimension) := by
  exact ⟨s2v_hardt_cad5_partition_union_dimension B P U,
    s2v_hardt_cad5_partition_dimension_mono Q R⟩

theorem s2v_hardt_cad5_closure_aux {n : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) :
    ∃ C : s2v_t11b_Formula n, ∃ Q : s2v_hardt_cad5_Partition C.realize,
      C.realize = closure S.realize ∧ Q.dimension = P.dimension := by
  obtain ⟨C, Q, hC⟩ := s2v_hardt_cad5_closure_partition S
  refine ⟨C, Q, hC, le_antisymm (s2v_hardt_cad5_closure_dimension_le S P C Q hC) ?_⟩
  apply s2v_hardt_cad5_partition_dimension_mono P Q
  intro x hx
  rw [hC]
  exact subset_closure hx

theorem s2v_hardt_cad5_boundary_aux {n : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) :
    ∃ B : s2v_t11b_Formula n, ∃ Q : s2v_hardt_cad5_Partition B.realize,
      B.realize = closure S.realize \ S.realize ∧
      (S.realize.Nonempty → Q.dimension < P.dimension) ∧
      (S.realize = ∅ → B.realize = ∅ ∧ Q.dimension = -1 ∧ P.dimension = -1) := by
  obtain ⟨B, Q, hB⟩ := s2v_hardt_cad5_boundary_partition S
  refine ⟨B, Q, hB, fun hn => s2v_hardt_cad5_boundary_dimension_lt S P B Q hB hn, ?_⟩
  intro hS
  have hBE : B.realize = ∅ := by rw [hB, hS, closure_empty, Set.sdiff_self]
  exact ⟨hBE, s2v_hardt_cad5_dimension_empty Q hBE, s2v_hardt_cad5_dimension_empty P hS⟩

theorem s2v_hardt_cad5_chart_top_aux {n d k : ℕ} (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ (x : C.realize) (z : EuclideanSpace ℝ (Fin d)),
      WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ G.realize ↔
        z = (e x).val)
    (J : s2v_t11b_Formula (d + n))
    (hJ : ∀ (z : {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
      (x : EuclideanSpace ℝ (Fin n)),
      WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ J.realize ↔
        x = (e.symm z).val)
    (Z : Fin k → s2v_t11b_Formula n)
    (PZ : s2v_hardt_cad5_Partition (⋃ j, (Z j).realize))
    (hZ : PZ.dimension < (d : ℤ)) :
    ∃ P : s2v_hardt_cad5_Partition (C.realize \ ⋃ j, (Z j).realize),
    ∃ R : s2v_t11b_Formula n, ∃ Q : s2v_hardt_cad5_Partition R.realize,
      (∀ i, P.dim i ≤ d) ∧
      (∀ i, P.dim i = d →
        IsOpen {x : C.realize | x.val ∈ (P.cell i).realize}) ∧
      R.realize = C.realize \ (⋃ i : {i : Fin P.count // P.dim i = d},
        (P.cell i.val).realize) ∧
      Q.dimension < (d : ℤ) := by
  obtain ⟨Q₀, hbound, ha, hopen⟩ := s2v_hardt_cad5_open_chart_refinement C e G hG J hJ Z
  exact s2v_hardt_cad5_chart_top_from_refinement C Z PZ hZ Q₀ hbound ha hopen

theorem s2v_hardt_cad5_partition_top_aux {n : ℕ} (S : s2v_t11b_Formula n)
    (P : s2v_hardt_cad5_Partition S.realize) :
    ∃ Z : s2v_t11b_Formula n, ∃ PZ : s2v_hardt_cad5_Partition Z.realize,
    ∃ U : s2v_t11b_Formula n, ∃ PU : s2v_hardt_cad5_Partition U.realize,
    ∃ R : s2v_t11b_Formula n, ∃ PR : s2v_hardt_cad5_Partition R.realize,
    ∃ parent : Fin PU.count → Fin P.count,
      Z.realize =
        (⋃ i, closure (P.cell i).realize \ (P.cell i).realize) ∪
        (⋃ i : {i : Fin P.count // (P.dim i : ℤ) < P.dimension},
          closure (P.cell i.val).realize) ∧
      (S.realize.Nonempty → PZ.dimension < P.dimension) ∧
      (∀ i, (PU.dim i : ℤ) = P.dimension ∧
        (P.dim (parent i) : ℤ) = P.dimension) ∧
      (∀ i, (PU.cell i).realize ⊆ (P.cell (parent i)).realize \ Z.realize) ∧
      (∀ i, IsOpen {x : S.realize | x.val ∈ (PU.cell i).realize}) ∧
      (∀ i, IsOpen {x : (P.cell (parent i)).realize | x.val ∈ (PU.cell i).realize}) ∧
      (∀ i j, i ≠ j → Disjoint (PU.cell j).realize (closure (PU.cell i).realize)) ∧
      R.realize = S.realize \ U.realize ∧
      (S.realize.Nonempty → PR.dimension < P.dimension) ∧
      (S.realize = ∅ → PU.count = 0 ∧ R.realize = ∅ ∧ PR.dimension = -1) := by
  classical
  by_cases hE : S.realize = ∅
  · exact s2v_hardt_cad5_finite_partition_top S P (hE ▸ Set.finite_empty)
  have hn : S.realize.Nonempty := Set.nonempty_iff_ne_empty.mpr hE
  obtain ⟨i, hi⟩ := s2v_hardt_cad5_maximal_cell P hn
  obtain ⟨Z, PZ, hZ, hPZ⟩ := s2v_hardt_cad5_exceptional_union P hi.symm
  obtain ⟨U, PU, R, PR, parent, hdim, hsub, hopen, hparentOpen, hsep, hR, hPR⟩ :=
    s2v_hardt_cad5_partition_top_assembly S P hi.symm Z PZ hZ hPZ
  exact ⟨Z, PZ, U, PU, R, PR, parent, hZ, fun _ => hPZ.trans_eq hi,
    hdim, hsub, hopen, hparentOpen, hsep, hR, fun _ => hPR,
    fun h => (hE h).elim⟩

end HodgeLean.Foundations.Program
