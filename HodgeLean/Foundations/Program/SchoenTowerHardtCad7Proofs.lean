import HodgeLean.Foundations.Program.SchoenTowerHardtCad6
import HodgeLean.Foundations.Program.SchoenTowerHardtStages
import HodgeLean.Foundations.Program.SchoenTowerHardtStageGraphs

/-! Pair and scalar assembly from finite frontier partitions. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad7_pair_aux {n m : ℕ}
    (f d : s2v_t11b_Formula n) (hf : IsCompact f.realize)
    (hd : IsCompact d.realize) (hdf : d.realize ⊆ f.realize)
    (b : Fin m → s2v_t11b_Formula n) :
    ∃ k : ℕ, ∃ c : Fin k → s2v_t11b_Formula n, ∃ dim : Fin k → ℕ,
      (∀ i, dim i ≤ n) ∧
      (∀ i, (c i).realize.Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = f.realize ∧
      (∀ i, Nonempty ((c i).realize ≃ₜ
        {t : EuclideanSpace ℝ (Fin (dim i)) | ∀ a, -1 < t a ∧ t a < 1})) ∧
      (∀ i, (c i).realize ⊆ d.realize ∨ Disjoint (c i).realize d.realize) ∧
      (∀ i j, (c i).realize ⊆ (b j).realize ∨
        Disjoint (c i).realize (b j).realize) ∧
      (∀ i j, ((c j).realize ∩ closure (c i).realize).Nonempty →
        (c j).realize ⊆ closure (c i).realize ∧ (j = i ∨ dim j < dim i)) ∧
      ∃ stage : Fin (n + 2) → s2v_t11b_Formula n,
        (∀ r, (stage r).realize = d.realize ∪
          ⋃ i ∈ {i | Disjoint (c i).realize d.realize ∧ dim i < r.val},
            (c i).realize) ∧
        (∀ r, IsCompact (stage r).realize) ∧
        (stage 0).realize = d.realize ∧
        (stage (Fin.last (n + 1))).realize = f.realize := by
  obtain ⟨_, Q, _, _, _, _, _, _, hmarks, hfront⟩ :=
    s2v_hardt_cad6_carrier f (Fin.cons d b)
  refine ⟨Q.count, Q.cell, Q.dim, Q.bound, Q.nonempty, ?_, Q.cover,
    (fun i => ⟨Q.chart i⟩), ?_, ?_, hfront, ?_⟩
  · intro i j hij
    exact Q.disjoint hij
  · intro i
    simpa only [Fin.cons_zero] using hmarks i 0
  · intro i j
    simpa only [Fin.cons_succ] using hmarks i j.succ
  · exact s2v_hardt_stages_of_partition f d Q.cell Q.dim hf hd hdf Q.bound Q.cover
      (fun i => by simpa only [Fin.cons_zero] using hmarks i 0) hfront

theorem s2v_hardt_cad7_scalar_aux {n m : ℕ}
    (f d : s2v_t11b_Formula (n + 1)) (hf : IsCompact f.realize)
    (hd : IsCompact d.realize) (hdf : d.realize ⊆ f.realize)
    (b : Fin m → s2v_t11b_Formula (n + 1)) :
    ∃ k : ℕ, ∃ c : Fin k → s2v_t11b_Formula (n + 1), ∃ dim : Fin k → ℕ,
      (∀ i, dim i ≤ n + 1) ∧
      (∀ i, (c i).realize.Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = f.realize ∧
      (∀ i, Nonempty ((c i).realize ≃ₜ
        {t : EuclideanSpace ℝ (Fin (dim i)) | ∀ a, -1 < t a ∧ t a < 1})) ∧
      (∀ i, (c i).realize ⊆ d.realize ∨ Disjoint (c i).realize d.realize) ∧
      (∀ i j, (c i).realize ⊆ (b j).realize ∨
        Disjoint (c i).realize (b j).realize) ∧
      (∀ i j, ((c j).realize ∩ closure (c i).realize).Nonempty →
        (c j).realize ⊆ closure (c i).realize ∧ (j = i ∨ dim j < dim i)) ∧
      ∃ stage : Fin ((n + 1) + 2) → s2v_t11b_Formula (n + 1),
        (∀ r, (stage r).realize = d.realize ∪
          ⋃ i ∈ {i | Disjoint (c i).realize d.realize ∧ dim i < r.val},
            (c i).realize) ∧
        (∀ r, IsCompact (stage r).realize) ∧
        (stage 0).realize = d.realize ∧
        (stage (Fin.last ((n + 1) + 1))).realize = f.realize ∧
        ∃ graph : Fin ((n + 1) + 2) → s2v_t11b_Formula ((n + 1) + 1),
          (∀ r z,
          z ∈ (graph r).realize ↔
            WithLp.toLp 2 (fun i : Fin (n + 1) => z i.castSucc) ∈ (stage r).realize ∧
            z (Fin.last (n + 1)) = z (Fin.castSucc (Fin.last n))) ∧
          (∀ r s z, z ∈ (graph r).realize →
            (z ∈ (graph s).realize ↔
              WithLp.toLp 2 (fun i : Fin (n + 1) => z i.castSucc) ∈ (stage s).realize)) := by
  obtain ⟨k, c, dim, hbound, hne, hdis, hcov, hchart, hdadapt, hbadapt,
    hfront, stage, hstage, hcompact, hzero, hlast⟩ :=
      s2v_hardt_cad7_pair_aux f d hf hd hdf b
  refine ⟨k, c, dim, hbound, hne, hdis, hcov, hchart, hdadapt, hbadapt,
    hfront, stage, hstage, hcompact, hzero, hlast, ?_⟩
  exact s2v_hardt_stage_graphs stage

end HodgeLean.Foundations.Program
