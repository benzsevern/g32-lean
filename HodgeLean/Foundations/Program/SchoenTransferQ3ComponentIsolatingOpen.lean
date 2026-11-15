import HodgeLean.Adapters.CycleClassSmoothChartsProofs

/-! Target component isolation for actual pure cycles. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
open scoped Classical
namespace HodgeLean.Foundations.Program

/-- A pure-cycle prime has a Zariski neighbourhood avoiding every other
surviving support component, including at the later complex test points. -/
theorem s4_q3_pure_cycle_component_isolating_open
    (W : Scheme.{0}) [CompactSpace W] (z : AlgebraicCycle W ℚ) (k : ℕ)
    (hz : ∀ t ∈ z.support, Order.coheight t = k) (x : W) (hx : x ∈ z.support) :
    ∃ A : W.Opens, x ∈ A ∧
      ∀ y ∈ A, ∀ t ∈ z.support, t ≠ x → y ∉ closure ({t} : Set W) := by
  classical
  let I := {t : W // t ∈ z.support ∧ t ≠ x}
  letI : Fintype I := (z.finite_support.subset (fun _ ht => ht.1)).fintype
  let B : Closeds W := ⨆ t : I, ⟨closure ({t.1} : Set W), isClosed_closure⟩
  have hxB : x ∉ B := by
    intro h
    obtain ⟨t, ht⟩ := (ccm5_mem_finite_iSup _ x).mp h
    have hcod := ccm5_intersection_coheight_lower_bound W k x t.1 x
      (Ne.symm t.2.2) (hz x hx) (hz t.1 t.2.1) (subset_closure (Set.mem_singleton x)) ht
    rw [hz x hx] at hcod
    exact (not_le_of_gt (show (k : ℕ∞) < (k + 1 : ℕ∞) by exact_mod_cast Nat.lt_succ_self k)) hcod
  refine ⟨B.compl, hxB, ?_⟩
  intro y hy t ht htx hyt
  apply hy
  exact (ccm5_mem_finite_iSup _ y).mpr ⟨⟨t, ht, htx⟩, hyt⟩

end HodgeLean.Foundations.Program
