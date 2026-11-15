import HodgeLean.Foundations.Program.SchoenTowerHardtCad5IndependentBoxes
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! Finite coordinate bounds from algebraic dependence and independence. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_independent_le_coordinates {n m : ℕ} (K : Subfield ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (hx : AlgebraicIndependent K x)
    (ha : ∀ i, IsAlgebraic (Algebra.adjoin K (Set.range y)) (x i)) : n ≤ m := by
  let M := AlgebraicIndependent.matroid K ℝ
  have hi : M.Indep (Set.range x) :=
    AlgebraicIndependent.matroid_indep_iff.mpr hx.to_subtype_range
  have hs : Set.range x ⊆ M.closure (Set.range y) := by
    rintro _ ⟨i, rfl⟩
    rw [AlgebraicIndependent.matroid_closure_eq]
    exact ha i
  have hc := hi.cardinalMk_le_cRk_of_subset hs
  rw [M.cRk_closure] at hc
  have hcard : Cardinal.mk (Fin n) ≤ Cardinal.mk (Fin m) := calc
    Cardinal.mk (Fin n) = Cardinal.mk (Set.range x) := (Cardinal.mk_range_eq x hx.injective).symm
    _ ≤ M.cRk (Set.range y) := hc
    _ ≤ Cardinal.mk (Set.range y) := M.cRk_le_cardinalMk _
    _ ≤ Cardinal.mk (Fin m) := Cardinal.mk_range_le
  simpa using hcard

theorem s2v_hardt_cad5_independent_coordinate_projection {n e d : ℕ}
    (K : Subfield ℝ) (x : Fin n → ℝ) (z : Fin e → ℝ)
    (hz : AlgebraicIndependent K z)
    (ha : ∀ i, IsAlgebraic (Algebra.adjoin K (Set.range x)) (z i))
    (hde : d < e) :
    ∃ r : Fin (d + 1) → Fin n, AlgebraicIndependent K (fun i => x (r i)) := by
  classical
  let M := AlgebraicIndependent.matroid K ℝ
  have hi : M.Indep (Set.range z) :=
    AlgebraicIndependent.matroid_indep_iff.mpr hz.to_subtype_range
  have hs : Set.range z ⊆ M.closure (Set.range x) := by
    rintro _ ⟨i, rfl⟩
    rw [AlgebraicIndependent.matroid_closure_eq]
    exact ha i
  have hc := hi.cardinalMk_le_cRk_of_subset hs
  rw [M.cRk_closure, Cardinal.mk_range_eq z hz.injective] at hc
  obtain ⟨B, hB⟩ := M.exists_isBasis (Set.range x)
  have hcard : Cardinal.mk (Fin (d + 1)) ≤ Cardinal.mk B := calc
    Cardinal.mk (Fin (d + 1)) ≤ Cardinal.mk (Fin e) := by simpa using (Nat.succ_le_of_lt hde)
    _ ≤ M.cRk (Set.range x) := hc
    _ = Cardinal.mk B := hB.cardinalMk_eq_cRk.symm
  obtain ⟨emb⟩ := (Cardinal.le_def (Fin (d + 1)) B).mp hcard
  choose r hr using fun i => hB.subset (emb i).property
  have hInd : AlgebraicIndependent K (fun i => (emb i).val) :=
    (AlgebraicIndependent.matroid_indep_iff.mp hB.indep).comp emb emb.injective
  refine ⟨r, ?_⟩
  have heq : (fun i => x (r i)) = (fun i => (emb i).val) := funext hr
  rw [heq]
  exact hInd

end HodgeLean.Foundations.Program
