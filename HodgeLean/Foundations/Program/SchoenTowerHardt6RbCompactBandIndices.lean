import HodgeLean.Foundations.Program.SchoenTowerHardtCad3
import Mathlib.Topology.Order.Compact

/-! A cylindrical band contained in a compact carrier has two finite root endpoints. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_compact_band_indices {n r : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : C.Nonempty)
    (ψ : Fin r → C → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hK : IsCompact K)
    (band : Fin (r + 1) → s2v_t11b_Formula (n + 1))
    (hb : ∀ i y, y ∈ (band i).realize ↔ ∃ a : C,
      (∀ v, y v.succ = a.val v) ∧
      (∀ j : Fin r, j.val < i.val → ψ j a < y 0) ∧
      (∀ j : Fin r, i.val ≤ j.val → y 0 < ψ j a))
    (i : Fin (r + 1)) (hsub : (band i).realize ⊆ K) :
    0 < i.val ∧ i.val < r := by
  obtain ⟨a, ha⟩ := hC
  let x : C := ⟨a, ha⟩
  have hheight : Continuous (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z 0) := by fun_prop
  have hcompact := hK.image hheight
  constructor
  · by_contra h
    have hi : i.val = 0 := by omega
    obtain ⟨M, hM⟩ := hcompact.bddBelow
    obtain ⟨L, hL⟩ := (Set.finite_range (fun j => ψ j x)).bddBelow
    let t := min L M - 1
    let z : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (Fin.cons t (fun v => a v))
    have hz : z ∈ (band i).realize := by
      apply (hb i z).mpr
      refine ⟨x, fun _ => rfl, (fun j hj => False.elim (by omega)), ?_⟩
      intro j _
      change t < ψ j x
      exact lt_of_lt_of_le (sub_one_lt (min L M) |>.trans_le (min_le_left L M))
        (hL ⟨j, rfl⟩)
    have hMt : M ≤ t := hM ⟨z, hsub hz, rfl⟩
    have htM : t < M := (sub_one_lt (min L M)).trans_le (min_le_right L M)
    exact (not_lt_of_ge hMt) htM
  · by_contra h
    have hi : i.val = r := by omega
    obtain ⟨M, hM⟩ := hcompact.bddAbove
    obtain ⟨U, hU⟩ := (Set.finite_range (fun j => ψ j x)).bddAbove
    let t := max U M + 1
    let z : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (Fin.cons t (fun v => a v))
    have hz : z ∈ (band i).realize := by
      apply (hb i z).mpr
      refine ⟨x, fun _ => rfl, ?_, (fun j hj => False.elim (by omega))⟩
      intro j _
      change ψ j x < t
      exact (hU ⟨j, rfl⟩).trans_lt ((le_max_left U M).trans_lt (lt_add_one (max U M)))
    have htM : t ≤ M := hM ⟨z, hsub hz, rfl⟩
    have hMt : M < t := (le_max_right U M).trans_lt (lt_add_one (max U M))
    exact (not_lt_of_ge htM) hMt

end HodgeLean.Foundations.Program
