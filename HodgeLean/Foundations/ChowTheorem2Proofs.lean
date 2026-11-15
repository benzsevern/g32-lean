import HodgeLean.Foundations.AnalyticSubset

/-! # Standard-chart cone comparison: proof obligation

HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations
open Set

/-- Analytic equations on a normalized standard slice lift to the cone off its vertex.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
standard affine coordinates in the cone proof of Chow's theorem. -/
theorem chow2_chart_cone_aux (n : ℕ) (C : Set (Fin (n + 1) → ℂ))
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ C, t • z ∈ C)
    (i : Fin (n + 1))
    (hslice : IsClosedAnalytic (Fin n → ℂ)
      {w | i.insertNth (1 : ℂ) w ∈ C})
    (x : Fin (n + 1) → ℂ) (hx : x ∈ C) (hxi : x i ≠ 0) :
    ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z i ≠ 0} ∧
      ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ C ↔ ∀ j, f j z = 0) := by
  let q : (Fin (n + 1) → ℂ) → (Fin n → ℂ) :=
    fun z j => z (i.succAbove j) / z i
  have hnorm (z : Fin (n + 1) → ℂ) (hz : z i ≠ 0) :
      i.insertNth (1 : ℂ) (q z) = (z i)⁻¹ • z := by
    apply Fin.insertNth_eq_iff.2
    constructor
    · simp [hz]
    · funext j
      simp [Fin.removeNth, q, div_eq_inv_mul, mul_comm]
  have hqx : i.insertNth (1 : ℂ) (q x) ∈ C := by
    rw [hnorm x hxi]
    exact hscale _ (inv_ne_zero hxi) x hx
  obtain ⟨V, hVo, hqxV, -, m, g, hg, hVg⟩ := hslice.2 (q x) hqx
  simp at hqxV hVg
  let P : Set (Fin (n + 1) → ℂ) := {z | z i ≠ 0}
  have hPo : IsOpen P := isOpen_compl_singleton.preimage (continuous_apply i)
  have hq : AnalyticOnNhd ℂ q P := by
    rw [analyticOnNhd_pi_iff]
    intro j
    have hn : AnalyticOnNhd ℂ (fun z : Fin (n + 1) → ℂ => z (i.succAbove j)) P := fun z _ =>
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ)
        (i.succAbove j)).analyticAt z
    have hd : AnalyticOnNhd ℂ (fun z : Fin (n + 1) → ℂ => z i) P := fun z _ =>
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) i).analyticAt z
    exact hn.div hd (fun z hz => hz)
  let U := q ⁻¹' V ∩ P
  have hUo : IsOpen U := by
    simpa [U, inter_comm] using hq.continuousOn.isOpen_inter_preimage hPo hVo
  refine ⟨U, hUo, ⟨hqxV, hxi⟩, inter_subset_right, m, fun j z => g j (q z), ?_, ?_⟩
  · intro j
    exact (hg j).comp (hq.mono inter_subset_right) inter_subset_left
  · intro z hz
    rw [← hVg (q z) hz.1]
    rw [hnorm z hz.2]
    constructor
    · exact fun h => hscale _ (inv_ne_zero hz.2) z h
    · intro h
      have hback := hscale (z i) hz.2 _ h
      simpa [smul_smul, mul_inv_cancel₀ hz.2] using hback

end HodgeLean.Foundations
