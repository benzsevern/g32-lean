import HodgeLean.Adapters.NormalConeB4aGysinAffineSliceIsolation

noncomputable section
namespace HodgeLean.Adapters
open Topology

/-- An isolated source slice in an embedded chart gives an isolated
normal disk whose full closed ball remains in the chart. -/
theorem a3b4a_gysin_chart_isolated_normal_radius
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {n c : ℕ} (f : X → Y) (hf : IsClosedEmbedding f)
    (g : X → (Fin n → ℂ))
    (Φ : OpenPartialHomeomorph Y ((Fin n → ℂ) × (Fin c → ℂ)))
    (hcoord : ∀ w, f w ∈ Φ.source → (Φ (f w)).1 = g w)
    (w₀ : X) (hw₀ : f w₀ ∈ Φ.source) (hΦ₀ : Φ (f w₀) = 0)
    (N : Set X) (hN : IsOpen N) (hwN : w₀ ∈ N)
    (hisolate : ∀ w ∈ N, g w = 0 → w = w₀) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ v ∈ Metric.closedBall (0 : Fin c → ℂ) ρ,
        ((0 : Fin n → ℂ), v) ∈ Φ.target) ∧
      ∀ v ∈ Metric.closedBall (0 : Fin c → ℂ) ρ,
        Φ.symm (0, v) ∈ Set.range f → v = 0 := by
  let C := f '' Nᶜ
  have hC : IsClosed C := hf.isClosedMap _ hN.isClosed_compl
  have h0tar : (0 : (Fin n → ℂ) × (Fin c → ℂ)) ∈ Φ.target := by
    rw [← hΦ₀]
    exact Φ.map_source hw₀
  have hsymm0 : Φ.symm (0 : (Fin n → ℂ) × (Fin c → ℂ)) = f w₀ := by
    rw [← hΦ₀]
    exact Φ.left_inv hw₀
  have h0not : Φ.symm (0 : (Fin n → ℂ) × (Fin c → ℂ)) ∉ C := by
    rintro ⟨w, hw, heq⟩
    have hww := hf.injective (heq.trans hsymm0)
    exact hw (hww.symm ▸ hwN)
  let O := Φ.target ∩ Φ.symm ⁻¹' Cᶜ
  have hO : IsOpen O :=
    Φ.continuousOn_symm.isOpen_inter_preimage Φ.open_target hC.isOpen_compl
  let J := (fun v : Fin c → ℂ => ((0 : Fin n → ℂ), v)) ⁻¹' O
  have hJ : IsOpen J := hO.preimage (continuous_const.prodMk continuous_id)
  have h0J : (0 : Fin c → ℂ) ∈ J := ⟨h0tar, h0not⟩
  obtain ⟨ε, hε, hεJ⟩ := Metric.isOpen_iff.mp hJ 0 h0J
  have hball (v : Fin c → ℂ) (hv : v ∈ Metric.closedBall 0 (ε / 2)) :
      ((0 : Fin n → ℂ), v) ∈ O := by
    apply hεJ
    rw [Metric.mem_ball, dist_zero_right]
    have hvnorm : ‖v‖ ≤ ε / 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    exact lt_of_le_of_lt hvnorm (half_lt_self hε)
  refine ⟨ε / 2, half_pos hε, (fun v hv => (hball v hv).1), ?_⟩
  intro v hv hsup
  obtain ⟨w, hw⟩ := hsup
  have hwN' : w ∈ N := by
    by_contra hn
    exact (hball v hv).2 ⟨w, hn, hw⟩
  have hsource := Φ.map_target (hball v hv).1
  rw [← hw] at hsource
  have hp := Φ.right_inv (hball v hv).1
  rw [← hw] at hp
  have hg : g w = 0 := (hcoord w hsource).symm.trans (congrArg Prod.fst hp)
  have hww := hisolate w hwN' hg
  rw [hww, hΦ₀] at hp
  exact (congrArg Prod.snd hp).symm

end HodgeLean.Adapters
