import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeCharts

/-! # Conserved finite fibre sums under a source chart

A centered chart transports finite local fibre sums, with their original
weights, to a coordinate ball.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem chart_fibre_length_conservation
    {M : Type} [TopologicalSpace M] (d : ℕ)
    (parameter : M → (Fin d → ℂ)) (length : (Fin d → ℂ) → M → ℕ∞)
    (x₀ : M) (m : ℕ)
    (e : OpenPartialHomeomorph M (Fin d → ℂ)) (hx : x₀ ∈ e.source) (he0 : e x₀ = 0)
    (hfamily : ∃ N₀ : Set M, IsOpen N₀ ∧ x₀ ∈ N₀ ∧
      ∀ N : Set M, IsOpen N → x₀ ∈ N → N ⊆ N₀ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin d → ℂ, ‖a‖ < δ →
          ∃ F : Finset M, (∀ w, w ∈ F ↔ w ∈ N ∧ parameter w = a) ∧
            ∑ w ∈ F, length a w = (m : ℕ∞)) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : Fin d → ℂ) r ⊆ e.target ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin d → ℂ, ‖a‖ < δ →
        ∃ T : Finset (Fin d → ℂ), (T : Set (Fin d → ℂ)) ⊆ Metric.ball 0 r ∧
          (∀ v ∈ Metric.ball (0 : Fin d → ℂ) r, parameter (e.symm v) = a ↔ v ∈ T) ∧
          ∑ v ∈ T, length a (e.symm v) = (m : ℕ∞) := by
  classical
  obtain ⟨N₀, hN₀, hxN₀, hcons⟩ := hfamily
  let O := e.target ∩ e.symm ⁻¹' N₀
  have hO : IsOpen O := e.isOpen_inter_preimage_symm hN₀
  have h0O : (0 : Fin d → ℂ) ∈ O := by
    rw [← he0]
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x₀) ∈ N₀
    rwa [e.left_inv hx]
  obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.mp hO 0 h0O
  let r := ρ / 2
  have hr : 0 < r := half_pos hρ
  have hball : Metric.closedBall (0 : Fin d → ℂ) r ⊆ O :=
    (Metric.closedBall_subset_ball (half_lt_self hρ)).trans hρO
  let N := e.source ∩ e ⁻¹' Metric.ball (0 : Fin d → ℂ) r
  have hN : IsOpen N := e.isOpen_inter_preimage Metric.isOpen_ball
  have hxN : x₀ ∈ N := ⟨hx, he0 ▸ Metric.mem_ball_self hr⟩
  have hNN₀ : N ⊆ N₀ := by
    intro w hw
    have hh := (hball (Metric.ball_subset_closedBall hw.2)).2
    change e.symm (e w) ∈ N₀ at hh
    rwa [e.left_inv hw.1] at hh
  obtain ⟨δ, hδ, hδc⟩ := hcons N hN hxN hNN₀
  refine ⟨r, hr, (fun _ hv => (hball hv).1), δ, hδ, ?_⟩
  intro a ha
  obtain ⟨F, hF, hsum⟩ := hδc a ha
  have hFN (w) (hw : w ∈ F) : w ∈ N := ((hF w).mp hw).1
  let T := F.image e
  have hTV : (T : Set (Fin d → ℂ)) ⊆ Metric.ball 0 r := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (hFN w hw).2
  refine ⟨T, hTV, ?_, ?_⟩
  · intro v hv
    have hvt : v ∈ e.target := (hball (Metric.ball_subset_closedBall hv)).1
    have hvin : e.symm v ∈ N := by
      refine ⟨e.map_target hvt, ?_⟩
      change e (e.symm v) ∈ Metric.ball 0 r
      rwa [e.right_inv hvt]
    constructor
    · intro hparams
      have hwF : e.symm v ∈ F := (hF _).mpr ⟨hvin, hparams⟩
      exact Finset.mem_image.mpr ⟨e.symm v, hwF, e.right_inv hvt⟩
    · intro hvT
      obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hvT
      have heinv : e.symm v = w := hwv ▸ e.left_inv (hFN w hw).1
      rw [heinv]
      exact ((hF w).mp hw).2
  · change ∑ v ∈ F.image e, length a (e.symm v) = _
    rw [Finset.sum_image]
    · calc
        _ = ∑ w ∈ F, length a w := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [e.left_inv (hFN w hw).1]
        _ = _ := hsum
    · intro w hw w' hw' heq
      exact e.injOn (hFN w hw).1 (hFN w' hw').1 heq


end AlgebraicGeometry.SingularCycles
