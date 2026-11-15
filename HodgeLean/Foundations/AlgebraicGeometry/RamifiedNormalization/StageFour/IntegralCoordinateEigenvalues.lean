import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.CanonicalBranchParameter
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.CoordinateEigenvalues

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Every integral evaluation retains the original generator, selector and canonical parameter eigenvalues under the specified ring restriction. -/
theorem normalized_binomial_deck_evaluation
    {A K : Type} [CommRing A] [Field K] (F : A →+* K)
    (σ : K ≃+* K) (ρ : normalizedChart F ≃+* normalizedChart F)
    (hρ : ∀ b, (ρ b : K) = σ (b : K))
    (s : A) (w q t c : normalizedChart F) (hc : IsUnit c)
    (hs : σ (F s) = F s) (hw : σ (w : K) = (c : K) * (w : K))
    (n a : ℕ) (A₀ B₀ : ℤ)
    (hq : (q : K) = (w : K) ^ n / F s ^ a)
    (ht : (t : K) = F s ^ A₀ * (w : K) ^ B₀) :
    ∀ ev : normalizedChart F →+* ℂ,
      ev (ρ w) = ev c * ev w ∧
      ev (ρ q) = ev c ^ n * ev q ∧
      ev (ρ t) = ev c ^ B₀ * ev t := by
  have hwR : ρ w = c * w := by
    apply Subtype.ext
    exact (hρ w).trans hw
  obtain ⟨hqK, htK⟩ := binomial_coordinate_eigenvalues σ (F s) (w : K) (c : K)
    hs hw n a A₀ B₀
  have hqR : ρ q = c ^ n * q := by
    apply Subtype.ext
    change (ρ q : K) = (c : K) ^ n * (q : K)
    rw [hρ, hq, hqK]
  let b : normalizedChart F := ⟨(c : K) ^ B₀, normalizedChart_unit_zpow F c hc B₀⟩
  have htR : ρ t = b * t := by
    apply Subtype.ext
    change (ρ t : K) = (c : K) ^ B₀ * (t : K)
    rw [hρ, ht, htK]
  intro ev
  refine ⟨?_, ?_, ?_⟩
  · rw [hwR, map_mul]
  · rw [hqR, map_mul, map_pow]
  · rw [htR, map_mul, normalizedChart_unit_zpow_eval F c b hc B₀ rfl ev]

end AlgebraicGeometry.RamifiedNormalization.StageFour
