import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ComponentSelector

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Integral unit powers retain generator reconstruction at every complex evaluation, including the zero parameter. -/
theorem normalized_binomial_evaluation_reconstruction
    {A K : Type} [CommRing A] [Field K] (F : A →+* K)
    (w q t : normalizedChart F) (hq : IsUnit q) (a : ℕ) (A₀ : ℤ)
    (hw : (w : K) = (t : K) ^ a * (q : K) ^ A₀) :
    ∀ ev : normalizedChart F →+* ℂ,
      ev w = ev t ^ a * ev q ^ A₀ := by
  let b : normalizedChart F := ⟨(q : K) ^ A₀, normalizedChart_unit_zpow F q hq A₀⟩
  have hwR : w = t ^ a * b := by
    apply Subtype.ext
    exact hw
  intro ev
  rw [hwR, map_mul, map_pow, normalizedChart_unit_zpow_eval F q b hq A₀ rfl ev]

end AlgebraicGeometry.RamifiedNormalization.StageFour
