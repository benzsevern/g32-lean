import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RootLabelTopology

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The root homeomorphism retains the literal root attached to each gcd label. -/
theorem binomialRootHomeomorph_symm_value
    (g : ℕ) (hg : 0 < g) (κ ζ : ℂ) (hκ : κ ≠ 0)
    (hζ : IsPrimitiveRoot ζ g) (j : ZMod g) :
    ((binomialRootHomeomorph g hg κ ζ hκ hζ).symm j).val = κ * ζ ^ j.val := by
  rfl

end AlgebraicGeometry.RamifiedNormalization.StageFour
