import HodgeLean.Adapters.NormalConeB4Defs

/-! # Supported-to-ordinary cycle-class map
The target retains the original scheme over the complex base.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual supported group for a rational cycle in the specified codimension.
Source: Fulton, Intersection Theory, §19.1; Hatcher, §3.1. -/
abbrev s2e_supportedClass (W : Over (Spec ↧ℂ)) (γ : AlgebraicCycle W.left ℚ) (k : ℕ) :=
  AlgebraicTopology.Singular.RelativeCohomology ℚ
    (TopPair.ofSubset (X := a3b4_an W.hom) (a3b4_cycleSupport W.hom γ)ᶜ) (2 * k)

example (W : Over (Spec ↧ℂ)) (γ : AlgebraicCycle W.left ℚ) (k : ℕ) :
    s2e_supportedClass W γ k := 0

/-- Forget support while retaining the original complex-point space as target.
Source: Hatcher, §3.1, relative-to-absolute cohomology. -/
def s2e_classToAbsolute (W : Over (Spec ↧ℂ)) (γ : AlgebraicCycle W.left ℚ) (k : ℕ) :
    s2e_supportedClass W γ k →ₗ[ℚ]
      AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W)) (2 * k) :=
  AlgebraicTopology.Singular.relativeCohomologyToAbsolute ℚ _ (2 * k)

example (W : Over (Spec ↧ℂ)) (γ : AlgebraicCycle W.left ℚ) (k : ℕ) :
    s2e_classToAbsolute W γ k 0 = 0 := map_zero _

end HodgeLean.Foundations.Program
