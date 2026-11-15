import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Actual affine sections of the vanishing ideal -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program.G32Native

/-- A regular function whose nonvanishing open avoids a closed set belongs to its actual vanishing ideal. -/
theorem conormal_mem_vanishingIdeal_of_basicOpen
    {X : Scheme} (Z : Closeds X) (U : X.affineOpens) (a : Γ(X, U.1))
    (h : ∀ x ∈ Z, x ∉ X.basicOpen a) :
    a ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  intro p hp
  by_contra ha
  have hb : p ∈ U.property.fromSpec ⁻¹ᵁ X.basicOpen a := by
    rw [U.property.fromSpec_preimage_basicOpen]
    exact ha
  exact h (U.property.fromSpec p) hp hb

end HodgeLean.Foundations.Program.G32Native
