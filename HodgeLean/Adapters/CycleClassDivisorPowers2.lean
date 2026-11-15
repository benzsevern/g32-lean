import HodgeLean.Adapters.CycleClassDivisorPowers2Proofs

/-! # Top-degree polarization powers (frozen specification)

An implication from the smooth projective integral group instances and the
dimension equality, with no positivity requirement on the degree-two class.
Only the top power is covered. Intermediate powers and divisor intersection
compatibility remain separate tasks. The theta square has a separate nonzero claim.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 2048
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Curves
namespace HodgeLean.Adapters

/-- Source: Hatcher, Algebraic Topology, Theorem 3.26; Fulton,
Intersection Theory, second edition, §19.1; finrank_HQ_abelian. -/
theorem ccm9_top_cycle_span (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (k : ℕ) (hk : dim X.left = k) :
    algebraicCycleClassSpan X k = ⊤ :=
  ccm9_top_cycle_span_aux X k hk

/-- Only the top power is asserted; no positivity of the class is required.
Source: Fulton, Intersection Theory, second edition, §19.1;
the top-degree line and its nonzero point class. -/
theorem ccm9_polarization_pow_algebraic (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (η : HQ X 2) (k : ℕ) (hk : dim X.left = k) :
    cupPow X (cupProductOf X) η k ∈ algebraicCycleClassSpan X k :=
  ccm9_polarization_pow_algebraic_aux X η k hk

/-- The product of the two point polarizations has nonzero square.
Source: Birkenhake--Lange, Complex Abelian Varieties, second edition,
§1.3 and §4.1; the exterior algebra of the direct sum of two rank-two spaces. -/
theorem ccm9_theta_square_ne_zero :
    cupPow (g3_power E 2) (cupProductOf (g3_power E 2)) ccm8_thetaClass 2 ≠ 0 :=
  ccm9_theta_square_ne_zero_aux

/-- W1: the constructed square has top degree four.
Source: spec_g2_dim_eq and E_dim. -/
example : algebraicCycleClassSpan (g3_power E 2) 2 = ⊤ :=
  ccm9_top_cycle_span (g3_power E 2) 2
    (by rw [spec_g2_dim_eq (g3_powerData E 2), E_dim])

/-- W2: the cubic point divisor supplies a nonzero algebraic top power.
Source: E_dim, the point-class construction, and its nonvanishing theorem. -/
example : cupPow E (cupProductOf E) ccm8_pointClass 1 ∈ algebraicCycleClassSpan E 1 ∧
    ccm8_pointClass ≠ 0 :=
  ⟨ccm9_polarization_pow_algebraic E ccm8_pointClass 1 E_dim,
    divisorCycleClass_pointDivisor_ne_zero E cubicInfinity cubicInfinity_isClosed⟩

/-- W3: the theta-product class supplies both surface top-power inputs.
All geometric instances and the dimension equality are constructed on E².
Source: the two top-power statements and spec_g2_dim_eq. -/
example :
    cupPow (g3_power E 2) (cupProductOf (g3_power E 2)) ccm8_thetaClass 2
        ∈ algebraicCycleClassSpan (g3_power E 2) 2 ∧
      cupPow (g3_power E 2) (cupProductOf (g3_power E 2)) ccm8_thetaClass 2 ≠ 0 :=
  ⟨ccm9_polarization_pow_algebraic (g3_power E 2) ccm8_thetaClass 2
    (by rw [spec_g2_dim_eq (g3_powerData E 2), E_dim]), ccm9_theta_square_ne_zero⟩

end HodgeLean.Adapters
