import HodgeLean.Foundations.Program.SchoenTransferE1
import HodgeLean.Foundations.Program.CyclotomicWeil
import Mathlib.LinearAlgebra.ExteriorPower.Pairing

/-! Actual alternating coordinate cup maps for determinant transport.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- The normalized alternating coordinate image, with the ordered E1 cup convention.
Source: Schoen (1988), Remark 1.4, p. 6. -/
def s4_e2_alternatingCup (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] (h : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] :
    (⋀[ℂ]^h (ℂ ⊗[ℚ] HQ Y 1)) →ₗ[ℂ] (ℂ ⊗[ℚ] HQ (g3_power Y h) h) :=
  letI := (finbetti_finiteBetti Y).finite 1
  (Nat.factorial h : ℂ)⁻¹ •
    (((s4_e1_oneCup Y h).comp (exteriorPower.toTensorPower ℚ (HQ Y 1) h)).baseChange ℂ ∘ₗ
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := HQ Y 1) h).symm.toLinearMap)

example (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] (h : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] : s4_e2_alternatingCup Y h 0 = 0 := map_zero _

/-- The intrinsic primitive curve space for a specified inverse residual character.
Source: Schoen (1988), Lemmas 1.1–1.2, pp. 5–6; Remark 1.4, pp. 6–7. -/
def s4_e2_curveSpace (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (t : cyc_Field S.m →ₐ[ℚ] ℂ) : Submodule ℂ (ℂ ⊗[ℚ] HQ Y 1) :=
  (LinearMap.ker (Polynomial.aeval
    (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
    (Polynomial.cyclotomic S.m ℚ))).baseChange ℂ ⊓
    ⨅ u : S.H, Module.End.eigenspace
      ((homPullback (a ((QuotientGroup.mk u)⁻¹)) 1).baseChange ℂ)
      (t (g32p_fieldValue S u))

example (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (t : cyc_Field S.m →ₐ[ℚ] ℂ) : 0 ∈ s4_e2_curveSpace S Y a e t := Submodule.zero_mem _

#print axioms s4_e2_alternatingCup
#print axioms s4_e2_curveSpace
end HodgeLean.Foundations.Program
