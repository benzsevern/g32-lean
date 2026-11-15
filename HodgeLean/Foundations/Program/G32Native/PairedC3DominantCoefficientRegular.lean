import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Ambient cancellation after pullback to a nonempty affine chart -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A dominant quasi-compact map between integral schemes preserves regular
coefficients on every nonempty affine source chart. Cancellation is in the
ambient section ring, before taking the residual quotient. -/
theorem pairedC3_dominant_affine_coefficient_regular
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ X) [IsDominant p] [QuasiCompact p]
    (U : X.affineOpens) (W : Y.affineOpens) [Nonempty W.1]
    (hW : W.1 ≤ p ⁻¹ᵁ U.1) (u : Γ(X, U)) (hu : IsRegular u) :
    IsRegular ((p.appLE U.1 W.1 hW).hom u) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty W.1)
  letI : Nonempty U.1 := ⟨⟨p x.val, hW x.property⟩⟩
  letI : IsSchemeTheoreticallyDominant p := .of_isDominant p
  have hinj : Function.Injective (p.appLE U.1 W.1 hW).hom :=
    (map_injective_of_isIntegral Y (homOfLE hW)).comp (p.app_injective U.1)
  apply IsRegular.of_ne_zero
  intro hz
  apply hu.ne_zero
  exact hinj (hz.trans (map_zero _).symm)

#print axioms pairedC3_dominant_affine_coefficient_regular
end HodgeLean.Foundations.Program.G32Native
