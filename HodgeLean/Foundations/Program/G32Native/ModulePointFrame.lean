import HodgeLean.Foundations.Program.G32Native.OpenPointFibreTransport
import HodgeLean.Foundations.Algebraic.GrassmannianDefs
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # Actual module point fibres in a specified local frame -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- A specified original local frame identifies the actual point fibre
with its original finite tuple of complex frame coefficients. -/
def modulePointFrameEquiv {W : Over (Spec ↧ℂ)} (M : W.left.Modules)
    (U : W.left.Opens) (p : ComplexPoint W) (hp : p ∈ Point.overOpen U) (k : ℕ)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules)) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback p.left).obj M) ≃ₗ[ℂ] (Fin k → ℂ) := by
  let a := liftToOpen W U p hp
  let E := (Scheme.Modules.pullback a).mapIso e ≪≫
    HodgeLean.Foundations.Algebraic.f5_pullbackFreeIso a (Fin k) ≪≫
    (tildeFinsupp (R := CommRingCat.of ℂ) (Fin k)).symm
  exact (openPointFibreEquiv M U p hp).symm.trans
    (((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso E).toLinearEquiv.trans
      (((tilde.toTildeΓNatIso (R := CommRingCat.of ℂ)).app
        (ModuleCat.of ℂ (Fin k →₀ ℂ))).symm.toLinearEquiv.trans
        (Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin k))))

#print axioms modulePointFrameEquiv
end HodgeLean.Foundations.Program.G32Native
