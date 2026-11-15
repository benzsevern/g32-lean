import HodgeLean.Foundations.Program.PeriodCoordinates
import HodgeLean.Foundations.Program.PrymVariationFrames

/-! # B6-4b: rational markings and their complexifications

The implication from a rational polarized marking to marked filtration coordinates uses
extension of scalars through ℤ → ℚ → ℂ. HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations.WeilHermitian
namespace HodgeLean.Foundations.Program

/-- Complexification of a rational marking, with the intermediate rational tensor removed.
Source: Bourbaki, Algebra, Ch. II, §5, transitivity of extension of scalars. -/
def b64b_complexMarking (M : Type*) [AddCommGroup M]
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice)) :
    (ℂ ⊗[ℤ] M) ≃ₗ[ℂ] (ℂ ⊗[ℤ] b60_Lattice) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ M).symm |>.trans
    ((m.baseChange ℚ ℂ _ _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ b60_Lattice))

example : b64b_complexMarking b60_Lattice (LinearEquiv.refl ℚ _) =
    LinearEquiv.refl ℂ _ := by
  apply LinearEquiv.toLinearMap_injective
  ext c
  simp [b64b_complexMarking, LinearEquiv.baseChange_tmul]

/-- The Hermitian form of a rationalized integral pairing and a quadratic action.
Its imaginary coefficient is the original rational pairing, with positive sign.
Source: van Geemen, LNM 1594, §5.2; `WeilHermitian.weilHermitian`. -/
def b64b_latticeH (M : Type*) [AddCommGroup M]
    (Q : LinearMap.BilinForm ℤ M)
    (J : {J : Module.End ℚ (ℚ ⊗[ℤ] M) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id})
    (hskew : ∀ x y, Q.baseChange ℚ (J.1 x) y = -Q.baseChange ℚ x (J.1 y)) :=
  weilHermitian (Q.baseChange ℚ) J hskew

example (M : Type*) [AddCommGroup M] (Q : LinearMap.BilinForm ℤ M)
    (J : {J : Module.End ℚ (ℚ ⊗[ℤ] M) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id})
    (hskew : ∀ x y, Q.baseChange ℚ (J.1 x) y = -Q.baseChange ℚ x (J.1 y))
    (x y : WithJ (ℚ ⊗[ℤ] M) J) :
    (b64b_latticeH M Q J hskew x y).im =
      Q.baseChange ℚ (WithJ.equiv J x) (WithJ.equiv J y) := rfl

end HodgeLean.Foundations.Program
