import HodgeLean.Foundations.Program.PrymParabolicIntersection
import HodgeLean.Foundations.Program.PrymParabolicDiscriminant
import HodgeLean.Foundations.Program.PeriodFibreMarking
import HodgeLean.Foundations.Program.PrymFamilyShared
import HodgeLean.Foundations.Program.ParabolicPolarizationBridgeChecks

/-! # Definitions for the H7 geometric transport

The restriction of a bilinear form on cellular `H₁(X̃(b4b_root); ℤ)` to the saturated coordinate
lattice `hg6_cellLattice`, and the Weil–Hermitian form of that restriction on
`ℚ ⊗ hg6_cellLattice` with H7's quadratic action `√−3 ↦ 1 + 2Z` (`hg7_cellAction`). Applied to
`hga_cellIntersection`, this is the geometric Weil form on the saturated cellular lattice.
Nothing here compares it with the cup form or computes a determinant class.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations.WeilHermitian
namespace HodgeLean.Foundations.Program

/-- The restriction of a bilinear form on cellular `H₁` to the saturated coordinate lattice.
Source: Bourbaki, *Algebra*, Ch. IX, §1 (restriction of a bilinear form); `hg6_cellLattice`. -/
def hg7g_cellForm (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root)) :
    LinearMap.BilinForm ℤ hg6_cellLattice :=
  B.compl₁₂ hg6_cellLattice.subtype hg6_cellLattice.subtype

example (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root)) (a w : hg6_cellLattice) :
    hg7g_cellForm B a w = B a w := rfl

/-- The integral Weil value `hga_cellWeil` is built from the restricted form.
Source: `hga_cellWeil`. -/
example (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root)) (a w : hg6_cellLattice) :
    hga_cellWeil B a w = ((hg7g_cellForm B a (hg6_cellOperator w) : ℤ) : hp_K) +
      QuadraticAlgebra.omega * ((hg7g_cellForm B a w : ℤ) : hp_K) := rfl

/-- The Weil–Hermitian form `E(x, Jy) + √−3 E(x, y)` of the restricted form on the rational
saturated cellular lattice, with `J = hg6_cellJ` (`hg7_cellAction`). The skewness argument is
the hypothesis of `weilHermitian`; for `B = hga_cellIntersection …` it holds because deck
transformations of the fibre preserve the intersection form.
Source: van Geemen, LNM 1594, §5.2; `b64b_latticeH`, `hg7_cellAction`. -/
def hg7g_cellH (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root))
    (hskew : ∀ x y, (hg7g_cellForm B).baseChange ℚ (hg7_cellAction.1 x) y =
      -(hg7g_cellForm B).baseChange ℚ x (hg7_cellAction.1 y)) :
    WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction →ₗ⋆[hp_K]
      WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction →ₗ[hp_K] hp_K :=
  b64b_latticeH hg6_cellLattice (hg7g_cellForm B) hg7_cellAction hskew

/-- The imaginary coefficient of the Weil form is the rationalized restricted form. -/
example (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root))
    (hskew : ∀ x y, (hg7g_cellForm B).baseChange ℚ (hg7_cellAction.1 x) y =
      -(hg7g_cellForm B).baseChange ℚ x (hg7_cellAction.1 y))
    (x y : WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction) :
    (hg7g_cellH B hskew x y).im =
      (hg7g_cellForm B).baseChange ℚ (WithJ.equiv hg7_cellAction x)
        (WithJ.equiv hg7_cellAction y) := rfl

end HodgeLean.Foundations.Program
