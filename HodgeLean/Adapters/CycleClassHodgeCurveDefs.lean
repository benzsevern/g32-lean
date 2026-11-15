import HodgeLean.RealDefs.Filtration

/-! # The sheaf of holomorphic `q`-forms placed in degree `q` (FROZEN DEFINITIONS)

`holomorphicFormsShifted X q` is the complex `Ω^q[-q]` on `X(ℂ)`: the degree-`q` term of upstream's
holomorphic de Rham complex `Ω•(X)`, alone in degree `q`. It is the graded piece
`σ_{≥q} Ω• / σ_{≥q+1} Ω•` of the Hodge filtration, so `ℍ^n(X; Ω^q[-q]) = H^{n-q}(X(ℂ), Ω^q)`.
For `q = 0` the sheaf is `𝒪_{X(ℂ)}`, the holomorphic functions.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The complex `Ω^q[-q]`: the degree-`q` term `Ω•(X).X q` of upstream's holomorphic de Rham
complex, concentrated in degree `q`. Up to `HomologicalComplex.extendXIso`, `Ω•(X).X q` is
upstream's `holomorphicDeRhamSheaf X (dim X.left) q` for `q ≥ 0`, and it is zero for `q < 0`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76,
§8.3.1 (the graded pieces `Gr^q_F Ω• = Ω^q[-q]` of the Hodge filtration on the holomorphic de Rham
complex); Mathlib's `HomologicalComplex.single`. -/
def holomorphicFormsShifted (q : ℤ) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) q).obj (Ω•(X).X q)

example (q : ℤ) : (holomorphicFormsShifted X q).X q ≅ Ω•(X).X q :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q _

end HodgeLean.Adapters
