import HodgeLean.Foundations.Program.CompensationCubicSmooth

namespace HodgeLean.Foundations.Program.CompensationCubic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable def affineEval (x y : ℂ) (h : W.toAffine.Equation x y) :
    W.toAffine.CoordinateRing →+* ℂ :=
  AdjoinRoot.lift (Polynomial.evalRingHom x) y (by
    rw [Polynomial.eval₂_evalRingHom]; exact h)

example (x y : ℂ) (h : W.toAffine.Equation x y) :
    affineEval x y h (AdjoinRoot.root W.toAffine.polynomial) = y := by
  simp [affineEval]

end HodgeLean.Foundations.Program.CompensationCubic
