import HodgeLean.Foundations.Program.G32Native.PositiveMetricNormalLinearity
import Mathlib.LinearAlgebra.Complex.Module

/-! # Complex linearity of the actual metric normal representatives

The Hermitian identity preserves the original metric orthogonal complement
under multiplication by the complex structure.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.TubularEuler

/-- The canonical metric representative commutes with the complex structure.
Source: Lee, Introduction to Smooth Manifolds, second edition, normal spaces
in Theorem 6.24; Hermitian orthogonal complements of complex subspaces.
HC no distance; AV milestone no distance. -/
theorem positiveMetricRepresentative_I_smul
    {E N : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
    [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
    (G : LinearMap.BilinForm ℝ E) (hsym : ∀ u v, G u v = G v u)
    (hpos : ∀ u, u ≠ 0 → 0 < G u u)
    (hHerm : ∀ u v, G (Complex.I • u) (Complex.I • v) = G u v)
    (T : E →ₗ[ℂ] N) (hT : Function.Surjective T) (n : N) :
    positiveMetricRepresentative G hsym hpos (T.restrictScalars ℝ) hT (Complex.I • n) =
      Complex.I • positiveMetricRepresentative G hsym hpos (T.restrictScalars ℝ) hT n := by
  let L := (LinearEquiv.smulOfNeZero ℂ E Complex.I Complex.I_ne_zero).restrictScalars ℝ
  let V := (LinearEquiv.smulOfNeZero ℂ N Complex.I Complex.I_ne_zero).restrictScalars ℝ
  exact positiveMetricRepresentative_transport G hsym hpos (T.restrictScalars ℝ) hT
    G hsym hpos (T.restrictScalars ℝ) hT L V hHerm (fun u => T.map_smul _ u) n

#print axioms positiveMetricRepresentative_I_smul

/-- The Hermitian metric normal section is complex linear on the original
quotient, with the same uniquely specified representative at each value.
Source: Hermitian orthogonal complements of complex subspaces;
`positiveMetricRepresentative_I_smul` and `positiveMetricRepresentativeLinearMap`.
For example, this gives the complex linear normal displacement required by
`Euclidean.normalMap_transverse_derivative` after the coordinate comparisons.
HC no distance; AV milestone no distance. -/
def hermitianMetricRepresentativeLinearMap
    {E N : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
    [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
    (G : LinearMap.BilinForm ℝ E) (hsym : ∀ u v, G u v = G v u)
    (hpos : ∀ u, u ≠ 0 → 0 < G u u)
    (hHerm : ∀ u v, G (Complex.I • u) (Complex.I • v) = G u v)
    (T : E →ₗ[ℂ] N) (hT : Function.Surjective T) : N →ₗ[ℂ] E where
  toFun := positiveMetricRepresentative G hsym hpos (T.restrictScalars ℝ) hT
  map_add' := (positiveMetricRepresentativeLinearMap G hsym hpos (T.restrictScalars ℝ) hT).map_add
  map_smul' a n := by
    let R := positiveMetricRepresentativeLinearMap G hsym hpos (T.restrictScalars ℝ) hT
    change R (a • n) = a • R n
    have hI (m : N) : R (Complex.I • m) = Complex.I • R m :=
      positiveMetricRepresentative_I_smul G hsym hpos hHerm T hT m
    have hreal (r : ℝ) (m : N) : R ((r : ℂ) • m) = (r : ℂ) • R m := by
      change R ((algebraMap ℝ ℂ r) • m) = (algebraMap ℝ ℂ r) • R m
      rw [IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul, R.map_smul]
    rw [← Complex.re_add_im a]
    simp only [add_smul, mul_smul, map_add, hreal, hI]

#print axioms hermitianMetricRepresentativeLinearMap

end HodgeLean.Foundations.TubularEuler
