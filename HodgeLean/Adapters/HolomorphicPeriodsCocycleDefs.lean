import HodgeLean.Adapters.HolomorphicPeriodsOnXDefs
import HodgeLean.Adapters.DeRhamAbelianProofs
import HodgeLean.Foundations.Singular.Cup
import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

/-! # The integration cochain of a holomorphic `1`-form on `X(ℂ)`

A singular `1`-simplex `σ : |Δ¹| → Y` is a path `[0, 1] → Y` through Mathlib's homeomorphism
`StdSimplex.homeomorphI : |Δ¹| ≃ₜ [0, 1]`, whose inverse sends `0` and `1` to the vertices `0` and
`1` (`simplexPath`). A loop `ℝ/ℤ → T` gives the singular `1`-simplex `[0, 1] → ℝ/ℤ → T` read
through the same homeomorphism (`loopSimplex`). A function on singular `n`-simplices extends
linearly to a singular `n`-cochain (`simplexCochain`); for a global holomorphic `1`-form `θ` on `X`
the function `σ ↦ ∫_σ θ` (stage 4h's `holomorphicPathIntegral`) gives the integration cochain
`singularIntegrationCochain` in `C^1(X(ℂ); ℂ)`. Rational singular cohomology base changes to
complex singular cohomology through universal coefficients (`cohomologyBaseChange`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open AlgebraicTopology.Simplicial AlgebraicTopology.Singular
open HodgeLean.Foundations
open scoped Simplicial TensorProduct

namespace HodgeLean.Adapters

section Simplices

/-- The path `[0, 1] → Y` of a singular `1`-simplex `σ : |Δ¹| → Y`: `σ` composed with the inverse
of Mathlib's homeomorphism `|Δ¹| ≃ₜ [0, 1]` (the weight of the vertex `1`).
Source: Hatcher, *Algebraic Topology*, §2.1 (singular simplices; a `1`-simplex is a path);
Mathlib's `Convexity.StdSimplex.homeomorphI`. -/
def simplexPath {Y : TopCat.{0}} (σ : (TopCat.toSSet.obj Y) _⦋1⦌) : C(unitInterval, Y) :=
  (Y.toSSetObjEquiv _ σ).comp ⟨_, Convexity.StdSimplex.homeomorphI.symm.continuous⟩

example {Y : TopCat.{0}} (σ : (TopCat.toSSet.obj Y) _⦋1⦌) (t : unitInterval) :
    simplexPath σ t = Y.toSSetObjEquiv _ σ (Convexity.StdSimplex.homeomorphI.symm t) := rfl

/-- The singular `1`-simplex of a loop `p : ℝ/ℤ → T`: the path `t ↦ p t` on `[0, 1]`, read on
`|Δ¹|` through Mathlib's homeomorphism `|Δ¹| ≃ₜ [0, 1]`.
Source: Hatcher, *Algebraic Topology*, §2.A (a loop as a singular `1`-cycle, Hurewicz in degree
one); Mathlib's `Convexity.StdSimplex.homeomorphI`. -/
def loopSimplex {T : Type} [TopologicalSpace T] (p : C(UnitAddCircle, T)) :
    (TopCat.toSSet.obj (TopCat.of T)) _⦋1⦌ :=
  ((TopCat.of T).toSSetObjEquiv _).symm
    ((p.comp ⟨fun t : unitInterval ↦ ((t : ℝ) : UnitAddCircle),
      (AddCircle.continuous_mk' 1).comp continuous_subtype_val⟩).comp
        ⟨_, Convexity.StdSimplex.homeomorphI.continuous⟩)

example {T : Type} [TopologicalSpace T] (p : C(UnitAddCircle, T))
    (s : Convexity.StdSimplex ℝ (Fin 2)) :
    (TopCat.of T).toSSetObjEquiv _ (loopSimplex p) s =
      p ((Convexity.StdSimplex.homeomorphI s : ℝ) : UnitAddCircle) := rfl

/-- The singular `n`-cochain with values `f σ` on the singular `n`-simplices `σ`: the linear
extension of `f` to the free module on simplices.
Source: Hatcher, *Algebraic Topology*, §3.1 (a cochain is a function on singular simplices);
Mathlib's `SSet.isColimitChainComplexXCofan`. -/
def simplexCochain (R : Type) [CommRing R] (Y : SSet.{0}) (n : ℕ) (f : Y _⦋n⦌ → R) :
    Cochain R Y n :=
  ((Y.isColimitChainComplexXCofan (ModuleCat.of R R) n).desc
    (Cofan.mk _ fun σ ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton R R (f σ)))).hom

example (R : Type) [CommRing R] (Y : SSet.{0}) (n : ℕ) (σ : Y _⦋n⦌) (f : Y _⦋n⦌ → R) :
    Y.ιChainComplex (R := ModuleCat.of R R) σ ≫ ModuleCat.ofHom (simplexCochain R Y n f) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R R (f σ)) :=
  (Y.isColimitChainComplexXCofan (ModuleCat.of R R) n).fac _ ⟨σ⟩

end Simplices

section Integration

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [SmoothOfRelativeDimension d X.hom]

/-- The integration cochain of a global holomorphic `1`-form `θ`: the singular `1`-cochain of
`X(ℂ)` with complex coefficients whose value on a singular `1`-simplex `σ` is `∫_σ θ`, stage 4h's
integral of `θ` along the path of `σ`.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., §10.38; Bott–Tu, *Differential Forms in
Algebraic Topology*, §15 (the de Rham map to singular cochains); stage 4h
`holomorphicPathIntegral`. -/
def singularIntegrationCochain (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) :
    Cochain ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1 :=
  simplexCochain ℂ _ 1 fun σ ↦ holomorphicPathIntegral X d θ (simplexPath σ)

example (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) :
    singularIntegrationCochain X d θ =
      simplexCochain ℂ _ 1 fun σ ↦ holomorphicPathIntegral X d θ (simplexPath σ) := rfl

end Integration

section BaseChange

/-- Rational singular cohomology base changed to complex coefficients: `H^n(Y; ℚ) = Hom(H_n(Y; ℚ), ℚ)`
(universal coefficients over a field), a rational functional extended `ℂ`-linearly to
`ℂ ⊗ H_n(Y; ℚ) = H_n(Y; ℂ)`, and `Hom(H_n(Y; ℂ), ℂ) = H^n(Y; ℂ)`.
Source: Hatcher, *Algebraic Topology*, §3.1 (universal coefficient theorem); upstream
`cohomologyEquivDualHomology` and the port of upstream's `qToCHomology_isBaseChange`
(`complexHomologyEquivBaseChange`). -/
def cohomologyBaseChange (Y : TopCat.{0}) (n : ℕ) :
    ℂ ⊗[ℚ] Cohomology ℚ Y n →ₗ[ℂ] Cohomology ℂ Y n :=
  (cohomologyEquivDualHomology ℂ Y n).symm.toLinearMap ∘ₗ
    (Module.Dual.congr (complexHomologyEquivBaseChange Y n)).toLinearMap ∘ₗ
      LinearMap.liftBaseChange ℂ
        (Module.Dual.baseChange ℂ ∘ₗ (cohomologyEquivDualHomology ℚ Y n).toLinearMap)

example (Y : TopCat.{0}) (n : ℕ) : cohomologyBaseChange Y n 0 = 0 := map_zero _

end BaseChange

end HodgeLean.Adapters
