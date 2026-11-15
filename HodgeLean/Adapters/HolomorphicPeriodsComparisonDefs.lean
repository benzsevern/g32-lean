import HodgeLean.Adapters.HolomorphicPeriodsCocycleDefs
import HodgeLean.Foundations.ComplexSheafSingularDefs

/-! # Coefficient change from `ℚ` to `ℂ`, on singular cochains and on sheaf cohomology

Two coefficient-change maps for the de Rham comparison of the integration cocycle. On singular
cochains of a simplicial set, `cochainBaseChange` sends a rational cochain `ψ` to the complex
cochain with the same values on simplices (built with stage 4i's `simplexCochain`). On sheaf
cohomology of `X(ℂ)`, `fieldCohomologyToComplex` is the map `H^n(X; ℚ) → H^n(X; ℂ)` induced by
upstream's morphism of constant sheaves `ℚ → ℂ` (`fieldToComplexConstantSheafComplexInt ℚ X`),
read through upstream's identification of hypercohomology of `K[0]` with `H^n(X; K)`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open AlgebraicTopology.Simplicial
open HodgeLean.Foundations
open scoped Simplicial

namespace HodgeLean.Adapters

/-- The base change of a rational singular `n`-cochain to complex coefficients: the complex cochain
whose value on each singular `n`-simplex `σ` is the value of `ψ` on `σ`, as a complex number.
Source: Hatcher, *Algebraic Topology*, §3.1 (cochains with coefficients in a group, change of
coefficients `Hom(C_n, ℚ) → Hom(C_n, ℂ)` along `ℚ → ℂ`); stage 4i `simplexCochain`. -/
def cochainBaseChange (Y : SSet.{0}) (n : ℕ) (ψ : Cochain ℚ Y n) : Cochain ℂ Y n :=
  simplexCochain ℂ Y n fun σ ↦ (ψ (chainOfSimplex ℚ σ) : ℂ)

example (Y : SSet.{0}) (n : ℕ) (ψ : Cochain ℚ Y n) :
    cochainBaseChange Y n ψ = simplexCochain ℂ Y n fun σ ↦ (ψ (chainOfSimplex ℚ σ) : ℂ) := rfl

/-- The map `H^n(X(ℂ); ℚ) → H^n(X(ℂ); ℂ)` on sheaf cohomology induced by the inclusion of constant
sheaves `ℚ → ℂ`: upstream's `fieldToComplexConstantSheafComplexInt ℚ X : ℚ[0] → ℂ[0]` on
hypercohomology, between upstream's identifications `ℍ^n(X; K[0]) ≃ H^n(X; K)` for `K = ℚ` and
`K = ℂ` (the complex `ℂ[0]` is upstream's `constantComplexSheafComplexInt X`, which unfolds to
`constantFieldSheafComplexInt ℂ X`).
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, II.4 (cohomology is a functor of the
coefficient sheaf); upstream `hypercohomologyMap` and `hypercohomologyAddEquivConstantCohomology`
(`Definitions/AlgebraicGeometry/Hodge/Filtration.lean`). -/
def fieldCohomologyToComplex (X : Over (Spec ↧ℂ)) (n : ℕ) : H^n(X; ℚ) →+ H^n(X; ℂ) :=
  (hypercohomologyAddEquivConstantCohomology ℂ X n).toAddMonoidHom.comp
    ((hypercohomologyMap X (fieldToComplexConstantSheafComplexInt ℚ X) n).comp
      (hypercohomologyAddEquivConstantCohomology ℚ X n).symm.toAddMonoidHom)

example (X : Over (Spec ↧ℂ)) (n : ℕ) : fieldCohomologyToComplex X n 0 = 0 := map_zero _

end HodgeLean.Adapters
