import HodgeLean.Adapters.CupCocycleSheaf
import HodgeLean.Adapters.HolomorphicPeriodsComparison
import HodgeLean.Adapters.CupProductOf
import HodgeLean.RealDefs.CupFiltered

/-! # Transport of the left cup with a degree-one cocycle: definitions

Stage hl4 of the `hL` track (`docs/specs/CupLeftTransport.md`). Two comparison maps through which
the action of `C_a` on hypercohomology (stage hl2, `cupLeftHypercohomology`) is read on `HQ X k`
and on `ℂ ⊗[ℚ] HQ X k`:

1. `sheafHypercohomologyFieldEquiv K X n : ℍ^n(S•_K) ≃+ H^n(X(ℂ); K)`, the last two legs of stage
   3c's `singularToFieldCohomology` (the inverse of the constants-to-cochains equivalence, then
   Mathlib's sheaf cohomology). Its composite with hl2's `singularToSheafHypercohomology` is
   `singularToFieldCohomology` (see the `example`). For `K = ℚ` it is the brief's `e_n`.
2. `complexSingularClass X n : ℂ ⊗[ℚ] HQ X n →ₗ[ℂ] H^n_sing(X(ℂ); ℂ)`, the base change to `ℂ` of
   `cupComparison X n`, followed by the universal-coefficient base change `cohomologyBaseChange`.
   It is the map through which stage 4j compares `bettiDeRhamHQ` with the complex comparison
   (`spec_deRham_singularToFieldCohomology_cohomologyBaseChange`).

Everything here is a definition. HC no distance; AV milestone no distance.
-/

noncomputable section

-- Boundary conversions between HQ and upstream sheaf cohomology have deep instance terms.
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry ComplexPoint
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- The identification `ℍ^n(X(ℂ); S•_K) ≃ H^n(X(ℂ); K)` of the hypercohomology of the
`K`-singular-cochain resolution with sheaf cohomology of the constant sheaf, for a field `K` and
smooth integral `X`: the inverse of upstream's constants-to-cochains equivalence (postcomposition
with the quasi-isomorphism `K[0] → S•_K`), then upstream's `ℍ^n(X; K[0]) ≃ H^n(X; K)`.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1 (singular cochain sheaves resolve the
constant sheaf); stage 3c `fieldHypercohomologySingularCochainAddEquiv` and upstream
`hypercohomologyAddEquivConstantCohomology`. -/
def sheafHypercohomologyFieldEquiv (K : Type) [Field K] (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    Hypercohomology X (singularCochainSheafComplexInt X K) n ≃+ H^n(X; K) :=
  (fieldHypercohomologySingularCochainAddEquiv K X n).symm.trans
    (hypercohomologyAddEquivConstantCohomology K X n)

example (K : Type) [Field K] (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (n : ℕ)
    (y : AlgebraicTopology.Singular.Cohomology K (TopCat.of (ComplexPoint X)) n) :
    singularToFieldCohomology K X n y =
      sheafHypercohomologyFieldEquiv K X n (singularToSheafHypercohomology X K n y) := rfl

/-- The complex singular class of `ω ∈ ℂ ⊗[ℚ] HQ X n`: the base change to `ℂ` of `cupComparison X n`
(so `z ⊗ v ↦ z ⊗ cupComparison X n v`), followed by the universal-coefficient base change
`ℂ ⊗[ℚ] H^n_sing(X(ℂ); ℚ) → H^n_sing(X(ℂ); ℂ)`.
Source: Hatcher, *Algebraic Topology*, §3.A (universal coefficients) and §3.1 (change of
coefficients); stage 4i `cohomologyBaseChange`; `cupComparison`. -/
def complexSingularClass (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (n : ℕ) :
    ℂ ⊗[ℚ] HQ X n →ₗ[ℂ] AlgebraicTopology.Singular.Cohomology ℂ (TopCat.of (ComplexPoint X)) n :=
  cohomologyBaseChange (TopCat.of (ComplexPoint X)) n ∘ₗ
    LinearMap.baseChange ℂ (cupComparison X n).toLinearMap

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ)
    (z : ℂ) (v : HQ X n) :
    complexSingularClass X n (z ⊗ₜ v) =
      cohomologyBaseChange (TopCat.of (ComplexPoint X)) n (z ⊗ₜ cupComparison X n v) := rfl

end HodgeLean.Adapters
