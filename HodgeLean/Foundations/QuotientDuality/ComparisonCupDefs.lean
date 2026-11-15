import HodgeLean.Adapters.RationalSheafComparisonDefs
import HodgeLean.Foundations.Singular.Cup

/-! # Rational cup transport to the actual sheaf carrier

The canonical comparison transports the independently constructed singular cup.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

/-- The sheaf-carrier cup transported from singular cup by the canonical rational comparison.
This construction applies to singular schemes and has no scheme smoothness parameter.
Source: Bredon, Sheaf Theory, II.7, cup products and comparison; Hatcher, section 3.2. -/
def comparisonSheafCup (X : Over (Spec ↧ℂ))
    (hX : ∀ (x : ComplexPoint X) (U : Opens (ComplexPoint X)), x ∈ U →
      ∃ V : Opens (ComplexPoint X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hb : ∀ n, Function.Bijective (HodgeLean.Adapters.RationalSheafComparison.comparison X hX n))
    (p q : ℕ) : HQ X p →ₗ[ℚ] HQ X q →ₗ[ℚ] HQ X (p + q) :=
  let e (n : ℕ) := LinearEquiv.ofBijective
    (HodgeLean.Adapters.RationalSheafComparison.comparison X hX n).toRatLinearMap (hb n)
  ((HodgeLean.Foundations.Singular.cup (R := ℚ) (TopCat.of (ComplexPoint X))
    (p := p) (q := q) (k := p + q) rfl).compl₁₂
      (e p).symm.toLinearMap (e q).symm.toLinearMap).compr₂ (e (p + q)).toLinearMap

example (X : Over (Spec ↧ℂ))
    (hX : ∀ (x : ComplexPoint X) (U : Opens (ComplexPoint X)), x ∈ U →
      ∃ V : Opens (ComplexPoint X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hb : ∀ n, Function.Bijective (HodgeLean.Adapters.RationalSheafComparison.comparison X hX n))
    (p q : ℕ) (u : Cohomology ℚ (TopCat.of (ComplexPoint X)) p)
    (v : Cohomology ℚ (TopCat.of (ComplexPoint X)) q) :
    comparisonSheafCup X hX hb p q
      (HodgeLean.Adapters.RationalSheafComparison.comparison X hX p u)
      (HodgeLean.Adapters.RationalSheafComparison.comparison X hX q v) =
    HodgeLean.Adapters.RationalSheafComparison.comparison X hX (p + q)
      (HodgeLean.Foundations.Singular.cup (R := ℚ) (TopCat.of (ComplexPoint X))
        (p := p) (q := q) (k := p + q) rfl u v) := by
  let e (n : ℕ) : Cohomology ℚ (TopCat.of (ComplexPoint X)) n ≃ₗ[ℚ] HQ X n :=
    LinearEquiv.ofBijective
      (HodgeLean.Adapters.RationalSheafComparison.comparison X hX n).toRatLinearMap (hb n)
  change e (p + q)
    (HodgeLean.Foundations.Singular.cup (R := ℚ) (TopCat.of (ComplexPoint X))
      (p := p) (q := q) (k := p + q) rfl
      ((e p).symm (e p u)) ((e q).symm (e q v))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  rfl

#print axioms comparisonSheafCup

end HodgeLean.Foundations.QuotientDuality
