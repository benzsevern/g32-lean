import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionChains
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CoefficientBaseChange
import Mathlib.RingTheory.Localization.Rat

/-! Finite rational chains and integral coefficient lifts.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Extending coefficients sends any integral simplex coefficient to its rational value.
Source: Hatcher, Algebraic Topology, section 2.1, singular chains with coefficients.
HC no distance; AV milestone no distance.
-/
theorem integralToRational_iota (X : SSet.{0}) (n : ℕ)
    (x : X.obj (Opposite.op (SimplexCategory.mk n))) (r : ℤ) :
    (integralToCoefficientChainComponent ℚ X n).hom
      ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom r) =
      (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x).hom (r : ℚ) := by
  have h := ConcreteCategory.congr_hom (iota_integralToCoefficientChainComponent ℚ X n x) r
  simpa using h

#print axioms integralToRational_iota
/-- One nonzero integer multiple of every finite rational singular chain has integral coefficients.
Source: Hatcher, Algebraic Topology, section 2.1, finite singular chains over rational coefficients.
HC no distance; AV milestone no distance.
-/
theorem rationalChain_integral_multiple (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X n) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ y : ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).X n,
      (integralToCoefficientChainComponent ℚ (TopCat.toSSet.obj X) n).hom y = (d : ℚ) • z := by
  classical
  let e := (chainGroupFinsuppIso ℚ X n).toLinearEquiv
  let c := e z
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) c.support c
  let a := fun i => if h : i ∈ c.support then (hd i h).choose else 0
  have ha (i) (hi : i ∈ c.support) : (a i : ℚ) = (d : ℤ) • c i := by
    dsimp only [a]
    rw [dif_pos hi]
    simpa using (hd i hi).choose_spec
  refine ⟨d, nonZeroDivisors.coe_ne_zero d, ∑ i ∈ c.support,
    ((TopCat.toSSet.obj X).ιChainComplex (R := AddCommGrpCat.of ℤ) i).hom (a i), ?_⟩
  apply e.injective
  simp only [map_sum, map_smul]
  change (∑ i ∈ c.support, e ((integralToCoefficientChainComponent ℚ
    (TopCat.toSSet.obj X) n).hom
      (((TopCat.toSSet.obj X).ιChainComplex (R := AddCommGrpCat.of ℤ) i).hom (a i)))) =
    (d : ℚ) • c
  calc
    _ = ∑ i ∈ c.support, Finsupp.single i (a i : ℚ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (congrArg e (integralToRational_iota (TopCat.toSSet.obj X) n i (a i))).trans
        (chainGroupFinsuppIso_iota ℚ X n i (a i : ℚ))
    _ = ∑ i ∈ c.support, Finsupp.single i ((d : ℚ) * c i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ha i hi, zsmul_eq_mul]
    _ = (d : ℚ) • c := by
      simp only [← smul_eq_mul, ← Finsupp.smul_single, ← Finset.smul_sum]
      rw [← Finsupp.sum, Finsupp.sum_single]

#print axioms rationalChain_integral_multiple
end HodgeLean.Foundations.RationalHomologyManifold
