import HodgeLean.Foundations.Singular.Transport
import HodgeLean.Foundations.Singular.Exterior
import HodgeLean.Foundations.SingularComparison
import HodgeLean.RealDefs.AbelianVariety

/-! # A cup-product instance on the real rational cohomology

Stage S7 retires O1 by instantiating `CupProduct` for every smooth projective
integral complex variety. HC no distance; AV milestone no distance.
The chosen comparison is not natural and no uniqueness of cup products is asserted.
-/

noncomputable section

-- Boundary conversions between HQ and upstream sheaf cohomology have deep instance terms.
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry ComplexPoint
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The fixed sheaf unit, with the compact HQ type for typeclass inference.
Source: upstream `fieldCohomologyClass ℚ X 1`, the constant degree-zero class. -/
def cupUnit : HQ X 0 := unitClass X

example : cupUnit X = unitClass X := rfl

/-- U1, rescaled to carry the fixed sheaf unit to the singular cup unit.
Source: `Foundations.rationalCohomologyLinearEquivSingular`,
`Foundations.Singular.normalizedEquiv` and `RealDefs.unitClass_ne_zero'`. -/
def cupComparison (n : ℕ) :
    HQ X n ≃ₗ[ℚ] AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint X)) n := by
  letI := Foundations.pathConnectedSpace_complexPoint X
  exact Foundations.Singular.normalizedEquiv (TopCat.of (ComplexPoint X))
    (fun n => (HQ.linearEquiv X n).trans
      (Foundations.rationalCohomologyLinearEquivSingular X n))
    (cupUnit X) (unitClass_ne_zero' X) n

/-- The normalized comparison preserves the actual constant class one.
Source: `Foundations.Singular.normalizedEquiv_unit`. -/
@[simp] theorem cupComparison_unit :
    cupComparison X 0 (cupUnit X) = Foundations.Singular.unit (TopCat.of (ComplexPoint X)) := by
  let := Foundations.pathConnectedSpace_complexPoint X
  exact Foundations.Singular.normalizedEquiv_unit _ _ _ _

example : cupComparison X 0 (cupUnit X) =
    Foundations.Singular.unit (TopCat.of (ComplexPoint X)) := cupComparison_unit X

/-- An instantiated `CupProduct` on upstream rational cohomology: every milestone's
`{μ : CupProduct X}` premise can be supplied by this value. This does not assert
that every instance is this product. The generic-point field is supplied by U3,
`RealDefs.cycleComponentSheafClass_generic`, already proved in `FundamentalClassUnit`.

Source: Hatcher, *Algebraic Topology*, §3.2 and Theorem 3.11, transported along
U1; upstream `Other/AlgebraicTopology/Singular/CohomologyZero.lean` at `2ead713`.
HC no distance; AV milestone no distance. Stage S7 retires O1 for smooth projective integral X. -/
@[hodge_milestone]
def cupProductOf : CupProduct X where
  cup := Foundations.Singular.transportedCup _ (cupComparison X)
  one_cup := by
    intro j a
    change Foundations.Singular.transportedCup _ (cupComparison X) _ (cupUnit X) a = a
    exact Foundations.Singular.transportedCup_one _ (cupComparison X) _ (cupComparison_unit X) a
  cup_one := by
    intro i a
    change Foundations.Singular.transportedCup _ (cupComparison X) _ a (cupUnit X) = a
    exact Foundations.Singular.transportedCup_unit _ (cupComparison X) _ (cupComparison_unit X) a
  assoc := Foundations.Singular.transportedCup_assoc _ (cupComparison X)
  graded_comm := Foundations.Singular.transportedCup_comm _ (cupComparison X)
  fundamental_cup := by
    intro x hx j a
    rw [cycleComponentSheafClass_generic X x hx]
    exact Foundations.Singular.transportedCup_one (V := HQ X) _ (cupComparison X) (cupUnit X) (cupComparison_unit X) a

example : CupProduct X := cupProductOf X

/-- The constructed product intertwines with the singular Alexander–Whitney product.
Source: `Foundations.Singular.map_transportedCup`. -/
@[simp] theorem cupComparison_cup {i j k : ℕ} (h : i + j = k) (a : HQ X i) (b : HQ X j) :
    cupComparison X k ((cupProductOf X).cup h a b) =
      Foundations.Singular.cup (TopCat.of (ComplexPoint X)) h
        (cupComparison X i a) (cupComparison X j b) :=
  Foundations.Singular.map_transportedCup _ (cupComparison X) h a b

/-- The comparison intertwines iterated products, including the empty product.
Source: induction using `cupComparison_cup` and the normalization of the unit. -/
theorem cupComparison_cupMulti (m : ℕ) (v : Fin m → HQ X 1) :
    cupComparison X m ((cupProductOf X).cupMulti m v) =
      Foundations.Singular.cupMulti (TopCat.of (ComplexPoint X)) m
        (fun i => cupComparison X 1 (v i)) := by
  induction m with
  | zero => exact cupComparison_unit X
  | succ m ih =>
    rw [CupProduct.cupMulti_succ _ m (Nat.add_comm 1 m), cupComparison_cup,
      Foundations.Singular.cupMulti_succ _ m (Nat.add_comm 1 m), ih]
    rfl

/-- The normalized comparison takes the sheaf-side wedge map to the singular
wedge map after applying its degree-one part to the exterior power.
Source: `cupComparison_cupMulti` and the universal property of exterior powers. -/
theorem cupComparison_cupWedgeMap (m : ℕ) :
    (cupComparison X m).toLinearMap ∘ₗ (cupProductOf X).cupWedgeMap m =
      Foundations.Singular.cupWedgeMap (TopCat.of (ComplexPoint X)) m ∘ₗ
        exteriorPower.map m (cupComparison X 1).toLinearMap := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, CupProduct.cupWedgeMap_ιMulti, exteriorPower.map_apply_ιMulti,
    Foundations.Singular.cupWedgeMap_ιMulti]
  exact cupComparison_cupMulti X m v

/-- The instantiated product has a nonzero unit.
Source: `RealDefs.CupProduct.unitClass_ne_zero`. -/
theorem cupProductOf_unit_ne_zero : (cupUnit X) ≠ 0 :=
  (cupProductOf X).unitClass_ne_zero

/-- Degree-zero scalar classes multiply their coefficients, in particular on Spec ℂ.
Source: bilinearity and the left unit law of `cupProductOf`. -/
theorem cupProductOf_constants (a b : ℚ) :
    (cupProductOf X).cup (zero_add 0) (a • (cupUnit X)) (b • (cupUnit X)) =
      (a * b) • (cupUnit X) := by
  have hu : (cupProductOf X).cup (zero_add 0) (cupUnit X) (cupUnit X) = cupUnit X :=
    (cupProductOf X).one_cup _
  simp [map_smul, LinearMap.smul_apply, hu, smul_smul, mul_comm]

/-- Scalar multiples of the fixed unit identify degree zero with ℚ. In particular,
the multiplication check on constants tests every degree-zero class.
Source: `Foundations.Singular.exists_smul_unit` transported by `cupComparison`. -/
def cupProductOf_zeroEquiv : ℚ ≃ₗ[ℚ] HQ X 0 :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℚ (HQ X 0) (cupUnit X)) (by
    constructor
    · intro a b hab
      change a • (cupUnit X) = b • unitClass X at hab
      exact (smul_left_injective ℚ (cupProductOf_unit_ne_zero X)) hab
    · intro a
      let := Foundations.pathConnectedSpace_complexPoint X
      obtain ⟨r, hr⟩ := Foundations.Singular.exists_smul_unit
        (TopCat.of (ComplexPoint X)) (cupComparison X 0 a)
      refine ⟨r, (cupComparison X 0).injective ?_⟩
      change cupComparison X 0 (r • (cupUnit X)) = _
      rw [map_smul, cupComparison_unit]
      exact hr)

/-- The degree-zero equivalence sends a scalar to its multiple of the unit.
Source: the defining linear map in `cupProductOf_zeroEquiv`. -/
@[simp] theorem cupProductOf_zeroEquiv_apply (a : ℚ) :
    cupProductOf_zeroEquiv X a = a • cupUnit X := rfl

example (a : ℚ) : cupProductOf_zeroEquiv X a = a • cupUnit X :=
  cupProductOf_zeroEquiv_apply X a

/-- In scalar coordinates cup in degree (0,0) is multiplication, for every X
in the scope of the construction (hence also for a projective presentation of Spec ℂ).
Source: `cupProductOf_constants` and `cupProductOf_zeroEquiv`. -/
theorem cupProductOf_zero_mul (a b : ℚ) :
    (cupProductOf X).cup (zero_add 0) (cupProductOf_zeroEquiv X a) (cupProductOf_zeroEquiv X b) =
      cupProductOf_zeroEquiv X (a * b) := by
  simp only [cupProductOf_zeroEquiv_apply]
  exact cupProductOf_constants X a b

/-- Degree-one classes anticommute for the instantiated product.
Source: Hatcher, *Algebraic Topology*, Theorem 3.11, in degrees (1,1). -/
theorem cupProductOf_anticomm (a b : HQ X 1) :
    (cupProductOf X).cup (rfl : 1 + 1 = 2) b a = -(cupProductOf X).cup rfl a b :=
  (cupProductOf X).cup_comm_one rfl a b

end HodgeLean.Adapters

#print axioms HodgeLean.Adapters.cupProductOf
