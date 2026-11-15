import HodgeLean.Adapters.AbelianPowerProofs
import HodgeLean.Adapters.AbelianCMData

/-! # The Powers flagship, stage G3 part 1: the power `A^r` (FROZEN SPEC)

Stage G3 (optional), part 1, of formalizing PW v0.3, Theorem 4.2 (`thm:gen`), "Hodge classes on
powers of abelian varieties of Weil type and of type IV with exact endomorphism algebra"
(doi:10.5281/zenodo.23570103). Every statement of G2 and G4 about powers takes power data
`P : AbelianPowerData A Y r` with `Y` in scope (`[GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
[Smooth Y.hom] [IsProjective Y.hom]`). This stage builds the candidate `Y = A^r`, the iterated
fibre product `g3_power A r` over `Spec ℂ` (`AbelianPowerDefs.lean`), and its power data
`g3_powerData A r`. Each theorem is proved by the matching `_aux` theorem in
`AbelianPowerProofs.lean`.

It claims:

* `A^r` with the projections `p_i = g3_proj A r i` is a categorical product of `r` copies of `A`
  in `Over (Spec ℂ)` (S1);
* for a commutative group object `A`, `A^r` is a commutative group object; the `p_i` and the
  inclusions `s_i` are group homomorphisms; `p_j ∘ s_i = δ_ij` and `Σ_i s_i ∘ p_i = 𝟙`; hence the
  power data `g3_powerData A r : AbelianPowerData A (g3_power A r) r`, unconditionally (S2–S6);
* `r = 1`: `p_0 = ρ_A` and `s_0 = ρ_A⁻¹` (agreement with G4's `Y = A` example up to the right
  unitor) (S7);
* falsification: for `r ≥ 1`, commutativity of `A^r` forces commutativity of `A`, so a
  non-commutative group object has no power data of this form; `r ≥ 1` is needed, since `A^0` is
  commutative for every `A` (S8);
* scheme properties: `A^r` is smooth over `ℂ`, of relative dimension `r · d` if `A` has relative
  dimension `d`; `A^r` is integral **if `A` is geometrically integral over `ℂ`** (S9–S11);
* degenerate cases: `A^0 = Spec ℂ` is integral and projective, and `A^1 = A ⊗ 𝟙_` is integral and
  projective when `A` is; so for `r ≤ 1` every scope instance of `A^r` is discharged, and the
  power-data statements of G4 apply to `g3_powerData A r` with no extra binder (S12–S15).

It does not claim: that `A^r` is integral for `r ≥ 2` without the binder
`[GeometricallyIntegral A.hom]` (geometric integrality of an integral scheme over `ℂ` is absent
from Mathlib); that `A^r` is projective for `r ≥ 2` (the Segre embedding is absent); the dimension
`dim (A^r) = r · dim A` of the irreducible space (it follows from G2's `spec_g2_dim_eq` once G2
merges, under the scope binders); any cohomological or Hodge statement about `A^r`. Where the
binders `[IsIntegral (g3_power A r).left]`, `[IsProjective (g3_power A r).hom]` appear, the
statement is an implication from them. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory Limits
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

variable (A : Over (Spec ↧ℂ))

/-! ### The categorical product -/

/-- **S1. `A^r` is the product of `r` copies of `A`.** The fan `(A^r, p_i)` is a limit fan in
`Over (Spec ℂ)`: by induction on `r`, from the binary product `A ⊗ A^r` (cartesian monoidal
structure) and the terminal object `𝟙_`, as in Mathlib's `extendFanIsLimit`.
Source: Mac Lane, *Categories for the Working Mathematician*, §III.4 (finite products from binary
products and a terminal object); Mathlib `Limits.extendFanIsLimit`,
`SemiCartesianMonoidalCategory.isTerminalTensorUnit`,
`CartesianMonoidalCategory.tensorProductIsBinaryProduct`. -/
theorem spec_g3_isLimit_fan (r : ℕ) :
    Nonempty (IsLimit (Fan.mk (g3_power A r) (g3_proj A r))) :=
  spec_g3_isLimit_fan_aux A r

/-- So `A^r` is isomorphic to Mathlib's `∏ᶜ` of the constant family. -/
example (r : ℕ) [HasProduct fun _ : Fin r => A] :
    Nonempty (g3_power A r ≅ ∏ᶜ fun _ : Fin r => A) :=
  (spec_g3_isLimit_fan A r).map fun h => h.conePointUniqueUpToIso (limit.isLimit _)

/-! ### The group structure and the power data -/

section Group

variable [GrpObj A]

/-- **S2. `A^r` is commutative.** By induction on `r`: Mathlib's `IsCommMonObj (𝟙_ C)` and
`IsCommMonObj (M ⊗ N)` for commutative `M`, `N`.
Source: Mumford, *Abelian Varieties*, §4 (abelian varieties are commutative); Mathlib
instances `IsCommMonObj (𝟙_ C)` and `IsCommMonObj (M ⊗ N)` (`Monoidal/Mon.lean`). -/
theorem spec_g3_isCommMonObj_power [IsCommMonObj A] (r : ℕ) : IsCommMonObj (g3_power A r) :=
  spec_g3_isCommMonObj_power_aux A r

example [IsCommMonObj A] (r : ℕ) : IsCommMonObj (g3_power A r) :=
  spec_g3_isCommMonObj_power A r

attribute [instance] spec_g3_isCommMonObj_power

/-- **S3. The projections are group homomorphisms.** `fst` and `snd` are monoid homomorphisms
(Mathlib), and composites of homomorphisms are homomorphisms. No commutativity is needed.
Source: Mathlib `CartesianMonoidalCategory` instances `IsMonHom (fst M N)`, `IsMonHom (snd M N)`
(`Monoidal/Cartesian/Mon.lean`), and `IsMonHom (f ≫ g)` (`Monoidal/Mon.lean`). -/
theorem spec_g3_isMonHom_proj (r : ℕ) (i : Fin r) : IsMonHom (g3_proj A r i) :=
  spec_g3_isMonHom_proj_aux A r i

example (r : ℕ) (i : Fin r) : IsMonHom (g3_proj A r i) :=
  spec_g3_isMonHom_proj A r i

/-- **S4. The inclusions are group homomorphisms.** The constant map `1 = toUnit ≫ η` is a
homomorphism for any monoid object, and `lift` of homomorphisms is one. No commutativity is
needed.
Source: Mathlib `IsMonHom (lift f g)`, `IsMonHom (toUnit M)` (`Monoidal/Cartesian/Mon.lean`), `η`
a monoid homomorphism `𝟙_ ⟶ M` (unit laws). -/
theorem spec_g3_isMonHom_incl (r : ℕ) (i : Fin r) : IsMonHom (g3_incl A r i) :=
  spec_g3_isMonHom_incl_aux A r i

example (r : ℕ) (i : Fin r) : IsMonHom (g3_incl A r i) :=
  spec_g3_isMonHom_incl A r i

/-- **S5. `p_j ∘ s_i = δ_ij`.** `fst ≫`, `snd ≫` pick the components of `lift`; `1 ≫ p_j = 1`
because `p_j` is a homomorphism (S3).
Source: Mac Lane, *Categories for the Working Mathematician*, §VIII.2 (biproduct identities);
Mathlib `CartesianMonoidalCategory.lift_fst`, `lift_snd`, `IsMonHom.one_hom`. -/
theorem spec_g3_incl_proj (r : ℕ) (i j : Fin r) :
    g3_incl A r i ≫ g3_proj A r j = if i = j then 𝟙 A else 1 :=
  spec_g3_incl_proj_aux A r i j

example (r : ℕ) (i j : Fin r) :
    g3_incl A r i ≫ g3_proj A r j = if i = j then 𝟙 A else 1 :=
  spec_g3_incl_proj A r i j

/-- **S6. `Σ_i s_i ∘ p_i = 𝟙`** in the commutative group `A^r ⟶ A^r`. The product in
`X ⟶ A ⊗ A^n` is componentwise, so the left side is `lift fst (snd ≫ Σ_i s_i ∘ p_i)`, which is
`lift fst snd = 𝟙` by induction; at `r = 0` both sides are the unique endomorphism of `𝟙_`.
Source: Mac Lane, *Categories for the Working Mathematician*, §VIII.2; Mathlib `Hom.commMonoid`,
`CartesianMonoidalCategory.lift_fst_snd`. -/
theorem spec_g3_prod_proj_incl [IsCommMonObj A] (r : ℕ) :
    ∏ i, (g3_proj A r i ≫ g3_incl A r i) = 𝟙 (g3_power A r) :=
  spec_g3_prod_proj_incl_aux A

example [IsCommMonObj A] (r : ℕ) :
    ∏ i, (g3_proj A r i ≫ g3_incl A r i) = 𝟙 (g3_power A r) :=
  spec_g3_prod_proj_incl A r

/-- **The power data of `A^r`**: `p_i = g3_proj A r i`, `s_i = g3_incl A r i`, with S3–S6. It
needs no scheme property of `A`.
Source: PW v0.3, Theorem 4.2 (the powers `A^r`); `spec_g3_isMonHom_proj`,
`spec_g3_isMonHom_incl`, `spec_g3_incl_proj`, `spec_g3_prod_proj_incl`. -/
def g3_powerData [IsCommMonObj A] (r : ℕ) : AbelianPowerData A (g3_power A r) r where
  proj := g3_proj A r
  incl := g3_incl A r
  proj_isMonHom := spec_g3_isMonHom_proj A r
  incl_isMonHom := spec_g3_isMonHom_incl A r
  incl_proj := spec_g3_incl_proj A r
  sum_proj_incl := spec_g3_prod_proj_incl A r

example [IsCommMonObj A] (r : ℕ) (i : Fin r) : (g3_powerData A r).proj i = g3_proj A r i := rfl

/-- **S7. `r = 1`: agreement with G4's `Y = A`.** `A^1 = A ⊗ 𝟙_`, and its projection and
inclusion are the right unitor `ρ_A : A ⊗ 𝟙_ ≅ A` and its inverse; G4's example
`AbelianPowerData A A 1` has `p = s = 𝟙 A`, so the two agree up to `ρ_A`.
Source: Mathlib `CartesianMonoidalCategory.rightUnitor_hom` (`ρ_ = fst`), `lift_fst`,
`toUnit_unique` (so `(ρ_ A).inv = lift (𝟙 A) (toUnit A)`). -/
theorem spec_g3_proj_incl_one : g3_proj A 1 0 = (ρ_ A).hom ∧ g3_incl A 1 0 = (ρ_ A).inv :=
  spec_g3_proj_incl_one_aux A

example : g3_proj A 1 0 = (ρ_ A).hom ∧ g3_incl A 1 0 = (ρ_ A).inv :=
  spec_g3_proj_incl_one A

/-- **S8. Falsification: a non-commutative `A` is excluded.** For `r ≥ 1`, `A` is a retract of
`A^r` by the homomorphisms `s_0`, `p_0` with `s_0 ≫ p_0 = 𝟙 A`, so commutativity of `A^r` forces
commutativity of `A`. So `IsCommMonObj A` in `g3_powerData` (and `IsCommMonObj Y` in
`AbelianPowerData`) cannot be dropped for `A^r`.
Source: Mac Lane, *Categories for the Working Mathematician*, §VIII.2; Mathlib
`isCommMonObj_iff_isMulCommutative` (a monoid object is commutative iff each `X ⟶ M` is). -/
theorem spec_g3_isCommMonObj_of_power {r : ℕ} (hr : 0 < r) [IsCommMonObj (g3_power A r)] :
    IsCommMonObj A :=
  spec_g3_isCommMonObj_of_power_aux A hr

example {r : ℕ} (hr : 0 < r) [IsCommMonObj (g3_power A r)] : IsCommMonObj A :=
  spec_g3_isCommMonObj_of_power A hr

/-- At `r = 0` the conclusion of S8 fails to follow: `A^0 = 𝟙_` is commutative for every group
object `A`, so `0 < r` is needed. -/
example : IsCommMonObj (g3_power A 0) := inferInstanceAs (IsCommMonObj (𝟙_ (Over (Spec ↧ℂ))))

end Group

/-! ### Scheme properties -/

/-- **S9. `A^r` is smooth over `ℂ`.** `(A ⊗ A^n).hom = pullback.fst A.hom (A^n).hom ≫ A.hom`; smooth
morphisms are stable under base change and composition; `𝟙` is smooth.
Source: Stacks Project, Morphisms of Schemes, section "Smooth morphisms" (composition and base
change); Mathlib
`smooth_isStableUnderBaseChange`, `smooth_comp`. -/
theorem spec_g3_smooth_power [Smooth A.hom] (r : ℕ) : Smooth (g3_power A r).hom :=
  spec_g3_smooth_power_aux A r

example [Smooth A.hom] (r : ℕ) : Smooth (g3_power A r).hom :=
  spec_g3_smooth_power A r

attribute [instance] spec_g3_smooth_power

/-- **S10. Relative dimension `r · d`.** As S9, with `SmoothOfRelativeDimension` (additive under
composition, stable under base change; `𝟙` has relative dimension `0`).
Source: Stacks Project, Morphisms of Schemes, section "Smooth morphisms"; Mathlib
`smoothOfRelativeDimension_comp`,
`smoothOfRelativeDimension_isStableUnderBaseChange`. -/
theorem spec_g3_smoothOfRelativeDimension_power (d : ℕ) [SmoothOfRelativeDimension d A.hom]
    (r : ℕ) : SmoothOfRelativeDimension (r * d) (g3_power A r).hom :=
  spec_g3_smoothOfRelativeDimension_power_aux A d r

example (d : ℕ) [SmoothOfRelativeDimension d A.hom] (r : ℕ) :
    SmoothOfRelativeDimension (r * d) (g3_power A r).hom :=
  spec_g3_smoothOfRelativeDimension_power A d r

/-- **S11. `A^r` is integral if `A` is geometrically integral.** By induction: `A.hom` is
geometrically integral, flat and universally open (smooth), and `A^n` is integral and locally
noetherian (of finite type over `ℂ`), so `A ×_ℂ A^n` is integral (Mathlib). The binder
`[GeometricallyIntegral A.hom]` is not derivable from `[IsIntegral A.left]` in Mathlib yet.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.3.15 (geometrically irreducible and reduced
schemes) and Ex. I.3.15 (products of varieties are irreducible); Mathlib `GeometricallyIntegral`,
`GeometricallyIntegral.isIntegral_of_isLocallyNoetherian`, `UniversallyOpen.of_flat`,
`LocallyOfFiniteType.isLocallyNoetherian`. -/
theorem spec_g3_isIntegral_power [Smooth A.hom] [GeometricallyIntegral A.hom] (r : ℕ) :
    IsIntegral (g3_power A r).left :=
  spec_g3_isIntegral_power_aux A r

example [Smooth A.hom] [GeometricallyIntegral A.hom] (r : ℕ) :
    IsIntegral (g3_power A r).left :=
  spec_g3_isIntegral_power A r

attribute [instance] spec_g3_isIntegral_power

/-! ### Degenerate cases: `r = 0` and `r = 1` are in scope -/

/-- **S12. `A^0 = Spec ℂ` is integral.**
Source: Mathlib `affine_isIntegral_iff` (`Spec R` is integral iff `R` is a domain). -/
theorem spec_g3_isIntegral_power_zero : IsIntegral (g3_power A 0).left :=
  spec_g3_isIntegral_power_zero_aux A

example : IsIntegral (g3_power A 0).left :=
  spec_g3_isIntegral_power_zero A

/-- **S13. `A^0 = Spec ℂ` is projective over `ℂ`.** `𝟙 (Spec ℂ)` has a projective presentation in
`ℙ^0`.
Source: `HodgeLean.Foundations.isProjective_specComplex_id` (`Foundations/ProjectivePoint.lean`). -/
theorem spec_g3_isProjective_power_zero : IsProjective (g3_power A 0).hom :=
  spec_g3_isProjective_power_zero_aux A

example : IsProjective (g3_power A 0).hom :=
  spec_g3_isProjective_power_zero A

/-- **S14. `A^1` is integral when `A` is.** `(A ⊗ 𝟙_).left = pullback A.hom (𝟙 _)`, and
`pullback.fst` is an isomorphism onto `A.left`.
Source: Mathlib `IsIntegral.of_isIso`, `pullback.fst` an isomorphism when the other leg is. -/
theorem spec_g3_isIntegral_power_one [IsIntegral A.left] : IsIntegral (g3_power A 1).left :=
  spec_g3_isIntegral_power_one_aux A

example [IsIntegral A.left] : IsIntegral (g3_power A 1).left :=
  spec_g3_isIntegral_power_one A

/-- **S15. `A^1` is projective when `A` is.** Precompose a presentation of `A.hom` with the
isomorphism `pullback.fst : A ×_ℂ Spec ℂ ≅ A`: an isomorphism followed by a closed immersion is a
closed immersion, and the composite with `ℙ^d → Spec ℂ` is `(A ⊗ 𝟙_).hom`.
Source: Hartshorne, *Algebraic Geometry*, §II.4 (projective morphisms); Mathlib
`IsClosedImmersion` (stable under composition, isomorphisms are closed immersions). -/
theorem spec_g3_isProjective_power_one [IsProjective A.hom] : IsProjective (g3_power A 1).hom :=
  spec_g3_isProjective_power_one_aux A

example [IsProjective A.hom] : IsProjective (g3_power A 1).hom :=
  spec_g3_isProjective_power_one A

attribute [instance] spec_g3_isIntegral_power_zero spec_g3_isProjective_power_zero
  spec_g3_isIntegral_power_one spec_g3_isProjective_power_one

/-! ### The non-vacuity link with G4 (and G2) -/

section Link

variable [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- `r = 0`, no extra binder: G4's falsification check applies to `A^0 = Spec ℂ`, so
`H¹(Spec ℂ) = 0`. -/
example (y : HQ (g3_power A 0) 1) : y = 0 :=
  spec_g4_eq_zero_of_powerData_zero (g3_powerData A 0) y

/-- `r = 1`, no extra binder: G4's pullback formula for `f_a` on `A^1`. -/
example (a : Fin 1 → AbelianEnd A) :
    homPullback ((g3_powerData A 1).sumMap a) 1 =
      ∑ i, homPullback ((g3_powerData A 1).proj i) 1 ∘ₗ abelianEndAction A (a i) :=
  spec_g4_homPullback_sumMap (g3_powerData A 1) a

/-- Every `r`, under exactly the two binders that remain: integrality and projectivity of `A^r`
(smoothness is S9). -/
example (r : ℕ) [IsIntegral (g3_power A r).left] [IsProjective (g3_power A r).hom]
    (a : Fin r → AbelianEnd A) :
    homPullback ((g3_powerData A r).sumMap a) 1 =
      ∑ i, homPullback ((g3_powerData A r).proj i) 1 ∘ₗ abelianEndAction A (a i) :=
  spec_g4_homPullback_sumMap (g3_powerData A r) a

/-- The same with integrality from S11: the remaining binders are `GeometricallyIntegral A.hom`
and projectivity of `A^r`. -/
example (r : ℕ) [GeometricallyIntegral A.hom] [IsProjective (g3_power A r).hom]
    (a : Fin r → AbelianEnd A) :
    homPullback ((g3_powerData A r).sumMap a) 1 =
      ∑ i, homPullback ((g3_powerData A r).proj i) 1 ∘ₗ abelianEndAction A (a i) :=
  spec_g4_homPullback_sumMap (g3_powerData A r) a

end Link

end HodgeLean.Adapters
