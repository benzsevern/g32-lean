import HodgeLean.Adapters.AbelianPowerLinkProofs

/-! # The Powers flagship, G3 link: Theorem 4.2 at `Y = A^r` for every `r` (FROZEN SPEC)

The link stage between G3 and the flagship statements F1 and G2, towards PW v0.3, Theorem 4.2
(`thm:gen`), "Hodge classes on powers of abelian varieties of Weil type and of type IV with exact
endomorphism algebra" (doi:10.5281/zenodo.23570103). F1 (`PWTheorem42Eisenstein.lean`) and G2
(`AbelianPowerHodge.lean`) are stated for any `Y` with power data `P : AbelianPowerData A Y r` and
the scope instances `[GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
[IsProjective Y.hom]`. G3 builds `A^r = g3_power A r` with `g3_powerData A r` and registers every
one of those instances for `A^r`, from the scope instances of `A` alone:

| instance on `A^r` | found by | from |
|---|---|---|
| `GrpObj` | `g3_grpObj` | `[GrpObj A]` |
| `IsCommMonObj` | `spec_g3_isCommMonObj_power` | `[IsCommMonObj A]` |
| `IsIntegral (·).left` | `spec_g3b_isIntegral_power` | `[IsIntegral A.left] [Smooth A.hom]` |
| `Smooth (·).hom` | `spec_g3_smooth_power` | `[Smooth A.hom]` |
| `IsProjective (·).hom` | `spec_g3c_isProjective_power` | `[IsProjective A.hom]` |

So this stage restates F1's and G2's main statements at `Y = g3_power A r`,
`P = g3_powerData A r`, for every `r`, with no binder on `A^r`. Each theorem is the matching `_aux`
theorem of `AbelianPowerLinkProofs.lean`, whose proofs are open.

It claims, as implications from the named binders:

* **G2 at `A^r`**: the model map `(g3_powerData A r).cohomologyMap k` is bijective; `dim A^r =
  r · dim A`; a model class is a rational exterior Hodge class exactly when its image is a Hodge
  class of `A^r`, and the image of the model's rational Hodge classes is `Hdg^p(A^r; ℚ)`; the unit
  goes to the unit; `Hdg^p(A^r; ℚ) = 0` for `p > r · dim A`; and `f_a^*` in degree `k` is
  `⋀^k (pwPowerPullback A θ a)` under the model map, for `a ∈ 𝒪^r`;
* **`r = 1`, agreement with `AbelianPowerData.one A`**: `A^1 = A ⊗ 𝟙_` is not `A`, and the model
  maps of `g3_powerData A 1` are those of `AbelianPowerData.one A` followed by the pullback along
  `p_0 = ρ_A`, in degree one and in every degree; and that pullback carries `Hdg^p(A; ℚ)` onto
  `Hdg^p(A^1; ℚ)`;
* **F1 at `A^r`, `L = k = ℚ(√-3)`**: from `hGk` alone, `Hdg^p(A^r; ℚ)` is the powers span and the
  pulled-Weil cup span (Theorem 4.2, first sentence); with `h11`, every Hodge class of `A^r` lies in
  the cup-closed span of `1`, the divisor classes and the planes `f_a^* W_k(A)`; and, from `hGk`,
  `hWA`, `hPull`, `hC9`, `h11` (F1's binders, with `Y := A^r`), every Hodge class of `A^r` is
  algebraic (Theorem 4.2, second sentence).

Checks (`example`s): every instance of the table, by `inferInstance`; `r = 0` (`A^0 = Spec ℂ`:
`Hdg^p = 0` for `p > 0`, `Hdg^0 = ⊤` under `hGk`, the empty sum `h1Map = 0`, the empty product
`f_a = 1`); `r = 1` (the powers span of `A^1` is the pullback of the one of `A`, and the generation
statements at `A^1` and at `AbelianPowerData.one A` agree); `dim A = 0` (`dim A^r = 0` and
`Hdg^p(A^r) = 0` for `p > 0`, every `r`); `r = 2`, the first case where G3 part 1 needed binders.

It does not claim: anything for `L ≠ k` or `k ≠ ℚ(√-3)` (stage F2, to be linked the same way once
it merges); that `hGk`, `hWA`, `hPull`, `hC9` or `h11` hold for any particular `A`; that the
binders `hPull` and `hC9` at `A^r` follow from cycle-class theory (they stay F1's binders); that
`g3_power A 1` equals `A` (it is isomorphic, by `ρ_A`); any statement for a power data on `A^r`
other than `g3_powerData A r` (F1 itself covers every one). HC no distance; AV milestone no
distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Adapters

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]

/-! ### Instance audit: every scope instance of `Y` is found for `Y = A^r` -/

example (r : ℕ) : GrpObj (g3_power A r) := inferInstance
example (r : ℕ) : IsCommMonObj (g3_power A r) := inferInstance
example (r : ℕ) : IsIntegral (g3_power A r).left := inferInstance
example (r : ℕ) : Smooth (g3_power A r).hom := inferInstance
example (r : ℕ) : IsProjective (g3_power A r).hom := inferInstance

/-- The group structure found is G3's `g3_grpObj`, the one `g3_powerData` is built on. -/
example (r : ℕ) : (inferInstance : GrpObj (g3_power A r)) = g3_grpObj A r := rfl

/-- `r = 2`: the first power for which G3 part 1 needed the integrality and projectivity binders. -/
example : IsIntegral (g3_power A 2).left ∧ IsProjective (g3_power A 2).hom :=
  ⟨inferInstance, inferInstance⟩

/-! ### G2 at `A^r` -/

/-- **The model map of `A^r` is bijective in every degree.** G2's
`spec_g2_cohomologyMap_bijective` at `P = g3_powerData A r`, with the scope instances of `A^r`
from G3.
Source: `spec_g2_cohomologyMap_bijective`; `g3_powerData`, `spec_g3b_isIntegral_power`,
`spec_g3c_isProjective_power`. -/
theorem spec_g3link_cohomologyMap_bijective (r k : ℕ) :
    Function.Bijective ((g3_powerData A r).cohomologyMap k) :=
  spec_g3link_cohomologyMap_bijective_aux A r k

/-- So `HQ (A^r) k` is a linear image of `⋀^k (HQ A 1 ⊗ ℚ^r)`, onto. -/
example (r k : ℕ) : Function.Surjective ((g3_powerData A r).cohomologyMap k) :=
  (spec_g3link_cohomologyMap_bijective A r k).2

/-- **`dim A^r = r · dim A`.** G2's `spec_g2_dim_eq` at `P = g3_powerData A r`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; `spec_g2_dim_eq`;
`g3_powerData`. -/
theorem spec_g3link_dim_eq (r : ℕ) : dim (g3_power A r).left = r * dim A.left :=
  spec_g3link_dim_eq_aux A r

/-- **Degenerate check `r = 0`**: `A^0 = Spec ℂ` is zero-dimensional. -/
example : dim (g3_power A 0).left = 0 := by
  rw [spec_g3link_dim_eq, zero_mul]

/-- **Degenerate check `dim A = 0`**: then every power is zero-dimensional. -/
example (h0 : dim A.left = 0) (r : ℕ) : dim (g3_power A r).left = 0 := by
  rw [spec_g3link_dim_eq, h0, mul_zero]

/-- **Rational Hodge classes of `A^r`, pointwise.** G2's `spec_g2_mem_rationalExteriorHodge_iff`
at `P = g3_powerData A r`.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5–6;
`spec_g2_mem_rationalExteriorHodge_iff`; `g3_powerData`. -/
theorem spec_g3link_mem_rationalExteriorHodge_iff (r p : ℕ)
    (v : ⋀[ℚ]^(2 * p) (HQ A 1 ⊗[ℚ] (Fin r → ℚ))) :
    letI := (finiteBetti_abelian A).finite 1
    v ∈ rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal r (2 * p) ↔
      ((g3_powerData A r).cohomologyMap (2 * p) v : H^(2 * p)(g3_power A r; ℚ)) ∈
        Hdg^p(g3_power A r; ℚ) :=
  spec_g3link_mem_rationalExteriorHodge_iff_aux A r p v

/-- So the image of a model Hodge class is a Hodge class of `A^r`. -/
example (r p : ℕ) (v : ⋀[ℚ]^(2 * p) (HQ A 1 ⊗[ℚ] (Fin r → ℚ)))
    (hv : letI := (finiteBetti_abelian A).finite 1
      v ∈ rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal r (2 * p)) :
    ((g3_powerData A r).cohomologyMap (2 * p) v : H^(2 * p)(g3_power A r; ℚ)) ∈
      Hdg^p(g3_power A r; ℚ) :=
  (spec_g3link_mem_rationalExteriorHodge_iff A r p v).1 hv

/-- **The model carries its rational Hodge classes onto `Hdg^p(A^r; ℚ)`.** G2's
`spec_g2_rationalExteriorHodge_map_eq` at `P = g3_powerData A r`: the transport F1 uses.
Source: `spec_g2_rationalExteriorHodge_map_eq`; `g3_powerData`. -/
theorem spec_g3link_rationalExteriorHodge_map_eq (r p : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    (rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal r (2 * p)).map
          ((g3_powerData A r).cohomologyMap (2 * p)) =
      Hdg^p(g3_power A r; ℚ) :=
  spec_g3link_rationalExteriorHodge_map_eq_aux A r p

/-- The image of the pointwise statement is the transport statement, read on one class. -/
example (r p : ℕ) (y : HQ (g3_power A r) (2 * p))
    (hy : (y : H^(2 * p)(g3_power A r; ℚ)) ∈ Hdg^p(g3_power A r; ℚ)) :
    letI := (finiteBetti_abelian A).finite 1
    ∃ v ∈ rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal r (2 * p),
      (g3_powerData A r).cohomologyMap (2 * p) v = y := by
  rw [← spec_g3link_rationalExteriorHodge_map_eq A r p] at hy
  exact hy

/-- **The unit goes to the unit.** G2's `spec_g2_cohomologyMap_zero` at `P = g3_powerData A r`.
Source: `spec_g2_cohomologyMap_zero`; `CupProduct.cupWedgeMap_zero`. -/
theorem spec_g3link_cohomologyMap_zero (r : ℕ) :
    (g3_powerData A r).cohomologyMap 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0) =
      cupUnit (g3_power A r) :=
  spec_g3link_cohomologyMap_zero_aux A r

/-- So the model map is nonzero in degree zero, also at `r = 0`. -/
example (r : ℕ) : (g3_powerData A r).cohomologyMap 0 ≠ 0 := fun h => by
  have := spec_g3link_cohomologyMap_zero A r
  rw [h, LinearMap.zero_apply] at this
  exact (cupProductOf (g3_power A r)).unitClass_ne_zero this.symm

/-- **`Hdg^p(A^r; ℚ) = 0` for `p > r · dim A`.** G2's `spec_g2_hodgeClasses_eq_bot_of_lt` at
`P = g3_powerData A r`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1;
`spec_g2_hodgeClasses_eq_bot_of_lt`. -/
theorem spec_g3link_hodgeClasses_eq_bot_of_lt (r p : ℕ) (hp : r * dim A.left < p) :
    Hdg^p(g3_power A r; ℚ) = ⊥ :=
  spec_g3link_hodgeClasses_eq_bot_of_lt_aux A r p hp

/-- **Degenerate check `r = 0`**: `A^0 = Spec ℂ` has no Hodge classes in positive degree. The
bound `0 < p` is needed: `Hdg^0` contains the nonzero unit class. -/
example (p : ℕ) (hp : 0 < p) : Hdg^p(g3_power A 0; ℚ) = ⊥ :=
  spec_g3link_hodgeClasses_eq_bot_of_lt A 0 p (by rwa [zero_mul])

/-- **Degenerate check `dim A = 0`**: no power of `A` has Hodge classes in positive degree. -/
example (h0 : dim A.left = 0) (r p : ℕ) (hp : 0 < p) : Hdg^p(g3_power A r; ℚ) = ⊥ :=
  spec_g3link_hodgeClasses_eq_bot_of_lt A r p (by rwa [h0, mul_zero])

/-- **`f_a^*` on `A^r` in every degree is `⋀ pwPowerPullback` under the model map**, for
`a ∈ 𝒪^r`. G2's `spec_g2_homPullback_pwSumMap_degree` at `P = g3_powerData A r`.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Weil classes"; `spec_g2_homPullback_pwSumMap_degree`;
`g3_powerData`. -/
theorem spec_g3link_homPullback_pwSumMap_degree {L : Type*} [Field L] [Algebra ℚ L] (r : ℕ)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (k : ℕ) :
    homPullback ((g3_powerData A r).pwSumMap θ a) k ∘ₗ
        ((torusCohomology_cupProductOf A).cupWedgeEquiv k).toLinearMap =
      (g3_powerData A r).cohomologyMap k ∘ₗ
        exteriorPower.map k (pwPowerPullback A θ (fun i => (a i : L))) :=
  spec_g3link_homPullback_pwSumMap_degree_aux A r θ a k

/-- **Mathlib conventions at `r = 0`**: the sum over `Fin 0` defining `h1Map` is empty, and the
product over `Fin 0` defining `f_a` is the unit `1` (the constant map to the identity point). -/
example : (g3_powerData A 0).h1Map = 0 := by
  simp [AbelianPowerData.h1Map]

example {L : Type*} [Field L] [Algebra ℚ L] (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (a : Fin 0 → pwOrder A θ) : (g3_powerData A 0).pwSumMap θ a = 1 := by
  simp [AbelianPowerData.pwSumMap, AbelianPowerData.sumMap]

/-! ### `r = 1`: agreement with `AbelianPowerData.one A` -/

/-- **`r = 1` in degree one.** For `A^1 = A ⊗ 𝟙_`, `Φ = p_0^* ∘ powerOneFlatten A`, where
`p_0 = g3_proj A 1 0` (`= ρ_A`, G3's S7): the single summand of `h1Map`. With G2's
`spec_g2_h1Map_one` (`(AbelianPowerData.one A).h1Map = powerOneFlatten A`), the model map of
`g3_powerData A 1` is the one of `AbelianPowerData.one A` followed by `p_0^*`.
Source: `AbelianPowerData.h1Map` (one summand at `r = 1`), `powerOneFlatten`,
`spec_homPullback_id`, `spec_g2_h1Map_one`. -/
theorem spec_g3link_h1Map_one :
    (g3_powerData A 1).h1Map = homPullback (g3_proj A 1 0) 1 ∘ₗ powerOneFlatten A :=
  spec_g3link_h1Map_one_aux A

example (x : HQ A 1) (c : Fin 1 → ℚ) :
    (g3_powerData A 1).h1Map (x ⊗ₜ[ℚ] c) = c 0 • homPullback (g3_proj A 1 0) 1 x := by
  rw [spec_g3link_h1Map_one, LinearMap.comp_apply]
  simp [powerOneFlatten]

/-- **`r = 1` in every degree.** `(g3_powerData A 1).cohomologyMap k = p_0^* ∘
(AbelianPowerData.one A).cohomologyMap k`. From the degree-one statement and G1b's
`spec_homPullback_eq_cupWedgeEquiv` (`f^*` in degree `k` is `⋀^k` of `f^*` in degree one through
the torus isomorphisms).
Source: `spec_g3link_h1Map_one`, `spec_g2_h1Map_one`, `spec_homPullback_eq_cupWedgeEquiv`;
Mathlib `exteriorPower.map_comp`. -/
theorem spec_g3link_cohomologyMap_one (k : ℕ) :
    (g3_powerData A 1).cohomologyMap k =
      homPullback (g3_proj A 1 0) k ∘ₗ (AbelianPowerData.one A).cohomologyMap k :=
  spec_g3link_cohomologyMap_one_aux A k

/-- **`p_0^*` carries the Hodge classes of `A` onto those of `A^1`.** `≤`: `p_0` is a
homomorphism (G3's S3), so G1b's `spec_homPullback_hodgeClasses` applies. `≥`: for `y` a Hodge
class of `A^1`, `y = p_0^* (s_0^* y)`, since `p_0 ≫ s_0 = ρ_A ≫ ρ_A⁻¹ = 𝟙` (G3's S7), and
`s_0^* y` is a Hodge class of `A` (S4 and G1b).
Source: `spec_homPullback_hodgeClasses` (stage G1b), `spec_homPullback_comp`,
`spec_homPullback_id`, `spec_g3_isMonHom_proj`, `spec_g3_isMonHom_incl`, `spec_g3_proj_incl_one`. -/
theorem spec_g3link_hodgeClasses_one (p : ℕ) :
    (Hdg^p(A; ℚ)).map (homPullback (g3_proj A 1 0) (2 * p)) = Hdg^p(g3_power A 1; ℚ) :=
  spec_g3link_hodgeClasses_one_aux A p

/-- So `Hdg^p(A^1; ℚ)` and `Hdg^p(A; ℚ)` have the same dimension (`p_0^*` is injective, with left
inverse `s_0^*`), consistent with `A^1 ≅ A`. -/
example (p : ℕ) :
    Function.Injective (homPullback (g3_proj A 1 0) (2 * p)) := by
  have h : g3_incl A 1 0 ≫ g3_proj A 1 0 = 𝟙 A := by
    simpa using spec_g3_incl_proj A 1 0 0
  intro x y hxy
  have := congrArg (homPullback (g3_incl A 1 0) (2 * p)) hxy
  rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← spec_homPullback_comp, h,
    spec_homPullback_id] at this

/-! ### F1 at `A^r` -/

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **PW v0.3, Theorem 4.2, first sentence, at `L = k = ℚ(√-3)`, on `A^r` for every `r`.** Under
(P3) in Lie-algebra form (`hGk`), `Hdg^p(A^r; ℚ) = pwPowerSpan … (g3_powerData A r) p`. F1's
`pw_thm_4_2_generation` at `Y = g3_power A r`, `P = g3_powerData A r`, with F1's binders unchanged
and no binder on `A^r`.
Source: PW v0.3, Theorem 4.2 (`thm:gen`), first sentence, at `e = 1`; `pw_thm_4_2_generation`;
`g3_powerData`, `spec_g3b_isIntegral_power`, `spec_g3c_isProjective_power`. -/
theorem spec_g3link_generation (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (r : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) = pwPowerSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r) p :=
  spec_g3link_generation_aux A θ u hu hL pol hη hRos hGk r

/-- **Degenerate check `r = 0`, `p = 0`**: under `hGk`, every class of `H⁰(Spec ℂ; ℚ)` is a Hodge
class, by F1's `f1_pwPowerSpan_zero`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3)
    (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u)) :
    Hdg^0(g3_power A 0; ℚ) = ⊤ := by
  rw [spec_g3link_generation A θ u hu hL pol hη hRos hGk 0 0, f1_pwPowerSpan_zero]
  rfl

/-- **Degenerate check `r = 1`: agreement with F1 at `AbelianPowerData.one A`.** The powers span
of `A^1` is the pullback along `p_0` of the one of `A` (`spec_g3link_cohomologyMap_one`), so the
generation statement on `A^1` and F1's on `A` give the same `Hdg^p(A^1; ℚ)` as
`spec_g3link_hodgeClasses_one`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3)
    (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u)) (p : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    Hdg^p(g3_power A 1; ℚ) =
      (pwPowerSpan A θ u 3 hu
        (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
          (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
            (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
        (AbelianPowerData.one A) p).map (homPullback (g3_proj A 1 0) (2 * p)) := by
  rw [spec_g3link_generation A θ u hu hL pol hη hRos hGk 1 p, pwPowerSpan, pwPowerSpan,
    ← Submodule.map_comp, ← spec_g3link_cohomologyMap_one]

/-- The same agreement, through F1's `r = 1` statement on `A` and `spec_g3link_hodgeClasses_one`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3)
    (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u)) (p : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    Hdg^p(g3_power A 1; ℚ) =
      (pwPowerSpan A θ u 3 hu
        (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
          (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
            (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
        (AbelianPowerData.one A) p).map (homPullback (g3_proj A 1 0) (2 * p)) := by
  rw [← spec_g3link_hodgeClasses_one A p,
    pw_thm_4_2_generation A θ u hu hL pol hη hRos hGk (AbelianPowerData.one A) p]

/-- **Theorem 4.2, first sentence, on `A^r` itself.** Under `hGk`, `Hdg^p(A^r; ℚ)` is the
cup-closed span of `1`, `Hdg¹(A^r; ℚ)` and the pullbacks `f_a^*` of the rational Weil classes of
`A`, `a ∈ 𝒪^r`. F1's `pw_thm_4_2_generation_cup` at `Y = g3_power A r`, `P = g3_powerData A r`.
Source: PW v0.3, Theorem 4.2, first sentence, and its proof, paragraph "Conclusion";
`pw_thm_4_2_generation_cup`; `g3_powerData`. -/
theorem spec_g3link_generation_cup (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (r : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) = f1_pulledWeilCupSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r) Hdg^1(g3_power A r; ℚ) p :=
  spec_g3link_generation_cup_aux A θ u hu hL pol hη hRos hGk r

/-- **`p > r · dim A`**: the cup-closed span of `A^r` vanishes there, by the generation statement
and `spec_g3link_hodgeClasses_eq_bot_of_lt`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3)
    (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (r p : ℕ) (hp : r * dim A.left < p) :
    letI := (finiteBetti_abelian A).finite 1
    f1_pulledWeilCupSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r) Hdg^1(g3_power A r; ℚ) p = ⊥ := by
  rw [← spec_g3link_generation_cup A θ u hu hL pol hη hRos hGk r p]
  exact spec_g3link_hodgeClasses_eq_bot_of_lt A r p hp

/-- **The divisor-class form on `A^r`.** Under `hGk` and Lefschetz (1,1) (`h11`), every Hodge
class of `A^r` lies in the cup-closed span of `1`, the divisor classes and the planes
`f_a^* W_k(A)`. F1's `f1_hdg_le_pulledWeilCupSpan_divisor` at `Y = g3_power A r`,
`P = g3_powerData A r`; only `≤` is claimed, as in F1.
Source: PW v0.3, Theorem 4.2, first sentence, and its proof, paragraph "Divisor classes";
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through `LefschetzOneOneHyp`);
`f1_hdg_le_pulledWeilCupSpan_divisor`; `g3_powerData`. -/
theorem spec_g3link_hdg_le_pulledWeilCupSpan_divisor (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (h11 : LefschetzOneOneHyp) (r : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ f1_pulledWeilCupSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r) (algebraicCycleClassSpan (g3_power A r) 1) p :=
  spec_g3link_hdg_le_pulledWeilCupSpan_divisor_aux A θ u hu hL pol hη hRos hGk h11 r

/-- At `r = 2`, the first power for which G3 part 1 needed binders, there is no binder on `A²`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3)
    (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (h11 : LefschetzOneOneHyp) :
    letI := (finiteBetti_abelian A).finite 1
    Hdg^1(g3_power A 2; ℚ) ≤ f1_pulledWeilCupSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A 2) (algebraicCycleClassSpan (g3_power A 2) 1) 1 :=
  spec_g3link_hdg_le_pulledWeilCupSpan_divisor A θ u hu hL pol hη hRos hGk h11 2 1

/-- **PW v0.3, Theorem 4.2, second sentence, at `L = k = ℚ(√-3)`, on `A^r` for every `r`.** If the
rational Weil classes of `A` are algebraic (`hWA`, (P4)), then under `hGk` every Hodge class of
`A^r` is algebraic, given F1's three classical cycle inputs at `Y = A^r`: `hPull` (pullback along
each `f_a = (g3_powerData A r).pwSumMap θ a`), `hC9` (cup products on `A^r`) and `h11`. F1's
`pw_thm_4_2_hc` at `Y = g3_power A r`, `P = g3_powerData A r`, F1's binders unchanged and no binder
on `A^r` itself.
Source: PW v0.3, Theorem 4.2, second sentence, and its proof, paragraph "Conclusion"; Fulton,
*Intersection Theory*, 2nd ed., Ch. 8 and Corollary 19.2 (through `hPull` and
`CycleClassMultiplicative`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2
(through `LefschetzOneOneHyp`); `pw_thm_4_2_hc`; `g3_powerData`. -/
theorem spec_g3link_hc (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (hWA : letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (f1_weilAction A θ u 3 hu)
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk))
    (r : ℕ)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback ((g3_powerData A r).pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan (g3_power A r) q)
    (hC9 : CycleClassMultiplicative (cupProductOf (g3_power A r))) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p :=
  spec_g3link_hc_aux A θ u hu hL pol hη hRos hGk hWA r hPull hC9 h11

/-- **The shape of PW v0.3, Corollary 5.1, on the actual powers.** For a sixfold `A` of Weil type
with `End⁰(A) = k` and (P3), (P4) as binders, the Hodge conjecture holds on `A^r` for every `r`,
given the classical cycle inputs on `A^r`; no `Y`, no power data and no instance on `A^r` is
quantified. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (_hθ : Function.Bijective θ) (_h6 : dim A.left = 6) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (hWA : letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (f1_weilAction A θ u 3 hu)
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk))
    (h11 : LefschetzOneOneHyp) :
    ∀ r : ℕ,
      (∀ (a : Fin r → pwOrder A θ) (q : ℕ),
        (algebraicCycleClassSpan A q).map
            (homPullback ((g3_powerData A r).pwSumMap θ a) (2 * q)) ≤
          algebraicCycleClassSpan (g3_power A r) q) →
      CycleClassMultiplicative (cupProductOf (g3_power A r)) →
      ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p :=
  fun r hPull hC9 => spec_g3link_hc A θ u hu hL pol hη hRos hGk hWA r hPull hC9 h11

end HodgeLean.Adapters
