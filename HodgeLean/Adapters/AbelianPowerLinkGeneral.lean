import HodgeLean.Adapters.AbelianPowerLinkGeneralProofs

/-! # The Powers flagship, G3 link part 2: F2 at `Y = A^r` for every `r` (FROZEN SPEC)

The second link stage between G3 and the flagship statements, towards PW v0.3, Theorem 4.2
(`thm:gen`), "Hodge classes on powers of abelian varieties of Weil type and of type IV with exact
endomorphism algebra" (doi:10.5281/zenodo.23570103). F2 (`PWTheorem42.lean`) states Theorem 4.2
for a CM number field `L` (`[NumberField L] [IsCMField L]`) for any `Y` with power data
`P : AbelianPowerData A Y r` and the scope instances `[GrpObj Y] [IsCommMonObj Y]
[IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]`. G3 builds `A^r = g3_power A r` with
`g3_powerData A r` and registers every one of those instances for `A^r`, from the scope instances
of `A` alone:

| instance on `A^r` | found by | from |
|---|---|---|
| `GrpObj` | `g3_grpObj` | `[GrpObj A]` |
| `IsCommMonObj` | `spec_g3_isCommMonObj_power` | `[IsCommMonObj A]` |
| `IsIntegral (·).left` | `spec_g3b_isIntegral_power` | `[IsIntegral A.left] [Smooth A.hom]` |
| `Smooth (·).hom` | `spec_g3_smooth_power` | `[Smooth A.hom]` |
| `IsProjective (·).hom` | `spec_g3c_isProjective_power` | `[IsProjective A.hom]` |

So this stage restates F2's four main statements at `Y = g3_power A r`, `P = g3_powerData A r`,
for every `r`, with no binder on `A^r` and F2's other binders unchanged (`L`, `θ`, `u`, `d`, `hd`,
`hu`, `pol`, `hη`, `hRos`, `hGk`, and `h11`, `hWA`, `hPull`, `hC9` where F2 has them; in `hPull`
and `hC9`, `Y` and `P` are replaced by `A^r` and `g3_powerData A r`). Each theorem is the matching
`_aux` theorem of `AbelianPowerLinkGeneralProofs.lean`, whose proofs are open. It mirrors the G3
link part 1 (`AbelianPowerLink.lean`, for F1), on which it does not depend.

It claims, as implications from the named binders:

* **Theorem 4.2, first sentence, on `A^r`, for a CM field `L`**: from `hGk` alone,
  `Hdg^p(A^r; ℚ)` is the powers span `pwPowerSpan … (g3_powerData A r) p` and the pulled-Weil cup
  span `f1_pulledWeilCupSpan … (g3_powerData A r) Hdg¹(A^r; ℚ) p`, for every `p`;
* **the divisor-class form on `A^r`**: with `h11`, every Hodge class of `A^r` lies in the
  cup-closed span of `1`, the divisor classes and the planes `f_a^* W_k(A)`, `a ∈ 𝒪^r`;
* **Theorem 4.2, second sentence, on `A^r`**: from `hGk`, `hWA`, `hPull`, `hC9`, `h11`, every
  Hodge class of `A^r` is algebraic.

As in F2, the paper's hypothesis `End⁰(A) = L` (`Function.Bijective θ`) is omitted, so each
statement is the paper's without that hypothesis; the literal paper forms are `example`s.

Checks (`example`s): every instance of the table, by `inferInstance`; `r = 0` (`A^0 = Spec ℂ`:
the powers span is `0` in positive degree and `Hdg^0 = ⊤`; the empty sum `h1Map = 0`, the empty
product `f_a = 1`); `r = 1` (the statements at `A^1 = A ⊗ 𝟙_`, with no binder on `A^1`);
`r = 2`, the first case where G3 part 1 needed binders; `p > r · dim A`; `dim A = 0` (the
powers span is `0` in every positive degree, for every `r`); at `[L : ℚ] = 2`, `d = 3`
the statements recover part 1's restatements of F1 at `A^r` (generation and HC), through F2's
`f2_rosati_of_finrank_two`; the shapes of PW v0.3, Corollaries 5.9 and 5.13 on the actual powers.

It does not claim: that `hGk`, `hWA`, `hPull`, `hC9`, `h11` or `hRos` hold for any particular
`A` or `pol`; that `hPull` and `hC9` at `A^r` follow from cycle-class theory (they stay F2's
binders); that `g3_power A 1` equals `A` (it is isomorphic, by `ρ_A`); any statement for a power
data on `A^r` other than `g3_powerData A r` (F2 itself covers every one). HC no distance; AV
milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic NumberField

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

/-- **Mathlib conventions at `r = 0`**: the sum over `Fin 0` defining `h1Map` is empty. -/
example : (g3_powerData A 0).h1Map = 0 := by
  simp [AbelianPowerData.h1Map]

variable {L : Type*} [Field L] [NumberField L] [IsCMField L]

/-- **Mathlib conventions at `r = 0`**: the product over `Fin 0` defining `f_a` is the unit `1`
(the constant map to the identity point), for a CM field `L`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin 0 → pwOrder A θ) :
    (g3_powerData A 0).pwSumMap θ a = 1 := by
  simp [AbelianPowerData.pwSumMap, AbelianPowerData.sumMap]

/-! ### Theorem 4.2, first sentence, on `A^r` -/

/-- **PW v0.3, Theorem 4.2, first sentence, for a CM field `L`, on `A^r` for every `r`.** Under
(P3) in Lie-algebra form (`hGk`, `R = θ(L)^*`),
`Hdg^p(A^r; ℚ) = pwPowerSpan … (g3_powerData A r) p`.
F2's `pw_thm_4_2_generation_general` at `Y = g3_power A r`, `P = g3_powerData A r`, with F2's
binders unchanged and no binder on `A^r`. As in F2, `End⁰(A) = L` is omitted.
Source: PW v0.3, Theorem 4.2 (`thm:gen`), first sentence; `pw_thm_4_2_generation_general`;
`g3_powerData`, `spec_g3b_isIntegral_power`, `spec_g3c_isProjective_power`. -/
theorem spec_g3link2_generation (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
    (hd : 0 < d) (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (r : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) = pwPowerSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r) p :=
  spec_g3link2_generation_aux A θ u hd hu pol hη hRos hGk r

/-- **Literal paper form** on `A^r`: the paper's `End⁰(A) = L` is the unused binder `_hθ`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (_hθ : Function.Bijective θ) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (r : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) = pwPowerSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r) p :=
  spec_g3link2_generation A θ u hd hu pol hη hRos hGk r

/-- **Degenerate check `r = 0`, `p = 0`**: under `hGk`, every class of `H⁰(Spec ℂ; ℚ)` is a Hodge
class, by F1's binder-free `f1_pwPowerSpan_zero`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u)) :
    Hdg^0(g3_power A 0; ℚ) = ⊤ := by
  rw [spec_g3link2_generation A θ u hd hu pol hη hRos hGk 0 0]
  exact f1_pwPowerSpan_zero A θ u d hu _ (g3_powerData A 0)

/-- **Degenerate checks `r = 0` and `p > r · dim A`**: there the powers span of `A^r` is `0`
(G2's `spec_g2_hodgeClasses_eq_bot_of_lt` at `g3_powerData A r`); at `r = 0` this is every
`p > 0`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (r p : ℕ) (hp : r * dim A.left < p) :
    letI := (finiteBetti_abelian A).finite 1
    pwPowerSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r) p = ⊥ := by
  rw [← spec_g3link2_generation A θ u hd hu pol hη hRos hGk r p]
  exact spec_g2_hodgeClasses_eq_bot_of_lt (g3_powerData A r) p hp

/-- **Degenerate check `dim A = 0`**: for every `r` and every `p > 0` the powers span of `A^r` is
`0`, through the `p > r · dim A` check above, since `r · 0 = 0 < p`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (h0 : dim A.left = 0) (r p : ℕ) (hp : 0 < p) :
    letI := (finiteBetti_abelian A).finite 1
    pwPowerSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r) p = ⊥ := by
  have hp' : r * dim A.left < p := by rwa [h0, mul_zero]
  rw [← spec_g3link2_generation A θ u hd hu pol hη hRos hGk r p]
  exact spec_g2_hodgeClasses_eq_bot_of_lt (g3_powerData A r) p hp'

/-- **Degenerate check `r = 1`**: the statement on `A^1 = A ⊗ 𝟙_` (isomorphic to `A` by `ρ_A`, not
equal), with no binder on `A^1`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u)) (p : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    Hdg^p(g3_power A 1; ℚ) = pwPowerSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A 1) p :=
  spec_g3link2_generation A θ u hd hu pol hη hRos hGk 1 p

/-- **The specialization `[L : ℚ] = 2`, `d = 3` recovers part 1's restatement of F1's generation
statement at `A^r`** (`spec_g3link_generation`, conclusion verbatim), with F1's `hRos` for `u`
alone, through F2's `f2_rosati_of_finrank_two`. -/
example (hL : Module.finrank ℚ L = 2) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (pol : HQ A 2)
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
  spec_g3link2_generation A θ u (by norm_num) hu pol hη
    (f2_rosati_of_finrank_two A hL θ u (by norm_num) hu pol hη hRos) hGk r

/-- **PW v0.3, Theorem 4.2, first sentence, on `A^r` itself, for a CM field `L`.** Under `hGk`,
`Hdg^p(A^r; ℚ)` is the cup-closed span of `1`, `Hdg¹(A^r; ℚ)` and the pullbacks `f_a^*` of the
rational Weil classes of `A`, `a ∈ 𝒪^r`. F2's `pw_thm_4_2_generation_cup_general` at
`Y = g3_power A r`, `P = g3_powerData A r`.
Source: PW v0.3, Theorem 4.2, first sentence, and its proof, paragraph "Conclusion";
`pw_thm_4_2_generation_cup_general`; `g3_powerData`. -/
theorem spec_g3link2_generation_cup (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
    (hd : 0 < d) (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (r : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) = f1_pulledWeilCupSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r) Hdg^1(g3_power A r; ℚ) p :=
  spec_g3link2_generation_cup_aux A θ u hd hu pol hη hRos hGk r

/-- **`p > r · dim A`**: the cup-closed span of `A^r` vanishes there, by the generation statement
and G2's `spec_g2_hodgeClasses_eq_bot_of_lt` at `g3_powerData A r`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (r p : ℕ) (hp : r * dim A.left < p) :
    letI := (finiteBetti_abelian A).finite 1
    f1_pulledWeilCupSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r) Hdg^1(g3_power A r; ℚ) p = ⊥ := by
  rw [← spec_g3link2_generation_cup A θ u hd hu pol hη hRos hGk r p]
  exact spec_g2_hodgeClasses_eq_bot_of_lt (g3_powerData A r) p hp

/-- The two spans of Theorem 4.2 on `A^r` agree, under `hGk`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (r p : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    pwPowerSpan A θ u d hu
        (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
        (g3_powerData A r) p =
      f1_pulledWeilCupSpan A θ u d hu
        (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
        (g3_powerData A r) Hdg^1(g3_power A r; ℚ) p :=
  (spec_g3link2_generation A θ u hd hu pol hη hRos hGk r p).symm.trans
    (spec_g3link2_generation_cup A θ u hd hu pol hη hRos hGk r p)

/-! ### The divisor-class form and Theorem 4.2, second sentence, on `A^r` -/

/-- **The divisor-class form on `A^r`, for a CM field `L`.** Under `hGk` and Lefschetz (1,1)
(`h11`), every Hodge class of `A^r` lies in the cup-closed span of `1`, the divisor classes
`algebraicCycleClassSpan (A^r) 1` and the planes `f_a^* W_k(A)`, `a ∈ 𝒪^r`. F2's
`f2_hdg_le_pulledWeilCupSpan_divisor` at `Y = g3_power A r`, `P = g3_powerData A r`; only `≤` is
claimed, as in F2.
Source: PW v0.3, Theorem 4.2, first sentence, and its proof, paragraph "Divisor classes";
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through `LefschetzOneOneHyp`);
`f2_hdg_le_pulledWeilCupSpan_divisor`; `g3_powerData`. -/
theorem spec_g3link2_hdg_le_pulledWeilCupSpan_divisor (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (h11 : LefschetzOneOneHyp) (r : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ f1_pulledWeilCupSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r) (algebraicCycleClassSpan (g3_power A r) 1) p :=
  spec_g3link2_hdg_le_pulledWeilCupSpan_divisor_aux A θ u hd hu pol hη hRos hGk h11 r

/-- At `r = 2`, `p = 1`, the first power for which G3 part 1 needed binders: no binder on `A²`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (h11 : LefschetzOneOneHyp) :
    letI := (finiteBetti_abelian A).finite 1
    Hdg^1(g3_power A 2; ℚ) ≤ f1_pulledWeilCupSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A 2) (algebraicCycleClassSpan (g3_power A 2) 1) 1 :=
  spec_g3link2_hdg_le_pulledWeilCupSpan_divisor A θ u hd hu pol hη hRos hGk h11 2 1

/-- **PW v0.3, Theorem 4.2, second sentence, for a CM field `L`, on `A^r` for every `r`.** If the
rational Weil classes of `A` for `k = ℚ(u)` are algebraic (`hWA`, (P4)), then under `hGk` every
Hodge class of `A^r` is algebraic, given F2's three classical cycle inputs at `Y = A^r`: `hPull`
(pullback along each `f_a = (g3_powerData A r).pwSumMap θ a`), `hC9` (cup products on `A^r`) and
`h11`. F2's `pw_thm_4_2_hc_general` at `Y = g3_power A r`, `P = g3_powerData A r`, F2's binders
unchanged and no binder on `A^r` itself. As in F2, `End⁰(A) = L` is omitted.
Source: PW v0.3, Theorem 4.2, second sentence, and its proof, paragraph "Conclusion"; Fulton,
*Intersection Theory*, 2nd ed., Ch. 8 and Corollary 19.2 (through `hPull` and
`CycleClassMultiplicative`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2
(through `LefschetzOneOneHyp`); `pw_thm_4_2_hc_general`; `g3_powerData`. -/
theorem spec_g3link2_hc (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
    (hd : 0 < d) (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (hWA : letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (f1_weilAction A θ u d hu)
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk))
    (r : ℕ)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback ((g3_powerData A r).pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan (g3_power A r) q)
    (hC9 : CycleClassMultiplicative (cupProductOf (g3_power A r))) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p :=
  spec_g3link2_hc_aux A θ u hd hu pol hη hRos hGk hWA r hPull hC9 h11

/-- **The specialization `[L : ℚ] = 2`, `d = 3` recovers part 1's restatement of F1's HC
statement at `A^r`** (`spec_g3link_hc`, binders `hPull`, `hC9`, `h11` and conclusion verbatim),
through F2's `f2_rosati_of_finrank_two`. -/
example (hL : Module.finrank ℚ L = 2) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (pol : HQ A 2)
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
  spec_g3link2_hc A θ u (by norm_num) hu pol hη
    (f2_rosati_of_finrank_two A hL θ u (by norm_num) hu pol hη hRos) hGk hWA r hPull hC9 h11

/-- **Degenerate check `r = 0`** for the HC statement: on `A^0 = Spec ℂ` the inputs `hPull` and
`hC9` mention only `A^0`, and the conclusion in degree zero places the unit class among the
algebraic classes. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (hWA : letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (f1_weilAction A θ u d hu)
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk))
    (hPull : ∀ (a : Fin 0 → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback ((g3_powerData A 0).pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan (g3_power A 0) q)
    (hC9 : CycleClassMultiplicative (cupProductOf (g3_power A 0))) (h11 : LefschetzOneOneHyp) :
    Hdg^0(g3_power A 0; ℚ) ≤ algebraicCycleClassSpan (g3_power A 0) 0 :=
  spec_g3link2_hc A θ u hd hu pol hη hRos hGk hWA 0 hPull hC9 h11 0

/-- **The shape of PW v0.3, Corollary 5.9 (case (Q6)), on the actual powers**: `L = kF` a CM field
of degree `4`, `End⁰(A) = L`, `dim A = 6`; (P3) and (P4) are binders, so the degree, the dimension
and the bijectivity are not used. The Hodge conjecture holds on `A^r` for every `r`, given the
classical cycle inputs on `A^r`; no `Y`, no power data and no instance on `A^r` is quantified. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (_hθ : Function.Bijective θ)
    (_hL : Module.finrank ℚ L = 4) (_h6 : dim A.left = 6) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (hWA : letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (f1_weilAction A θ u d hu)
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
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
  fun r hPull hC9 => spec_g3link2_hc A θ u hd hu pol hη hRos hGk hWA r hPull hC9 h11

/-- **The shape of PW v0.3, Corollary 5.13(1) (CM type, `m = 1`, `e = 6`), on the actual
powers**: `L` a CM field of degree `12`, `End⁰(A) = L`, `dim A = 6`; (P3) and (P4) are binders. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (_hθ : Function.Bijective θ)
    (_hL : Module.finrank ℚ L = 12) (_h6 : dim A.left = 6) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (hWA : letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (f1_weilAction A θ u d hu)
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
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
  fun r hPull hC9 => spec_g3link2_hc A θ u hd hu pol hη hRos hGk hWA r hPull hC9 h11

end HodgeLean.Adapters
