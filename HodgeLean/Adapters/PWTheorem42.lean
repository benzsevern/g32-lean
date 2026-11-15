import HodgeLean.Adapters.PWTheorem42Proofs

/-! # The Powers flagship, stage F2: Theorem 4.2 for a general CM field (FROZEN SPEC)

Stage F2 of the Powers flagship plan (`docs/roadmap/pw-flagship-plan.md`, §4.2, row F2): PW v0.3,
Theorem 4.2 (`thm:gen`), "Hodge classes on powers of abelian varieties of Weil type and of type
IV with exact endomorphism algebra" (doi:10.5281/zenodo.23570103), for a CM field `L = kF`
acting on `A`, `k = ℚ(u)`, `u² = -d`, `d > 0`. Each theorem restates the matching `_aux`
theorem in `PWTheorem42Proofs.lean`. There is no definitions file: the objects are F1's
(`f1_weilAction`, `pwPowerSpan`, `f1_pulledWeilCupSpan`, `PWTheorem42EisensteinDefs.lean`), which
are already stated for any field `L` and any `d`.

The setting: an abelian `A` (a commutative group object over `ℂ`, integral, smooth and projective);
a CM number field `L` (`[NumberField L] [IsCMField L]`, with Mathlib's complex conjugation
`IsCMField.complexConj L` as the CM conjugation `c`); a `ℚ`-algebra map `θ : L →ₐ[ℚ] End⁰(A)` (no
bijectivity); `u : L` with `u² = -d`, `d > 0`; a class `pol ∈ H²(A; ℚ)` whose 2-vector is
nondegenerate (`hη`), with form `E = polarizationForm … hη`, satisfying the Rosati condition for
all of `θ(L)`, `E(θ(a)^* x, y) = E(x, θ(c a)^* y)` (`hRos`); and power data
`P : AbelianPowerData A Y r` (stage G4), a stand-in for `Y = A^r`. The only Hodge-group binder is
`hGk`, the Lie-algebra form of the paper's (P3) `Hg(A) = G_k(A)` with `R = θ(L)^*`; Weil type is
derived from it (`isWeilType_of_hodgeLieIsGk`). No dimension, signature or discriminant
hypothesis, no family-M hypothesis. The paper also assumes `End⁰(A) = L`, represented here by
`Function.Bijective θ`. The two frozen sentences deliberately omit that hypothesis and hence
strengthen the paper's theorem. Their Lean proofs do not use it: the paper routes the
endomorphism-algebra assumption through the description of `G_k`, while the explicit (P3) binder
`hGk` supplies that description directly. Literal-paper-form examples below add the unused binder.

It claims, as implications from the named binders:

* **the Rosati condition at `L = k`**: for `[L : ℚ] = 2`, F1's `hRos` (the Rosati condition for
  `u` alone) gives the Rosati condition for all of `θ(L)` (`f2_rosati_of_finrank_two`); for every
  CM `L`, the Rosati condition for `θ(L)` gives F1's `hRos` (`f2_isRosatiSkew_of_rosati`);
* **Theorem 4.2, first sentence (generation)**, from `hGk` alone: `Hdg^p(Y; ℚ) = pwPowerSpan … p`
  for every `p`, the image under G2's model map of the model span `cmPowerSpan θ(L)^*` generated
  by `1`, the rational degree-two Hodge classes and the pullbacks of the rational Weil classes of
  `A` (`pw_thm_4_2_generation_general`); and the same on `Y` itself,
  `Hdg^p(Y; ℚ) = f1_pulledWeilCupSpan … Hdg¹(Y; ℚ) p` (`pw_thm_4_2_generation_cup_general`);
* **the divisor-class form**, from `hGk` and Lefschetz (1,1) (`h11`): every Hodge class of `Y` lies
  in the cup-closed span of `1`, the span of divisor classes and the planes `f_a^* W_k(A)`,
  `a ∈ 𝒪^r` (`f2_hdg_le_pulledWeilCupSpan_divisor`);
* **Theorem 4.2, second sentence (HC)**, from `hGk`, the paper's (P4) `hWA`, and three classical
  cycle inputs kept as explicit binders (`hPull`, `hC9`, `h11`, as in F1):
  `Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p` for every `p` (`pw_thm_4_2_hc_general`).

Checks (`example`s): the model statement on `H¹(A)` (A6's S8 at the abelian variety); `r = 0`,
`r = 1` (`Y = A`), `p = 0`, `p > r · dim A`; at `[L : ℚ] = 2` the two Rosati conditions agree, the
powers span is F-1575's `divisorPulledWeilSpan` form (A6's S9), and F1's `pw_thm_4_2_generation`
and `pw_thm_4_2_hc` are recovered; (P4) is recovered from the conclusion at `r = 1`; `hGk` is not
automatic (PW-0's S12); and examples of the shapes of PW v0.3, Corollary 5.9 (case (Q6)) and
Corollary 5.13 (CM type, `m = 1`).

It does not claim: the existence of `A^r` or of power data for `r ≥ 2` (power data is a binder);
that `hGk`, `hWA`, `hPull`, `hC9`, `h11` or `hRos` hold for any particular `A`, `Y` or `pol` (in
particular no positivity of `pol` is assumed, so `hRos` is not derived from it); the algebraic-group
form of (P3) (only its Lie-algebra form is stated); that `A` is simple or `End⁰(A) = L` (the latter
is a paper hypothesis omitted in this strengthening because `hGk` directly supplies the only
consequence used by the Lean proof; literal-paper and corollary-shaped examples carry it unused); a
counterexample to generation without (P3); that the divisor-class span equals the Hodge classes
(that needs `CycleClassIsHodge`, not bound). HC no distance; AV milestone no distance.
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
variable {L : Type*} [Field L] [NumberField L] [IsCMField L]

/-- **The Rosati condition at `L = k`.** For a CM field of degree `2` (`L = ℚ(u)`, `e = 1`), the
Rosati condition for `J = θ(u)^*` alone (F1's `hRos`, `IsRosatiSkew`) gives the Rosati condition
for all of `θ(L)` with the CM conjugation: `L = ℚ ⊕ ℚu`, the conjugation fixes `ℚ` and sends `u`
to `-u` (it is not the identity, `complexConj_ne_one`, and `c(u)² = u²`), so
`E(θ(p + qu)^* x, y) = E(x, θ(p - qu)^* y)`.
Source: PW v0.3, Subsection 2.3 (the Rosati involution induces complex conjugation on `L`); Mathlib
`NumberField.IsCMField.complexConj_ne_one`; `polarizationForm_skew` (`RealDefs/F1569.lean`). -/
theorem f2_rosati_of_finrank_two (hL : Module.finrank ℚ L = 2) (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u)) :
    ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y) :=
  f2_rosati_of_finrank_two_aux A hL θ u hd hu pol hη hRos

/-- **The Rosati condition for `θ(L)` contains F1's `hRos`.** For every CM field `L`, the Rosati
condition for all of `θ(L)` makes `J = θ(u)^*` skew for the polarization 2-vector: the CM
conjugation sends `u` to `-u` (`c(u)² = u²`, and `c(u) = u` would put `u` in the totally real
subfield `L⁺`, where `u² = -d < 0` is impossible), and `isRosatiSkew_iff_dualForm`.
Source: PW v0.3, Subsection 2.3; Mathlib `NumberField.IsCMField.complexConj_eq_self_iff`;
`isRosatiSkew_iff_dualForm` (`Foundations/DualForm.lean`). -/
theorem f2_isRosatiSkew_of_rosati (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) hη x
          (pwAction A θ (IsCMField.complexConj L a) y)) :
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u) :=
  f2_isRosatiSkew_of_rosati_aux A θ u hd hu pol hη hRos

/-- At `[L : ℚ] = 2` the two Rosati conditions are equivalent. -/
example (hL : Module.finrank ℚ L = 2) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol)) :
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u) ↔
      ∀ (a : L) (x y : HQ A 1),
        polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
          polarizationForm (torusCohomology_cupProductOf A) hη x
            (pwAction A θ (IsCMField.complexConj L a) y) :=
  ⟨f2_rosati_of_finrank_two A hL θ u hd hu pol hη, f2_isRosatiSkew_of_rosati A θ u hd hu pol hη⟩

/-- **The model statement on `H¹(A)`**: A6's S8 at `V = H¹(A; ℚ)`, `ι = θ(·)^*`, `E` the
polarization form. Under `hGk` the rational Hodge classes of `⋀^k (H¹(A) ⊗ ℚ^r)` are
`cmPowerSpan θ(L)^*`, for every `r` and `k`. -/
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
    (r k : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal r k =
      cmPowerSpan (pwActionRange A θ)
        (rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
          (abelianWeightOneHodgeStructure A).isInternal r 2)
        ((f1_weilAction A θ u d hu).weilClasses
          (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
            (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A))
          (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
            (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
              (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)) k :=
  letI := (finiteBetti_abelian A).finite 1
  spec_a6_rationalExteriorHodge_eq_cmPowerSpan (pwAction A θ) (f1_weilAction A θ u d hu) u rfl
    (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A))
    (polarizationForm (torusCohomology_cupProductOf A) hη)
    (nondegenerate_polarizationForm (torusCohomology_cupProductOf A) hη)
    (isAlt_polarizationForm (torusCohomology_cupProductOf A) hη) hRos hd
    (by rw [hu, map_neg]) hGk r k

/-- **`hGk` is not automatic** (PW-0's S12): on the CM-point structure `hsuCMHodge` the Hodge Lie
algebra is a line and `HodgeLieIsGk` fails. -/
example :
    ¬ HodgeLieIsGk hsuCMHodge spec_hsuCMHodge_isInternal hsuE (Algebra.adjoin ℚ {hsuJ}) hsuJ :=
  spec_pw0_not_hodgeLieIsGk_hsuCMHodge

variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] {r : ℕ}

/-- **PW v0.3, Theorem 4.2, first sentence: generation on every power, for a CM field `L`.**
Under (P3) in Lie-algebra form (`hGk`, with `R = θ(L)^*`), for any power data
`P : AbelianPowerData A Y r`, the rational Hodge classes `Hdg^p(Y; ℚ)` are exactly
`pwPowerSpan … P p`: the image under G2's model map of the model span `cmPowerSpan θ(L)^*`
generated by `1`, the rational degree-two Hodge classes and the pullbacks of the rational Weil
classes of `A` along every `cmPowerPullback`, `a ∈ L^r`. This is the paper's first sentence without
its hypothesis `End⁰(A) = L` (`Function.Bijective θ`), hence a strengthening: the Lean proof uses
only (P3), supplied directly by `hGk`. Weil type is derived; any `d > 0`; no dimension, signature or
discriminant hypothesis.
Source: PW v0.3, Theorem 4.2 (`thm:gen`), first sentence;
`spec_a6_rationalExteriorHodge_eq_cmPowerSpan` (A6's S8, the model),
`spec_g2_rationalExteriorHodge_map_eq` (G2, the transport). -/
theorem pw_thm_4_2_generation_general (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (P : AbelianPowerData A Y r) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(Y; ℚ) = pwPowerSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P p :=
  pw_thm_4_2_generation_general_aux A θ u hd hu pol hη hRos hGk P

/-- **Literal paper form of Theorem 4.2's first sentence.** The paper's `End⁰(A) = L` hypothesis is
the unused binder `_hθ`; the strengthened frozen statement supplies the conclusion. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (_hθ : Function.Bijective θ) (u : L) {d : ℚ}
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
    (P : AbelianPowerData A Y r) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(Y; ℚ) = pwPowerSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P p :=
  pw_thm_4_2_generation_general A θ u hd hu pol hη hRos hGk P

/-- **Degenerate check `r = 1`**: for `Y = A` (`AbelianPowerData.one A`), the Hodge classes of `A`
itself are the powers span. -/
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
    Hdg^p(A; ℚ) = pwPowerSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (AbelianPowerData.one A) p :=
  pw_thm_4_2_generation_general A θ u hd hu pol hη hRos hGk (AbelianPowerData.one A) p

/-- **Degenerate checks `r = 0` and `p > r · dim A`**: there the powers span is `0` (G2's
`spec_g2_hodgeClasses_eq_bot_of_lt`); at `r = 0` this is every `p > 0`. -/
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
    (P : AbelianPowerData A Y r) (p : ℕ) (hp : r * dim A.left < p) :
    letI := (finiteBetti_abelian A).finite 1
    pwPowerSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P p = ⊥ := by
  rw [← pw_thm_4_2_generation_general A θ u hd hu pol hη hRos hGk P p]
  exact spec_g2_hodgeClasses_eq_bot_of_lt P p hp

/-- **Degenerate check `p = 0`**: with F1's binder-free `f1_pwPowerSpan_zero`, every class of
`HQ Y 0` is a Hodge class (`H⁰` is of type `(0, 0)`), for every `r`, including `r = 0`. -/
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
    (P : AbelianPowerData A Y r) :
    Hdg^0(Y; ℚ) = ⊤ := by
  rw [pw_thm_4_2_generation_general A θ u hd hu pol hη hRos hGk P 0]
  exact f1_pwPowerSpan_zero A θ u d hu _ P

/-- **The specialization `L = k` in the model form** (A6's S9): for `[L : ℚ] = 2` the powers span
is the image of F-1575's `divisorPulledWeilSpan` for `J = θ(u)^*`. -/
example (hL : Module.finrank ℚ L = 2) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
    (hd : 0 < d) (hu : u ^ 2 = -algebraMap ℚ L d)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A θ u d hu).IsWeilType)
    (P : AbelianPowerData A Y r) (p : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    pwPowerSpan A θ u d hu hW P p =
      (divisorPulledWeilSpan (pwAction A θ u)
        (rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
          (abelianWeightOneHodgeStructure A).isInternal r 2)
        ((f1_weilAction A θ u d hu).weilClasses
          (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
            (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) hW)
        (2 * p)).map (P.cohomologyMap (2 * p)) := by
  let := (finiteBetti_abelian A).finite 1
  unfold pwPowerSpan
  rw [← spec_a6_cmPowerSpan_range_eq_divisorPulledWeilSpan hL (pwAction A θ) u hd
    (by rw [hu, map_neg])]
  rfl

/-- **The specialization `L = k = ℚ(√-3)` recovers the CM-number-field, degree-two instance of
F1's `pw_thm_4_2_generation` after replacing F1's `hL`.** Here `hRos` is for `u` alone. -/
example (hL : Module.finrank ℚ L = 2) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (P : AbelianPowerData A Y r) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(Y; ℚ) = pwPowerSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P p :=
  pw_thm_4_2_generation_general A θ u (by norm_num) hu pol hη
    (f2_rosati_of_finrank_two A hL θ u (by norm_num) hu pol hη hRos) hGk P

/-- **Theorem 4.2, first sentence, on `Y` itself, for a CM field `L`.** As in the model-span form,
this omits `End⁰(A) = L` and strengthens the paper: `hGk` supplies (P3) directly. Under `hGk`,
`Hdg^p(Y; ℚ)` is the degree-`2p` part of the least cup-closed family in `HQ Y (2·)` containing
`1`, `Hdg¹(Y; ℚ)` and the pullbacks `f_a^*` of the rational Weil classes `weilClassOf` of `A`, for
`a ∈ 𝒪^r`. From `pw_thm_4_2_generation_general` exactly as F1's `pw_thm_4_2_generation_cup` from
F1's generation statement (F1's proof uses `L = k` only there): `≤` transports the model span
along the multiplicative model map, clearing denominators `L^r → 𝒪^r`
(`spec_g4_exists_nat_mul_mem_pwOrder`); `≥` because the generators are Hodge classes
(`weilClassOf_le_hdg`, `spec_homPullback_hodgeClasses`) and Hodge classes are cup-closed.
Source: PW v0.3, Theorem 4.2, first sentence, and its proof, paragraph "Conclusion";
`pw_thm_4_2_generation_general`; F1's `pw_thm_4_2_generation_cup`. -/
theorem pw_thm_4_2_generation_cup_general (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (P : AbelianPowerData A Y r) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(Y; ℚ) = f1_pulledWeilCupSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      P Hdg^1(Y; ℚ) p :=
  pw_thm_4_2_generation_cup_general_aux A θ u hd hu pol hη hRos hGk P

/-- The two spans of Theorem 4.2 on `Y` agree, under `hGk`. -/
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
    (P : AbelianPowerData A Y r) (p : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    pwPowerSpan A θ u d hu
        (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
          (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
            (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P p =
      f1_pulledWeilCupSpan A θ u d hu
        (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
          (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
            (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
        P Hdg^1(Y; ℚ) p :=
  (pw_thm_4_2_generation_general A θ u hd hu pol hη hRos hGk P p).symm.trans
    (pw_thm_4_2_generation_cup_general A θ u hd hu pol hη hRos hGk P p)

/-- **The divisor-class form, for a CM field `L`** (the paper's literal "generated by the divisor
classes"). Like the frozen generation statement it omits `End⁰(A) = L`, whose role is replaced by
the direct (P3) binder `hGk`. Under `hGk` and Lefschetz (1,1) (`h11`), every Hodge class of `Y` lies in the
cup-closed span of `1`, the span of divisor classes `algebraicCycleClassSpan Y 1` and the planes
`f_a^* W_k(A)`, `a ∈ 𝒪^r`. By `pw_thm_4_2_generation_cup_general` and
`Hdg¹(Y; ℚ) ≤ algebraicCycleClassSpan Y 1` (`h11.holds Y`). Only `≤` is claimed: `≥` would need
divisor classes to be Hodge classes (`CycleClassIsHodge`), which is not bound.
Source: PW v0.3, Theorem 4.2, first sentence, and its proof, paragraph "Divisor classes" (the
Lefschetz (1,1) theorem); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`LefschetzOneOneHyp`). -/
theorem f2_hdg_le_pulledWeilCupSpan_divisor (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (h11 : LefschetzOneOneHyp) (P : AbelianPowerData A Y r) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ f1_pulledWeilCupSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      P (algebraicCycleClassSpan Y 1) p :=
  f2_hdg_le_pulledWeilCupSpan_divisor_aux A θ u hd hu pol hη hRos hGk h11 P

/-- In degree one this is Lefschetz (1,1) for `Y` again, through the span. -/
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
    (h11 : LefschetzOneOneHyp) (P : AbelianPowerData A Y r) :
    letI := (finiteBetti_abelian A).finite 1
    Hdg^1(Y; ℚ) ≤ f1_pulledWeilCupSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      P (algebraicCycleClassSpan Y 1) 1 :=
  f2_hdg_le_pulledWeilCupSpan_divisor A θ u hd hu pol hη hRos hGk h11 P 1

/-- **PW v0.3, Theorem 4.2, second sentence, for a CM field `L`: the Hodge conjecture on every
power.** This omits the paper's hypothesis `End⁰(A) = L` (`Function.Bijective θ`) and is therefore
a strengthening. The Lean proof does not use it: (P3) is supplied directly by `hGk`. If the
rational Weil classes of `A` for `k = ℚ(u)` are algebraic (`hWA`, the paper's
(P4)), then, under `hGk`, every Hodge class of `Y` is algebraic, given three classical cycle inputs
kept as explicit binders: pullback along each `f_a = P.pwSumMap θ a` maps algebraic classes to
algebraic classes (`hPull`), algebraic classes are closed under cup product on `Y` (`hC9`, C9), and
Lefschetz (1,1) (`h11`). By `f2_hdg_le_pulledWeilCupSpan_divisor`: `algebraicCycleClassSpan Y` is
a closed family.
Source: PW v0.3, Theorem 4.2, second sentence, and its proof, paragraph "Conclusion" ("If
`W_k(A)` is spanned by algebraic classes, so is each `f_a^* W_k(A)`"); Fulton, *Intersection
Theory*, 2nd ed., Ch. 8 and Corollary 19.2 (pullback and products of cycle classes, through `hPull`
and `CycleClassMultiplicative`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2
(through `LefschetzOneOneHyp`). -/
theorem pw_thm_4_2_hc_general (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (P : AbelianPowerData A Y r)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q)
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  pw_thm_4_2_hc_general_aux A θ u hd hu pol hη hRos hGk hWA P hPull hC9 h11

/-- **Literal paper form of Theorem 4.2's second sentence.** The paper's `End⁰(A) = L` hypothesis
is the unused binder `_hθ`; the strengthened frozen statement supplies the conclusion. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (_hθ : Function.Bijective θ) (u : L) {d : ℚ}
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
    (P : AbelianPowerData A Y r)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q)
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  pw_thm_4_2_hc_general A θ u hd hu pol hη hRos hGk hWA P hPull hC9 h11

/-- **(P4) cannot be dropped**: the conclusion of `pw_thm_4_2_hc_general` for `Y = A` gives `hWA`
back, since the rational Weil classes are Hodge classes (`weilClassOf_le_hdg`). So at `r = 1` the
statement is equivalent to (P4) given the other inputs. Any `L`, any `d`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ) (hu : u ^ 2 = -algebraMap ℚ L d)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A θ u d hu).IsWeilType)
    (hHC : ∀ p : ℕ, Hdg^p(A; ℚ) ≤ algebraicCycleClassSpan A p) :
    letI := (finiteBetti_abelian A).finite 1
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (f1_weilAction A θ u d hu) hW :=
  (weilClassOf_le_hdg _ _ _ _ (cupFiltered_cupProductOf_of_abelian A) _ hW).trans (hHC _)

/-- **The specialization `L = k = ℚ(√-3)` recovers the CM-number-field, degree-two instance of
F1's `pw_thm_4_2_hc` after replacing F1's `hL`.** -/
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
    (P : AbelianPowerData A Y r)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q)
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  pw_thm_4_2_hc_general A θ u (by norm_num) hu pol hη
    (f2_rosati_of_finrank_two A hL θ u (by norm_num) hu pol hη hRos) hGk hWA P hPull hC9 h11

/-- **The shape of PW v0.3, Corollary 5.9 (case (Q6))**: `L = kF` a CM field of degree `4`
(`e = 2`), `k` any imaginary quadratic field (`u² = -d`), `End⁰(A) = L` (`θ` bijective),
`dim A = 6` (`m = 3`). The paper derives (P3) from Proposition 5.6 and (P4) from (I4) after a
change of polarization; here both are binders, so the degree, the dimension and the bijectivity
are not used. The Hodge conjecture then holds on every power `Y`, given the classical cycle inputs
on that power. -/
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
    ∀ (r : ℕ) (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
      [Smooth Y.hom] [IsProjective Y.hom] (P : AbelianPowerData A Y r),
      (∀ (a : Fin r → pwOrder A θ) (q : ℕ),
        (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
          algebraicCycleClassSpan Y q) →
      CycleClassMultiplicative (cupProductOf Y) →
      ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  fun _ _ _ _ _ _ _ P hPull hC9 =>
    pw_thm_4_2_hc_general A θ u hd hu pol hη hRos hGk hWA P hPull hC9 h11

/-- **The shape of PW v0.3, Corollary 5.13(1) (CM type, `m = 1`, `e = 6`)**: `L = kF` a CM field
of degree `12`, `End⁰(A) = L`, `dim A = 6`. The paper derives (P3) from `dim Hg(A) = 5` and (P4)
from (I4); here both are binders. As for the Corollary 5.9 check, the conclusion is the Hodge
conjecture for every `r`, every power target `Y`, and every power datum `P`, given the classical
cycle inputs on that power. -/
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
    ∀ (r : ℕ) (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
      [Smooth Y.hom] [IsProjective Y.hom] (P : AbelianPowerData A Y r),
      (∀ (a : Fin r → pwOrder A θ) (q : ℕ),
        (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
          algebraicCycleClassSpan Y q) →
      CycleClassMultiplicative (cupProductOf Y) →
      ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  fun _ _ _ _ _ _ _ P hPull hC9 =>
    pw_thm_4_2_hc_general A θ u hd hu pol hη hRos hGk hWA P hPull hC9 h11

end HodgeLean.Adapters
