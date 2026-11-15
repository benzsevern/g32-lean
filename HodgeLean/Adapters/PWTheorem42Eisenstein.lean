import HodgeLean.Adapters.PWTheorem42EisensteinProofs

/-! # The Powers flagship, stage F1 (milestone M1): Theorem 4.2 for `L = k = ℚ(√-3)` (FROZEN SPEC)

Stage F1 of the Powers flagship plan (`docs/roadmap/pw-flagship-plan.md`, §4.2, row F1): PW v0.3,
Theorem 4.2 (`thm:gen`), "Hodge classes on powers of abelian varieties of Weil type and of type
IV with exact endomorphism algebra" (doi:10.5281/zenodo.23570103), in the case `L = k = ℚ(u)`,
`u² = -3` (`e = 1`). Each theorem is proved by the matching `_aux` theorem in
`PWTheorem42EisensteinProofs.lean`; the definitions are in `PWTheorem42EisensteinDefs.lean`.

The setting: an abelian `A` (a commutative group object over `ℂ`, integral, smooth and projective);
a field `L` with `θ : L →ₐ[ℚ] End⁰(A)` and `u : L`, `u² = -3`, generating `L` over `ℚ`
(`hL : Algebra.adjoin ℚ {u} = ⊤`, so `L = ℚ(√-3)`); a class `pol ∈ H²(A; ℚ)` whose 2-vector is
nondegenerate (`hη`) and Rosati-compatible with `J = θ(u)^*` (`hRos`); and power data
`P : AbelianPowerData A Y r` (stage G4), a stand-in for `Y = A^r`. The only Hodge-group binder is
`hGk`, the Lie-algebra form of the paper's (P3) `Hg(A) = G_k(A)`; Weil type is derived from it
(`isWeilType_of_hodgeLieIsGk`). No family-M hypothesis, no dimension hypothesis.

It claims, as implications from the named binders:

* **(P3) at `L = k` is `hSU`**: `hGk` is equivalent to F-1575's equality `F1575MemberHodgeGroupIsSU`'s
  shape for `J = θ(u)^*` (`f1_hodgeLieIsGk_iff`);
* **the model statement**: from `hGk`, the rational Hodge classes of `⋀^k (H¹(A) ⊗ ℚ^m)` are
  F-1575's `divisorPulledWeilSpan` for `J = θ(u)^*`; so F-1575's S4 holds for every member of `M`
  whose action comes from `θ`, with `hSU` replaced by `hGk`
  (`f1_rationalExteriorHodge_eq_divisorPulledWeilSpan`);
* **degree zero**: `pwPowerSpan … 0 = ⊤`, with no binder (`f1_pwPowerSpan_zero`);
* **Theorem 4.2, first sentence (generation)**, from `hGk` alone: `Hdg^p(Y; ℚ) = pwPowerSpan … p`
  for every `p`, the image of PW-0's model span under G2's model map (`pw_thm_4_2_generation`);
  and the same on `Y` itself, `Hdg^p(Y; ℚ) = f1_pulledWeilCupSpan … Hdg¹(Y; ℚ) p`, the cup-closed
  span of `1`, `Hdg¹(Y; ℚ)` and the pullbacks `f_a^*` of the rational Weil classes of `A`,
  `a ∈ 𝒪^r` (`pw_thm_4_2_generation_cup`);
* **the divisor-class form**, from `hGk` and Lefschetz (1,1) (`h11`): every Hodge class of `Y` lies
  in the cup-closed span of `1`, the span of divisor classes and the planes `f_a^* W_k(A)`
  (`f1_hdg_le_pulledWeilCupSpan_divisor`);
* **Theorem 4.2, second sentence (HC)**, from `hGk`, the paper's (P4) `hWA` (the rational Weil
  classes of `A` are algebraic), and three classical cycle inputs kept as explicit binders:
  algebraic classes pull back along every `f_a` (`hPull`), multiply (`hC9`), and `Hdg¹` is spanned
  by divisor classes (`h11`): `Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p` for every `p`
  (`pw_thm_4_2_hc`).

Checks (`example`s): `r = 0`, `r = 1` (`Y = A`), `p = 0`, `p > r · dim A`; F1575PowersFix S3 and
S4 for a member of `M` whose action is `θ(u)^*`, with `hSU` replaced by `hGk`; (P4) is recovered
from the conclusion at `r = 1`, so it cannot be dropped; and two examples of the shape of PW v0.3,
Corollary 5.1.

It does not claim: anything for `L ≠ k` (`e > 1`) or `k ≠ ℚ(√-3)` (stage F2); the existence of `A^r`
or of power data for `r ≥ 2` (power data is a binder); that `hGk`, `hWA`, `hPull`, `hC9` or `h11`
hold for any particular `A` or `Y`; the algebraic-group form of (P3) (only its Lie-algebra form is
stated); a counterexample to generation without (P3) (none is constructed); that the divisor-class
span equals the Hodge classes (that needs cycle classes to be Hodge, `CycleClassIsHodge`, not
bound). HC no distance; AV milestone no distance.
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
variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **(P3) at `L = k = ℚ(√-3)` is F-1575's `hSU`.** For `L = ℚ(u)`, the image of `L` in
`End_ℚ H¹(A)` is `ℚ[J]`, `J = θ(u)^*` (`spec_g4_pwActionRange_eq_adjoin`), and PW-0's
`spec_pw0_hodgeLieIsGk_adjoin_iff` turns `HodgeLieIsGk` at `ℚ[J]` into the equality of the
complexified Hodge Lie algebra with `complexSU`, which is the body of
`F1575MemberHodgeGroupIsSU`.
Source: PW v0.3, proof of Theorem 3.1, first paragraph (`L = k`, `G_k(A) = SU(V, H)`);
`spec_g4_pwActionRange_eq_adjoin`, `spec_pw0_hodgeLieIsGk_adjoin_iff`, `isAlt_polarizationForm`. -/
theorem f1_hodgeLieIsGk_iff (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u)) :
    letI := (finiteBetti_abelian A).finite 1
    HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u) ↔
      complexSpan (hodgeLieAlgebra (abelianWeightOneHodgeStructure A).H
          (abelianWeightOneHodgeStructure A).isInternal).toSubmodule =
        (complexSU (polarizationForm (torusCohomology_cupProductOf A) hη)
          (nondegenerate_polarizationForm (torusCohomology_cupProductOf A) hη)
          (f1_weilAction A θ u 3 hu).J (f1_weilAction A θ u 3 hu).J_sq
          (polarizationForm_skew (torusCohomology_cupProductOf A) hη hRos)).toSubmodule :=
  f1_hodgeLieIsGk_iff_aux A θ u hu hL pol hη hRos

/-- For a member of `M` whose action is `θ(u)^*`, F-1575's `hSU` is `hGk`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3)
    (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (f1_weilAction A θ u 3 hu) pol) :
    letI := (finiteBetti_abelian A).finite 1
    F1575MemberHodgeGroupIsSU (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
        (f1_weilAction A θ u 3 hu) hM ↔
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate) (pwActionRange A θ)
        (pwAction A θ u) :=
  (f1_hodgeLieIsGk_iff A θ u hu hL pol hM.nondegenerate hM.rosati).symm

/-- **The specialization: F-1575's powers result in the model, from (P3).** Under `hGk`, the
rational Hodge classes of `⋀^k (H¹(A) ⊗ ℚ^m)` are exactly F-1575's `divisorPulledWeilSpan` for
`J = θ(u)^*`, generated by `1`, the rational degree-two Hodge classes and the pullbacks
`x ↦ x ⊗ r + J x ⊗ s` of the rational Weil classes. Any dimension; Weil type derived.
Source: PW v0.3, Theorem 4.2 at `L = k = ℚ(√-3)`; F-1575 / TR54 §3;
`spec_pw0_rationalExteriorHodge_eq_divisorPulledWeilSpan` with `f1_hodgeLieIsGk_iff`;
`f1575Power_rationalExteriorHodge_eq_hodgeTwoPulledWeilSpan` (the case of a member of `M`). -/
theorem f1_rationalExteriorHodge_eq_divisorPulledWeilSpan (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (m k : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal m k =
      divisorPulledWeilSpan (pwAction A θ u)
        (rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
          (abelianWeightOneHodgeStructure A).isInternal m 2)
        ((f1_weilAction A θ u 3 hu).weilClasses
          (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
            (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A))
          (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
            (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
              (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)) k :=
  f1_rationalExteriorHodge_eq_divisorPulledWeilSpan_aux A θ u hu hL pol hη hRos hGk m k

/-- **F1575PowersFix S4 for a member of `M` with action `θ(u)^*`, with `hSU` replaced by `hGk`.**
The span `f1575PowerHodgeTwoPulledWeilSpan hM` is `divisorPulledWeilSpan` by definition; `hM`
enters only through its nondegeneracy and Rosati fields. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3)
    (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (f1_weilAction A θ u 3 hu) pol)
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate) (pwActionRange A θ)
        (pwAction A θ u))
    (m k : ℕ) :
    letI := (torusCohomology_cupProductOf A).finite
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
    rationalExteriorHodge S.weight1.H S.weight1.isInternal m k =
      f1575PowerHodgeTwoPulledWeilSpan hM m k :=
  f1_rationalExteriorHodge_eq_divisorPulledWeilSpan A θ u hu hL pol hM.nondegenerate hM.rosati
    hGk m k

/-- **F1575PowersFix S3 (the complex form) for a member of `M` with action `θ(u)^*`, with `hSU`
replaced by `hGk`**: PW-0's `spec_pw0_exteriorHodgeClasses_eq_divisorPulledWeilSpan` with `hSU`
from `f1_hodgeLieIsGk_iff`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3)
    (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (f1_weilAction A θ u 3 hu) pol)
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate) (pwActionRange A θ)
        (pwAction A θ u))
    (m k : ℕ) :
    letI := (torusCohomology_cupProductOf A).finite
    let S := abelianVarietyCohomologyOf (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
    exteriorHodgeClasses S.weight1.H S.weight1.isInternal m k =
      ((f1575PowerHodgeTwoPulledWeilSpan hM m k).baseChange ℂ).map
        (exteriorBaseChange k).toLinearMap :=
  letI := (finiteBetti_abelian A).finite 1
  spec_pw0_exteriorHodgeClasses_eq_divisorPulledWeilSpan (f1_weilAction A θ u 3 hu)
    (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) hM.isWeilType
    (polarizationForm (torusCohomology_cupProductOf A) hM.nondegenerate)
    (nondegenerate_polarizationForm _ hM.nondegenerate)
    (polarizationForm_skew _ hM.nondegenerate hM.rosati)
    ((f1_hodgeLieIsGk_iff A θ u hu hL pol hM.nondegenerate hM.rosati).1 hGk) m k

variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] {r : ℕ}

/-- **Degenerate check `p = 0`, with no binder**: the powers span is all of `HQ Y 0`. In degree
`0` the model `⋀^0 (H¹(A) ⊗ ℚ^r) = ℚ` is spanned by the unit, which `cmPowerSpan` contains, and
the model map `P.cohomologyMap 0` is bijective (`spec_g2_cohomologyMap_bijective`).
Source: `IsCMPowerClosed.unit_mem`; Mathlib `exteriorPower` in degree zero;
`spec_g2_cohomologyMap_bijective`, `spec_g2_cohomologyMap_zero`. -/
theorem f1_pwPowerSpan_zero (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ)
    (hu : u ^ 2 = -algebraMap ℚ L d)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A θ u d hu).IsWeilType)
    (P : AbelianPowerData A Y r) :
    pwPowerSpan A θ u d hu hW P 0 = ⊤ :=
  f1_pwPowerSpan_zero_aux A θ u d hu hW P

/-- So the unit class lies in the powers span, even at `r = 0`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ) (hu : u ^ 2 = -algebraMap ℚ L d)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A θ u d hu).IsWeilType)
    (P : AbelianPowerData A Y r) :
    (show HQ Y (2 * 0) from cupUnit Y) ∈ pwPowerSpan A θ u d hu hW P 0 := by
  rw [f1_pwPowerSpan_zero]
  trivial

/-- **PW v0.3, Theorem 4.2, first sentence, at `L = k = ℚ(√-3)`: generation on every power.**
Under (P3) in Lie-algebra form (`hGk`), for any power data `P : AbelianPowerData A Y r`, the
rational Hodge classes `Hdg^p(Y; ℚ)` are exactly `pwPowerSpan … P p`: the image under G2's model
map of PW-0's span generated by `1`, the rational degree-two Hodge classes and the pullbacks of
the rational Weil classes of `A` along every `f_a`. Implication from `hGk` alone; Weil type is
derived; no dimension, discriminant or positivity hypothesis.
Source: PW v0.3, Theorem 4.2 (`thm:gen`), first sentence, at `e = 1`;
`spec_pw0_rationalExteriorHodge_eq_cmPowerSpan` (the model, at `R = ℚ[J]`),
`spec_g4_pwActionRange_eq_adjoin`, `spec_g2_rationalExteriorHodge_map_eq` (the transport). -/
theorem pw_thm_4_2_generation (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
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
  pw_thm_4_2_generation_aux A θ u hu hL pol hη hRos hGk P

/-- **Degenerate check `r = 1`**: for `Y = A` (`AbelianPowerData.one A`), the Hodge classes of `A`
itself are the powers span. -/
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
    Hdg^p(A; ℚ) = pwPowerSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (AbelianPowerData.one A) p :=
  pw_thm_4_2_generation A θ u hu hL pol hη hRos hGk (AbelianPowerData.one A) p

/-- **Degenerate checks `r = 0` and `p > r · dim A`**: there the powers span is `0` (G2's
`spec_g2_hodgeClasses_eq_bot_of_lt`); at `r = 0` this is every `p > 0`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3)
    (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (P : AbelianPowerData A Y r) (p : ℕ) (hp : r * dim A.left < p) :
    letI := (finiteBetti_abelian A).finite 1
    pwPowerSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P p = ⊥ := by
  rw [← pw_thm_4_2_generation A θ u hu hL pol hη hRos hGk P p]
  exact spec_g2_hodgeClasses_eq_bot_of_lt P p hp

/-- **Theorem 4.2, first sentence, on `Y` itself.** Under `hGk`, `Hdg^p(Y; ℚ)` is the degree-`2p`
part of the least cup-closed family in `HQ Y (2·)` containing `1`, `Hdg¹(Y; ℚ)` and the pullbacks
`f_a^*` of the rational Weil classes `weilClassOf` of `A`, for `a ∈ 𝒪^r`. `≤`: transport the model
span (`pw_thm_4_2_generation`) along the model map, which is multiplicative, sends the model's
degree-two Hodge classes onto `Hdg¹(Y; ℚ)` (G2) and each Weil pullback over `L^r` to a nonzero
multiple of one over `𝒪^r` (G4 `spec_g4_exists_nat_mul_mem_pwOrder`, G2
`spec_g2_homPullback_pwSumMap_degree`). `≥`: the generators are Hodge classes (Weil's theorem
`weilClassOf_le_hdg`, G1b `spec_homPullback_hodgeClasses`) and Hodge classes of `Y` are closed
under cup product (`cupFiltered_cupProductOf_of_abelian`).
Source: PW v0.3, Theorem 4.2, first sentence, and its proof, paragraph "Conclusion";
`pw_thm_4_2_generation`, `divisorWeilSpan` (the `r = 1` shape). -/
theorem pw_thm_4_2_generation_cup (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (P : AbelianPowerData A Y r) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(Y; ℚ) = f1_pulledWeilCupSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      P Hdg^1(Y; ℚ) p :=
  pw_thm_4_2_generation_cup_aux A θ u hu hL pol hη hRos hGk P

/-- The two spans of Theorem 4.2 on `Y` agree, under `hGk`. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3)
    (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (P : AbelianPowerData A Y r) (p : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    pwPowerSpan A θ u 3 hu
        (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
          (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
            (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P p =
      f1_pulledWeilCupSpan A θ u 3 hu
        (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
          (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
            (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
        P Hdg^1(Y; ℚ) p :=
  (pw_thm_4_2_generation A θ u hu hL pol hη hRos hGk P p).symm.trans
    (pw_thm_4_2_generation_cup A θ u hu hL pol hη hRos hGk P p)

/-- **The divisor-class form** (the paper's literal "generated by the divisor classes"). Under
`hGk` and Lefschetz (1,1) (`h11`), every Hodge class of `Y` lies in the cup-closed span of `1`, the
span of divisor classes `algebraicCycleClassSpan Y 1` and the planes `f_a^* W_k(A)`, `a ∈ 𝒪^r`.
By `pw_thm_4_2_generation_cup` and `Hdg¹(Y; ℚ) ≤ algebraicCycleClassSpan Y 1` (`h11.holds Y`): a
family closed for the larger degree-two space is closed for the smaller one. Only `≤` is claimed:
`≥` would need divisor classes to be Hodge classes (`CycleClassIsHodge`), which is not bound.
Source: PW v0.3, Theorem 4.2, first sentence, and its proof, paragraph "Divisor classes" (the
Lefschetz (1,1) theorem); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`LefschetzOneOneHyp`). -/
theorem f1_hdg_le_pulledWeilCupSpan_divisor (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (h11 : LefschetzOneOneHyp) (P : AbelianPowerData A Y r) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ f1_pulledWeilCupSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      P (algebraicCycleClassSpan Y 1) p :=
  f1_hdg_le_pulledWeilCupSpan_divisor_aux A θ u hu hL pol hη hRos hGk h11 P

/-- In degree one this is Lefschetz (1,1) for `Y` again, through the span. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3)
    (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (h11 : LefschetzOneOneHyp) (P : AbelianPowerData A Y r) :
    letI := (finiteBetti_abelian A).finite 1
    Hdg^1(Y; ℚ) ≤ f1_pulledWeilCupSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      P (algebraicCycleClassSpan Y 1) 1 :=
  f1_hdg_le_pulledWeilCupSpan_divisor A θ u hu hL pol hη hRos hGk h11 P 1

/-- **PW v0.3, Theorem 4.2, second sentence, at `L = k = ℚ(√-3)`: the Hodge conjecture on every
power.** If the rational Weil classes of `A` are algebraic (`hWA`, the paper's (P4)), then, under
`hGk`, every Hodge class of `Y` is algebraic, given three classical cycle inputs kept as explicit
binders: pullback along each `f_a = P.pwSumMap θ a` maps algebraic classes to algebraic classes
(`hPull`), algebraic classes are closed under cup product on `Y` (`hC9`, C9), and Lefschetz (1,1)
(`h11`). By `f1_hdg_le_pulledWeilCupSpan_divisor`: `algebraicCycleClassSpan Y` is a closed family
(unit `unitClass_mem_algebraicCycleClassSpan`; divisor classes; `f_a^*` of the Weil classes by
`hWA` and `hPull`; cup products by `hC9`).
Source: PW v0.3, Theorem 4.2, second sentence, and its proof, paragraph "Conclusion" ("If
`W_k(A)` is spanned by algebraic classes, so is each `f_a^* W_k(A)`"); Fulton, *Intersection
Theory*, 2nd ed., Ch. 8 and Corollary 19.2 (pullback and products of cycle classes, through `hPull`
and `CycleClassMultiplicative`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2
(through `LefschetzOneOneHyp`). -/
theorem pw_thm_4_2_hc (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (P : AbelianPowerData A Y r)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q)
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  pw_thm_4_2_hc_aux A θ u hu hL pol hη hRos hGk hWA P hPull hC9 h11

/-- **(P4) cannot be dropped**: the conclusion of `pw_thm_4_2_hc` for `Y = A` gives `hWA` back,
since the rational Weil classes are Hodge classes (Weil's theorem `weilClassOf_le_hdg`, with
`cupFiltered_cupProductOf_of_abelian`). So the statement is not stronger than its hypothesis
allows: at `r = 1` it is equivalent to (P4) given the other inputs. -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3)
    (hW : letI := (finiteBetti_abelian A).finite 1; (f1_weilAction A θ u 3 hu).IsWeilType)
    (hHC : ∀ p : ℕ, Hdg^p(A; ℚ) ≤ algebraicCycleClassSpan A p) :
    letI := (finiteBetti_abelian A).finite 1
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (f1_weilAction A θ u 3 hu) hW :=
  (weilClassOf_le_hdg _ _ _ _ (cupFiltered_cupProductOf_of_abelian A) _ hW).trans (hHC _)

/-- **The shape of PW v0.3, Corollary 5.1, for sixfolds**: `k = ℚ(√-3)`, `A` of Weil type with
`End⁰(A) = k` (`θ` bijective) and `dim A = 6`. The paper derives (P3) from Theorem 3.1 and (P4)
from (I2); here both are binders, so the dimension and the bijectivity are not used. The Hodge
conjecture then holds on every power `Y` (every `r`, every power data), given the classical cycle
inputs on that power. -/
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
    ∀ (r : ℕ) (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
      [Smooth Y.hom] [IsProjective Y.hom] (P : AbelianPowerData A Y r),
      (∀ (a : Fin r → pwOrder A θ) (q : ℕ),
        (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
          algebraicCycleClassSpan Y q) →
      CycleClassMultiplicative (cupProductOf Y) →
      ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  fun _ _ _ _ _ _ _ P hPull hC9 =>
    pw_thm_4_2_hc A θ u hu hL pol hη hRos hGk hWA P hPull hC9 h11

/-- **Corollary 5.1's shape at `r = 1`**: the Hodge conjecture for `A` itself (`Y = A`,
`AbelianPowerData.one A`, whose maps `f_a` are the endomorphisms `a ∈ 𝒪`). -/
example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (hu : u ^ 2 = -algebraMap ℚ L 3)
    (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
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
    (hPull : ∀ (a : Fin 1 → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map
          (homPullback ((AbelianPowerData.one A).pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan A q)
    (hC9 : CycleClassMultiplicative (cupProductOf A)) (h11 : LefschetzOneOneHyp) (p : ℕ) :
    Hdg^p(A; ℚ) ≤ algebraicCycleClassSpan A p :=
  pw_thm_4_2_hc A θ u hu hL pol hη hRos hGk hWA (AbelianPowerData.one A) hPull hC9 h11 p

end HodgeLean.Adapters
