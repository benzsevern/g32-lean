import HodgeLean.Papers.PapersWeilCupEisenstein
import HodgeLean.Papers.PapersWeilCupGeneral
import HodgeLean.Papers.PapersWeilCupPowers
import HodgeLean.Papers.SkeletonG32
import HodgeLean.Papers.SkeletonG34
import HodgeLean.Papers.SkeletonTT

/-! # Paper theorems with cup-closure restricted to the PW algebra

Claimed: each `papw_` theorem is the corresponding `papl_` theorem with
`hC9 : CycleClassMultiplicative (cupProductOf Y)` replaced by the narrower
`papw_PWCupClosed`, cup-closure of algebraic classes inside the PW algebra
`f1_pulledWeilCupSpan … (algebraicCycleClassSpan Y 1)`. The conclusion is unchanged.

Not claimed: `hC9` itself; `papw_PWCupClosed` itself, which stays a classical input; any of `hGk`,
`hWA` or `hPull`. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters NumberField

namespace HodgeLean.Papers

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]

section Eisenstein

variable {L : Type*} [Field L] [Algebra ℚ L]
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] {r : ℕ}

/-- As `papl_skelg32_theorem92_conditional`, with `hC9` replaced by `papw_PWCupClosed`
(cup-closure inside the PW algebra).
Source: G32 v0.16, Theorem 9.2 (`thm:powers`); Fulton, *Intersection Theory*, 2nd ed., Chapter 8 and Corollary 19.2;
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papw_skelg32_theorem92_conditional (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9w : papw_PWCupClosed A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_pw_thm_4_2_hc A θ u hu hL pol hη hRos hGk hWA P hPull hC9w

/-- The conclusion of `skelg32_theorem92_conditional`, under its own hypotheses, from `papw_skelg32_theorem92_conditional`. -/
example : type_of% @HodgeLean.Papers.skelg32_theorem92_conditional := by
  intro A _ _ _ _ _ L _ _ Y _ _ _ _ _ r θ u hu hL pol hη hRos hGk hWA P hPull hC9w _h11 p
  exact papw_skelg32_theorem92_conditional A θ u hu hL pol hη hRos hGk hWA P hPull
    (papw_PWCupClosed_of_hC9 A θ u 3 hu _ P hC9w) p

/--
info: 'HodgeLean.Papers.papw_skelg32_theorem92_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papw_skelg32_theorem92_conditional

/-- As `papl_skelg32_theoremB`, with `hC9` replaced by `papw_PWCupClosed`
(cup-closure inside the PW algebra).
Source: G32 v0.16, Theorem B, its proof, and Theorem 9.2; Fulton, *Intersection Theory*,
2nd ed., Chapter 8 and Corollary 19.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papw_skelg32_theoremB (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (hM : letI := (finiteBetti_abelian A).finite 1
      IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
        (f1_weilAction A θ u 3 hu) pol)
    (hA : letI := (finiteBetti_abelian A).finite 1
      G32TheoremAStatement A (f1_weilAction A θ u 3 hu) pol)
    (P : AbelianPowerData A Y r)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q)
    (hC9w : papw_PWCupClosed A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_skelg32_theorem92_conditional A θ u hu hL pol hη hRos hGk (hA hM) P hPull hC9w

/-- The conclusion of `skelg32_theoremB`, under its own hypotheses, from `papw_skelg32_theoremB`. -/
example : type_of% @HodgeLean.Papers.skelg32_theoremB := by
  intro A _ _ _ _ _ L _ _ Y _ _ _ _ _ r θ u hu hL pol hη hRos hGk hM hA P hPull hC9w _h11 p
  exact papw_skelg32_theoremB A θ u hu hL pol hη hRos hGk hM hA P hPull
    (papw_PWCupClosed_of_hC9 A θ u 3 hu _ P hC9w) p

/--
info: 'HodgeLean.Papers.papw_skelg32_theoremB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papw_skelg32_theoremB

/-- As `papl_skelg34_theorem112_conditional`, with `hC9` replaced by `papw_PWCupClosed`
(cup-closure inside the PW algebra).
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem 11.2 (`thm:powers`) and Theorem C;
Fulton, *Intersection Theory*, 2nd ed., Chapter 8 and Corollary 19.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papw_skelg34_theorem112_conditional (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9w : papw_PWCupClosed A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p := by
  exact papw_pw_thm_4_2_hc A θ u hu hL pol hη hRos hGk hWA P hPull hC9w

/-- The conclusion of `skelg34_theorem112_conditional`, under its own hypotheses, from `papw_skelg34_theorem112_conditional`. -/
example : type_of% @HodgeLean.Papers.skelg34_theorem112_conditional := by
  intro A _ _ _ _ _ L _ _ Y _ _ _ _ _ r θ u hu hL pol hη hRos hGk hWA P hPull hC9w _h11 p
  exact papw_skelg34_theorem112_conditional A θ u hu hL pol hη hRos hGk hWA P hPull
    (papw_PWCupClosed_of_hC9 A θ u 3 hu _ P hC9w) p

/--
info: 'HodgeLean.Papers.papw_skelg34_theorem112_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papw_skelg34_theorem112_conditional

/-- As `papl_skelg34_theoremC`, with `hC9` replaced by `papw_PWCupClosed`
(cup-closure inside the PW algebra).
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem C and its proof in §11;
Fulton, *Intersection Theory*, 2nd ed., Chapter 8 and Corollary 19.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papw_skelg34_theoremC (hB : G34TheoremBStatement A) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (hPos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
    (hDim : TopologicalSpace.dim A.left = 6)
    (P : AbelianPowerData A Y r)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q)
    (hC9w : papw_PWCupClosed A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p := by
  let := (finiteBetti_abelian A).finite 1
  have hW := isWeilType_of_hodgeLieIsGk (by norm_num : (0 : ℚ) < 3)
    (f1_weilAction A θ u 3 hu)
    (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk
  have hWA := hB (f1_weilAction A θ u 3 hu) hW pol hη hRos hPos hDim
  exact papw_skelg34_theorem112_conditional A θ u hu hL pol hη hRos hGk hWA P hPull hC9w

/-- The conclusion of `skelg34_theoremC`, under its own hypotheses, from `papw_skelg34_theoremC`. -/
example : type_of% @HodgeLean.Papers.skelg34_theoremC := by
  intro A _ _ _ _ _ L _ _ Y _ _ _ _ _ r hB θ u hu hL pol hη hRos hGk hPos hDim P hPull hC9w _h11 p
  exact papw_skelg34_theoremC A hB θ u hu hL pol hη hRos hGk hPos hDim P hPull
    (papw_PWCupClosed_of_hC9 A θ u 3 hu _ P hC9w) p

/--
info: 'HodgeLean.Papers.papw_skelg34_theoremC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papw_skelg34_theoremC

end Eisenstein


section General

variable {L : Type*} [Field L] [NumberField L] [IsCMField L]
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] {r : ℕ}

/-- As `papl_skeltt_theorem82_conditional`, with `hC9` replaced by `papw_PWCupClosed`
(cup-closure inside the PW algebra).
Source: TT v0.15, Theorem 8.2 (`thm:powers`) and proof; Fulton, *Intersection Theory*, 2nd ed.,
Chapter 8 and Corollary 19.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papw_skeltt_theorem82_conditional (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (hC9w : papw_PWCupClosed A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_pw_thm_4_2_hc_general A θ u hd hu pol hη hRos hGk hWA P hPull hC9w

/-- The conclusion of `skeltt_theorem82_conditional`, under its own hypotheses, from `papw_skeltt_theorem82_conditional`. -/
example : type_of% @HodgeLean.Papers.skeltt_theorem82_conditional := by
  intro A _ _ _ _ _ L _ _ _ Y _ _ _ _ _ r θ u d hd hu pol hη hRos hGk hWA P hPull hC9w _h11 p
  exact papw_skeltt_theorem82_conditional A θ u hd hu pol hη hRos hGk hWA P hPull
    (papw_PWCupClosed_of_hC9 A θ u d hu _ P hC9w) p

/--
info: 'HodgeLean.Papers.papw_skeltt_theorem82_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papw_skeltt_theorem82_conditional

/-- As `papl_skeltt_g32_powers`, with `hC9` replaced by `papw_PWCupClosed`
(cup-closure inside the PW algebra).
Source: TT v0.15, Corollary 10.1 (`cor:g32`), powers clause, and Theorem 8.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papw_skeltt_g32_powers (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (pol : HQ A 2)
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
    (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (f1_weilAction A θ u 3 hu) pol)
    (hCell : TTG32CellStatement A (f1_weilAction A θ u 3 hu) pol)
    (P : AbelianPowerData A Y r)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q)
    (hC9w : papw_PWCupClosed A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p := by
  have hWA := hCell hM
  exact papw_skeltt_theorem82_conditional A θ u (by norm_num) hu pol hη hRos hGk
    hWA P hPull hC9w

/-- The conclusion of `skeltt_g32_powers`, under its own hypotheses, from `papw_skeltt_g32_powers`. -/
example : type_of% @HodgeLean.Papers.skeltt_g32_powers := by
  intro A _ _ _ _ _ L _ _ _ Y _ _ _ _ _ r θ u hu pol hη hRos hGk hM hCell P hPull hC9w _h11 p
  exact papw_skeltt_g32_powers A θ u hu pol hη hRos hGk hM hCell P hPull
    (papw_PWCupClosed_of_hC9 A θ u 3 hu _ P hC9w) p

/--
info: 'HodgeLean.Papers.papw_skeltt_g32_powers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papw_skeltt_g32_powers

end General
end HodgeLean.Papers
