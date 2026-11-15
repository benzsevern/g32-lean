import HodgeLean.Papers.PapersLefschetzEisenstein
import HodgeLean.Papers.PapersLefschetzGeneral
import HodgeLean.Papers.PapersLefschetzPowers
import HodgeLean.Papers.SkeletonG32
import HodgeLean.Papers.SkeletonG34
import HodgeLean.Papers.SkeletonTT

/-! # Paper theorems with the Lefschetz (1,1) premise supplied on abelian varieties

The PW v0.3 Theorem 4.2 statements, their power-link and `noPull` siblings, and the main-theorem
connectors of the G32, G34 and TT skeletons all take `h11 : LefschetzOneOneHyp`, the universal
Lefschetz (1,1) theorem over every smooth projective complex variety. Each proof uses it at one
variety only: the power target `Y` (or `g3_power A r`), which carries
`[GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]`. There the scoped statement
`LefschetzOneOneFor Y` is `chowG_lefschetzOneOne_abelian Y` (handoff 215).

Claimed: for each listed theorem, a `papl_` theorem with the same binders except `h11` and the same
conclusion, proved by copying the original proof body with `chowG_lefschetzOneOne_abelian Y` in place
of `h11.holds Y`. Each is an implication from the remaining binders (`hGk`, `hWA` or the paper's
Theorem A, B or cell statement, `hPull` where not supplied by `ccm6_hPull`, and `hC9`). An
`example` after each theorem derives the original's conclusion from the original's hypotheses
through the new theorem.

Not claimed: the universal `LefschetzOneOneHyp`; any of `hGk`, `hWA`, `hPull` or `hC9`; any
consumer that uses `h11` at a variety without a group structure in scope
(`docs/specs/PapersLefschetz.md`). HC no distance; AV milestone no distance.
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

/-- **G32 Theorem 9.2, powers connector, without `h11`.** As
`skelg32_theorem92_conditional`, with Lefschetz (1,1) on the power from
`chowG_lefschetzOneOne_abelian`.
Source: G32 v0.16, Theorem 9.2 (`thm:powers`); Fulton, *Intersection Theory*, 2nd ed., Chapter 8 and Corollary 19.2;
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_skelg32_theorem92_conditional (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papl_pw_thm_4_2_hc A θ u hu hL pol hη hRos hGk hWA P hPull hC9

/-- The conclusion of `skelg32_theorem92_conditional`, under its own hypotheses, from `papl_skelg32_theorem92_conditional`. -/
example : type_of% @HodgeLean.Papers.skelg32_theorem92_conditional := by
  intro A _ _ _ _ _ L _ _ Y _ _ _ _ _ r θ u hu hL pol hη hRos hGk hWA P hPull hC9 _h11 p
  exact papl_skelg32_theorem92_conditional A θ u hu hL pol hη hRos hGk hWA P hPull hC9 p

/--
info: 'HodgeLean.Papers.papl_skelg32_theorem92_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_skelg32_theorem92_conditional

/-- **G32 Theorem A implies Theorem B, without `h11`.** As `skelg32_theoremB`: the paper's
Theorem A is a statement-only premise, applied to membership in `M`.
Source: G32 v0.16, Theorem B, its proof, and Theorem 9.2; Fulton, *Intersection Theory*,
2nd ed., Chapter 8 and Corollary 19.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_skelg32_theoremB (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papl_skelg32_theorem92_conditional A θ u hu hL pol hη hRos hGk (hA hM) P hPull hC9

/-- The conclusion of `skelg32_theoremB`, under its own hypotheses, from `papl_skelg32_theoremB`. -/
example : type_of% @HodgeLean.Papers.skelg32_theoremB := by
  intro A _ _ _ _ _ L _ _ Y _ _ _ _ _ r θ u hu hL pol hη hRos hGk hM hA P hPull hC9 _h11 p
  exact papl_skelg32_theoremB A θ u hu hL pol hη hRos hGk hM hA P hPull hC9 p

/--
info: 'HodgeLean.Papers.papl_skelg32_theoremB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_skelg32_theoremB

/-- **G34 v1.5 Theorem 11.2, without `h11`.** As `skelg34_theorem112_conditional`, with
Lefschetz (1,1) on the power from `chowG_lefschetzOneOne_abelian`.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem 11.2 (`thm:powers`) and Theorem C;
Fulton, *Intersection Theory*, 2nd ed., Chapter 8 and Corollary 19.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_skelg34_theorem112_conditional (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p := by
  exact papl_pw_thm_4_2_hc A θ u hu hL pol hη hRos hGk hWA P hPull hC9

/-- The conclusion of `skelg34_theorem112_conditional`, under its own hypotheses, from `papl_skelg34_theorem112_conditional`. -/
example : type_of% @HodgeLean.Papers.skelg34_theorem112_conditional := by
  intro A _ _ _ _ _ L _ _ Y _ _ _ _ _ r θ u hu hL pol hη hRos hGk hWA P hPull hC9 _h11 p
  exact papl_skelg34_theorem112_conditional A θ u hu hL pol hη hRos hGk hWA P hPull hC9 p

/--
info: 'HodgeLean.Papers.papl_skelg34_theorem112_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_skelg34_theorem112_conditional

/-- **G34 Theorem C from Theorem B, without `h11`.** As `skelg34_theoremC`: the paper's
Theorem B is a statement-only premise.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem C and its proof in §11;
Fulton, *Intersection Theory*, 2nd ed., Chapter 8 and Corollary 19.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_skelg34_theoremC (hB : G34TheoremBStatement A) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p := by
  let := (finiteBetti_abelian A).finite 1
  have hW := isWeilType_of_hodgeLieIsGk (by norm_num : (0 : ℚ) < 3)
    (f1_weilAction A θ u 3 hu)
    (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk
  have hWA := hB (f1_weilAction A θ u 3 hu) hW pol hη hRos hPos hDim
  exact papl_skelg34_theorem112_conditional A θ u hu hL pol hη hRos hGk hWA P hPull hC9

/-- The conclusion of `skelg34_theoremC`, under its own hypotheses, from `papl_skelg34_theoremC`. -/
example : type_of% @HodgeLean.Papers.skelg34_theoremC := by
  intro A _ _ _ _ _ L _ _ Y _ _ _ _ _ r hB θ u hu hL pol hη hRos hGk hPos hDim P hPull hC9 _h11 p
  exact papl_skelg34_theoremC A hB θ u hu hL pol hη hRos hGk hPos hDim P hPull hC9 p

/--
info: 'HodgeLean.Papers.papl_skelg34_theoremC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_skelg34_theoremC

end Eisenstein


section General

variable {L : Type*} [Field L] [NumberField L] [IsCMField L]
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] {r : ℕ}

/-- **TT v0.15 Theorem 8.2, without `h11`.** As `skeltt_theorem82_conditional`, with
Lefschetz (1,1) on the power from `chowG_lefschetzOneOne_abelian`.
Source: TT v0.15, Theorem 8.2 (`thm:powers`) and proof; Fulton, *Intersection Theory*, 2nd ed.,
Chapter 8 and Corollary 19.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_skeltt_theorem82_conditional (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papl_pw_thm_4_2_hc_general A θ u hd hu pol hη hRos hGk hWA P hPull hC9

/-- The conclusion of `skeltt_theorem82_conditional`, under its own hypotheses, from `papl_skeltt_theorem82_conditional`. -/
example : type_of% @HodgeLean.Papers.skeltt_theorem82_conditional := by
  intro A _ _ _ _ _ L _ _ _ Y _ _ _ _ _ r θ u d hd hu pol hη hRos hGk hWA P hPull hC9 _h11 p
  exact papl_skeltt_theorem82_conditional A θ u hd hu pol hη hRos hGk hWA P hPull hC9 p

/--
info: 'HodgeLean.Papers.papl_skeltt_theorem82_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_skeltt_theorem82_conditional

/-- **TT's G32 cell conclusion with Theorem 8.2, without `h11`.** As `skeltt_g32_powers`: TT's
cell theorem is a statement-only premise.
Source: TT v0.15, Corollary 10.1 (`cor:g32`), powers clause, and Theorem 8.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_skeltt_g32_powers (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p := by
  have hWA := hCell hM
  exact papl_skeltt_theorem82_conditional A θ u (by norm_num) hu pol hη hRos hGk
    hWA P hPull hC9

/-- The conclusion of `skeltt_g32_powers`, under its own hypotheses, from `papl_skeltt_g32_powers`. -/
example : type_of% @HodgeLean.Papers.skeltt_g32_powers := by
  intro A _ _ _ _ _ L _ _ _ Y _ _ _ _ _ r θ u hu pol hη hRos hGk hM hCell P hPull hC9 _h11 p
  exact papl_skeltt_g32_powers A θ u hu pol hη hRos hGk hM hCell P hPull hC9 p

/--
info: 'HodgeLean.Papers.papl_skeltt_g32_powers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_skeltt_g32_powers

end General
end HodgeLean.Papers
