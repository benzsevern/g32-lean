import HodgeLean.Adapters.KleimanProduct
import HodgeLean.Papers.G32NarrowWiring
import HodgeLean.Papers.G32Wiring
import HodgeLean.Papers.G34Wiring
import HodgeLean.Papers.PapersWeilCup

/-! # Paper theorems with the PW cup-closure input supplied

Each `cupw_` theorem is the corresponding theorem that takes
`hC9w : papw_PWCupClosed …`, with that binder removed and supplied by
`hc9k_papw_PWCupClosed` (cycle-class multiplicativity on smooth projective complex integral
commutative group varieties, Kleiman stage 4). Every other named premise stays a binder.
The inventory is in `docs/specs/CupWiring.md`.
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

/-- As `papw_pw_thm_4_2_hc`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
Source: PW v0.3, Theorem 4.2, second sentence, and its proof, paragraph "Conclusion"; Fulton, *Intersection
Theory*, 2nd ed., Ch. 8 and Corollary 19.2 (through `hPull` and `CycleClassMultiplicative`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215).
-/
theorem cupw_papw_pw_thm_4_2_hc (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
        algebraicCycleClassSpan Y q) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_pw_thm_4_2_hc A θ u hu hL pol hη hRos hGk hWA P hPull
    (hc9k_papw_PWCupClosed A θ u 3 hu _ _)

/--
info: 'HodgeLean.Papers.cupw_papw_pw_thm_4_2_hc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_papw_pw_thm_4_2_hc

/-- As `papw_skelg32_theorem92_conditional`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
Source: G32 v0.16, Theorem 9.2 (`thm:powers`); Fulton, *Intersection Theory*, 2nd ed., Chapter 8 and Corollary 19.2;
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215).
-/
theorem cupw_papw_skelg32_theorem92_conditional (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
        algebraicCycleClassSpan Y q) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_skelg32_theorem92_conditional A θ u hu hL pol hη hRos hGk hWA P hPull
    (hc9k_papw_PWCupClosed A θ u 3 hu _ _)

/--
info: 'HodgeLean.Papers.cupw_papw_skelg32_theorem92_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_papw_skelg32_theorem92_conditional

/-- As `papw_skelg32_theoremB`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
Source: G32 v0.16, Theorem B, its proof, and Theorem 9.2; Fulton, *Intersection Theory*,
2nd ed., Chapter 8 and Corollary 19.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215).
-/
theorem cupw_papw_skelg32_theoremB (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
        algebraicCycleClassSpan Y q) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_skelg32_theoremB A θ u hu hL pol hη hRos hGk hM hA P hPull
    (hc9k_papw_PWCupClosed A θ u 3 hu _ _)

/--
info: 'HodgeLean.Papers.cupw_papw_skelg32_theoremB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_papw_skelg32_theoremB

/-- As `papw_skelg34_theorem112_conditional`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem 11.2 (`thm:powers`) and Theorem C;
Fulton, *Intersection Theory*, 2nd ed., Chapter 8 and Corollary 19.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215).
-/
theorem cupw_papw_skelg34_theorem112_conditional (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
        algebraicCycleClassSpan Y q) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_skelg34_theorem112_conditional A θ u hu hL pol hη hRos hGk hWA P hPull
    (hc9k_papw_PWCupClosed A θ u 3 hu _ _)

/--
info: 'HodgeLean.Papers.cupw_papw_skelg34_theorem112_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_papw_skelg34_theorem112_conditional

/-- As `papw_skelg34_theoremC`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem C and its proof in §11;
Fulton, *Intersection Theory*, 2nd ed., Chapter 8 and Corollary 19.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215).
-/
theorem cupw_papw_skelg34_theoremC (hB : G34TheoremBStatement A) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
        algebraicCycleClassSpan Y q) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_skelg34_theoremC A hB θ u hu hL pol hη hRos hGk hPos hDim P hPull
    (hc9k_papw_PWCupClosed A θ u 3 hu _ _)

/--
info: 'HodgeLean.Papers.cupw_papw_skelg34_theoremC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_papw_skelg34_theoremC

/-- As `papw_pw_thm_4_2_hc_noPull`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
Source: PW v0.3, Theorem 4.2, second sentence; `ccm6_hPull` (`CycleClassPullbackSpan.lean`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215).
-/
theorem cupw_papw_pw_thm_4_2_hc_noPull (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (P : AbelianPowerData A Y r) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_pw_thm_4_2_hc_noPull A θ u hu hL pol hη hRos hGk hWA P
    (hc9k_papw_PWCupClosed A θ u 3 hu _ _)

/--
info: 'HodgeLean.Papers.cupw_papw_pw_thm_4_2_hc_noPull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_papw_pw_thm_4_2_hc_noPull

/-- As `papw_spec_g3link_hc`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
Source: PW v0.3, Theorem 4.2 (the powers `A^r`); Fulton, *Intersection
Theory*, 2nd ed., Ch. 8 and Corollary 19.2 (through `hPull` and `CycleClassMultiplicative`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215).
-/
theorem cupw_papw_spec_g3link_hc (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
        algebraicCycleClassSpan (g3_power A r) q) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p :=
  papw_spec_g3link_hc A θ u hu hL pol hη hRos hGk hWA r hPull
    (hc9k_papw_PWCupClosed A θ u 3 hu _ _)

/--
info: 'HodgeLean.Papers.cupw_papw_spec_g3link_hc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_papw_spec_g3link_hc

/-- As `papw_spec_g3link_hc_noPull`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
Source: PW v0.3, Theorem 4.2 (the powers `A^r`); `ccm6_hPull` (`CycleClassPullbackSpan.lean`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215).
-/
theorem cupw_papw_spec_g3link_hc_noPull (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (r : ℕ) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p :=
  papw_spec_g3link_hc_noPull A θ u hu hL pol hη hRos hGk hWA r
    (hc9k_papw_PWCupClosed A θ u 3 hu _ _)

/--
info: 'HodgeLean.Papers.cupw_papw_spec_g3link_hc_noPull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_papw_spec_g3link_hc_noPull

/-- As `g32w_papw_skelg32_theoremB`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
-/
theorem cupw_g32w_papw_skelg32_theoremB (B : g32a_premises) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (P : AbelianPowerData A Y r)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  g32w_papw_skelg32_theoremB A B θ u hu hL pol hη hRos hGk hM P hPull
    (hc9k_papw_PWCupClosed A θ u 3 hu _ _)

/--
info: 'HodgeLean.Papers.cupw_g32w_papw_skelg32_theoremB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_g32w_papw_skelg32_theoremB

/-- As `g32nw_papw_skelg32_theoremB`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
-/
theorem cupw_g32nw_papw_skelg32_theoremB (B : g32n_premises) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (P : AbelianPowerData A Y r)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  g32nw_papw_skelg32_theoremB A B θ u hu hL pol hη hRos hGk hM P hPull
    (hc9k_papw_PWCupClosed A θ u 3 hu _ _)

/--
info: 'HodgeLean.Papers.cupw_g32nw_papw_skelg32_theoremB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_g32nw_papw_skelg32_theoremB

end Eisenstein

section General

variable {L : Type*} [Field L] [NumberField L] [IsCMField L]
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] {r : ℕ}

/-- As `papw_pw_thm_4_2_hc_general`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
Source: PW v0.3, Theorem 4.2, second sentence, and its proof, paragraph "Conclusion"; Fulton, *Intersection
Theory*, 2nd ed., Ch. 8 and Corollary 19.2 (through `hPull` and `CycleClassMultiplicative`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215).
-/
theorem cupw_papw_pw_thm_4_2_hc_general (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
        algebraicCycleClassSpan Y q) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_pw_thm_4_2_hc_general A θ u hd hu pol hη hRos hGk hWA P hPull
    (hc9k_papw_PWCupClosed A θ u _ hu _ _)

/--
info: 'HodgeLean.Papers.cupw_papw_pw_thm_4_2_hc_general' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_papw_pw_thm_4_2_hc_general

/-- As `papw_skeltt_theorem82_conditional`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
Source: TT v0.15, Theorem 8.2 (`thm:powers`) and proof; Fulton, *Intersection Theory*, 2nd ed.,
Chapter 8 and Corollary 19.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215).
-/
theorem cupw_papw_skeltt_theorem82_conditional (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
        algebraicCycleClassSpan Y q) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_skeltt_theorem82_conditional A θ u hd hu pol hη hRos hGk hWA P hPull
    (hc9k_papw_PWCupClosed A θ u _ hu _ _)

/--
info: 'HodgeLean.Papers.cupw_papw_skeltt_theorem82_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_papw_skeltt_theorem82_conditional

/-- As `papw_skeltt_g32_powers`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
Source: TT v0.15, Corollary 10.1 (`cor:g32`), powers clause, and Theorem 8.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215).
-/
theorem cupw_papw_skeltt_g32_powers (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
        algebraicCycleClassSpan Y q) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_skeltt_g32_powers A θ u hu pol hη hRos hGk hM hCell P hPull
    (hc9k_papw_PWCupClosed A θ u 3 hu _ _)

/--
info: 'HodgeLean.Papers.cupw_papw_skeltt_g32_powers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_papw_skeltt_g32_powers

/-- As `papw_pw_thm_4_2_hc_general_noPull`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
Source: PW v0.3, Theorem 4.2, second sentence; `ccm6_hPull` (`CycleClassPullbackSpan.lean`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215).
-/
theorem cupw_papw_pw_thm_4_2_hc_general_noPull (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (P : AbelianPowerData A Y r) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_pw_thm_4_2_hc_general_noPull A θ u hd hu pol hη hRos hGk hWA P
    (hc9k_papw_PWCupClosed A θ u _ hu _ _)

/--
info: 'HodgeLean.Papers.cupw_papw_pw_thm_4_2_hc_general_noPull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_papw_pw_thm_4_2_hc_general_noPull

/-- As `papw_spec_g3link2_hc`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
Source: PW v0.3, Theorem 4.2 (the powers `A^r`); Fulton, *Intersection
Theory*, 2nd ed., Ch. 8 and Corollary 19.2 (through `hPull` and `CycleClassMultiplicative`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215).
-/
theorem cupw_papw_spec_g3link2_hc (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
        algebraicCycleClassSpan (g3_power A r) q) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p :=
  papw_spec_g3link2_hc A θ u hd hu pol hη hRos hGk hWA r hPull
    (hc9k_papw_PWCupClosed A θ u _ hu _ _)

/--
info: 'HodgeLean.Papers.cupw_papw_spec_g3link2_hc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_papw_spec_g3link2_hc

/-- As `papw_spec_g3link2_hc_noPull`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
Source: PW v0.3, Theorem 4.2 (the powers `A^r`); `ccm6_hPull` (`CycleClassPullbackSpan.lean`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215).
-/
theorem cupw_papw_spec_g3link2_hc_noPull (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (r : ℕ) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p :=
  papw_spec_g3link2_hc_noPull A θ u hd hu pol hη hRos hGk hWA r
    (hc9k_papw_PWCupClosed A θ u _ hu _ _)

/--
info: 'HodgeLean.Papers.cupw_papw_spec_g3link2_hc_noPull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_papw_spec_g3link2_hc_noPull

/-- As `g32w_papw_skeltt_g32_powers`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
-/
theorem cupw_g32w_papw_skeltt_g32_powers (B : g32a_premises) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (P : AbelianPowerData A Y r)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  g32w_papw_skeltt_g32_powers A B θ u hu pol hη hRos hGk hM P hPull
    (hc9k_papw_PWCupClosed A θ u 3 hu _ _)

/--
info: 'HodgeLean.Papers.cupw_g32w_papw_skeltt_g32_powers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_g32w_papw_skeltt_g32_powers

/-- As `g32nw_papw_skeltt_g32_powers`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
-/
theorem cupw_g32nw_papw_skeltt_g32_powers (B : g32n_premises) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (P : AbelianPowerData A Y r)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  g32nw_papw_skeltt_g32_powers A B θ u hu pol hη hRos hGk hM P hPull
    (hc9k_papw_PWCupClosed A θ u 3 hu _ _)

/--
info: 'HodgeLean.Papers.cupw_g32nw_papw_skeltt_g32_powers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_g32nw_papw_skeltt_g32_powers

end General

section G34

variable (hComp : ∀
  (W : letI := (finiteBetti_abelian A).finite 1
    HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
  (hW : letI := (finiteBetti_abelian A).finite 1; W.IsWeilType)
  (pol : HQ A 2)
  (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
  (_hRos : letI := (finiteBetti_abelian A).finite 1;
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J)
  (_hPos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
  (_hDim : TopologicalSpace.dim A.left = 6),
  (∀ (X : Over (Spec ↧ℂ)),
    [GrpObj X] → [IsCommMonObj X] → [IsIntegral X.left] →
    [Smooth X.hom] → [IsProjective X.hom] → G34TheoremAStatement X) →
  letI := (finiteBetti_abelian A).finite 1
  WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hW)

variable {L : Type*} [Field L] [Algebra ℚ L]
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] {r : ℕ}

include hComp in
/-- As `g34w_papw_skelg34_theoremC`, with the cup-closure input `hC9w` supplied
by `hc9k_papw_PWCupClosed`.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem C and its proof in §11;
Fulton, *Intersection Theory*, 2nd ed., Chapter 8 and Corollary 19.2; Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215).
-/
theorem cupw_g34w_papw_skelg34_theoremC (B : g34a_premises) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
        algebraicCycleClassSpan Y q) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  g34w_papw_skelg34_theoremC A hComp B θ u hu hL pol hη hRos hGk hPos hDim P hPull
    (hc9k_papw_PWCupClosed A θ u 3 hu _ _)

/--
info: 'HodgeLean.Papers.cupw_g34w_papw_skelg34_theoremC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cupw_g34w_papw_skelg34_theoremC

end G34

end HodgeLean.Papers
