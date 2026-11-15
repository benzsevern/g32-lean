import HodgeLean.Papers.G32Assembly
import HodgeLean.Papers.PapersLefschetz
import HodgeLean.Papers.PapersWeilCup

/-! # G32 Theorem A wiring

The seven literature premises bundled by `g32a_premises` supply the Theorem A input used by
the G32 and TT powers theorems. The TT cell adapter only reconciles the placement of the
canonical finite-module instance; the memberwise statements are otherwise identical.
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

/-- G32 Theorem A supplies TT's G32 cell statement for the same action and polarization. -/
theorem g32w_ttCell_of_g32
    (W : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol → TTG32CellStatement A W pol := by
  intro hA hM
  exact hA hM

/--
info: 'HodgeLean.Papers.g32w_ttCell_of_g32' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms g32w_ttCell_of_g32

section Eisenstein

variable {L : Type*} [Field L] [Algebra ℚ L]
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
  [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ}

/-- G32 Theorem B from the seven named Theorem A premises. -/
theorem g32w_skelg32_theoremB (B : g32a_premises) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
        algebraicCycleClassSpan Y q)
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  skelg32_theoremB A θ u hu hL pol hη hRos hGk hM
    (g32a_theoremA_of_premises B A _ pol) P hPull hC9 h11

/-- The former statement follows when its explicit Theorem A input is retained. -/
example : type_of% @HodgeLean.Papers.skelg32_theoremB := by
  exact skelg32_theoremB

/--
info: 'HodgeLean.Papers.g32w_skelg32_theoremB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms g32w_skelg32_theoremB

/-- The Lefschetz-specialized G32 Theorem B from the seven named premises. -/
theorem g32w_papl_skelg32_theoremB (B : g32a_premises) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
        algebraicCycleClassSpan Y q)
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papl_skelg32_theoremB A θ u hu hL pol hη hRos hGk hM
    (g32a_theoremA_of_premises B A _ pol) P hPull hC9

/-- The former specialized statement follows when its explicit Theorem A input is retained. -/
example : type_of% @HodgeLean.Papers.papl_skelg32_theoremB := by
  exact papl_skelg32_theoremB

/--
info: 'HodgeLean.Papers.g32w_papl_skelg32_theoremB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms g32w_papl_skelg32_theoremB

/-- The narrow cup-input G32 Theorem B from the seven named premises. -/
theorem g32w_papw_skelg32_theoremB (B : g32a_premises) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
        algebraicCycleClassSpan Y q)
    (hC9w : papw_PWCupClosed A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_skelg32_theoremB A θ u hu hL pol hη hRos hGk hM
    (g32a_theoremA_of_premises B A _ pol) P hPull hC9w

/-- The former narrow-input statement follows when its explicit Theorem A input is retained. -/
example : type_of% @HodgeLean.Papers.papw_skelg32_theoremB := by
  exact papw_skelg32_theoremB

/--
info: 'HodgeLean.Papers.g32w_papw_skelg32_theoremB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms g32w_papw_skelg32_theoremB

end Eisenstein

section General

variable {L : Type*} [Field L] [NumberField L] [IsCMField L]
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
  [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ}

/-- TT's G32 powers conclusion from the seven named G32 premises. -/
theorem g32w_skeltt_g32_powers (B : g32a_premises) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
        algebraicCycleClassSpan Y q)
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  skeltt_g32_powers A θ u hu pol hη hRos hGk hM
    (g32w_ttCell_of_g32 A _ pol (g32a_theoremA_of_premises B A _ pol))
    P hPull hC9 h11

/-- The former TT statement follows when its explicit cell input is retained. -/
example : type_of% @HodgeLean.Papers.skeltt_g32_powers := by
  exact skeltt_g32_powers

/--
info: 'HodgeLean.Papers.g32w_skeltt_g32_powers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms g32w_skeltt_g32_powers

/-- The Lefschetz-specialized TT G32 powers conclusion from the seven named premises. -/
theorem g32w_papl_skeltt_g32_powers (B : g32a_premises) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
        algebraicCycleClassSpan Y q)
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papl_skeltt_g32_powers A θ u hu pol hη hRos hGk hM
    (g32w_ttCell_of_g32 A _ pol (g32a_theoremA_of_premises B A _ pol))
    P hPull hC9

/-- The former specialized TT statement follows when its explicit cell input is retained. -/
example : type_of% @HodgeLean.Papers.papl_skeltt_g32_powers := by
  exact papl_skeltt_g32_powers

/--
info: 'HodgeLean.Papers.g32w_papl_skeltt_g32_powers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms g32w_papl_skeltt_g32_powers

/-- The narrow cup-input TT G32 powers conclusion from the seven named premises. -/
theorem g32w_papw_skeltt_g32_powers (B : g32a_premises) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
        algebraicCycleClassSpan Y q)
    (hC9w : papw_PWCupClosed A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_skeltt_g32_powers A θ u hu pol hη hRos hGk hM
    (g32w_ttCell_of_g32 A _ pol (g32a_theoremA_of_premises B A _ pol))
    P hPull hC9w

/-- The former narrow-input TT statement follows when its explicit cell input is retained. -/
example : type_of% @HodgeLean.Papers.papw_skeltt_g32_powers := by
  exact papw_skeltt_g32_powers

/--
info: 'HodgeLean.Papers.g32w_papw_skeltt_g32_powers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms g32w_papw_skeltt_g32_powers

end General
end HodgeLean.Papers
