import HodgeLean.Papers.PapersWeilCupEisenstein
import HodgeLean.Papers.PapersWeilCupGeneral
import HodgeLean.Adapters.PWTheorem42NoPull

/-! # PW Theorem 4.2 on `A^r` with cup-closure restricted to the PW algebra

Claimed: each `papw_` theorem is the corresponding `papl_` theorem with
`hC9 : CycleClassMultiplicative (cupProductOf Y)` replaced by the narrower
`papw_PWCupClosed`, cup-closure of algebraic classes inside the PW algebra
`f1_pulledWeilCupSpan … (algebraicCycleClassSpan Y 1)`. The conclusion is unchanged.

Not claimed: `hC9` itself; `papw_PWCupClosed` itself, which stays a classical input; any of `hGk`,
`hWA` or `hPull`.
HC no distance; AV milestone no distance.
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

/-- As `papl_pw_thm_4_2_hc_noPull`, with `hC9` replaced by `papw_PWCupClosed`
(cup-closure inside the PW algebra).
Source: PW v0.3, Theorem 4.2, second sentence; `ccm6_hPull` (`CycleClassPullbackSpan.lean`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papw_pw_thm_4_2_hc_noPull (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9w : papw_PWCupClosed A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_pw_thm_4_2_hc A θ u hu hL pol hη hRos hGk hWA P (ccm6_hPull P θ) hC9w

/-- The conclusion of `pw_thm_4_2_hc_noPull`, under its own hypotheses, from `papw_pw_thm_4_2_hc_noPull`. -/
example : type_of% @HodgeLean.Adapters.pw_thm_4_2_hc_noPull := by
  intro A _ _ _ _ _ L _ _ Y _ _ _ _ _ r θ u hu hL pol hη hRos hGk hWA P hC9w _h11 p
  exact papw_pw_thm_4_2_hc_noPull A θ u hu hL pol hη hRos hGk hWA P
    (papw_PWCupClosed_of_hC9 A θ u 3 hu _ P hC9w) p

/--
info: 'HodgeLean.Papers.papw_pw_thm_4_2_hc_noPull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papw_pw_thm_4_2_hc_noPull

/-- As `papl_spec_g3link_hc`, with `hC9` replaced by `papw_PWCupClosed`
(cup-closure inside the PW algebra).
Source: PW v0.3, Theorem 4.2 (the powers `A^r`); Fulton, *Intersection
Theory*, 2nd ed., Ch. 8 and Corollary 19.2 (through `hPull` and `CycleClassMultiplicative`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papw_spec_g3link_hc (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9w : papw_PWCupClosed A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r)) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p := by
  exact papw_pw_thm_4_2_hc A θ u hu hL pol hη hRos hGk hWA (g3_powerData A r) hPull hC9w

/-- The conclusion of `spec_g3link_hc`, under its own hypotheses, from `papw_spec_g3link_hc`. -/
example : type_of% @HodgeLean.Adapters.spec_g3link_hc := by
  intro A _ _ _ _ _ L _ _ θ u hu hL pol hη hRos hGk hWA r hPull hC9w _h11 p
  exact papw_spec_g3link_hc A θ u hu hL pol hη hRos hGk hWA r hPull
    (papw_PWCupClosed_of_hC9 A θ u 3 hu _ (g3_powerData A r) hC9w) p

/--
info: 'HodgeLean.Papers.papw_spec_g3link_hc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papw_spec_g3link_hc

/-- As `papl_spec_g3link_hc_noPull`, with `hC9` replaced by `papw_PWCupClosed`
(cup-closure inside the PW algebra).
Source: PW v0.3, Theorem 4.2 (the powers `A^r`); `ccm6_hPull` (`CycleClassPullbackSpan.lean`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papw_spec_g3link_hc_noPull (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9w : papw_PWCupClosed A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r)) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p :=
  papw_spec_g3link_hc A θ u hu hL pol hη hRos hGk hWA r (ccm6_hPull (g3_powerData A r) θ) hC9w

/-- The conclusion of `spec_g3link_hc_noPull`, under its own hypotheses, from `papw_spec_g3link_hc_noPull`. -/
example : type_of% @HodgeLean.Adapters.spec_g3link_hc_noPull := by
  intro A _ _ _ _ _ L _ _ θ u hu hL pol hη hRos hGk hWA r hC9w _h11 p
  exact papw_spec_g3link_hc_noPull A θ u hu hL pol hη hRos hGk hWA r
    (papw_PWCupClosed_of_hC9 A θ u 3 hu _ (g3_powerData A r) hC9w) p

/--
info: 'HodgeLean.Papers.papw_spec_g3link_hc_noPull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papw_spec_g3link_hc_noPull

end Eisenstein


section General

variable {L : Type*} [Field L] [NumberField L] [IsCMField L]
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] {r : ℕ}

/-- As `papl_pw_thm_4_2_hc_general_noPull`, with `hC9` replaced by `papw_PWCupClosed`
(cup-closure inside the PW algebra).
Source: PW v0.3, Theorem 4.2, second sentence; `ccm6_hPull` (`CycleClassPullbackSpan.lean`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papw_pw_thm_4_2_hc_general_noPull (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (hC9w : papw_PWCupClosed A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk) P) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papw_pw_thm_4_2_hc_general A θ u hd hu pol hη hRos hGk hWA P (ccm6_hPull P θ) hC9w

/-- The conclusion of `pw_thm_4_2_hc_general_noPull`, under its own hypotheses, from `papw_pw_thm_4_2_hc_general_noPull`. -/
example : type_of% @HodgeLean.Adapters.pw_thm_4_2_hc_general_noPull := by
  intro A _ _ _ _ _ L _ _ _ Y _ _ _ _ _ r θ u d hd hu pol hη hRos hGk hWA P hC9w _h11 p
  exact papw_pw_thm_4_2_hc_general_noPull A θ u hd hu pol hη hRos hGk hWA P
    (papw_PWCupClosed_of_hC9 A θ u d hu _ P hC9w) p

/--
info: 'HodgeLean.Papers.papw_pw_thm_4_2_hc_general_noPull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papw_pw_thm_4_2_hc_general_noPull

/-- As `papl_spec_g3link2_hc`, with `hC9` replaced by `papw_PWCupClosed`
(cup-closure inside the PW algebra).
Source: PW v0.3, Theorem 4.2 (the powers `A^r`); Fulton, *Intersection
Theory*, 2nd ed., Ch. 8 and Corollary 19.2 (through `hPull` and `CycleClassMultiplicative`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papw_spec_g3link2_hc (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (hC9w : papw_PWCupClosed A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r)) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p :=
  papw_pw_thm_4_2_hc_general A θ u hd hu pol hη hRos hGk hWA (g3_powerData A r) hPull hC9w

/-- The conclusion of `spec_g3link2_hc`, under its own hypotheses, from `papw_spec_g3link2_hc`. -/
example : type_of% @HodgeLean.Adapters.spec_g3link2_hc := by
  intro A _ _ _ _ _ L _ _ _ θ u d hd hu pol hη hRos hGk hWA r hPull hC9w _h11 p
  exact papw_spec_g3link2_hc A θ u hd hu pol hη hRos hGk hWA r hPull
    (papw_PWCupClosed_of_hC9 A θ u d hu _ (g3_powerData A r) hC9w) p

/--
info: 'HodgeLean.Papers.papw_spec_g3link2_hc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papw_spec_g3link2_hc

/-- As `papl_spec_g3link2_hc_noPull`, with `hC9` replaced by `papw_PWCupClosed`
(cup-closure inside the PW algebra).
Source: PW v0.3, Theorem 4.2 (the powers `A^r`); `ccm6_hPull` (`CycleClassPullbackSpan.lean`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papw_spec_g3link2_hc_noPull (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (hC9w : papw_PWCupClosed A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r)) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p :=
  papw_spec_g3link2_hc A θ u hd hu pol hη hRos hGk hWA r (ccm6_hPull (g3_powerData A r) θ) hC9w

/-- The conclusion of `spec_g3link2_hc_noPull`, under its own hypotheses, from `papw_spec_g3link2_hc_noPull`. -/
example : type_of% @HodgeLean.Adapters.spec_g3link2_hc_noPull := by
  intro A _ _ _ _ _ L _ _ _ θ u d hd hu pol hη hRos hGk hWA r hC9w _h11 p
  exact papw_spec_g3link2_hc_noPull A θ u hd hu pol hη hRos hGk hWA r
    (papw_PWCupClosed_of_hC9 A θ u d hu _ (g3_powerData A r) hC9w) p

/--
info: 'HodgeLean.Papers.papw_spec_g3link2_hc_noPull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papw_spec_g3link2_hc_noPull

end General
end HodgeLean.Papers
