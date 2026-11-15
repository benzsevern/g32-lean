import HodgeLean.Papers.PapersLefschetzEisenstein
import HodgeLean.Papers.PapersLefschetzGeneral
import HodgeLean.Adapters.PWTheorem42NoPull

/-! # PW Theorem 4.2 on `A^r` and with `ccm6_hPull`, Lefschetz (1,1) supplied

The `noPull` compositions (`PWTheorem42NoPull.lean`) and the `A^r` statements
(`spec_g3link_hc`, `spec_g3link2_hc`) without `h11`. Overview in `PapersLefschetz.lean`.

Not claimed: the universal `LefschetzOneOneHyp`; any of `hGk`, `hWA`, `hPull` or `hC9`.
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

/-- The HC conclusion of `papl_pw_thm_4_2_hc` with the powers pullback premise supplied by
`ccm6_hPull`, as `pw_thm_4_2_hc_noPull`.
Source: PW v0.3, Theorem 4.2, second sentence; `ccm6_hPull` (`CycleClassPullbackSpan.lean`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_pw_thm_4_2_hc_noPull (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papl_pw_thm_4_2_hc A θ u hu hL pol hη hRos hGk hWA P (ccm6_hPull P θ) hC9

/-- The conclusion of `pw_thm_4_2_hc_noPull`, under its own hypotheses, from `papl_pw_thm_4_2_hc_noPull`. -/
example : type_of% @HodgeLean.Adapters.pw_thm_4_2_hc_noPull := by
  intro A _ _ _ _ _ L _ _ Y _ _ _ _ _ r θ u hu hL pol hη hRos hGk hWA P hC9 _h11 p
  exact papl_pw_thm_4_2_hc_noPull A θ u hu hL pol hη hRos hGk hWA P hC9 p

/--
info: 'HodgeLean.Papers.papl_pw_thm_4_2_hc_noPull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_pw_thm_4_2_hc_noPull

/-- **PW v0.3, Theorem 4.2, second sentence, at `L = k = ℚ(√-3)`, on `A^r`, without `h11`.** As
`spec_g3link_hc`, with Lefschetz (1,1) for `g3_power A r` from `chowG_lefschetzOneOne_abelian`.
Source: PW v0.3, Theorem 4.2 (the powers `A^r`); Fulton, *Intersection
Theory*, 2nd ed., Ch. 8 and Corollary 19.2 (through `hPull` and `CycleClassMultiplicative`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_spec_g3link_hc (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9 : CycleClassMultiplicative (cupProductOf (g3_power A r))) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p := by
  exact papl_pw_thm_4_2_hc A θ u hu hL pol hη hRos hGk hWA (g3_powerData A r) hPull hC9

/-- The conclusion of `spec_g3link_hc`, under its own hypotheses, from `papl_spec_g3link_hc`. -/
example : type_of% @HodgeLean.Adapters.spec_g3link_hc := by
  intro A _ _ _ _ _ L _ _ θ u hu hL pol hη hRos hGk hWA r hPull hC9 _h11 p
  exact papl_spec_g3link_hc A θ u hu hL pol hη hRos hGk hWA r hPull hC9 p

/--
info: 'HodgeLean.Papers.papl_spec_g3link_hc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_spec_g3link_hc

/-- The HC conclusion of `papl_spec_g3link_hc` with the powers pullback premise supplied by
`ccm6_hPull`, as `spec_g3link_hc_noPull`.
Source: PW v0.3, Theorem 4.2 (the powers `A^r`); `ccm6_hPull` (`CycleClassPullbackSpan.lean`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_spec_g3link_hc_noPull (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9 : CycleClassMultiplicative (cupProductOf (g3_power A r))) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p :=
  papl_spec_g3link_hc A θ u hu hL pol hη hRos hGk hWA r (ccm6_hPull (g3_powerData A r) θ) hC9

/-- The conclusion of `spec_g3link_hc_noPull`, under its own hypotheses, from `papl_spec_g3link_hc_noPull`. -/
example : type_of% @HodgeLean.Adapters.spec_g3link_hc_noPull := by
  intro A _ _ _ _ _ L _ _ θ u hu hL pol hη hRos hGk hWA r hC9 _h11 p
  exact papl_spec_g3link_hc_noPull A θ u hu hL pol hη hRos hGk hWA r hC9 p

/--
info: 'HodgeLean.Papers.papl_spec_g3link_hc_noPull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_spec_g3link_hc_noPull

end Eisenstein


section General

variable {L : Type*} [Field L] [NumberField L] [IsCMField L]
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] {r : ℕ}

/-- The HC conclusion of `papl_pw_thm_4_2_hc_general` with the powers pullback premise supplied
by `ccm6_hPull`, as `pw_thm_4_2_hc_general_noPull`.
Source: PW v0.3, Theorem 4.2, second sentence; `ccm6_hPull` (`CycleClassPullbackSpan.lean`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_pw_thm_4_2_hc_general_noPull (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  papl_pw_thm_4_2_hc_general A θ u hd hu pol hη hRos hGk hWA P (ccm6_hPull P θ) hC9

/-- The conclusion of `pw_thm_4_2_hc_general_noPull`, under its own hypotheses, from `papl_pw_thm_4_2_hc_general_noPull`. -/
example : type_of% @HodgeLean.Adapters.pw_thm_4_2_hc_general_noPull := by
  intro A _ _ _ _ _ L _ _ _ Y _ _ _ _ _ r θ u d hd hu pol hη hRos hGk hWA P hC9 _h11 p
  exact papl_pw_thm_4_2_hc_general_noPull A θ u hd hu pol hη hRos hGk hWA P hC9 p

/--
info: 'HodgeLean.Papers.papl_pw_thm_4_2_hc_general_noPull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_pw_thm_4_2_hc_general_noPull

/-- **PW v0.3, Theorem 4.2, second sentence, for a CM field `L`, on `A^r`, without `h11`.** As
`spec_g3link2_hc`, with Lefschetz (1,1) for `g3_power A r` from `chowG_lefschetzOneOne_abelian`.
Source: PW v0.3, Theorem 4.2 (the powers `A^r`); Fulton, *Intersection
Theory*, 2nd ed., Ch. 8 and Corollary 19.2 (through `hPull` and `CycleClassMultiplicative`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_spec_g3link2_hc (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (hC9 : CycleClassMultiplicative (cupProductOf (g3_power A r))) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p :=
  papl_pw_thm_4_2_hc_general A θ u hd hu pol hη hRos hGk hWA (g3_powerData A r) hPull hC9

/-- The conclusion of `spec_g3link2_hc`, under its own hypotheses, from `papl_spec_g3link2_hc`. -/
example : type_of% @HodgeLean.Adapters.spec_g3link2_hc := by
  intro A _ _ _ _ _ L _ _ _ θ u d hd hu pol hη hRos hGk hWA r hPull hC9 _h11 p
  exact papl_spec_g3link2_hc A θ u hd hu pol hη hRos hGk hWA r hPull hC9 p

/--
info: 'HodgeLean.Papers.papl_spec_g3link2_hc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_spec_g3link2_hc

/-- The HC conclusion of `papl_spec_g3link2_hc` with the powers pullback premise supplied by
`ccm6_hPull`, as `spec_g3link2_hc_noPull`.
Source: PW v0.3, Theorem 4.2 (the powers `A^r`); `ccm6_hPull` (`CycleClassPullbackSpan.lean`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_spec_g3link2_hc_noPull (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (hC9 : CycleClassMultiplicative (cupProductOf (g3_power A r))) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p :=
  papl_spec_g3link2_hc A θ u hd hu pol hη hRos hGk hWA r (ccm6_hPull (g3_powerData A r) θ) hC9

/-- The conclusion of `spec_g3link2_hc_noPull`, under its own hypotheses, from `papl_spec_g3link2_hc_noPull`. -/
example : type_of% @HodgeLean.Adapters.spec_g3link2_hc_noPull := by
  intro A _ _ _ _ _ L _ _ _ θ u d hd hu pol hη hRos hGk hWA r hC9 _h11 p
  exact papl_spec_g3link2_hc_noPull A θ u hd hu pol hη hRos hGk hWA r hC9 p

/--
info: 'HodgeLean.Papers.papl_spec_g3link2_hc_noPull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_spec_g3link2_hc_noPull

end General
end HodgeLean.Papers
