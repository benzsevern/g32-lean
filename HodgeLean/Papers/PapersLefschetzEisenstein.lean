import HodgeLean.Adapters.PWTheorem42Eisenstein
import HodgeLean.Foundations.ChowProjective

/-! # PW Theorem 4.2 at `L = ℚ(√-3)` with Lefschetz (1,1) supplied on the power

The divisor-class form and the HC statement of `PWTheorem42Eisenstein.lean` without `h11`:
the proof bodies of the `_aux` theorems, with `chowG_lefschetzOneOne_abelian Y` in place of
`h11.holds Y`. Overview in `PapersLefschetz.lean`.

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

/-- **The divisor-class form at `L = k = ℚ(√-3)`, without `h11`.** As
`f1_hdg_le_pulledWeilCupSpan_divisor`, with Lefschetz (1,1) for `Y` from
`chowG_lefschetzOneOne_abelian Y`.
Source: PW v0.3, Theorem 4.2, first sentence, and its proof, paragraph "Divisor classes" (the
Lefschetz (1,1) theorem); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_f1_hdg_le_pulledWeilCupSpan_divisor (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ f1_pulledWeilCupSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      P (algebraicCycleClassSpan Y 1) p := by
  intro p
  refine (pw_thm_4_2_generation_cup A θ u hu hL pol hη hRos hGk P p).le.trans ?_
  exact le_iInf₂ fun F hF => iInf₂_le F
    ⟨hF.unit_mem, le_trans (chowG_lefschetzOneOne_abelian Y) hF.divisor_le, hF.pullback_le,
      hF.cup_mem⟩

/-- The conclusion of `f1_hdg_le_pulledWeilCupSpan_divisor`, under its own hypotheses, from `papl_f1_hdg_le_pulledWeilCupSpan_divisor`. -/
example : type_of% @HodgeLean.Adapters.f1_hdg_le_pulledWeilCupSpan_divisor := by
  intros
  apply @papl_f1_hdg_le_pulledWeilCupSpan_divisor <;> assumption

/--
info: 'HodgeLean.Papers.papl_f1_hdg_le_pulledWeilCupSpan_divisor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_f1_hdg_le_pulledWeilCupSpan_divisor

/-- **PW v0.3, Theorem 4.2, second sentence, at `L = k = ℚ(√-3)`, without `h11`.** As
`pw_thm_4_2_hc`: under `hGk`, `hWA`, `hPull` and `hC9`, every Hodge class of `Y` is algebraic.
Source: PW v0.3, Theorem 4.2, second sentence, and its proof, paragraph "Conclusion"; Fulton, *Intersection
Theory*, 2nd ed., Ch. 8 and Corollary 19.2 (through `hPull` and `CycleClassMultiplicative`);
Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2 (through
`chowG_lefschetzOneOne_abelian`, handoff 215). -/
theorem papl_pw_thm_4_2_hc (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
  intro p
  refine (papl_f1_hdg_le_pulledWeilCupSpan_divisor A θ u hu hL pol hη hRos hGk P p).trans ?_
  refine iInf₂_le (fun q => algebraicCycleClassSpan Y q) ⟨unitClass_mem_algebraicCycleClassSpan,
    le_rfl, fun a => (Submodule.map_mono hWA).trans (hPull a _),
    fun h a b ha hb => hC9.mem h a b ha hb⟩

/-- The conclusion of `pw_thm_4_2_hc`, under its own hypotheses, from `papl_pw_thm_4_2_hc`. -/
example : type_of% @HodgeLean.Adapters.pw_thm_4_2_hc := by
  intro A _ _ _ _ _ L _ _ Y _ _ _ _ _ r θ u hu hL pol hη hRos hGk hWA P hPull hC9 _h11 p
  exact papl_pw_thm_4_2_hc A θ u hu hL pol hη hRos hGk hWA P hPull hC9 p

/--
info: 'HodgeLean.Papers.papl_pw_thm_4_2_hc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms papl_pw_thm_4_2_hc

end Eisenstein
end HodgeLean.Papers
