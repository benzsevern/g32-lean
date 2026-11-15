import HodgeLean.Adapters.PWTheorem42
import HodgeLean.Foundations.GeometricIntegralityC
import HodgeLean.Foundations.SegreProjective

/-! # The Powers flagship, G3 link part 2: proof obligations

One `_aux` theorem per statement of `AbelianPowerLinkGeneral.lean`. Each is F2's
statement (`PWTheorem42.lean`) at `Y = g3_power A r`, `P = g3_powerData A r`; the scope instances
of `A^r` are found by instance search: `g3_grpObj`, `spec_g3_isCommMonObj_power`,
`spec_g3b_isIntegral_power`, `spec_g3_smooth_power`, `spec_g3c_isProjective_power`. Each proof
is the F2 theorem applied at `P := g3_powerData A r`. HC no distance; AV milestone no distance.
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

theorem spec_g3link2_generation_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
  pw_thm_4_2_generation_general A θ u hd hu pol hη hRos hGk (g3_powerData A r)

theorem spec_g3link2_generation_cup_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
  pw_thm_4_2_generation_cup_general A θ u hd hu pol hη hRos hGk (g3_powerData A r)

theorem spec_g3link2_hdg_le_pulledWeilCupSpan_divisor_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
  f2_hdg_le_pulledWeilCupSpan_divisor A θ u hd hu pol hη hRos hGk h11 (g3_powerData A r)

theorem spec_g3link2_hc_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
  pw_thm_4_2_hc_general A θ u hd hu pol hη hRos hGk hWA (g3_powerData A r) hPull hC9 h11

end HodgeLean.Adapters
