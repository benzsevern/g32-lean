import HodgeLean.Adapters.AbelianPowerLink
import HodgeLean.Adapters.AbelianPowerLinkGeneral
import HodgeLean.Adapters.CycleClassPullbackSpan

/-! # PW Theorem 4.2 with the powers pullback premise supplied

Four compositions of the existing HC statements with `ccm6_hPull`.
These are implications from the remaining explicit inputs, including algebraicity
of Weil classes, cycle-class multiplicativity and Lefschetz (1,1).
HC no distance; AV milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic NumberField

namespace HodgeLean.Adapters

/-- The HC conclusion with the powers pullback premise supplied.
Source: `pw_thm_4_2_hc_general` (`PWTheorem42.lean`);
`ccm6_hPull` (`CycleClassPullbackSpan.lean`). -/
theorem pw_thm_4_2_hc_general_noPull (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom]
    {L : Type*} [Field L] [NumberField L] [IsCMField L]
    {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
    [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ}
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  pw_thm_4_2_hc_general A θ u hd hu pol hη hRos hGk hWA P (ccm6_hPull P θ) hC9 h11

#print axioms pw_thm_4_2_hc_general_noPull

/-- The HC conclusion with the powers pullback premise supplied.
Source: `pw_thm_4_2_hc` (`PWTheorem42Eisenstein.lean`);
`ccm6_hPull` (`CycleClassPullbackSpan.lean`). -/
theorem pw_thm_4_2_hc_noPull (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom]
    {L : Type*} [Field L] [Algebra ℚ L]
    {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
    [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ}
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  pw_thm_4_2_hc A θ u hu hL pol hη hRos hGk hWA P (ccm6_hPull P θ) hC9 h11

#print axioms pw_thm_4_2_hc_noPull

/-- The HC conclusion with the powers pullback premise supplied.
Source: `spec_g3link_hc` (`AbelianPowerLink.lean`);
`ccm6_hPull` (`CycleClassPullbackSpan.lean`). -/
theorem spec_g3link_hc_noPull (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom]
    {L : Type*} [Field L] [Algebra ℚ L]
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9 : CycleClassMultiplicative (cupProductOf (g3_power A r))) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p :=
  spec_g3link_hc A θ u hu hL pol hη hRos hGk hWA r (ccm6_hPull (g3_powerData A r) θ) hC9 h11

#print axioms spec_g3link_hc_noPull

/-- The HC conclusion with the powers pullback premise supplied.
Source: `spec_g3link2_hc` (`AbelianPowerLinkGeneral.lean`);
`ccm6_hPull` (`CycleClassPullbackSpan.lean`). -/
theorem spec_g3link2_hc_noPull (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom]
    {L : Type*} [Field L] [NumberField L] [IsCMField L]
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (hC9 : CycleClassMultiplicative (cupProductOf (g3_power A r))) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p :=
  spec_g3link2_hc A θ u hd hu pol hη hRos hGk hWA r (ccm6_hPull (g3_powerData A r) θ) hC9 h11

#print axioms spec_g3link2_hc_noPull

/-! Structural witnesses used by the original G3 examples. -/

example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom] (r : ℕ) :
    GrpObj (g3_power A r) := inferInstance

example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom] (r : ℕ) :
    IsCommMonObj (g3_power A r) := inferInstance

example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom] (r : ℕ) :
    IsIntegral (g3_power A r).left := inferInstance

example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom] (r : ℕ) :
    Smooth (g3_power A r).hom := inferInstance

example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
    [Smooth A.hom] [IsProjective A.hom] (r : ℕ) :
    IsProjective (g3_power A r).hom := inferInstance

end HodgeLean.Adapters
