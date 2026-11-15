import HodgeLean.Papers.SkeletonG32Defs

/-! # G32 main-theorem skeleton: proof obligations -/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic
open HodgeLean.Adapters

namespace HodgeLean.Papers

theorem skelg32_order_seven_aux :
    (∀ k < 7, papers8_A.det.coeff k = 0) ∧
      papers8_A.det.coeff 7 =
        -4869337150302392927709794715527302500429442156335511356109310625 / 2 ^ 72 :=
  papers_g32_minor_order_seven

theorem skelg32_rank_constant_aux : papers8_M0.rank = 5 :=
  papers_g32_rank_constant

theorem skelg32_minor_ne_zero_aux : papers8_A.det ≠ 0 :=
  papers_g32_minor_ne_zero

theorem skelg32_rank_ratFunc_aux :
    (papers8_Mpoly.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).rank = 9 :=
  papers_g32_rank_ratFunc

theorem skelg32_powerSeries_order_aux
    (B : Matrix (Fin 9) (Fin 10) (PowerSeries ℚ))
    (hB : ∀ (i : Fin 9) (j : Fin 10) (k : ℕ), k ≤ 7 →
      PowerSeries.coeff k (B i j) = PowerSeries.coeff k (papers8_Mseries i j)) :
    PowerSeries.order (B.submatrix id Fin.succ).det = 7 :=
  papers_g32_powerSeries_order B hB

theorem skelg32_powerSeries_order_complex_aux
    (B : Matrix (Fin 9) (Fin 10) (PowerSeries ℂ))
    (hB : ∀ (i : Fin 9) (j : Fin 10) (k : ℕ), k ≤ 7 →
      PowerSeries.coeff k (B i j) =
        algebraMap ℚ ℂ (PowerSeries.coeff k (papers8_Mseries i j))) :
    PowerSeries.order (B.submatrix id Fin.succ).det = 7 :=
  papers_g32_powerSeries_order_complex B hB

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]
variable {L : Type*} [Field L] [Algebra ℚ L]
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
  [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ}

theorem skelg32_theorem92_conditional_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
  HodgeLean.Adapters.pw_thm_4_2_hc A θ u hu hL pol hη hRos hGk hWA P hPull hC9 h11

end HodgeLean.Papers
