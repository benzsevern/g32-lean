import HodgeLean.Papers.SkeletonG32Proofs

/-! # G32 v0.16 main-theorem skeleton (FROZEN SPEC)

Theorem A is an unasserted statement in the definitions module. Theorem B is a proved
implication from that statement, with the classical cycle inputs explicit. Theorem 9.2
provides the conditional powers connector. The finite certificate does not by itself identify a
period-map codifferential.

HC no distance; AV milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic
open HodgeLean.Adapters

namespace HodgeLean.Papers

/-- **G32 Proposition 5.9, exact certificate step.** The displayed omitted-column determinant
has no coefficient below degree seven and has the displayed nonzero degree-seven coefficient.
This is the finite certificate; identifying its matrix with a period-map codifferential is a
separate geometric step not currently expressible.
Source: G32 v0.16, Proposition 5.9 and Appendix C, "The rank certificate". -/
theorem skelg32_order_seven :
    (∀ k < 7, papers8_A.det.coeff k = 0) ∧
      papers8_A.det.coeff 7 =
        -4869337150302392927709794715527302500429442156335511356109310625 / 2 ^ 72 :=
  skelg32_order_seven_aux

example : papers8_A.det.coeff 0 = 0 := skelg32_order_seven.1 0 (by decide)

/-- G32 Proposition 5.9: the constant jet has rank five.
Source: G32 v0.16, Proposition 5.9 and Appendix C. -/
theorem skelg32_rank_constant : papers8_M0.rank = 5 :=
  skelg32_rank_constant_aux

/-- G32 Proposition 5.9: the omitted-column polynomial minor is nonzero.
Source: G32 v0.16, Proposition 5.9 and Appendix C. -/
theorem skelg32_minor_ne_zero : papers8_A.det ≠ 0 :=
  skelg32_minor_ne_zero_aux

/-- G32 Proposition 5.9: the exported matrix has rank nine over rational functions.
Source: G32 v0.16, Proposition 5.9 and Appendix C. -/
theorem skelg32_rank_ratFunc :
    (papers8_Mpoly.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).rank = 9 :=
  skelg32_rank_ratFunc_aux

/-- G32 Proposition 5.9: every rational matching jet has minor order seven.
Source: G32 v0.16, Proposition 5.9 and Appendix C. -/
theorem skelg32_powerSeries_order
    (B : Matrix (Fin 9) (Fin 10) (PowerSeries ℚ))
    (hB : ∀ (i : Fin 9) (j : Fin 10) (k : ℕ), k ≤ 7 →
      PowerSeries.coeff k (B i j) = PowerSeries.coeff k (papers8_Mseries i j)) :
    PowerSeries.order (B.submatrix id Fin.succ).det = 7 :=
  skelg32_powerSeries_order_aux B hB

/-- G32 Proposition 5.9: every complex matching jet has minor order seven.
Source: G32 v0.16, Proposition 5.9 and Appendix C. -/
theorem skelg32_powerSeries_order_complex
    (B : Matrix (Fin 9) (Fin 10) (PowerSeries ℂ))
    (hB : ∀ (i : Fin 9) (j : Fin 10) (k : ℕ), k ≤ 7 →
      PowerSeries.coeff k (B i j) =
        algebraMap ℚ ℂ (PowerSeries.coeff k (papers8_Mseries i j))) :
    PowerSeries.order (B.submatrix id Fin.succ).det = 7 :=
  skelg32_powerSeries_order_complex_aux B hB

example : PowerSeries.order
    (Matrix.submatrix (fun i j => papers8_Mseries i j + (PowerSeries.X : PowerSeries ℚ) ^ 8)
      id Fin.succ).det = 7 := by
  apply skelg32_powerSeries_order
  intro i j k hk
  have hne : k ≠ 8 := by omega
  simp only [map_add, PowerSeries.coeff_X_pow, ite_eq_right hne, add_zero]

example : PowerSeries.order
    (Matrix.submatrix (fun i j => PowerSeries.map (algebraMap ℚ ℂ) (papers8_Mseries i j) +
      (PowerSeries.X : PowerSeries ℂ) ^ 8) id Fin.succ).det = 7 := by
  apply skelg32_powerSeries_order_complex
  intro i j k hk
  have hne : k ≠ 8 := by omega
  simp only [map_add, PowerSeries.coeff_X_pow, ite_eq_right hne, add_zero,
    PowerSeries.coeff_map]

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]
variable {L : Type*} [Field L] [Algebra ℚ L]
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
  [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ}

/-- **G32 Theorem 9.2, conditional powers connector.** For an Eisenstein action and supplied power
data, algebraic Weil classes and the Lie-algebra form of the full special-unitary Hodge-group
hypothesis imply the Hodge conjecture on that power, using the three named classical cycle
inputs.  No discriminant binder is included because it is not used by Theorem 9.2.
The paper supplies `hWA` from Theorem A for Theorem B; its printed proof derives the
cycle operations `hPull`, `hC9` and `h11` from classical results.
Source: G32 v0.16, Theorem 9.2 (`thm:powers`); Fulton, *Intersection Theory*,
2nd ed., Chapter 8 and Corollary 19.2; Griffiths--Harris, *Principles of Algebraic Geometry*,
Chapter 1, Section 2. -/
theorem skelg32_theorem92_conditional (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
  skelg32_theorem92_conditional_aux A θ u hu hL pol hη hRos hGk hWA P hPull hC9 h11

/-- **G32 Theorem A implies Theorem B.** The paper's own Theorem A is supplied as a
statement-only premise. Applying it to membership in `M` supplies algebraicity of the Weil
classes; the conditional Theorem 9.2 connector supplies all powers with classical cycle inputs.
Source: G32 v0.16, Theorem B, its proof, and Theorem 9.2; Fulton, *Intersection Theory*,
2nd ed., Chapter 8 and Corollary 19.2; Griffiths--Harris, Chapter 1, Section 2. -/
theorem skelg32_theoremB (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  skelg32_theorem92_conditional A θ u hu hL pol hη hRos hGk (hA hM) P hPull hC9 h11

end HodgeLean.Papers
