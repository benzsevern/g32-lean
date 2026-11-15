import HodgeLean.Papers.SkeletonTTProofs

/-!
# TT v0.15 main-theorem skeleton (FROZEN SPEC)

The G32 and QI cell conclusions are expressible and remain open targets. The geometric
implication from transfer data, dominance and spreading is not yet expressible. The G32 powers
composition takes its named cell statement as an explicit premise, while conditional Theorem 8.2 remains a separate proved
connector. Finite certificates are reused in `SkeletonTTCertificates.lean`.
-/

noncomputable section
set_option maxHeartbeats 400000
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Symplectic
open HodgeLean.Foundations.InvariantsExterior HodgeLean.Adapters NumberField
open HodgeLean.Foundations.SchurWeyl

namespace HodgeLean.Papers

/-- The invariant-theory input to TT's powers theorem, in the repository's `sl(W)` Lie-module
form: invariants are generated degreewise by contractions and the two determinant families.
Source: TT v0.15, Lemma 8.1 (`lem:sl`), citing Severn, *Hodge classes on certain six-dimensional
abelian varieties*, Lemma 9.2. -/
theorem skeltt_invariants {K W U U' : Type*} [Field K] [CharZero K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup U'] [Module K U'] [FiniteDimensional K U'] (k : ℕ) :
    (LieModule.maxTrivSubmodule K (slEnd K W)
      (⋀[K]^k (HodgeLean.Foundations.InvariantsExterior.Space K W U U')) : Submodule K _) =
      HodgeLean.Foundations.InvariantsExterior.generatedDegree
        (K := K) (W := W) (U := U) (U' := U') k :=
  skeltt_invariants_aux k

/-- A constructed degenerate instance: zero standard and multiplicity spaces in degree zero. -/
example :
    (LieModule.maxTrivSubmodule ℚ (slEnd ℚ (Fin 0 → ℚ))
      (⋀[ℚ]^0 (HodgeLean.Foundations.InvariantsExterior.Space ℚ
        (Fin 0 → ℚ) (Fin 0 → ℚ) (Fin 0 → ℚ))) : Submodule ℚ _) =
      HodgeLean.Foundations.InvariantsExterior.generatedDegree
        (K := ℚ) (W := Fin 0 → ℚ) (U := Fin 0 → ℚ) (U' := Fin 0 → ℚ) 0 :=
  skeltt_invariants 0

/-- Positive-dimensional witness: standard space of dimension two, both multiplicities one. -/
example :
    (LieModule.maxTrivSubmodule ℚ (slEnd ℚ (Fin 2 → ℚ))
      (⋀[ℚ]^2 (HodgeLean.Foundations.InvariantsExterior.Space ℚ
        (Fin 2 → ℚ) (Fin 1 → ℚ) (Fin 1 → ℚ))) : Submodule ℚ _) =
      HodgeLean.Foundations.InvariantsExterior.generatedDegree
        (K := ℚ) (W := Fin 2 → ℚ) (U := Fin 1 → ℚ) (U' := Fin 1 → ℚ) 2 :=
  skeltt_invariants 2

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]
variable {L : Type*} [Field L] [NumberField L] [IsCMField L]
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
  [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ}

/-- Conditional Theorem 8.2 for supplied power data, separate from TT's main transfer chain.
The premise `hWA` is supplied by Theorem 7.1 in that chain. The remaining inputs state the
memberwise Hodge-Lie hypothesis and classical cycle functoriality, products and Lefschetz (1,1).
Source: TT v0.15, Theorem 8.2 (`thm:powers`) and proof; Fulton, *Intersection Theory*, 2nd ed.,
Chapter 8 and Corollary 19.2; Griffiths--Harris, *Principles of Algebraic Geometry*, Chapter 1 §2. -/
theorem skeltt_theorem82_conditional (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) {d : ℚ}
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
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p :=
  skeltt_theorem82_conditional_aux A θ u hd hu pol hη hRos hGk hWA P hPull hC9 h11

/-- Composition of the G32 cell conclusion with conditional Theorem 8.2.
The premise is TT's own cell theorem, statement only; no transfer proof is asserted.
Source: TT v0.15, Corollary 10.1 (`cor:g32`), powers clause, and Theorem 8.2. -/
theorem skeltt_g32_powers (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
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
    (hC9 : CycleClassMultiplicative (cupProductOf Y)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p := by
  have hWA := hCell hM
  exact skeltt_theorem82_conditional A θ u (by norm_num) hu pol hη hRos hGk
    hWA P hPull hC9 h11

end HodgeLean.Papers
