import HodgeLean.Adapters.TopCupPower

/-! # Abelian milestones with the torus hypotheses supplied
Stage S13. HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
namespace HodgeLean.Adapters
variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- The abelian curve milestone with O1, C7 and C1 supplied by S7 and S13.
Source: `RealDefs.hdg_le_span_abelian_g1` (F-1690).

Checks: F-1690

HC no distance; AV milestone no distance. -/
@[hodge_milestone] theorem hdg_le_span_abelian_g1_cupProductOf
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hH : CycleClassIsHodge X)
    (h11 : LefschetzOneOneHyp) (hg : dim X.left = 1) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_abelian_g1 (finiteBetti_abelian X) hB hD
    (torusCohomology_cupProductOf X) hH h11 hg

/-- The abelian surface milestone with O1, C7 and C1 supplied.
O3 is reduced to nondegeneracy of the specified polarization preimage.
Source: `RealDefs.hdg_le_span_abelian_g2` (F-1690), `hardLefschetz_abelian`.

Checks: F-1690

HC no distance; AV milestone no distance. -/
@[hodge_milestone] theorem hdg_le_span_abelian_g2_cupProductOf
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : Foundations.Symplectic.IsNondegenerate
      (((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm η))
    (h11 : LefschetzOneOneHyp) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_abelian_g2 (finiteBetti_abelian X) hB hD
    (torusCohomology_cupProductOf X) hM hH hA (hardLefschetz_abelian X hη) h11 hg

/-- The abelian threefold milestone with O1, C7 and C1 supplied.
O3 is reduced to nondegeneracy; filteredness of cup remains an explicit premise.
Source: `RealDefs.hdg_le_span_abelian_g3` (F-1690), `hardLefschetz_abelian`.

Checks: F-1690

HC no distance; AV milestone no distance. -/
@[hodge_milestone] theorem hdg_le_span_abelian_g3_cupProductOf
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : Foundations.Symplectic.IsNondegenerate
      (((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm η))
    (hC : CupFiltered X (cupProductOf X))
    (h11 : LefschetzOneOneHyp) (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_abelian_g3 (finiteBetti_abelian X) hB hD
    (torusCohomology_cupProductOf X) hM hH hA (hardLefschetz_abelian X hη) hC h11 hg

/-- The abelian dimension-2 milestone with O3 reduced to nonvanishing of the top cup power,
which remains an explicit input until the curves lane's divisor stages J1--J2.
Source: `RealDefs.hdg_le_span_abelian_g2` (F-1690), `hardLefschetz_abelian_of_cupPow`.

Checks: F-1690

HC no distance; AV milestone no distance. -/
@[hodge_milestone] theorem hdg_le_span_abelian_g2_of_cupPow
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : cupPow X (cupProductOf X) η 2 ≠ 0)
    (h11 : LefschetzOneOneHyp) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_abelian_g2 (finiteBetti_abelian X) hB hD
    (torusCohomology_cupProductOf X) hM hH hA
    (hardLefschetz_abelian_of_cupPow X (by rw [hg]; exact hη)) h11 hg

/-- The abelian dimension-3 milestone with O3 reduced to nonvanishing of the top cup power,
which remains an explicit input until the curves lane's divisor stages J1--J2.
Source: `RealDefs.hdg_le_span_abelian_g3` (F-1690), `hardLefschetz_abelian_of_cupPow`.

Checks: F-1690

HC no distance; AV milestone no distance. -/
@[hodge_milestone] theorem hdg_le_span_abelian_g3_of_cupPow
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : cupPow X (cupProductOf X) η 3 ≠ 0)
    (hC : CupFiltered X (cupProductOf X))
    (h11 : LefschetzOneOneHyp) (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_abelian_g3 (finiteBetti_abelian X) hB hD
    (torusCohomology_cupProductOf X) hM hH hA
    (hardLefschetz_abelian_of_cupPow X (by rw [hg]; exact hη)) hC h11 hg

#print axioms hdg_le_span_abelian_g2_of_cupPow
#print axioms hdg_le_span_abelian_g3_of_cupPow
#print axioms hdg_le_span_abelian_g1_cupProductOf
#print axioms hdg_le_span_abelian_g2_cupProductOf
#print axioms hdg_le_span_abelian_g3_cupProductOf
end HodgeLean.Adapters
