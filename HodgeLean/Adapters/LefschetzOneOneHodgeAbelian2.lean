import HodgeLean.Adapters.LefschetzOneOneHodgeAbelian2Proofs

/-! # Scoped Lefschetz (1,1) restatements for abelian surfaces and threefolds -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

/-- Every rational `(1,1)` class is a rational multiple of the class of an integral alternating
Riemann form.  The positive integer `N` is its common denominator.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1; Voisin,
*Hodge Theory and Complex Algebraic Geometry I*, §7.2. -/
theorem spec_hdg_one_exists_riemann_latticeClassHQ
    (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (x : H^(2 * 1)(X; ℚ)) (hx : x ∈ Hdg^1(X; ℚ)) :
    ∃ (N : ℕ) (hN : 0 < N)
      (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
      (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ]
        (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
      (∀ l m : abelianPeriodLattice X, B l m = E l m) ∧
      (∀ l : abelianPeriodLattice X, E l l = 0) ∧
      IsTypeOneOne (fun v w ↦ B v w) ∧
      x = (N : ℚ)⁻¹ • latticeClassHQ X E :=
  spec_hdg_one_exists_riemann_latticeClassHQ_aux X hF hBdR x hx

example (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (x : H^(2 * 1)(X; ℚ)) (hx : x ∈ Hdg^1(X; ℚ)) :=
  spec_hdg_one_exists_riemann_latticeClassHQ X hF hBdR x hx

/-- Denominators can be cleared in the rational Riemann-form presentation.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1. -/
theorem spec_hdg_one_clear_denominators
    (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (x : H^(2 * 1)(X; ℚ)) (hx : x ∈ Hdg^1(X; ℚ)) :
    ∃ (N : ℕ) (hN : 0 < N)
      (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
      (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ]
        (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
      (∀ l m : abelianPeriodLattice X, B l m = E l m) ∧
      (∀ l : abelianPeriodLattice X, E l l = 0) ∧
      IsTypeOneOne (fun v w ↦ B v w) ∧ N • x = latticeClassHQ X E :=
  spec_hdg_one_clear_denominators_aux X hF hBdR x hx

example (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (x : H^(2 * 1)(X; ℚ)) (hx : x ∈ Hdg^1(X; ℚ)) :=
  spec_hdg_one_clear_denominators X hF hBdR x hx

/-- Rational divisor Hodge classes are exactly the span of integral Riemann lattice classes.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1. -/
theorem spec_hdg_one_eq_span_riemann_latticeClassHQ
    (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X) :
    Hdg^1(X; ℚ) = Submodule.span ℚ
      {x : H^(2 * 1)(X; ℚ) | ∃
        (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
        (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ]
          (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
        (∀ l m : abelianPeriodLattice X, B l m = E l m) ∧
        (∀ l : abelianPeriodLattice X, E l l = 0) ∧
        IsTypeOneOne (fun v w ↦ B v w) ∧ x = latticeClassHQ X E} :=
  spec_hdg_one_eq_span_riemann_latticeClassHQ_aux X hF hBdR

example (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X) :=
  spec_hdg_one_eq_span_riemann_latticeClassHQ X hF hBdR

/-- Scoped Lefschetz `(1,1)` is equivalent to algebraicity of every Riemann lattice class.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §2. -/
theorem spec_lefschetzOneOneFor_iff_riemann_latticeClassHQ
    (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X) :
    LefschetzOneOneFor X ↔
      ∀ (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
        (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ]
          (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
        (∀ l m : abelianPeriodLattice X, B l m = E l m) →
        (∀ l : abelianPeriodLattice X, E l l = 0) →
        IsTypeOneOne (fun v w ↦ B v w) →
        latticeClassHQ X E ∈ algebraicCycleClassSpan X 1 :=
  spec_lefschetzOneOneFor_iff_riemann_latticeClassHQ_aux X hF hBdR

example (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X) :=
  spec_lefschetzOneOneFor_iff_riemann_latticeClassHQ X hF hBdR

/-- The abelian-surface milestone only needs Lefschetz `(1,1)` for this `X`.
Source: `HodgeBlocks.hodgeConjecture_g2`; `abelian_hdg_le_span_g2`.

Checks: F-1690 -/
@[hodge_milestone] theorem spec_abelian_hdg_le_span_g2_of_for {μ : CupProduct X}
    (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η)
    (hL : HardLefschetz X μ η) (h11 : LefschetzOneOneFor X) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  spec_abelian_hdg_le_span_g2_of_for_aux X hT hM hH hA hL h11 hg

example {μ : CupProduct X} (hT : TorusCohomology μ)
    (hM : CycleClassMultiplicative μ) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η) (hL : HardLefschetz X μ η)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 2) :=
  spec_abelian_hdg_le_span_g2_of_for X hT hM hH hA hL h11 hg

/-- The abelian-threefold milestone needs Lefschetz `(1,1)` only for `X`.
Source: `HodgeBlocks.hodgeConjecture_g3`; `abelian_hdg_le_span_g3`.

Checks: F-1690 -/
@[hodge_milestone] theorem spec_abelian_hdg_le_span_g3_of_for {μ : CupProduct X}
    (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η)
    (hL : HardLefschetz X μ η) (hC : CupFiltered X μ)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  spec_abelian_hdg_le_span_g3_of_for_aux X hT hM hH hA hL hC h11 hg

example {μ : CupProduct X} (hT : TorusCohomology μ)
    (hM : CycleClassMultiplicative μ) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η) (hL : HardLefschetz X μ η)
    (hC : CupFiltered X μ) (h11 : LefschetzOneOneFor X) (hg : dim X.left = 3) :=
  spec_abelian_hdg_le_span_g3_of_for X hT hM hH hA hL hC h11 hg

/-- The finite-Betti surface restatement with scoped Lefschetz `(1,1)`.
Source: `harvestBetti_hdg_le_span_abelian_g2`.

Checks: F-1690 -/
@[hodge_milestone] theorem spec_harvestBetti_hdg_le_span_abelian_g2_of_for {μ : CupProduct X}
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (hM : CycleClassMultiplicative μ) (hH : CycleClassIsHodge X) {η : HQ X 2}
    (hA : AlgebraicTimesDivisor X μ η) (hL : HardLefschetz X μ η)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  spec_harvestBetti_hdg_le_span_abelian_g2_of_for_aux X hB hD hT hM hH hA hL h11 hg

example {μ : CupProduct X} (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η)
    (hL : HardLefschetz X μ η) (h11 : LefschetzOneOneFor X)
    (hg : dim X.left = 2) :=
  spec_harvestBetti_hdg_le_span_abelian_g2_of_for X hB hD hT hM hH hA hL h11 hg

/-- The finite-Betti threefold restatement with scoped Lefschetz `(1,1)`.
Source: `harvestBetti_hdg_le_span_abelian_g3`.

Checks: F-1690 -/
@[hodge_milestone] theorem spec_harvestBetti_hdg_le_span_abelian_g3_of_for {μ : CupProduct X}
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (hM : CycleClassMultiplicative μ) (hH : CycleClassIsHodge X) {η : HQ X 2}
    (hA : AlgebraicTimesDivisor X μ η) (hL : HardLefschetz X μ η)
    (hC : CupFiltered X μ) (h11 : LefschetzOneOneFor X) (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  spec_harvestBetti_hdg_le_span_abelian_g3_of_for_aux X hB hD hT hM hH hA hL hC h11 hg

example {μ : CupProduct X} (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η)
    (hL : HardLefschetz X μ η) (hC : CupFiltered X μ)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 3) :=
  spec_harvestBetti_hdg_le_span_abelian_g3_of_for X hB hD hT hM hH hA hL hC h11 hg

/-- Surface cup-product restatement with scoped Lefschetz `(1,1)`.
Source: `abelian_hdg_le_span_g2_cupProductOf`.

Checks: F-1690 -/
@[hodge_milestone] theorem spec_abelian_hdg_le_span_g2_cupProductOf_of_for
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : Symplectic.IsNondegenerate
      (((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm η))
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  spec_abelian_hdg_le_span_g2_cupProductOf_of_for_aux X hM hH hA hη h11 hg

example (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : Symplectic.IsNondegenerate
      (((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm η))
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 2) :=
  spec_abelian_hdg_le_span_g2_cupProductOf_of_for X hM hH hA hη h11 hg

/-- Threefold cup-product restatement with scoped Lefschetz `(1,1)`.
Source: `abelian_hdg_le_span_g3_cupProductOf`.

Checks: F-1690 -/
@[hodge_milestone] theorem spec_abelian_hdg_le_span_g3_cupProductOf_of_for
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : Symplectic.IsNondegenerate
      (((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm η))
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  spec_abelian_hdg_le_span_g3_cupProductOf_of_for_aux X hM hH hA hη h11 hg

example (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : Symplectic.IsNondegenerate
      (((torusCohomology_cupProductOf X).cupWedgeEquiv 2).symm η))
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 3) :=
  spec_abelian_hdg_le_span_g3_cupProductOf_of_for X hM hH hA hη h11 hg

/-- Surface top-cup-power restatement with scoped Lefschetz `(1,1)`.
Source: `abelian_hdg_le_span_g2_of_cupPow`.

Checks: F-1690 -/
@[hodge_milestone] theorem spec_abelian_hdg_le_span_g2_of_cupPow_of_for
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : cupPow X (cupProductOf X) η 2 ≠ 0)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  spec_abelian_hdg_le_span_g2_of_cupPow_of_for_aux X hM hH hA hη h11 hg

example (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : cupPow X (cupProductOf X) η 2 ≠ 0)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 2) :=
  spec_abelian_hdg_le_span_g2_of_cupPow_of_for X hM hH hA hη h11 hg

/-- Threefold top-cup-power restatement with scoped Lefschetz `(1,1)`.
Source: `abelian_hdg_le_span_g3_of_cupPow`.

Checks: F-1690 -/
@[hodge_milestone] theorem spec_abelian_hdg_le_span_g3_of_cupPow_of_for
    (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : cupPow X (cupProductOf X) η 3 ≠ 0)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  spec_abelian_hdg_le_span_g3_of_cupPow_of_for_aux X hM hH hA hη h11 hg

example (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    {η : HQ X 2} (hA : AlgebraicTimesDivisor X (cupProductOf X) η)
    (hη : cupPow X (cupProductOf X) η 3 ≠ 0)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 3) :=
  spec_abelian_hdg_le_span_g3_of_cupPow_of_for X hM hH hA hη h11 hg

/-! ## Degenerate-input checks -/

example (hg : dim X.left = 0) : LefschetzOneOneFor X :=
  spec_lefschetzOneOneFor_dim_zero X hg

/-- On an abelian curve every rational degree-two class has type `(1,1)`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.2. -/
theorem spec_hdg_one_dim_one (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (hg : dim X.left = 1) (x : H^(2 * 1)(X; ℚ)) : x ∈ Hdg^1(X; ℚ) :=
  spec_hdg_one_dim_one_aux X hF hBdR hg x

example (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (hg : dim X.left = 1) (x : H^(2 * 1)(X; ℚ)) :=
  spec_hdg_one_dim_one X hF hBdR hg x

example (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X) :
    (latticeClassHQ X 0 : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ) := by
  let B : (Fin (dim X.left) → ℂ) →ₗ[ℝ]
      (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ := 0
  exact spec_latticeClassHQ_mem_hdg_of_riemann X hF hBdR 0 B
    (by simp [B]) (by simp) (by simp [B, IsTypeOneOne])

/-- Conditional contrapositive: a class outside `Hdg¹` cannot be the class of a Riemann form.
Source: the Hodge-type implication for Riemann forms. -/
theorem spec_non_hodge_not_riemann_latticeClassHQ
    (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (x : H^(2 * 1)(X; ℚ)) (hx : x ∉ Hdg^1(X; ℚ)) :
    ¬ ∃ (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
      (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ]
        (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
      (∀ l m : abelianPeriodLattice X, B l m = E l m) ∧
      (∀ l : abelianPeriodLattice X, E l l = 0) ∧
      IsTypeOneOne (fun v w ↦ B v w) ∧ x = latticeClassHQ X E :=
  spec_non_hodge_not_riemann_latticeClassHQ_aux X hF hBdR x hx

example (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (x : H^(2 * 1)(X; ℚ)) (hx : x ∉ Hdg^1(X; ℚ)) :=
  spec_non_hodge_not_riemann_latticeClassHQ X hF hBdR x hx

end HodgeLean.Adapters
