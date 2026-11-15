import HodgeLean.Adapters.LefschetzOneOneHodgeAbelianProofs

/-!
# The Hodge half of Lefschetz (1,1) for abelian varieties (FROZEN SPEC)

This stage states the implication from an integral alternating form satisfying the first Riemann
relation to a rational `(1,1)` class. It also scopes the algebraic conclusion to one variety,
shows that the global `LefschetzOneOneHyp` implies that scoped proposition, checks dimension zero,
and restates one representative abelian milestone over the scoped proposition.

It does not claim the converse classification of all rational `(1,1)` classes, denominator
clearing, or algebraicity of Appell--Humbert line bundles. In particular it weakens and scopes
`LefschetzOneOneHyp`; it does not discharge that global hypothesis. HC no distance; AV milestone
no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.AppellHumbert

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

/-- An integral alternating form whose real extension satisfies the first Riemann relation gives
a rational Hodge class of degree two. No positivity or nondegeneracy is assumed.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1; Voisin,
*Hodge Theory and Complex Algebraic Geometry I*, §7.2 (Hodge decomposition of a complex torus). -/
theorem spec_latticeClassHQ_mem_hdg_of_riemann
    (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X)
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ)
    (hBext : ∀ l m : abelianPeriodLattice X, B l m = E l m)
    (hE : ∀ l : abelianPeriodLattice X, E l l = 0)
    (h11 : IsTypeOneOne (fun v w ↦ B v w)) :
    (latticeClassHQ X E : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ) :=
  spec_latticeClassHQ_mem_hdg_of_riemann_aux X hF hBdR E B hBext hE h11

example (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X) :
    (latticeClassHQ X 0 : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ) := by
  let B : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ := 0
  exact spec_latticeClassHQ_mem_hdg_of_riemann X hF hBdR 0 B
    (by simp [B]) (by simp) (by simp [B, IsTypeOneOne])

/-- The global Lefschetz `(1,1)` hypothesis implies its specialization to `X`.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §2. -/
theorem spec_lefschetzOneOneFor_of_global (h11 : LefschetzOneOneHyp) :
    LefschetzOneOneFor X :=
  spec_lefschetzOneOneFor_of_global_aux X h11

example (h11 : LefschetzOneOneHyp) (x : H^(2 * 1)(X; ℚ)) (hx : x ∈ Hdg^1(X; ℚ)) :
    x ∈ algebraicCycleClassSpan X 1 :=
  spec_lefschetzOneOneFor_of_global X h11 hx

/-- In complex dimension zero, degree-two cohomology vanishes, so the scoped proposition holds.
Source: Hatcher, *Algebraic Topology*, §3.1 (cohomology vanishes above the dimension). -/
theorem spec_lefschetzOneOneFor_dim_zero (hg : dim X.left = 0) :
    LefschetzOneOneFor X :=
  spec_lefschetzOneOneFor_dim_zero_aux X hg

example (hg : dim X.left = 0) (x : H^(2 * 1)(X; ℚ)) (hx : x ∈ Hdg^1(X; ℚ)) :
    x ∈ algebraicCycleClassSpan X 1 :=
  spec_lefschetzOneOneFor_dim_zero X hg hx

/-- The abelian curve milestone only needs Lefschetz `(1,1)` for this `X`, not the global
hypothesis.
Source: `HodgeBlocks.hodgeConjecture_g1`; `abelian_hdg_le_span_g1_cupProductOf`.

Checks: F-1690 -/
@[hodge_milestone] theorem spec_abelian_hdg_le_span_g1_of_for
    (hH : CycleClassIsHodge X)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 1) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  spec_abelian_hdg_le_span_g1_of_for_aux X hH h11 hg

example (hM : CycleClassMultiplicative (cupProductOf X)) (hH : CycleClassIsHodge X)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 1) :
    Hdg^1(X; ℚ) ≤ algebraicCycleClassSpan X 1 :=
  spec_abelian_hdg_le_span_g1_of_for X hH h11 hg 1

end HodgeLean.Adapters
