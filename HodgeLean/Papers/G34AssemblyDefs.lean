import HodgeLean.Papers.G34Supply
import HodgeLean.Papers.G34Compensation

/-! # G34 Theorems A and B, assembly: the premise bundle (definitions)

The assembly of the premise-first route to G34 v1.5 Theorem A at `(n, δ) = (4, [1])`. This file
records one object, `g34a_premises`: the seven named literature premises that the route takes on
trust, bundled with their sources. Each field is a premise already named by a stage (the
universal family of the generic transfer, the Prym family of stage 2, Proposition 4.6 of stage 3,
the boundary period map and the parabolic polarization of the boundary certificate) or a field of
`wtr_StageFields` in its exact shape (Hilbert spreading, isogeny transport).

The compensation premise of `G34Compensation`, used for Theorem B, is a premise about one given
sixfold, so it is not a field here; the Theorem B statement takes it as an explicit binder.

No field states `G34TheoremAStatement`, `G34TheoremBStatement`, membership of an arbitrary
eightfold, a discriminant of an arbitrary eightfold, dominance, a rank or an open subset of `𝓗₄`.
Nothing here asserts Theorem A or Theorem B. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

/-- **The seven premises of G34 Theorem A**, bundled. This is what Lean takes on trust for the
premise-first route to G34 v1.5 Theorem A, the family `M(4, ℚ(√-3), [1])` of split abelian
eightfolds of Weil type.

* `F` (generic transfer): the universal family over the period domain `𝓗₄`, each fibre a member
  of `M(4, ℚ(√-3), [1])`, with Landherr coverage.
  Source: Landherr, Abh. Math. Sem. Hamburg 11 (1936), 245–248; van Geemen, LNM 1594 (1994),
  §§5.4–5.11; G34 v1.5, Subsection 2.1 and Lemma 2.2 (second sentence).
* `P` (stage 2): the `G₃₄` Hurwitz family of twenty reflections with its Prym–Tyurin factors
  `A_σ(C_s)`, the Nielsen tuples, the Chevalley–Weil dimension and Hodge-number links, and the
  polarization clauses.
  Source: G34 v1.5, Subsections 3.1–3.2, Proposition 3.1, Definition 3.2, Lemma 3.3, Section 9
  and Lemma 9.1; Frediani–Ghigi–Penegini, IMRN 2015, Theorem 2.10; Birkenhake–Lange, Ch. 12.
* `h46` (stage 3): the Weil classes of every Prym–Tyurin factor are algebraic.
  Source: G34 v1.5, Proposition 4.6 and Corollary 4.7, with Theorem 5.1 (Brauer; Serre, §10.5,
  Theorem 20); Schoen, Compositio Math. 65 (1988), Theorem 2.0 and Corollary 3.1, with G34
  Lemma 4.4; Milne, Duke Math. J. 96 (1999), Theorem 3.2.
* `Φ` (boundary certificate): the boundary period map over `F` and the Prym–Tyurin factors: the
  Gauss–Manin and local-monodromy identification (Lemmas 8.1 and 8.2), the limit Hodge filtration
  with the Cattani–Kaplan–Schmid Hodge–Tate input (Lemma 8.3), the differentiated nilpotent orbit
  limit, and the isogeny link from parameter values to universal fibres (Theorem 6.2).
  Source: G34 v1.5, Section 8 and Theorem 6.2; Dettweiler–Wewers, Israel J. Math. 156 (2006);
  Schmid, Invent. Math. 22 (1973), (4.12); Cattani–Kaplan–Schmid, Ann. of Math. 123 (1986),
  (1.15) and (4.5).
* `hpar` (boundary certificate): on each Prym–Tyurin factor, the Weil Hermitian form has, in some
  basis, Gram matrix a nonzero rational multiple of the printed `h = ϑ𝒮` or of its conjugate.
  Source: G34 v1.5, Proposition 7.1 and Lemma 7.2; Appendix A.
* `spread`: the points of `𝓗₄` whose universal fibre has algebraic Weil classes form a countable
  union of closed analytic subsets.
  Source: G34 v1.5, Lemma 6.1; Voisin, *Hodge Theory and Complex Algebraic Geometry II*,
  §3.3.2.
* `transport`: algebraicity of the Weil classes is invariant under `K`-linear polarized isogeny.
  Source: G34 v1.5, Lemma 2.2 (first sentence).

`spread` and `transport` have exactly the types of the fields of the same name of
`wtr_StageFields F` at `(4, [1])`. `Φ` is stated over `P.fiber` and `hpar` for the stage-2 proof
`g34h_fiber_polarized P s`, the arguments that `g34b_dominant` and `g34b_fiber_disc` take.
Source: G34 v1.5, Theorem A and its proof (Sections 2–9), with the citations above. -/
structure g34a_premises where
  /-- The universal family over `𝓗₄` (Landherr, van Geemen). -/
  F : wtr_UniversalFamily 4 1
  /-- Stage 2: the `G₃₄` Hurwitz family and its Prym–Tyurin factors (Chevalley–Weil, G34
  Lemma 3.3). -/
  P : g34h_PrymFamily
  /-- Stage 3: G34 Proposition 4.6 (Brauer, Schoen, Milne). -/
  h46 : g34s_Prop46 P
  /-- Boundary: the period map near the maximal degeneration (G34 Section 8, Theorem 6.2). -/
  Φ : g34b_BoundaryPeriodMap F P.fiber
  /-- Boundary: the parabolic-polarization comparison (G34 Proposition 7.1). -/
  hpar : ∀ s, g34b_ParabolicPolarization (g34h_fiber_polarized P s)
  /-- Hilbert spreading (G34 Lemma 6.1, Voisin). -/
  spread : ∃ C : Set (Set (wtr_Domain 4)), C.Countable ∧
    (∀ Z ∈ C, IsClosedAnalytic (Fin (4 ^ 2) → ℂ) Z) ∧ {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C
  /-- Isogeny transport (G34 Lemma 2.2). -/
  transport : ∀ P Q : wtr_Variety 4, wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q)

/-- The bundle carries the stage-3 premise in the exact shape of the stage field `fiber_alg`. -/
example (B : g34a_premises) : ∀ s, wtr_WeilAlg (B.P.fiber s) :=
  g34s_fiber_alg B.P B.h46

/-- The bundle carries the boundary premise, from which `g34b_dominant` gives dominance. -/
example (B : g34a_premises) :
    ∃ U : Set (wtr_Domain 4), IsOpen U ∧ U.Nonempty ∧
      ∀ m ∈ U, ∃ s, wtr_KIsog (B.P.fiber s) (B.F.univ m) :=
  g34b_dominant B.F B.P.fiber B.Φ

/-- The bundle carries the parabolic polarization, from which `g34b_fiber_disc` gives the split
discriminant. -/
example (B : g34a_premises) (s : B.P.S) : wtr_disc (g34h_fiber_polarized B.P s) = 1 :=
  g34b_fiber_disc B.P.fiber (g34h_fiber_polarized B.P) B.hpar s

end HodgeLean.Papers
