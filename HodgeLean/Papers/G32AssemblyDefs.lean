import HodgeLean.Papers.G32Moduli
import HodgeLean.Papers.G32Family
import HodgeLean.Papers.G32Supply
import HodgeLean.Papers.G32Dominance
import HodgeLean.Papers.G32Disc

/-! # G32 Theorem A, assembly: the premise bundle (definitions)

The assembly of the premise-first route to G32 v0.16 Theorem A. This file records one object,
`g32a_premises`: the seven named literature premises that the route takes on trust, bundled with
their sources. Each field is a premise already named by a stage (the universal family of stage 1,
the Prym family of stage 2, Proposition 4.6 of stage 3, the period map of stage 4, the parabolic
polarization of stage 5) or a field of the transfer datum in its exact shape (Hilbert spreading,
isogeny transport).

No field states `G32TheoremAStatement`, membership of an arbitrary sixfold, a discriminant of an
arbitrary sixfold, dominance or an open subset of `𝓗₃`. Nothing here asserts Theorem A. HC no
distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

/-- **The seven premises of G32 Theorem A**, bundled. This is what Lean takes on trust for the
premise-first route to G32 v0.16 Theorem A. The six stage files on the route have Lean proofs; the
five assembly statements built from this bundle are composed from them.

* `F` (stage 1): the universal family over the period domain `𝓗₃`, each fibre a member of
  `M = (3, ℚ(√-3), [-2])`, with Landherr coverage.
  Source: Landherr, Abh. Math. Sem. Hamburg 11 (1936), 245–248; van Geemen, LNM 1594 (1994),
  §§5.4–5.11; G32 v0.16, Subsection 2.1 and Lemma 2.2 (second sentence).
* `P` (stage 2): the `G₃₂` Hurwitz family with its Prym factors `A_ρ(C_s)`, Nielsen tuples, the
  Chevalley–Weil dimension and Hodge-number links, and the polarization clauses.
  Source: G32 v0.16, Subsections 3.1–3.3, Proposition 3.1, Lemma 3.3, Lemma 3.6;
  Frediani–Ghigi–Penegini, IMRN 2015, Theorem 2.10; Birkenhake–Lange, Ch. 12.
* `h46` (stage 3): the Weil classes of every Prym factor are algebraic.
  Source: G32 v0.16, Proposition 4.6 with Proposition 4.5; Schoen, Theorem 2.0 and Corollary 3.1;
  Milne, Theorem 3.2.
* `R` (stage 4): a local analytic period map from a parameter chart of the Hurwitz family into
  `𝓗₃`, with the fibre-to-isogeny property and the codifferential identified with a certified jet.
  Source: Frediani–Ghigi–Penegini, IMRN 2015, §§2–3; G32 v0.16, Lemma 5.1, Lemma 5.6, Lemma 5.8
  and the first paragraph of the proof of Theorem 7.2; Katz, Ann. of Math. Stud. 139, Theorem 1.1.2.
* `hpol` (stage 5): on each Prym factor, the Weil Hermitian form has, in some basis, Gram matrix a
  positive rational multiple of the printed parabolic matrix `g32H0`.
  Source: G32 v0.16, Section 6 and Proposition 6.3.
* `spread`: the points of `𝓗₃` whose universal fibre has algebraic Weil classes form a countable
  union of closed analytic subsets.
  Source: G32 v0.16, Lemma 7.1; Voisin, *Hodge Theory and Complex Algebraic Geometry II*, §3.3.2.
* `transport`: algebraicity of the Weil classes is invariant under `K`-linear polarized isogeny.
  Source: G32 v0.16, Lemma 2.2 (first sentence).

`spread` and `transport` have exactly the types of the fields of the same name of
`g32m_StageFields F`. `hpol` is stated for the stage-2 proof `g32h_fiber_polarized P s`, the
argument the stage-5 premise `g32d_ParabolicPolarization` takes.
Source: G32 v0.16, Theorem A and its proof (Sections 2–7), with the citations above. -/
structure g32a_premises where
  /-- Stage 1: the universal family over `𝓗₃` (Landherr, van Geemen). -/
  F : g32m_UniversalFamily
  /-- Stage 2: the Hurwitz family and its Prym factors (Chevalley–Weil, G32 Lemma 3.3). -/
  P : g32h_PrymFamily
  /-- Stage 3: G32 Proposition 4.6 (Schoen, Milne). -/
  h46 : g32s_Prop46 P
  /-- Stage 4: the period map (FGP codifferential, the Schlesinger jet). -/
  R : g32r_PeriodMap F P
  /-- Stage 5: the parabolic-polarization comparison (G32 Proposition 6.3). -/
  hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s)
  /-- Hilbert spreading (G32 Lemma 7.1, Voisin). -/
  spread : ∃ C : Set (Set g32m_Domain), C.Countable ∧
    (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C
  /-- Isogeny transport (G32 Lemma 2.2). -/
  transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q)

/-- The bundle carries the stage-3 premise in the exact shape of the stage field `fiber_alg`. -/
example (B : g32a_premises) : ∀ s, g32t_WeilAlg (B.P.fiber s) :=
  g32s_fiber_alg B.P B.h46

/-- The bundle carries the stage-4 premise, from which `g32r_dominant` gives dominance. -/
example (B : g32a_premises) :
    ∃ U : Set g32m_Domain, IsOpen U ∧ U.Nonempty ∧
      ∀ m ∈ U, ∃ s, g32t_KIsog (B.P.fiber s) (B.F.univ m) :=
  g32r_dominant B.F B.P B.R

end HodgeLean.Papers
