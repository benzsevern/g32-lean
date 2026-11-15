import HodgeLean.Papers.SkeletonG32Defs
import HodgeLean.Adapters.AbelianHomPullbackDefs
import HodgeLean.Adapters.CycleClassPullbackDefs
import HodgeLean.Foundations.AnalyticSubset

/-! # G32 Theorem A, the transfer layer: definitions

The final step of G32 v0.16 (Section 7, Theorem 7.2 and the proof of Theorem A) passes from a
family of sixfolds whose Weil classes are algebraic, and whose image in the moduli space contains
a nonempty open set, to every polarized sixfold of Weil type for `ℚ(√-3)` with discriminant
`[-2]`. This file records the carriers of that step:

* `g32t_Sixfold`: a complex abelian variety with the five instances of `G32TheoremAStatement`,
  a rational Weil action of `ℚ(√-3)` on `H¹` and a degree-two class, bundled;
* `g32t_IsMember`, `g32t_WeilAlg`: membership in `M = (3, ℚ(√-3), [-2])` and algebraicity of the
  Weil classes, read through `IsMemberOfM` and `WeilClassesAlgebraic`;
* `g32t_PolarizedWeil`: membership without the discriminant clause;
* `g32t_KIsog`: a `K`-linear isogeny multiplying the polarization by a positive rational;
* `G32TransferDatum`: the outputs of the earlier stages and the literature premises that the
  transfer step consumes, each as a field.

Nothing here asserts Theorem A, and no field states it. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm HodgeLean.Adapters

namespace HodgeLean.Papers

/-- **A complex abelian variety with a rational Weil action of `ℚ(√-3)` and a degree-two
class**, bundled. `X` carries the five instances of `G32TheoremAStatement`; `W` is a rational
endomorphism `J` of `H¹(X(ℂ); ℚ)` with `J² = -3` preserving the Hodge pieces (the cohomological
form of an embedding `ℚ(√-3) → End⁰(X)`, Birkenhake–Lange, Ch. 1, not formalized); `pol` is a
class in `H²(X(ℂ); ℚ)`, intended to be a polarization. No condition is imposed: membership is
`g32t_IsMember`.
Source: G32 v0.16, Definition 2.1 (the triple `(A, ι, E)`), in the cohomological vocabulary of
`G32TheoremAStatement`. -/
structure g32t_Sixfold where
  /-- The abelian variety. -/
  X : Over (Spec ↧ℂ)
  [grp : GrpObj X]
  [comm : IsCommMonObj X]
  [integral : IsIntegral X.left]
  [smooth : Smooth X.hom]
  [projective : IsProjective X.hom]
  /-- The rational Weil action of `ℚ(√-3)` on `H¹`, `J² = -3`. -/
  W : letI := (torusCohomology_cupProductOf X).finite
    HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1 3
  /-- The degree-two class. -/
  pol : HQ X 2

attribute [instance] g32t_Sixfold.grp g32t_Sixfold.comm g32t_Sixfold.integral
  g32t_Sixfold.smooth g32t_Sixfold.projective

/-- **Membership in `M = (3, ℚ(√-3), [-2])`**: `IsMemberOfM` for the bundled data, with the
constructed cup product and the abelian package. It is the premise of `G32TheoremAStatement`.
Source: G32 v0.16, Theorem A (the hypotheses); F-1569 (the family `M`), through `IsMemberOfM`. -/
def g32t_IsMember (P : g32t_Sixfold) : Prop :=
  IsMemberOfM (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
    (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X) P.W P.pol

/-- **The Weil classes of a bundled sixfold are algebraic**: for every proof that `W` is of Weil
type, `WeilClassesAlgebraic` holds. Since `WeilClassesAlgebraic` depends on that proof only
through proof irrelevance, this is the paper's "`W_K(A)` is spanned by algebraic classes" when
`W` is of Weil type. When `W` is not of Weil type it holds vacuously; Theorem A's conclusion
reads it only on members, which are of Weil type.
Source: G32 v0.16, Section 2 (`W_K(A)`) and Lemma 7.1 (the locus `𝓜^alg`), through
`WeilClassesAlgebraic`. -/
def g32t_WeilAlg (P : g32t_Sixfold) : Prop :=
  ∀ hW : letI := (torusCohomology_cupProductOf P.X).finite; P.W.IsWeilType,
    WeilClassesAlgebraic (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
      (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X) P.W hW

/-- On a member, `g32t_WeilAlg` is the conclusion of `G32TheoremAStatement` for that member. -/
example (P : g32t_Sixfold) (hP : g32t_IsMember P) (h : g32t_WeilAlg P) :
    WeilClassesAlgebraic (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
      (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X) P.W
      hP.isWeilType :=
  h _

/-- **A polarized sixfold of Weil type for `ℚ(√-3)`**: every clause of `IsMemberOfM` except the
discriminant. This is what G32's Lemma 3.6 (`A_ρ(C)` is a polarized sixfold of Weil type) gives
for every fibre of the Hurwitz family, before the discriminant is computed in Section 6.
Source: G32 v0.16, Lemma 3.6 and Definition 2.1; the clauses of `IsMemberOfM`. -/
structure g32t_PolarizedWeil (P : g32t_Sixfold) : Prop where
  dim_eq : dim P.X.left = 6
  isWeilType : letI := (torusCohomology_cupProductOf P.X).finite; P.W.IsWeilType
  nondegenerate : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf P.X) P.pol)
  rosati : letI := (torusCohomology_cupProductOf P.X).finite
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf P.X) P.pol) P.W.J
  positive : PolarizationPositive (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
    (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X) nondegenerate

/-- The Hermitian discriminant class of a polarized sixfold of Weil type, `weilDatumClass`.
Source: G32 v0.16, Section 2 (`disc H ∈ ℚ^×/Nm K^×`, after van Geemen, Lemma 5.2), through
`weilDatumClass`. -/
def g32t_disc {P : g32t_Sixfold} (h : g32t_PolarizedWeil P) :
    ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0) :=
  weilDatumClass (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
    (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X) P.W h.nondegenerate
    h.rosati

/-- Membership is a polarized sixfold of Weil type together with discriminant `[-2]`: the two
pieces are exactly the clauses of `IsMemberOfM`.
Source: the definition of `IsMemberOfM` (F-1569). -/
theorem g32t_isMember_iff (P : g32t_Sixfold) :
    g32t_IsMember P ↔ ∃ h : g32t_PolarizedWeil P, g32t_disc h = classNegTwo :=
  ⟨fun h => ⟨⟨h.dim_eq, h.isWeilType, h.nondegenerate, h.rosati, h.positive⟩, h.datum⟩,
    fun ⟨h, hd⟩ => ⟨h.dim_eq, h.isWeilType, h.nondegenerate, h.rosati, h.positive, hd⟩⟩

example (P : g32t_Sixfold) (h : g32t_PolarizedWeil P) (hd : g32t_disc h = classNegTwo) :
    g32t_IsMember P :=
  (g32t_isMember_iff P).2 ⟨h, hd⟩

/-- **A `K`-linear polarized isogeny `P → Q`**: a homomorphism `f : P.X ⟶ Q.X` that is an
isogeny on complex points (finite kernel, surjective: `ccm2_IsogenyOnPoints`), whose pullback on
`H¹` intertwines the two Weil actions (`f^* ∘ J_Q = J_P ∘ f^*`), and whose pullback on `H²`
sends `Q.pol` to a positive rational multiple of `P.pol`.

These are the isogenies of G32's Section 2: "a `K`-linear isogeny that multiplies the
polarization by a positive rational number". The multiplication-by-`N` isogenies of Lemma 2.2
and of the proof of Theorem 7.2 are of this kind.
Source: G32 v0.16, Section 2 and Lemma 2.2; Mumford, *Abelian Varieties*, §18 (isogenies);
Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (`f^*` on `H¹`), through
`homPullback`. -/
def g32t_KIsog (P Q : g32t_Sixfold) : Prop :=
  letI := (torusCohomology_cupProductOf P.X).finite
  letI := (torusCohomology_cupProductOf Q.X).finite
  ∃ f : P.X ⟶ Q.X, IsMonHom f ∧ ccm2_IsogenyOnPoints f ∧
    (∀ x, homPullback f 1 (Q.W.J x) = P.W.J (homPullback f 1 x)) ∧
    ∃ c : ℚ, 0 < c ∧ homPullback f 2 Q.pol = c • P.pol

/-- The intertwining clause for `J_Q` and `J_P` gives the same clause for the conjugate actions
`-J_Q` and `-J_P`. -/
example (P Q : g32t_Sixfold) (f : P.X ⟶ Q.X) :
    letI := (torusCohomology_cupProductOf P.X).finite
    letI := (torusCohomology_cupProductOf Q.X).finite
    (∀ x, homPullback f 1 (Q.W.J x) = P.W.J (homPullback f 1 x)) →
      ∀ x, homPullback f 1 (-Q.W.J x) = -P.W.J (homPullback f 1 x) := by
  intro h x
  rw [map_neg, h]

/-- **The transfer datum of G32 Theorem 7.2.** A family of sixfolds over an index set `S` (the
Hurwitz component `Hur°`), the nine-dimensional moduli space `M = Γ(ℓ)\𝓗₃` as a connected
Hausdorff analytic complex manifold, and its universal family `univ`, with the outputs of the
earlier stages and the literature premises as fields:

* `fiber_polarized` (stage 2, G32 Lemma 3.6): each fibre is a polarized sixfold of Weil type;
* (c) `fiber_disc` (stage 5, G32 Proposition 6.3): each fibre has discriminant `[-2]`;
* (a) `fiber_alg` (stage 3, G32 Proposition 4.6, from Schoen and Milne): the Weil classes of
  each fibre are algebraic;
* (b) `dominant` (stage 4, G32 Corollary 5.11 and the first paragraph of the proof of Theorem
  7.2, from the rank-nine certificate): a nonempty open `U ⊆ M` each of whose points carries a
  fibre of `univ` receiving a `K`-linear polarized isogeny from some fibre of the family;
* (d) `spread` (G32 Lemma 7.1, Voisin's relative-Hilbert argument): the points of `M` where the
  Weil classes of the universal fibre are algebraic form a countable union of closed analytic
  subsets (closed algebraic subsets of the quasi-projective `M` are closed analytic);
* (e) `cover` (G32 Lemma 2.2, second sentence, from Landherr's theorem and van Geemen §5):
  every member of `M = (3, ℚ(√-3), [-2])` has a `K`-linear polarized isogeny to a fibre of
  `univ`;
* (f) `transport` (G32 Lemma 2.2, first sentence): algebraicity of the Weil classes is invariant
  under `K`-linear polarized isogeny.

The family structure of `fiber` and `univ` (an abelian scheme over a base) is not recorded: the
repository has no families of abelian schemes. The fields use the fibres only pointwise, and
the family structure enters through the stages that supply (b) and (d).
Source: G32 v0.16, Section 2.1 (the moduli space `𝓜` and its universal abelian scheme), Lemma
2.2, Lemma 7.1, Theorem 7.2 and the proof of Theorem A; van Geemen, *An introduction to the Hodge
conjecture for abelian varieties*, LNM 1594 (1994), §§5.2–5.11; Voisin, *Hodge Theory and Complex
Algebraic Geometry II*, §3.3.2. -/
structure G32TransferDatum where
  /-- The index set of the family (the Hurwitz component). -/
  S : Type
  /-- The fibres of the family. -/
  fiber : S → g32t_Sixfold
  /-- Stage 2: each fibre is a polarized sixfold of Weil type for `ℚ(√-3)`. -/
  fiber_polarized : ∀ s, g32t_PolarizedWeil (fiber s)
  /-- (c) Stage 5: each fibre has Hermitian discriminant `[-2]`. -/
  fiber_disc : ∀ s, g32t_disc (fiber_polarized s) = classNegTwo
  /-- (a) Stage 3: the Weil classes of each fibre are algebraic. -/
  fiber_alg : ∀ s, g32t_WeilAlg (fiber s)
  /-- The moduli space `Γ(ℓ)\𝓗₃`. -/
  M : Type
  [topM : TopologicalSpace M]
  [t2M : T2Space M]
  [connM : ConnectedSpace M]
  [chartM : ChartedSpace (Fin 9 → ℂ) M]
  [manifoldM : IsManifold 𝓘(ℂ, Fin 9 → ℂ) ω M]
  /-- The fibres of the universal family over `M`. -/
  univ : M → g32t_Sixfold
  /-- (b) Stage 4: dominance. -/
  dominant : ∃ U : Set M, IsOpen U ∧ U.Nonempty ∧ ∀ m ∈ U, ∃ s, g32t_KIsog (fiber s) (univ m)
  /-- (d) Hilbert spreading. -/
  spread : ∃ C : Set (Set M), C.Countable ∧ (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧
    {m | g32t_WeilAlg (univ m)} = ⋃₀ C
  /-- (e) Landherr coverage. -/
  cover : ∀ P, g32t_IsMember P → ∃ m, g32t_KIsog P (univ m)
  /-- (f) Isogeny transport. -/
  transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q)

attribute [instance] G32TransferDatum.topM G32TransferDatum.t2M G32TransferDatum.connM
  G32TransferDatum.chartM G32TransferDatum.manifoldM

/-- The fields fit together: a fibre over a point of the dominant open set transports its
algebraicity to the universal fibre over that point. -/
example (D : G32TransferDatum) (m : D.M) (s : D.S) (h : g32t_KIsog (D.fiber s) (D.univ m)) :
    g32t_WeilAlg (D.univ m) :=
  (D.transport _ _ h).1 (D.fiber_alg s)

end HodgeLean.Papers
