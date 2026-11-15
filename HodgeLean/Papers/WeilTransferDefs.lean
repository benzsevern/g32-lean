import HodgeLean.Papers.G32ModuliDefs

/-! # The generic Weil transfer: definitions

G32's transfer layer (`G32TransferDefs`) and moduli layer (`G32ModuliDefs`) are written for one
family `M = (3, ℚ(√-3), [-2])`: abelian sixfolds, discriminant `[-2]`, period domain `𝓗₃ ⊆ ℂ⁹`.
The argument of G32 v0.16, Section 7, does not use these values. This file records the same
carriers for a half-dimension `n` and a discriminant class `δ`, with the field kept at
`K = ℚ(√-3)`:

* `wtr_Variety n`: the carrier `g32t_Sixfold` (an abelian variety with a rational Weil action of
  `ℚ(√-3)` on `H¹` and a degree-two class), tagged by `n`; no dimension is imposed on it;
* `wtr_PolarizedWeil n`, `wtr_disc`, `wtr_IsMember n δ`, `wtr_WeilAlg`, `wtr_KIsog`: membership
  in `M(n, ℚ(√-3), δ)` (an abelian `2n`-fold of Weil type with a positive polarization and
  Hermitian discriminant `δ`), algebraicity of the Weil classes, and `K`-linear polarized
  isogenies;
* `WeilTransferDatum n δ`: the transfer datum, with base charted on `ℂ^{n²}`;
* `wtr_toMat`, `wtr_periodSet`, `wtr_Domain`: the period domain `𝓗_n = {Z ∈ Mₙ(ℂ) | 1 - Zᴴ Z > 0}`
  as a subset and as an open subset of `ℂ^{n²}`;
* `wtr_UniversalFamily n δ`, `wtr_StageFields`, `wtr_transferFields`: the universal-family
  premise over `𝓗_n`, the remaining stage fields, and the datum they assemble;
* `wtr_ofG32`, `wtr_ofG32Family`: a G32 transfer datum and a G32 universal family are the
  instances `n = 3`, `δ = [-2]`.

Nothing here asserts a Theorem A, and no field states one. HC no distance; AV milestone no
distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj Manifold ContDiff ComplexOrder Matrix
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm HodgeLean.Adapters

namespace HodgeLean.Papers

/-- **The carrier at half-dimension `n`**: a complex abelian variety with the five instances, a
rational Weil action `W` of `ℚ(√-3)` on `H¹` (`J² = -3`) and a degree-two class `pol`, exactly
G32's `g32t_Sixfold`. The tag `n` records which family the carrier is meant for; it imposes no
condition, since `g32t_Sixfold` imposes none (dimension six enters G32 only through
membership). Here the dimension `2n` enters through `wtr_PolarizedWeil n`.
Source: G32 v0.16, Definition 2.1 (the triple `(A, ι, E)`), for abelian varieties of any
dimension; van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, LNM 1594
(1994), §5.2 (Weil type in dimension `2n`); through `g32t_Sixfold`. -/
abbrev wtr_Variety (_n : ℕ) : Type 1 := g32t_Sixfold

/-- The carriers for all `n` are G32's bundled sixfolds. -/
example (P : g32t_Sixfold) : wtr_Variety 4 := P

/-- **A polarized abelian `2n`-fold of Weil type for `ℚ(√-3)`**: the clauses of `IsMemberOfM`
except the discriminant, with `dim = 2n` in place of `dim = 6`. At `n = 3` these are the fields
of `g32t_PolarizedWeil`.
Source: G32 v0.16, Definition 2.1 and Section 2; van Geemen, LNM 1594, §5.2; the clauses of
`IsMemberOfM` and `g32t_PolarizedWeil`. -/
structure wtr_PolarizedWeil (n : ℕ) (P : wtr_Variety n) : Prop where
  dim_eq : dim P.X.left = 2 * n
  isWeilType : letI := (torusCohomology_cupProductOf P.X).finite; P.W.IsWeilType
  nondegenerate : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf P.X) P.pol)
  rosati : letI := (torusCohomology_cupProductOf P.X).finite
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf P.X) P.pol) P.W.J
  positive : PolarizationPositive (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
    (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X) nondegenerate

/-- **The Hermitian discriminant class** `weilDatumClass ∈ ℚˣ ⧸ Nm(ℚ(√-3)ˣ)` of a polarized
`2n`-fold of Weil type; the body of `g32t_disc`. Since `dim_K H¹ = 2n` is even, the class does
not depend on the scale of the polarization (`weilDetClass_smul_of_even`).
Source: G32 v0.16, Section 2 (`disc H ∈ ℚ^×/Nm K^×`); van Geemen, LNM 1594, Lemma 5.2;
through `weilDatumClass`. -/
def wtr_disc {n : ℕ} {P : wtr_Variety n} (h : wtr_PolarizedWeil n P) :
    ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0) :=
  weilDatumClass (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
    (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X) P.W h.nondegenerate
    h.rosati

/-- **Membership in `M(n, ℚ(√-3), δ)`**: a polarized abelian `2n`-fold of Weil type for
`ℚ(√-3)` whose Hermitian discriminant class is `δ`. At `n = 3`, `δ = [-2]` this is
`g32t_IsMember` (`wtr_isMember_three_iff`).
Source: G32 v0.16, Section 2 (the families `(n, K, δ)`); van Geemen, LNM 1594, §§5.2–5.4;
F-1569 (the family `M = (3, ℚ(√-3), [-2])`), through `IsMemberOfM`. -/
structure wtr_IsMember (n : ℕ) (δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0))
    (P : wtr_Variety n) : Prop where
  polarized : wtr_PolarizedWeil n P
  disc_eq : wtr_disc polarized = δ

/-- A member of `M(4, ℚ(√-3), δ)` is an abelian eightfold. -/
example (δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) (P : wtr_Variety 4)
    (h : wtr_IsMember 4 δ P) : dim P.X.left = 8 :=
  h.polarized.dim_eq

/-- **The Weil classes are algebraic**: for every proof that `W` is of Weil type,
`WeilClassesAlgebraic` holds; the body of `g32t_WeilAlg`, which does not depend on the
dimension.
Source: G32 v0.16, Section 2 (`W_K(A)`) and Lemma 7.1; van Geemen, LNM 1594, §5.2 (the space
`W_K = ⋀ⁿ_K H¹` of Weil classes); through `WeilClassesAlgebraic`. -/
def wtr_WeilAlg {n : ℕ} (P : wtr_Variety n) : Prop :=
  ∀ hW : letI := (torusCohomology_cupProductOf P.X).finite; P.W.IsWeilType,
    WeilClassesAlgebraic (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
      (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X) P.W hW

/-- On a member, `wtr_WeilAlg` gives `WeilClassesAlgebraic` for its Weil-type proof. -/
example (n : ℕ) (δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) (P : wtr_Variety n)
    (hP : wtr_IsMember n δ P) (h : wtr_WeilAlg P) :
    WeilClassesAlgebraic (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
      (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X) P.W
      hP.polarized.isWeilType :=
  h _

/-- **A `K`-linear polarized isogeny `P → Q`**: an isogeny on complex points intertwining the
Weil actions on `H¹` and pulling `Q.pol` back to a positive rational multiple of `P.pol`. The
relation does not depend on the dimension, so it is `g32t_KIsog` itself.
Source: G32 v0.16, Section 2 and Lemma 2.2; Mumford, *Abelian Varieties*, §18; Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., §1.2; through `g32t_KIsog` and `homPullback`. -/
def wtr_KIsog {n : ℕ} (P Q : wtr_Variety n) : Prop :=
  g32t_KIsog P Q

/-- The generic isogeny relation at `n = 3` is G32's. -/
example (P Q : g32t_Sixfold) : wtr_KIsog (n := 3) P Q ↔ g32t_KIsog P Q := Iff.rfl

/-- **The generic transfer datum** `WeilTransferDatum n δ`, the generalization of
`G32TransferDatum`: a family of carriers over `S`, a connected Hausdorff analytic complex
manifold `M` charted on `ℂ^{n²}` (the moduli space `Γ\𝓗_n`), its universal fibres `univ`, and
the fields

* `fiber_polarized`: each fibre is a polarized `2n`-fold of Weil type;
* (c) `fiber_disc`: each fibre has discriminant `δ`;
* (a) `fiber_alg`: the Weil classes of each fibre are algebraic;
* (b) `dominant`: a nonempty open `U ⊆ M` each of whose points carries a universal fibre
  receiving a `K`-linear polarized isogeny from some fibre of the family;
* (d) `spread`: the algebraicity locus in `M` is a countable union of closed analytic subsets;
* (e) `cover`: every member of `M(n, ℚ(√-3), δ)` has a `K`-linear polarized isogeny to a
  universal fibre;
* (f) `transport`: algebraicity of the Weil classes is invariant under `K`-linear polarized
  isogeny.

The field shapes are those of `G32TransferDatum`, with `Fin 9` replaced by `Fin (n ^ 2)`, `6` by
`2 n` and `[-2]` by `δ`. As there, the family structure of `fiber` and `univ` is not recorded.
Source: G32 v0.16, Section 2.1, Lemma 2.2, Lemma 7.1, Theorem 7.2 and the proof of Theorem A,
whose argument is uniform in `(n, δ)`; van Geemen, LNM 1594, §§5.2–5.11; Voisin, *Hodge Theory
and Complex Algebraic Geometry II*, §3.3.2. -/
structure WeilTransferDatum (n : ℕ) (δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) where
  /-- The index set of the family. -/
  S : Type
  /-- The fibres of the family. -/
  fiber : S → wtr_Variety n
  /-- Each fibre is a polarized `2n`-fold of Weil type for `ℚ(√-3)`. -/
  fiber_polarized : ∀ s, wtr_PolarizedWeil n (fiber s)
  /-- (c) Each fibre has Hermitian discriminant `δ`. -/
  fiber_disc : ∀ s, wtr_disc (fiber_polarized s) = δ
  /-- (a) The Weil classes of each fibre are algebraic. -/
  fiber_alg : ∀ s, wtr_WeilAlg (fiber s)
  /-- The moduli space. -/
  M : Type
  [topM : TopologicalSpace M]
  [t2M : T2Space M]
  [connM : ConnectedSpace M]
  [chartM : ChartedSpace (Fin (n ^ 2) → ℂ) M]
  [manifoldM : IsManifold 𝓘(ℂ, Fin (n ^ 2) → ℂ) ω M]
  /-- The fibres of the universal family over `M`. -/
  univ : M → wtr_Variety n
  /-- (b) Dominance. -/
  dominant : ∃ U : Set M, IsOpen U ∧ U.Nonempty ∧ ∀ m ∈ U, ∃ s, wtr_KIsog (fiber s) (univ m)
  /-- (d) Hilbert spreading. -/
  spread : ∃ C : Set (Set M), C.Countable ∧ (∀ Z ∈ C, IsClosedAnalytic (Fin (n ^ 2) → ℂ) Z) ∧
    {m | wtr_WeilAlg (univ m)} = ⋃₀ C
  /-- (e) Landherr coverage. -/
  cover : ∀ P, wtr_IsMember n δ P → ∃ m, wtr_KIsog P (univ m)
  /-- (f) Isogeny transport. -/
  transport : ∀ P Q : wtr_Variety n, wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q)

attribute [instance] WeilTransferDatum.topM WeilTransferDatum.t2M WeilTransferDatum.connM
  WeilTransferDatum.chartM WeilTransferDatum.manifoldM

/-- The fields fit together as in G32: a fibre over a point of the dominant open set transports
its algebraicity to the universal fibre. -/
example (n : ℕ) (δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) (D : WeilTransferDatum n δ)
    (m : D.M) (s : D.S) (h : wtr_KIsog (D.fiber s) (D.univ m)) : wtr_WeilAlg (D.univ m) :=
  (D.transport _ _ h).1 (D.fiber_alg s)

section Bridge

/-- **At `n = 3` the polarized clauses are G32's.** `2 * 3` and `6` agree by computation.
Source: the definitions of `wtr_PolarizedWeil` and `g32t_PolarizedWeil`. -/
theorem wtr_polarizedWeil_three_iff (P : g32t_Sixfold) :
    wtr_PolarizedWeil 3 P ↔ g32t_PolarizedWeil P :=
  ⟨fun h => ⟨h.dim_eq, h.isWeilType, h.nondegenerate, h.rosati, h.positive⟩,
    fun h => ⟨h.dim_eq, h.isWeilType, h.nondegenerate, h.rosati, h.positive⟩⟩

/-- **At `n = 3`, `δ = [-2]`, generic membership is G32's membership.**
Source: the definitions of `wtr_IsMember` and `g32t_IsMember`; `g32t_isMember_iff`. -/
theorem wtr_isMember_three_iff (P : g32t_Sixfold) :
    wtr_IsMember 3 classNegTwo P ↔ g32t_IsMember P :=
  ⟨fun h => (g32t_isMember_iff P).2 ⟨(wtr_polarizedWeil_three_iff P).1 h.polarized, h.disc_eq⟩,
    fun h =>
      let ⟨h', hd⟩ := (g32t_isMember_iff P).1 h
      ⟨(wtr_polarizedWeil_three_iff P).2 h', hd⟩⟩

example (P : g32t_Sixfold) (h : g32t_IsMember P) : dim P.X.left = 2 * 3 :=
  ((wtr_isMember_three_iff P).2 h).polarized.dim_eq

/-- At `n = 3` the generic discriminant is G32's. -/
example (P : g32t_Sixfold) (h : wtr_PolarizedWeil 3 P) :
    wtr_disc h = g32t_disc ((wtr_polarizedWeil_three_iff P).1 h) :=
  rfl

/-- **A G32 transfer datum is a generic transfer datum at `n = 3`, `δ = [-2]`.** Every field is
the G32 field: `ℂ⁹` is `ℂ^{3²}` by computation, the discriminant field is unchanged, and `cover`
is read through `wtr_isMember_three_iff`.
Source: the fields of `G32TransferDatum` and `WeilTransferDatum`. -/
def wtr_ofG32 (D : G32TransferDatum) : WeilTransferDatum 3 classNegTwo where
  S := D.S
  fiber := D.fiber
  fiber_polarized s := (wtr_polarizedWeil_three_iff _).2 (D.fiber_polarized s)
  fiber_disc := D.fiber_disc
  fiber_alg := D.fiber_alg
  M := D.M
  chartM := D.chartM
  manifoldM := D.manifoldM
  univ := D.univ
  dominant := D.dominant
  spread := D.spread
  cover P hP := D.cover P ((wtr_isMember_three_iff P).1 hP)
  transport := D.transport

/-- The bridge keeps the base, the family and the universal fibres. -/
example (D : G32TransferDatum) :
    (wtr_ofG32 D).M = D.M ∧ (wtr_ofG32 D).fiber = D.fiber ∧ HEq (wtr_ofG32 D).univ D.univ :=
  ⟨rfl, rfl, HEq.rfl⟩

end Bridge

section Domain

/-- **The coordinates `ℂ^{n²} ≅ Mₙ(ℂ)`**: the entry `(i, j)` is the coordinate `n i + j`, via
`finProdFinEquiv` and `n ^ 2 = n * n`.
Source: the identification of `Mₙ(ℂ)` with `ℂ^{n·n}`, Mathlib's `finProdFinEquiv`; at `n = 3`
this is `g32m_toMat`. -/
def wtr_toMat (n : ℕ) (z : Fin (n ^ 2) → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => z (Fin.cast (sq n).symm (finProdFinEquiv (i, j)))

/-- At `n = 3` the coordinates are G32's. -/
example (z : Fin 9 → ℂ) : wtr_toMat 3 z = g32m_toMat z := rfl

/-- **The period domain `𝓗_n`, bounded realization**: `{Z ∈ Mₙ(ℂ) | 1 - Zᴴ Z > 0}`, the
classical domain `ℜ_I(n, n)` of `SU(n, n)`, of complex dimension `n²`. Over `ℝ` every Hermitian
form of signature `(n, n)` is isometric to `diag(1ₙ, -1ₙ)`, so this is the domain for every
discriminant `δ`; `δ` enters only through the lattice and the arithmetic group.
Source: G32 v0.16, Subsection 2.1 (`𝓗_n`, connected of dimension `n²`); van Geemen, LNM 1594,
§§5.5–5.10; Hua, *Harmonic Analysis of Functions of Several Complex Variables in the Classical
Domains*, Transl. Math. Monographs 6, AMS (1963), Introduction (the domain `ℜ_I(m, n)`). -/
def wtr_periodSet (n : ℕ) : Set (Fin (n ^ 2) → ℂ) :=
  {z | (1 - (wtr_toMat n z)ᴴ * wtr_toMat n z).PosDef}

/-- At `n = 3` the period set is G32's. -/
example : wtr_periodSet 3 = g32m_periodSet := rfl

/-- **The period domain as an open subset of `ℂ^{n²}`**: the interior of `wtr_periodSet n`;
that the interior changes nothing is the frozen statement `wtr_domain_coe`. It carries Mathlib's
open-subset charted-space and analytic-manifold instances.
Source: G32 v0.16, Subsection 2.1; Mathlib, `TopologicalSpace.Opens.instChartedSpace`. -/
def wtr_Domain (n : ℕ) : Opens (Fin (n ^ 2) → ℂ) :=
  ⟨interior (wtr_periodSet n), isOpen_interior⟩

example (n : ℕ) : ChartedSpace (Fin (n ^ 2) → ℂ) (wtr_Domain n) := inferInstance

example (n : ℕ) : IsManifold 𝓘(ℂ, Fin (n ^ 2) → ℂ) ω (wtr_Domain n) := inferInstance

example (n : ℕ) : T2Space (wtr_Domain n) := inferInstance

/-- At `n = 3` the open subset is G32's. -/
example : wtr_Domain 3 = g32m_Domain := rfl

end Domain

section Family

/-- **The universal family over `𝓗_n` (premise).** For each point `τ` of the period domain a
carrier `univ τ`, with

* `member`: each fibre is a member of `M(n, ℚ(√-3), δ)`;
* `cover`: every member of `M(n, ℚ(√-3), δ)` has a `K`-linear polarized isogeny to some fibre.

In van Geemen's construction a point of `𝓗_n` gives a weight-one Hodge structure of Weil type on
the `K`-Hermitian space `(V, H)` of dimension `2n`, signature `(n, n)` and discriminant `δ`,
polarized by `Tr_{K/ℚ}(H/2ϑ)`; with an `𝒪_K`-lattice it is an abelian `2n`-fold. `cover` is
Landherr's theorem: a `K`-Hermitian space over a number field is determined up to isometry by
its dimension, its signatures and its discriminant, so the space `H₁(A, ℚ)` of every member is
isometric to `(V, H)`. For `δ` whose sign is not `(-1)ⁿ` there is no member and no fibre, and
no universal family exists; this premise is then unsatisfiable, not false.

As for `g32m_UniversalFamily`, the family structure and the compatibility of the Hodge
structure of `univ τ` with `τ` are not recorded. This structure is a premise; nothing derives
it.
Source: Landherr, *Äquivalenz Hermitescher Formen über einem beliebigen algebraischen
Zahlkörper*, Abh. Math. Sem. Hamburg 11 (1936), 245–248, as stated in van Geemen, LNM 1594,
§5.4; van Geemen, LNM 1594, §§5.5–5.11 (the universal family) and 5.10 (every polarized Hodge
structure of Weil type arises from a point); G32 v0.16, Subsection 2.1 and Lemma 2.2. -/
structure wtr_UniversalFamily (n : ℕ) (δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) where
  /-- The fibre over a point of `𝓗_n`. -/
  univ : wtr_Domain n → wtr_Variety n
  /-- Each fibre is a member of `M(n, ℚ(√-3), δ)`. -/
  member : ∀ τ, wtr_IsMember n δ (univ τ)
  /-- Landherr coverage. -/
  cover : ∀ P, wtr_IsMember n δ P → ∃ τ, wtr_KIsog P (univ τ)

/-- A universal family gives, for each member, an isogeny target that is again a member. -/
example (n : ℕ) (δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) (F : wtr_UniversalFamily n δ)
    (P : wtr_Variety n) (hP : wtr_IsMember n δ P) :
    ∃ Q, wtr_IsMember n δ Q ∧ wtr_KIsog P Q :=
  let ⟨τ, h⟩ := F.cover P hP
  ⟨F.univ τ, F.member τ, h⟩

/-- **The fields of `WeilTransferDatum n δ` that the other stages supply**, over the base `𝓗_n`
and the universal fibres of `F`; the generalization of `g32m_StageFields`. Each field has the
type of the field of `WeilTransferDatum` with the same name, with `M := wtr_Domain n` and
`univ := F.univ`.
Source: G32 v0.16, Lemma 2.2, Lemma 3.6, Proposition 4.6, Corollary 5.11, Proposition 6.3,
Lemma 7.1; the fields of `WeilTransferDatum`. -/
structure wtr_StageFields {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (F : wtr_UniversalFamily n δ) where
  /-- The index set of the family. -/
  S : Type
  /-- The fibres of the family. -/
  fiber : S → wtr_Variety n
  /-- Each fibre is a polarized `2n`-fold of Weil type for `ℚ(√-3)`. -/
  fiber_polarized : ∀ s, wtr_PolarizedWeil n (fiber s)
  /-- Each fibre has Hermitian discriminant `δ`. -/
  fiber_disc : ∀ s, wtr_disc (fiber_polarized s) = δ
  /-- The Weil classes of each fibre are algebraic. -/
  fiber_alg : ∀ s, wtr_WeilAlg (fiber s)
  /-- Dominance. -/
  dominant : ∃ U : Set (wtr_Domain n), IsOpen U ∧ U.Nonempty ∧
    ∀ m ∈ U, ∃ s, wtr_KIsog (fiber s) (F.univ m)
  /-- Hilbert spreading. -/
  spread : ∃ C : Set (Set (wtr_Domain n)), C.Countable ∧
    (∀ Z ∈ C, IsClosedAnalytic (Fin (n ^ 2) → ℂ) Z) ∧ {m | wtr_WeilAlg (F.univ m)} = ⋃₀ C
  /-- Isogeny transport. -/
  transport : ∀ P Q : wtr_Variety n, wtr_KIsog P Q → (wtr_WeilAlg P ↔ wtr_WeilAlg Q)

/-- **The generic bridge to the transfer layer**: the datum with `M := wtr_Domain n`,
`univ := F.univ`, `cover := F.cover` and the other fields from `R`. Connectedness of `𝓗_n` is an
instance argument; it is the frozen statement `wtr_domain_connectedSpace`.
Source: G32 v0.16, Subsection 2.1 and Theorem 7.2; the generalization of `g32m_transferFields`. -/
def wtr_transferFields {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (F : wtr_UniversalFamily n δ) [ConnectedSpace (wtr_Domain n)] (R : wtr_StageFields F) :
    WeilTransferDatum n δ where
  S := R.S
  fiber := R.fiber
  fiber_polarized := R.fiber_polarized
  fiber_disc := R.fiber_disc
  fiber_alg := R.fiber_alg
  M := wtr_Domain n
  univ := F.univ
  dominant := R.dominant
  spread := R.spread
  cover := F.cover
  transport := R.transport

example (n : ℕ) (δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) (F : wtr_UniversalFamily n δ)
    [ConnectedSpace (wtr_Domain n)] (R : wtr_StageFields F) :
    (wtr_transferFields F R).fiber = R.fiber ∧ (wtr_transferFields F R).M = wtr_Domain n :=
  ⟨rfl, rfl⟩

/-- **A G32 universal family is a generic one at `n = 3`, `δ = [-2]`**: `g32m_Domain` is
`wtr_Domain 3` by computation, and membership is read through `wtr_isMember_three_iff`.
Source: the fields of `g32m_UniversalFamily` and `wtr_UniversalFamily`. -/
def wtr_ofG32Family (F : g32m_UniversalFamily) : wtr_UniversalFamily 3 classNegTwo where
  univ := F.univ
  member τ := (wtr_isMember_three_iff _).2 (F.member τ)
  cover P hP := F.cover P ((wtr_isMember_three_iff P).1 hP)

example (F : g32m_UniversalFamily) (τ : g32m_Domain) : (wtr_ofG32Family F).univ τ = F.univ τ :=
  rfl

end Family

end HodgeLean.Papers
