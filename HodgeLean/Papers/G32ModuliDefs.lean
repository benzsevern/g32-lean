import HodgeLean.Papers.G32TransferDefs

/-! # G32 Theorem A, stage 1: the Weil-moduli interface (definitions)

Stage 1 of the premise-first route to G32 v0.16 Theorem A supplies the moduli-space fields of
`G32TransferDatum`: the nine-dimensional base `M`, the universal fibres `univ` and Landherr
coverage `cover`. This file records:

* `g32m_toMat`: the coordinates `ℂ⁹ ≅ M₃(ℂ)`;
* `g32m_periodSet`: the bounded realization `{Z ∈ M₃(ℂ) | 1 - Zᴴ Z > 0}` of the Hermitian
  symmetric domain `𝓗₃` of `SU(3,3)`, as a subset of `ℂ⁹`;
* `g32m_Domain`: its interior, an open subset of `ℂ⁹`, which carries Mathlib's charted-space and
  analytic-manifold structure;
* `g32m_UniversalFamily`: the named premise holding the universal fibres over `𝓗₃` and Landherr
  coverage;
* `g32m_StageFields`: the fields of `G32TransferDatum` that stages 2–6 still supply, over this
  base;
* `g32m_transferFields`: the transfer datum with `M`, `univ` and `cover` taken from stage 1.

Nothing here asserts Theorem A, and no field states it. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj Manifold ContDiff ComplexOrder Matrix
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm HodgeLean.Adapters

namespace HodgeLean.Papers

/-- **The coordinates `ℂ⁹ ≅ M₃(ℂ)`**: the entry `(i, j)` of the matrix is the coordinate
`finProdFinEquiv (i, j) = 3 i + j`.
Source: the identification of `M₃(ℂ)` with `ℂ^{3·3}`, Mathlib's `finProdFinEquiv`. -/
def g32m_toMat (z : Fin 9 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun i j => z (finProdFinEquiv (i, j))

example : g32m_toMat (fun k => (k : ℂ)) 1 2 = 5 := by
  simp [g32m_toMat, finProdFinEquiv]; norm_num

/-- **The period domain `𝓗₃`, bounded realization.** For the Hermitian form
`H = diag(1, 1, 1, -1, -1, -1)` of signature `(3,3)` on `ℂ⁶`, a three-dimensional subspace on
which `H` is positive is the graph `{(x, Z x)}` of a unique `Z ∈ M₃(ℂ)`, and `H` is positive on
it exactly when `1 - Zᴴ Z` is positive definite. So `𝓗₃` is
`{Z ∈ M₃(ℂ) | 1 - Zᴴ Z > 0}`, the classical domain `ℜ_I(3, 3)`, of complex dimension `3² = 9`.
Over `ℝ` every Hermitian form of signature `(3,3)` is isometric to `H`, so this is the domain of
G32's Subsection 2.1 for the discriminant-`[-2]` space `(V, H)`; the discriminant enters only
through the lattice and the arithmetic group.
Source: G32 v0.16, Subsection 2.1 (`𝓗_n`, the `n`-dimensional subspaces of `V_ℝ` on which `H` is
positive, connected of dimension `n²`); van Geemen, *An introduction to the Hodge conjecture for
abelian varieties*, LNM 1594 (1994), §§5.5–5.10; Hua, *Harmonic Analysis of Functions of Several
Complex Variables in the Classical Domains*, Transl. Math. Monographs 6, AMS (1963),
Introduction (the domain `ℜ_I(m, n)`). -/
def g32m_periodSet : Set (Fin 9 → ℂ) :=
  {z | (1 - (g32m_toMat z)ᴴ * g32m_toMat z).PosDef}

/-- Membership unfolds to the positivity of `1 - Zᴴ Z`. -/
example (z : Fin 9 → ℂ) (h : (1 - (g32m_toMat z)ᴴ * g32m_toMat z).PosDef) :
    z ∈ g32m_periodSet :=
  h

/-- **The period domain as an open subset of `ℂ⁹`**: the interior of `g32m_periodSet`. That
`g32m_periodSet` is already open, so that this is `𝓗₃` itself, is the frozen statement
`g32m_domain_coe`. As an open subset of the model space it carries Mathlib's
`ChartedSpace (Fin 9 → ℂ)` and `IsManifold 𝓘(ℂ, Fin 9 → ℂ) ω` instances.
Source: G32 v0.16, Subsection 2.1; Mathlib, `TopologicalSpace.Opens.instChartedSpace`. -/
def g32m_Domain : Opens (Fin 9 → ℂ) :=
  ⟨interior g32m_periodSet, isOpen_interior⟩

example : ChartedSpace (Fin 9 → ℂ) g32m_Domain := inferInstance

example : IsManifold 𝓘(ℂ, Fin 9 → ℂ) ω g32m_Domain := inferInstance

example : T2Space g32m_Domain := inferInstance

/-- **The universal family over `𝓗₃` (premise).** For each point `τ` of the period domain, a
bundled sixfold `univ τ`, the fibre at `τ`, with

* `member`: each fibre is a member of `M = (3, ℚ(√-3), [-2])`, i.e. a polarized abelian sixfold
  of Weil type for `ℚ(√-3)` with Hermitian discriminant `[-2]`;
* `cover`: every member of `M` has a `K`-linear polarized isogeny to some fibre.

In the paper a point `τ ∈ 𝓗₃` gives the weight-one Hodge structure of Weil type on `V`, polarized
by `Tr_{K/ℚ}(H/2ϑ)`; with the `𝒪_K`-lattice `Λ ⊂ V` this is the complex torus `V_ℝ/Λ` with the
complex structure of `τ`, an abelian variety by the Riemann relations; the fibres over `𝓗₃` are
those of the universal abelian scheme over `Γ(ℓ)\𝓗₃` pulled back along `𝓗₃ → Γ(ℓ)\𝓗₃`. `cover`
is Landherr's theorem: the `K`-Hermitian space `(H₁(A, ℚ), H)` of a member is isometric to
`(V, H)`, the image of `H₁(A, ℤ)` is commensurable with `Λ`, and multiplication by an integer is
a `K`-linear isogeny to the fibre at the point given by the complex structure of `A`.

The family structure (an abelian scheme over a base, analytic variation of the fibres) and the
compatibility of the Hodge structure of `univ τ` with the point `τ` are not recorded: the
repository has no families of abelian schemes, and the transfer step uses the fibres pointwise.
This structure is a premise; nothing derives it.
Source: Landherr, *Äquivalenz Hermitescher Formen über einem beliebigen algebraischen
Zahlkörper*, Abh. Math. Sem. Hamburg 11 (1936), 245–248, as stated in van Geemen, LNM 1594,
§5.4; van Geemen, LNM 1594, §§5.5–5.11 (the universal family) and 5.10 (every polarized Hodge
structure of Weil type arises from a point); G32 v0.16, Subsection 2.1 and Lemma 2.2 (second
sentence and its proof). -/
structure g32m_UniversalFamily where
  /-- The fibre over a point of `𝓗₃`. -/
  univ : g32m_Domain → g32t_Sixfold
  /-- Each fibre is a member of `M = (3, ℚ(√-3), [-2])`. -/
  member : ∀ τ, g32t_IsMember (univ τ)
  /-- Landherr coverage. -/
  cover : ∀ P, g32t_IsMember P → ∃ τ, g32t_KIsog P (univ τ)

/-- A universal family gives, for each member `P`, an isogeny target that is again a member. -/
example (F : g32m_UniversalFamily) (P : g32t_Sixfold) (hP : g32t_IsMember P) :
    ∃ Q, g32t_IsMember Q ∧ g32t_KIsog P Q :=
  let ⟨τ, h⟩ := F.cover P hP
  ⟨F.univ τ, F.member τ, h⟩

/-- **The fields of `G32TransferDatum` that stages 2–6 still supply**, over the base `𝓗₃` and the
universal fibres of `F`: the family `S`, `fiber` with its stage-2, stage-3 and stage-5 fields,
dominance (stage 4), Hilbert spreading and isogeny transport. Each field has exactly the type
of the field of `G32TransferDatum` with the same name, with `M := g32m_Domain` and
`univ := F.univ`.
Source: G32 v0.16, Lemma 2.2, Lemma 3.6, Proposition 4.6, Corollary 5.11, Proposition 6.3,
Lemma 7.1; the fields of `G32TransferDatum`. -/
structure g32m_StageFields (F : g32m_UniversalFamily) where
  /-- The index set of the family (the Hurwitz component). -/
  S : Type
  /-- The fibres of the family. -/
  fiber : S → g32t_Sixfold
  /-- Stage 2: each fibre is a polarized sixfold of Weil type for `ℚ(√-3)`. -/
  fiber_polarized : ∀ s, g32t_PolarizedWeil (fiber s)
  /-- Stage 5: each fibre has Hermitian discriminant `[-2]`. -/
  fiber_disc : ∀ s, g32t_disc (fiber_polarized s) = classNegTwo
  /-- Stage 3: the Weil classes of each fibre are algebraic. -/
  fiber_alg : ∀ s, g32t_WeilAlg (fiber s)
  /-- Stage 4: dominance. -/
  dominant : ∃ U : Set g32m_Domain, IsOpen U ∧ U.Nonempty ∧
    ∀ m ∈ U, ∃ s, g32t_KIsog (fiber s) (F.univ m)
  /-- Hilbert spreading. -/
  spread : ∃ C : Set (Set g32m_Domain), C.Countable ∧
    (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C
  /-- Isogeny transport. -/
  transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q)

/-- **The bridge to the transfer layer.** From a universal family `F` and the remaining stage
fields `R`, the transfer datum whose `M` is the period domain `𝓗₃` (with Mathlib's open-subset
manifold structure), whose `univ` is `F.univ` and whose `cover` is `F.cover`. Connectedness of
`𝓗₃` is an instance argument; it is the frozen statement `g32m_domain_connectedSpace`.
Source: G32 v0.16, Subsection 2.1 and Theorem 7.2; the fields of `G32TransferDatum`. -/
def g32m_transferFields (F : g32m_UniversalFamily) [ConnectedSpace g32m_Domain]
    (R : g32m_StageFields F) : G32TransferDatum where
  S := R.S
  fiber := R.fiber
  fiber_polarized := R.fiber_polarized
  fiber_disc := R.fiber_disc
  fiber_alg := R.fiber_alg
  M := g32m_Domain
  univ := F.univ
  dominant := R.dominant
  spread := R.spread
  cover := F.cover
  transport := R.transport

/-- The bridge fills `univ` and `cover` from stage 1 and nothing else. -/
example (F : g32m_UniversalFamily) [ConnectedSpace g32m_Domain] (R : g32m_StageFields F) :
    (g32m_transferFields F R).univ = F.univ ∧ (g32m_transferFields F R).fiber = R.fiber :=
  ⟨rfl, rfl⟩

end HodgeLean.Papers
