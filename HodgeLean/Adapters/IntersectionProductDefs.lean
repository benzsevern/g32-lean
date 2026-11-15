import HodgeLean.Adapters.ChowCorrespondenceDefs

/-! # Serre's intersection product on cycles, by construction

Track A3, route R2 (Serre's Tor formula with a moving lemma), first sub-stage. Every object is
built from existing data:
* `a3i_stalkIdeal X z u` is the prime of the local ring `𝒪_{X,z}` cut out by the subvariety
  `closure {u}`: the point of `Spec 𝒪_{X,z}` over `u` (Mathlib's `Scheme.fromSpecStalk`), and the
  unit ideal when `u` does not specialize to `z`;
* `a3i_torModule X z u v i = Tor_i^{𝒪_{X,z}}(𝒪_{X,z}/𝔭_u, 𝒪_{X,z}/𝔭_v)`, with Mathlib's `Tor`
  in `ModuleCat`;
* `a3i_serreMult X z u v = Σ_{i ≤ dim 𝒪_{X,z}} (-1)^i length Tor_i`, Serre's intersection
  multiplicity, where `dim 𝒪_{X,z}` is the coheight of `z`;
* `a3i_intersectPrime X u v` puts Serre's multiplicity on each irreducible component of the
  scheme-theoretic intersection `closure {u} ∩ closure {v}`, indexed exactly as
  `ccm11_intersectionCycle`; `a3i_intersect X c d` is its bilinear extension;
* `a3i_MeetProperly X u v` says every component has codimension `codim u + codim v`;
* `a3i_ratAll X` is the sum over all dimensions of A2's `a2_ratEquivDim`, `a3i_ChowTotal X` the
  quotient of all rational cycles by it, and `a3i_chowMul` multiplies two classes through a
  chosen pair of properly meeting representatives (zero when none exists).

That `a3i_chowMul` does not depend on the chosen representatives, and that representatives
exist, are statements of the frozen spec `HodgeLean.Adapters.IntersectionProduct`, not
properties of these definitions. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Adapters

universe u

/-! ## Serre's multiplicity -/

/-- The ideal of the subvariety `closure {u}` in the local ring `𝒪_{X,z}`: when `u ⤳ z`, the
prime of `𝒪_{X,z}` whose point of `Spec 𝒪_{X,z}` maps to `u`; otherwise the unit ideal, so that
the quotient `𝒪_{X,z}/𝔭_u` is the stalk at `z` of the reduced subscheme `closure {u}` in both
cases.
Source: Mathlib, `AlgebraicGeometry.Scheme.fromSpecStalk` and `range_fromSpecStalk`
(Stacks Project, Tag 01J7); Hartshorne, *Algebraic Geometry*, II, Exercise 3.11 (closed
subschemes and ideals of the local rings). -/
def a3i_stalkIdeal (X : Scheme.{u}) (z u : X) : Ideal (X.presheaf.stalk z) := by
  classical
  exact if h : ∃ p : Spec (X.presheaf.stalk z), X.fromSpecStalk z p = u then
    (show PrimeSpectrum (X.presheaf.stalk z) from Classical.choose h).asIdeal
  else ⊤

example (X : Scheme.{u}) (z u : X) (h : ¬ ∃ p : Spec (X.presheaf.stalk z), X.fromSpecStalk z p = u) :
    a3i_stalkIdeal X z u = ⊤ := by
  simp [a3i_stalkIdeal, h]

/-- `Tor_i^{𝒪_{X,z}}(𝒪_{X,z}/𝔭_u, 𝒪_{X,z}/𝔭_v)`, Mathlib's `Tor` in the category of
`𝒪_{X,z}`-modules (derived in the second variable).
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, the modules
`Tor_i^A(M, N)`; Mathlib, `CategoryTheory.Tor`. -/
def a3i_torModule (X : Scheme.{u}) (z u v : X) (i : ℕ) : ModuleCat.{u} (X.presheaf.stalk z) :=
  ((Tor (ModuleCat.{u} (X.presheaf.stalk z)) i).obj
    (ModuleCat.of _ (X.presheaf.stalk z ⧸ a3i_stalkIdeal X z u))).obj
    (ModuleCat.of _ (X.presheaf.stalk z ⧸ a3i_stalkIdeal X z v))

example (X : Scheme.{u}) (z u v : X) : ModuleCat.{u} (X.presheaf.stalk z) :=
  a3i_torModule X z u v 0

/-- Serre's intersection multiplicity of `closure {u}` and `closure {v}` along `closure {z}`:
`Σ_{i=0}^{dim 𝒪_{X,z}} (-1)^i length Tor_i^{𝒪_{X,z}}(𝒪_{X,z}/𝔭_u, 𝒪_{X,z}/𝔭_v)`, with
`dim 𝒪_{X,z}` the coheight of `z`. On a regular local ring `Tor_i` vanishes above the dimension,
so the sum is Serre's alternating sum.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, definition of
`i(X, V·W, Z)`; Fulton, *Intersection Theory*, second edition, §20.4 (Serre's Tor formula). -/
def a3i_serreMult (X : Scheme.{u}) (z u v : X) : ℤ :=
  ∑ i ∈ Finset.range ((Order.coheight z).toNat + 1),
    (-1 : ℤ) ^ i * ((Module.length (X.presheaf.stalk z) (a3i_torModule X z u v i)).toNat : ℤ)

example (X : Scheme.{u}) (z u v : X) :
    a3i_serreMult X z u v = ∑ i ∈ Finset.range ((Order.coheight z).toNat + 1),
      (-1 : ℤ) ^ i * ((Module.length (X.presheaf.stalk z) (a3i_torModule X z u v i)).toNat : ℤ) :=
  rfl

/-! ## The intersection cycle -/

/-- `closure {u}` and `closure {v}` meet properly: every irreducible component of their
scheme-theoretic intersection has codimension `codim u + codim v`. An empty intersection is
proper. This is the first condition of `hc9k_transverseLocus`.
Source: Fulton, *Intersection Theory*, second edition, §7.1 (proper intersection);
Serre, *Algèbre locale, multiplicités*, Chapitre V. -/
def a3i_MeetProperly (X : Scheme.{u}) (u v : X) : Prop :=
  ∀ w : (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme,
    closure ({w} : Set (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme) ∈
      irreducibleComponents (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme →
    Order.coheight ((ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι w) =
      Order.coheight u + Order.coheight v

example (X : Scheme.{u}) (u v : X) (h : a3i_MeetProperly X u v)
    (w : (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme)
    (hw : closure ({w} : Set (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme) ∈
      irreducibleComponents (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme) :
    Order.coheight ((ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι w) =
      Order.coheight u + Order.coheight v :=
  h w hw

/-- Two cycles meet properly when every pair of their components does.
Source: Fulton, *Intersection Theory*, second edition, §7.1 and §8.2. -/
def a3i_CyclesMeetProperly (X : Scheme.{u}) {R : Type*} [Zero R] (c d : AlgebraicCycle X R) :
    Prop :=
  ∀ u v, c u ≠ 0 → d v ≠ 0 → a3i_MeetProperly X u v

example (X : Scheme.{u}) (d : AlgebraicCycle X ℚ) : a3i_CyclesMeetProperly X 0 d :=
  fun _ _ h => (h rfl).elim

/-- The intersection cycle of two prime cycles: each irreducible component `closure {w}` of the
scheme-theoretic intersection of `closure {u}` and `closure {v}` carries Serre's multiplicity
`a3i_serreMult X w u v`. The index set is that of `ccm11_intersectionCycle`, which carries the
length of `𝒪_{X,w}/(𝔭_u + 𝔭_v)` instead.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, the product
`V · W = Σ i(Z) Z`; Fulton, *Intersection Theory*, second edition, §8.2 and §20.4. -/
def a3i_intersectPrime (X : Scheme.{u}) (u v : X) : AlgebraicCycle X ℚ := by
  classical
  exact ∑ᶠ y : (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme,
    if closure ({y} : Set (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme then
      Function.locallyFinsuppWithin.single
        ((ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι y)
        ((a3i_serreMult X ((ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι y) u v : ℤ) :
          ℚ)
    else 0

example (X : Scheme.{u}) (u v : X) : AlgebraicCycle X ℚ := a3i_intersectPrime X u v

/-- The intersection product of two rational cycles, the bilinear extension of
`a3i_intersectPrime`. It is the intersection product when the two cycles meet properly on a
smooth variety; otherwise it is only a cycle supported on the intersection.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V (bilinear extension);
Fulton, *Intersection Theory*, second edition, §8.2. -/
def a3i_intersect (X : Scheme.{u}) (c d : AlgebraicCycle X ℚ) : AlgebraicCycle X ℚ :=
  ∑ᶠ u : X, ∑ᶠ v : X, (a3i_intersectPrime X u v).mapRange (c u * d v * ·) (mul_zero _)

example (X : Scheme.{u}) (c d : AlgebraicCycle X ℚ) :
    a3i_intersect X c d =
      ∑ᶠ u : X, ∑ᶠ v : X, (a3i_intersectPrime X u v).mapRange (c u * d v * ·) (mul_zero _) :=
  rfl

/-- The fundamental cycle `[X]` of an irreducible scheme: its generic point with coefficient
`1`.
Source: Fulton, *Intersection Theory*, second edition, §1.5, the cycle `[X]`. -/
def a3i_fundamental (X : Scheme.{u}) [IrreducibleSpace X] : AlgebraicCycle X ℚ := by
  classical
  exact Function.locallyFinsuppWithin.single (genericPoint X) 1

example (X : Scheme.{u}) [IrreducibleSpace X] : a3i_fundamental X (genericPoint X) = 1 := by
  classical
  simp [a3i_fundamental]

/-! ## Cohen–Macaulay quotients -/

/-- The quotient `A/𝔭` of a local ring is Cohen–Macaulay as an `A`-module: some sequence of
elements of the maximal ideal of length `dim A/𝔭` is weakly regular on `A/𝔭`. For `𝔭 = ⊤`
this fails, since the Krull dimension of the zero ring is `⊥`.
Source: Matsumura, *Commutative Ring Theory*, §17 (depth and Cohen–Macaulay modules;
depth is at most dimension); Bruns–Herzog, *Cohen–Macaulay Rings*,
Definition 2.1.1. -/
def a3i_IsCMQuotient {A : Type*} [CommRing A] [IsLocalRing A] (𝔭 : Ideal A) : Prop :=
  ∃ rs : List A, (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal A) ∧
    RingTheory.Sequence.IsWeaklyRegular (A ⧸ 𝔭) rs ∧
    (rs.length : WithBot ℕ∞) = ringKrullDim (A ⧸ 𝔭)

example {A : Type*} [CommRing A] [IsLocalRing A] (𝔭 : Ideal A) (h : a3i_IsCMQuotient 𝔭) :
    ∃ n : ℕ, (n : WithBot ℕ∞) = ringKrullDim (A ⧸ 𝔭) :=
  let ⟨rs, _, _, hrs⟩ := h
  ⟨rs.length, hrs⟩

/-! ## Codimension and the total Chow group -/

/-- The cycles of pure codimension `p`: every point with a nonzero coefficient has coheight
`p`.
Source: Fulton, *Intersection Theory*, second edition, §1.3 and §8.3, the group `Z^p X`. -/
def a3i_codimCycles (X : Scheme.{u}) (R : Type*) [Ring R] (p : ℕ) :
    AddSubgroup (AlgebraicCycle X R) where
  carrier := {c | ∀ x, c x ≠ 0 → Order.coheight x = p}
  add_mem' {c d} hc hd x hx := by
    by_cases h : c x = 0
    · exact hd x (by simpa [h] using hx)
    · exact hc x h
  zero_mem' x hx := (hx rfl).elim
  neg_mem' {c} hc x hx := hc x (by simpa using hx)

example (X : Scheme.{u}) (p : ℕ) : (0 : AlgebraicCycle X ℚ) ∈ a3i_codimCycles X ℚ p :=
  (a3i_codimCycles X ℚ p).zero_mem

/-- The rational cycles rationally equivalent to zero, in all dimensions: the sum over `k` of
A2's `a2_ratEquivDim X ℚ k`.
Source: Fulton, *Intersection Theory*, second edition, §1.3, `Rat_* X = ⊕_k Rat_k X`. -/
def a3i_ratAll (X : Scheme.{u}) [IsLocallyNoetherian X] : AddSubgroup (AlgebraicCycle X ℚ) :=
  ⨆ k : ℕ, a2_ratEquivDim X ℚ k

example (X : Scheme.{u}) [IsLocallyNoetherian X] (k : ℕ) :
    a2_ratEquivDim X ℚ k ≤ a3i_ratAll X :=
  le_iSup (fun k : ℕ => a2_ratEquivDim X ℚ k) k

/-- The total rational Chow group `A_*(X)_ℚ = Z_*(X)_ℚ / Rat_*(X)_ℚ`, all dimensions together;
on a smooth variety of dimension `n` its codimension-`p` part is `CH^p X = A_{n-p} X`.
Source: Fulton, *Intersection Theory*, second edition, §1.3 and §8.3 (the ring `A^* X`). -/
abbrev a3i_ChowTotal (X : Scheme.{u}) [IsLocallyNoetherian X] :=
  AlgebraicCycle X ℚ ⧸ a3i_ratAll X

example (X : Scheme.{u}) [IsLocallyNoetherian X] : AddCommGroup (a3i_ChowTotal X) :=
  inferInstance

/-- The product on the total Chow group: for classes `a`, `b`, choose cycles `α`, `β` that
represent them and meet properly, and take the class of `a3i_intersect X α β`; when no such pair
exists, `0`. The moving lemma and the independence statement of the frozen spec make this the
intersection product of Fulton, Chapter 8.
Source: Fulton, *Intersection Theory*, second edition, §8.3 and §11.4 (Chow's moving
lemma route); Serre, *Algèbre locale, multiplicités*, Chapitre V. -/
def a3i_chowMul (X : Scheme.{u}) [IsLocallyNoetherian X] (a b : a3i_ChowTotal X) :
    a3i_ChowTotal X := by
  classical
  exact if h : ∃ αβ : AlgebraicCycle X ℚ × AlgebraicCycle X ℚ,
      (QuotientAddGroup.mk αβ.1 : a3i_ChowTotal X) = a ∧
        (QuotientAddGroup.mk αβ.2 : a3i_ChowTotal X) = b ∧
        a3i_CyclesMeetProperly X αβ.1 αβ.2 then
    QuotientAddGroup.mk (a3i_intersect X (Classical.choose h).1 (Classical.choose h).2)
  else 0

example (X : Scheme.{u}) [IsLocallyNoetherian X] (a b : a3i_ChowTotal X) : a3i_ChowTotal X :=
  a3i_chowMul X a b

end HodgeLean.Adapters
