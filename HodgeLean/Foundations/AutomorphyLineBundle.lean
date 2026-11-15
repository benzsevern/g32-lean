import HodgeLean.Foundations.AutomorphyLineBundleProofs

/-! # The line bundle of a factor of automorphy (FROZEN SPEC)

Scope. This module specifies the descent step of the Appell--Humbert route (stage 1 of 3): from a
factor of automorphy `a : L → V → ℂ` on a subgroup `L` of a complex normed space `V` to the sheaf
`L(a)` of its sections on the quotient `V ⧸ L`. The sections over `U` are the holomorphic
functions `f` on the preimage of `U` with `f (x + l) = a l x * f x` (`sectionsOn`). Claimed:
* `L(a)` is a sheaf on `V ⧸ L`, for every `a` (gluing);
* the implication from the cocycle identity and holomorphy of `a` to local triviality: over the
  image of an open `W ⊆ V` whose `L`-translates are disjoint, restriction to `W` identifies the
  sections with the holomorphic functions on `W`, and for discrete `L` such `W` cover `V`;
* multiplication of sections lands in `L(a * b)`, and a nowhere-vanishing section of `L(a)`
  identifies `L(b)` with `L(a * b)` (the local form of `L(a·b) ≅ L(a) ⊗ L(b)`);
* `L(1)` is the structure sheaf of `V ⧸ L` (invariant functions descend), and a coboundary factor
  `h (v + l) / h v` gives a bundle isomorphic to `L(1)`;
* falsification: where the cocycle identity fails, every section vanishes; for holomorphic `a`
  failing it at one point, `L(a)` has no nonzero section over any open set; the constant factor `2`
  has none at all;
* instances for the holomorphic Appell--Humbert factor `holFactor D`: global sections of
  `L(holFactor D)` are the theta functions `sections D`, and `L(holFactor D)` is locally trivial.

Not claimed: a total space or `FiberBundle` structure, a complex-manifold structure on `V ⧸ L`
beyond the structure sheaf `structureSheafOn`, a sheaf-of-modules tensor product, the analytic
Picard group or the exponential sequence, the first Chern class (stage 2), algebraization by GAGA
or ampleness (stage 3), and the dimension of the space of theta functions.
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.AutomorphyLineBundle

open AppellHumbert

universe u

section General

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V] (L : Submodule ℤ V)

/-- The sections of `L(a)` form a sheaf of sets on `V ⧸ L`, for every factor `a`: holomorphy and
the functional equation are both local on the preimage, which the preimages of a cover cover.
Source: Mumford, *Abelian Varieties*, 2nd ed., Ch. I, §2, and Hartshorne, *Algebraic Geometry*,
Ch. II, §1 (sheaf axioms). -/
theorem spec_presheaf_isSheaf (a : L → V → ℂ) : TopCat.Presheaf.IsSheaf (presheaf L a) :=
  spec_presheaf_isSheaf_aux L a

example (a : L → V → ℂ) : TopCat.Presheaf.IsSheaf (presheaf L a) := spec_presheaf_isSheaf L a

/-- The product of a section of `L(a)` and a section of `L(b)` is a section of `L(a * b)`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.1 (factors multiply under
tensor product). -/
theorem spec_sectionsOn_mul (a b : L → V → ℂ) (U : Set (Torus L))
    (f g : proj L ⁻¹' U → ℂ) (hf : f ∈ sectionsOn L a U) (hg : g ∈ sectionsOn L b U) :
    f * g ∈ sectionsOn L (a * b) U :=
  spec_sectionsOn_mul_aux L a b U f g hf hg

example (a b : L → V → ℂ) (U : Set (Torus L))
    (f g : proj L ⁻¹' U → ℂ) (hf : f ∈ sectionsOn L a U) (hg : g ∈ sectionsOn L b U) :
    f * g ∈ sectionsOn L (a * b) U :=
  spec_sectionsOn_mul L a b U f g hf hg

/-- A nowhere-vanishing section `s` of `L(a)` over `U` makes multiplication by `s` an isomorphism
from the sections of `L(b)` to those of `L(a * b)`; the inverse divides by `s`. This is the local
form of `L(a * b) ≅ L(a) ⊗ L(b)`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.1. -/
theorem spec_mulEquiv_of_ne_zero (a b : L → V → ℂ) (U : Set (Torus L))
    (s : proj L ⁻¹' U → ℂ) (hs : s ∈ sectionsOn L a U) (hs₀ : ∀ x, s x ≠ 0) :
    ∃ e : sectionsOn L b U ≃ₗ[ℂ] sectionsOn L (a * b) U,
      ∀ g x, (e g : proj L ⁻¹' U → ℂ) x = s x * (g : proj L ⁻¹' U → ℂ) x :=
  spec_mulEquiv_of_ne_zero_aux L a b U s hs hs₀

example (a b : L → V → ℂ) (U : Set (Torus L))
    (s : proj L ⁻¹' U → ℂ) (hs : s ∈ sectionsOn L a U) (hs₀ : ∀ x, s x ≠ 0) :
    ∃ e : sectionsOn L b U ≃ₗ[ℂ] sectionsOn L (a * b) U,
      ∀ g x, (e g : proj L ⁻¹' U → ℂ) x = s x * (g : proj L ⁻¹' U → ℂ) x :=
  spec_mulEquiv_of_ne_zero L a b U s hs hs₀

/-- For a discrete subgroup `L`, every point of `V` has an open neighbourhood whose
`L`-translates are pairwise disjoint, so the images of such sets cover `V ⧸ L`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; Mathlib's
`AddSubgroup.isAddQuotientCoveringMap_of_comm`. -/
theorem spec_exists_disjoint_nhds [DiscreteTopology L] (v : V) :
    ∃ W : Set V, IsOpen W ∧ v ∈ W ∧
      ∀ l : L, ((· + (l : V)) '' W ∩ W).Nonempty → l = 0 :=
  spec_exists_disjoint_nhds_aux L v

example [DiscreteTopology L] (v : V) :
    ∃ W : Set V, IsOpen W ∧ v ∈ W ∧
      ∀ l : L, ((· + (l : V)) '' W ∩ W).Nonempty → l = 0 :=
  spec_exists_disjoint_nhds L v

/-- Local triviality. For a holomorphic factor satisfying the cocycle identity, normalized by
`a 0 v = 1` (without it `a ≡ 0` satisfies the cocycle and has no nonzero section), and an open
`W ⊆ V` with disjoint `L`-translates, restriction to `W` is an isomorphism from the sections of
`L(a)` over `proj '' W` to the holomorphic functions on `W`; the inverse sends `g` to
`w + l ↦ a l w * g w`. Applied to the open subsets of `W`, it identifies `L(a)` with the structure
sheaf over `proj '' W`.
Source: Mumford, *Abelian Varieties*, 2nd ed., Ch. I, §2, and Birkenhake--Lange, *Complex
Abelian Varieties*, 2nd ed., §2.1. -/
theorem spec_restrictEquiv_of_disjoint (a : L → V → ℂ)
    (hcoc : ∀ (l m : L) (v : V), a (l + m) v = a l (v + m) * a m v)
    (ha₀ : ∀ v, a 0 v = 1)
    (hhol : ∀ l, Differentiable ℂ (a l)) (W : Set V) (hW : IsOpen W)
    (hdisj : ∀ l : L, ((· + (l : V)) '' W ∩ W).Nonempty → l = 0) :
    ∃ e : sectionsOn L a (proj L '' W) ≃ₗ[ℂ] holomorphicOn W,
      ∀ f (w : W), (e f : W → ℂ) w =
        (f : proj L ⁻¹' (proj L '' W) → ℂ) ⟨w, Set.mem_image_of_mem _ w.2⟩ :=
  spec_restrictEquiv_of_disjoint_aux L a hcoc ha₀ hhol W hW hdisj

example (a : L → V → ℂ)
    (hcoc : ∀ (l m : L) (v : V), a (l + m) v = a l (v + m) * a m v)
    (ha₀ : ∀ v, a 0 v = 1)
    (hhol : ∀ l, Differentiable ℂ (a l)) (W : Set V) (hW : IsOpen W)
    (hdisj : ∀ l : L, ((· + (l : V)) '' W ∩ W).Nonempty → l = 0) :
    ∃ e : sectionsOn L a (proj L '' W) ≃ₗ[ℂ] holomorphicOn W,
      ∀ f (w : W), (e f : W → ℂ) w =
        (f : proj L ⁻¹' (proj L '' W) → ℂ) ⟨w, Set.mem_image_of_mem _ w.2⟩ :=
  spec_restrictEquiv_of_disjoint L a hcoc ha₀ hhol W hW hdisj

/-- The trivial factor gives the structure sheaf: an `L`-invariant holomorphic function on the
preimage of `U` descends to a holomorphic function on `U`, and conversely.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and §2.1. -/
theorem spec_one_equiv_structureSheaf (U : Set (Torus L)) :
    ∃ e : sectionsOn L 1 U ≃ₗ[ℂ] structureSheafOn L U,
      ∀ f (x : proj L ⁻¹' U), (e f : U → ℂ) ⟨proj L x, x.2⟩ = (f : proj L ⁻¹' U → ℂ) x :=
  spec_one_equiv_structureSheaf_aux L U

example (U : Set (Torus L)) :
    ∃ e : sectionsOn L 1 U ≃ₗ[ℂ] structureSheafOn L U,
      ∀ f (x : proj L ⁻¹' U), (e f : U → ℂ) ⟨proj L x, x.2⟩ = (f : proj L ⁻¹' U → ℂ) x :=
  spec_one_equiv_structureSheaf L U

/-- A coboundary factor `a l v = h (v + l) / h v`, for `h` holomorphic and nowhere zero, gives a
bundle isomorphic to the trivial one: multiplication by `h` sends sections of `L(1)` to sections
of `L(a)`, over every `U`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.1 (equivalent factors give
isomorphic bundles). -/
theorem spec_coboundary_equiv_one (a : L → V → ℂ) (h : V → ℂ) (hh : Differentiable ℂ h)
    (hh₀ : ∀ v, h v ≠ 0) (ha : ∀ (l : L) (v : V), a l v = h (v + l) / h v)
    (U : Set (Torus L)) :
    ∃ e : sectionsOn L 1 U ≃ₗ[ℂ] sectionsOn L a U,
      ∀ f (x : proj L ⁻¹' U), (e f : proj L ⁻¹' U → ℂ) x = h x * (f : proj L ⁻¹' U → ℂ) x :=
  spec_coboundary_equiv_one_aux L a h hh hh₀ ha U

example (a : L → V → ℂ) (h : V → ℂ) (hh : Differentiable ℂ h)
    (hh₀ : ∀ v, h v ≠ 0) (ha : ∀ (l : L) (v : V), a l v = h (v + l) / h v)
    (U : Set (Torus L)) :
    ∃ e : sectionsOn L 1 U ≃ₗ[ℂ] sectionsOn L a U,
      ∀ f (x : proj L ⁻¹' U), (e f : proj L ⁻¹' U → ℂ) x = h x * (f : proj L ⁻¹' U → ℂ) x :=
  spec_coboundary_equiv_one L a h hh hh₀ ha U

/-- Falsification, pointwise: a section vanishes at every point where the cocycle identity fails,
because translating by `l + m` in one step or in two steps must give the same value.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.1. -/
theorem spec_section_eq_zero_of_cocycle_failure (a : L → V → ℂ) (U : Set (Torus L))
    (f : proj L ⁻¹' U → ℂ) (hf : f ∈ sectionsOn L a U) (l m : L) (x : proj L ⁻¹' U)
    (hfail : a (l + m) x ≠ a l ((x : V) + m) * a m x) : f x = 0 :=
  spec_section_eq_zero_of_cocycle_failure_aux L a U f hf l m x hfail

example (a : L → V → ℂ) (U : Set (Torus L))
    (f : proj L ⁻¹' U → ℂ) (hf : f ∈ sectionsOn L a U) (l m : L) (x : proj L ⁻¹' U)
    (hfail : a (l + m) x ≠ a l ((x : V) + m) * a m x) : f x = 0 :=
  spec_section_eq_zero_of_cocycle_failure L a U f hf l m x hfail

/-- Falsification: a holomorphic factor that fails the cocycle identity at a single point has no
nonzero section over any open set. The defect is holomorphic and not identically zero, so it
vanishes only on a set with empty interior (identity theorem), and a section is zero off that set.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.1, and Gunning--Rossi,
*Analytic Functions of Several Complex Variables*, Ch. I, §A (identity theorem). -/
theorem spec_sectionsOn_eq_bot_of_cocycle_failure (a : L → V → ℂ)
    (hhol : ∀ l, Differentiable ℂ (a l))
    (hfail : ∃ (l m : L) (v : V), a (l + m) v ≠ a l (v + m) * a m v)
    (U : Set (Torus L)) (hU : IsOpen U) : sectionsOn L a U = ⊥ :=
  spec_sectionsOn_eq_bot_of_cocycle_failure_aux L a hhol hfail U hU

example (a : L → V → ℂ) (hhol : ∀ l, Differentiable ℂ (a l))
    (hfail : ∃ (l m : L) (v : V), a (l + m) v ≠ a l (v + m) * a m v)
    (U : Set (Torus L)) (hU : IsOpen U) : sectionsOn L a U = ⊥ :=
  spec_sectionsOn_eq_bot_of_cocycle_failure L a hhol hfail U hU

/-- Falsification, concretely: the constant factor `2` fails the cocycle identity at `l = m = 0`
(`2 ≠ 2 * 2`), and `L(2)` has no nonzero section over any set.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.1. -/
theorem spec_constTwo_sections_eq_bot (U : Set (Torus L)) :
    sectionsOn L (fun _ _ ↦ 2) U = ⊥ :=
  spec_constTwo_sections_eq_bot_aux L U

example (U : Set (Torus L)) : sectionsOn L (fun _ _ ↦ 2) U = ⊥ :=
  spec_constTwo_sections_eq_bot L U

end General

section AppellHumbert

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The global sections of the bundle of the holomorphic Appell--Humbert factor are exactly the
theta functions `sections D` of the frozen sections spec.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.2 and §3.1. -/
theorem spec_appellHumbert_globalSections (D : Datum (V := V)) :
    ∃ e : sectionsOn D.lattice (holFactor D) Set.univ ≃ₗ[ℂ] sections D,
      ∀ f (v : V), (e f : V → ℂ) v =
        (f : proj D.lattice ⁻¹' Set.univ → ℂ) ⟨v, Set.mem_univ _⟩ :=
  spec_appellHumbert_globalSections_aux D

example (D : Datum (V := V)) :
    ∃ e : sectionsOn D.lattice (holFactor D) Set.univ ≃ₗ[ℂ] sections D,
      ∀ f (v : V), (e f : V → ℂ) v =
        (f : proj D.lattice ⁻¹' Set.univ → ℂ) ⟨v, Set.mem_univ _⟩ :=
  spec_appellHumbert_globalSections D

/-- The bundle of the holomorphic Appell--Humbert factor is locally trivial: over the image of an
open `W` with disjoint lattice translates, restriction to `W` identifies its sections with the
holomorphic functions on `W`. The inputs are `spec_holFactor_cocycle` and holomorphy of
`holFactor D l`, which is affine-exponential in `v`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.2 and Theorem 2.2.3. -/
theorem spec_appellHumbert_restrictEquiv (D : Datum (V := V)) (W : Set V) (hW : IsOpen W)
    (hdisj : ∀ l : D.lattice, ((· + (l : V)) '' W ∩ W).Nonempty → l = 0) :
    ∃ e : sectionsOn D.lattice (holFactor D) (proj D.lattice '' W) ≃ₗ[ℂ] holomorphicOn W,
      ∀ f (w : W), (e f : W → ℂ) w =
        (f : proj D.lattice ⁻¹' (proj D.lattice '' W) → ℂ) ⟨w, Set.mem_image_of_mem _ w.2⟩ :=
  spec_appellHumbert_restrictEquiv_aux D W hW hdisj

example (D : Datum (V := V)) (W : Set V) (hW : IsOpen W)
    (hdisj : ∀ l : D.lattice, ((· + (l : V)) '' W ∩ W).Nonempty → l = 0) :
    ∃ e : sectionsOn D.lattice (holFactor D) (proj D.lattice '' W) ≃ₗ[ℂ] holomorphicOn W,
      ∀ f (w : W), (e f : W → ℂ) w =
        (f : proj D.lattice ⁻¹' (proj D.lattice '' W) → ℂ) ⟨w, Set.mem_image_of_mem _ w.2⟩ :=
  spec_appellHumbert_restrictEquiv D W hW hdisj

end AppellHumbert

end HodgeLean.Foundations.AutomorphyLineBundle
