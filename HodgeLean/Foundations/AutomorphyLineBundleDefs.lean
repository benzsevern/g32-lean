import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Sheaves.Presheaf
import HodgeLean.Foundations.AppellHumbertSectionsDefs

/-! # Definitions for the factor-of-automorphy line bundle spec (FROZEN)

This file is part of the frozen factor-of-automorphy descent spec. Do not edit it.
HC no distance; AV milestone no distance.

A factor of automorphy is an arbitrary function `a : L → V → ℂ` on a subgroup `L` of a complex
normed space `V`; no cocycle identity, holomorphy or nonvanishing is built in, so that the
statements can take them as explicit hypotheses and the falsification checks can drop them.
The sections of the descended bundle `L(a)` over a set `U` of the quotient `V ⧸ L` are the
functions on the preimage of `U` that are restrictions of a function holomorphic on that preimage
and satisfy `f (x + l) = a l x * f x`.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace HodgeLean.Foundations.AutomorphyLineBundle

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V] (L : Submodule ℤ V)

/-- The quotient `V ⧸ L` of `V` by the subgroup `L`, acting by translation. For a full lattice
it is the complex torus `X = V/Λ`.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
abbrev Torus : Type u := V ⧸ L.toAddSubgroup

/-- The projection `V → V ⧸ L`.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
abbrev proj : V → Torus L := QuotientAddGroup.mk

example (v : V) : proj L v = (v : V ⧸ L.toAddSubgroup) := rfl

omit [NormedSpace ℂ V] in
/-- Translation by a point of `L` does not move the projection.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
theorem proj_add (v : V) (l : L) : proj L (v + l) = proj L v := by
  rw [proj, QuotientAddGroup.eq]
  simp

example (v : V) (l : L) : proj L (v + l) = proj L v := proj_add L v l

/-- The holomorphic functions on a set `S ⊆ V`: functions on `S` that are restrictions of a
function `V → ℂ` which is complex differentiable on `S`. For open `S` this is the space of
holomorphic functions on `S`.

Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, Ch. I, §A. -/
def holomorphicOn (S : Set V) : Submodule ℂ (S → ℂ) where
  carrier := {g | ∃ G : V → ℂ, DifferentiableOn ℂ G S ∧ ∀ x : S, g x = G x}
  zero_mem' := ⟨0, differentiableOn_const 0, fun _ ↦ rfl⟩
  add_mem' := fun {f g} ⟨F, hF, hf⟩ ⟨G, hG, hg⟩ ↦
    ⟨F + G, hF.add hG, fun x ↦ by simp [hf x, hg x]⟩
  smul_mem' := fun c f ⟨F, hF, hf⟩ ↦
    ⟨c • F, hF.const_smul c, fun x ↦ by simp [hf x]⟩

example (S : Set V) (g : S → ℂ) : g ∈ holomorphicOn S ↔
    ∃ G : V → ℂ, DifferentiableOn ℂ G S ∧ ∀ x : S, g x = G x := Iff.rfl

/-- Translation by `l ∈ L`, as a self-map of the preimage of `U ⊆ V ⧸ L`.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
def shift {U : Set (Torus L)} (l : L) (x : proj L ⁻¹' U) : proj L ⁻¹' U :=
  ⟨(x : V) + l, by
    change proj L ((x : V) + l) ∈ U
    rw [proj_add]; exact x.2⟩

example {U : Set (Torus L)} (l : L) (x : proj L ⁻¹' U) :
    (shift L l x : V) = (x : V) + l := rfl

/-- The sections over `U ⊆ V ⧸ L` of the line bundle `L(a)` descended from a factor of automorphy
`a`: holomorphic functions `f` on the preimage of `U` with `f (x + l) = a l x * f x` for every
`l ∈ L`. The pairs `(x, f x)` modulo `(x, t) ∼ (x + l, a l x * t)` are the points of the total
space `(V × ℂ)/L`; this file only records the sections.

Source: Mumford, *Abelian Varieties*, 2nd ed., Ch. I, §2, and Birkenhake--Lange, *Complex Abelian
Varieties*, 2nd ed., §2.1 (factors of automorphy). -/
def sectionsOn (a : L → V → ℂ) (U : Set (Torus L)) : Submodule ℂ (proj L ⁻¹' U → ℂ) where
  carrier := {f | f ∈ holomorphicOn (proj L ⁻¹' U) ∧
    ∀ (l : L) (x : proj L ⁻¹' U), f (shift L l x) = a l x * f x}
  zero_mem' := ⟨(holomorphicOn _).zero_mem, fun _ _ ↦ by simp⟩
  add_mem' := fun {f g} hf hg ↦ ⟨(holomorphicOn _).add_mem hf.1 hg.1, fun l x ↦ by
    simp only [Pi.add_apply, hf.2 l x, hg.2 l x, mul_add]⟩
  smul_mem' := fun c f hf ↦ ⟨(holomorphicOn _).smul_mem c hf.1, fun l x ↦ by
    simp only [Pi.smul_apply, smul_eq_mul, hf.2 l x]; ring⟩

example (a : L → V → ℂ) (U : Set (Torus L)) (f : proj L ⁻¹' U → ℂ) :
    f ∈ sectionsOn L a U ↔ f ∈ holomorphicOn (proj L ⁻¹' U) ∧
      ∀ (l : L) (x : proj L ⁻¹' U), f (shift L l x) = a l x * f x := Iff.rfl

/-- Restriction of sections of `L(a)` from `U` to a subset `U' ⊆ U`.

Source: Mumford, *Abelian Varieties*, 2nd ed., Ch. I, §2. -/
def restrict (a : L → V → ℂ) {U U' : Set (Torus L)} (h : U' ⊆ U) :
    sectionsOn L a U →ₗ[ℂ] sectionsOn L a U' :=
  (LinearMap.funLeft ℂ ℂ (Set.inclusion (Set.preimage_mono h))).restrict fun f hf ↦ by
    obtain ⟨⟨F, hF, hfF⟩, heq⟩ := hf
    exact ⟨⟨F, hF.mono (Set.preimage_mono h), fun x ↦ hfF _⟩, fun l x ↦ heq l (Set.inclusion _ x)⟩

example (a : L → V → ℂ) {U U' : Set (Torus L)} (h : U' ⊆ U) (f : sectionsOn L a U)
    (x : proj L ⁻¹' U') :
    (restrict L a h f : proj L ⁻¹' U' → ℂ) x = (f : proj L ⁻¹' U → ℂ) ⟨x, Set.preimage_mono h x.2⟩ :=
  rfl

/-- The presheaf of sets `U ↦ L(a)(U)` on the quotient `V ⧸ L`, with restriction of functions.

Source: Mumford, *Abelian Varieties*, 2nd ed., Ch. I, §2. -/
def presheaf (a : L → V → ℂ) : TopCat.Presheaf (Type u) (TopCat.of (Torus L)) where
  obj U := sectionsOn L a (U.unop : Set (Torus L))
  map i := TypeCat.ofHom (restrict L a (leOfHom i.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

example (a : L → V → ℂ) (U : (Opens (TopCat.of (Torus L)))ᵒᵖ) :
    (presheaf L a).obj U = sectionsOn L a (U.unop : Set (Torus L)) := rfl

/-- Pullback of a function on `U ⊆ V ⧸ L` to the preimage of `U`.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
def pullback (U : Set (Torus L)) : (U → ℂ) →ₗ[ℂ] (proj L ⁻¹' U → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun x ↦ ⟨proj L x, x.2⟩

example (U : Set (Torus L)) (g : U → ℂ) (x : proj L ⁻¹' U) :
    pullback L U g x = g ⟨proj L x, x.2⟩ := rfl

/-- The structure sheaf of the quotient: a function on `U ⊆ V ⧸ L` is holomorphic when its
pullback to the preimage of `U` is holomorphic. This is the complex structure for which the
projection is a local biholomorphism.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
def structureSheafOn (U : Set (Torus L)) : Submodule ℂ (U → ℂ) :=
  (holomorphicOn (proj L ⁻¹' U)).comap (pullback L U)

example (U : Set (Torus L)) (g : U → ℂ) :
    g ∈ structureSheafOn L U ↔ pullback L U g ∈ holomorphicOn (proj L ⁻¹' U) := Iff.rfl

end HodgeLean.Foundations.AutomorphyLineBundle
