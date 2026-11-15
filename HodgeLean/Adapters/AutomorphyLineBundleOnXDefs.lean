import HodgeLean.Adapters.AutomorphyChernHQDefs
import HodgeLean.Foundations.AutomorphyLineBundleDefs

/-! # The line bundle of a factor of automorphy on `X(ℂ)`: definitions (FROZEN)

For a smooth projective integral complex group `X` with S12 period lattice
`Λ = abelianPeriodLattice X ⊆ ℂ^g`, `g = dim X.left`, and exponential `exp : ℂ^g → X(ℂ)`, the
sections over `U ⊆ X(ℂ)` of the bundle `L(a)` of a factor of automorphy `a : Λ → ℂ^g → ℂ` are the
holomorphic functions `f` on `exp⁻¹(U)` with `f (x + l) = a l x * f x`. This is the stage-1 sheaf
`AutomorphyLineBundle.sectionsOn` on `ℂ^g ⧸ Λ`, moved to `X(ℂ)` along the S12 uniformization. The
holomorphic functions on `U ⊆ X(ℂ)` are those of upstream's complex-manifold structure. No
cocycle identity, holomorphy or nonvanishing is built into `a`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open scoped Manifold CategoryTheory.MonObj

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- The S12 exponential `ℂ^g → X(ℂ)`, `g = dim X.left`, as a map to the complex points, with the
commutativity that S12 derives from properness and integrality (as in `abelianPeriodLattice`).

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; S12 `complexExponential`. -/
def abelianExp (v : Fin (dim X.left) → ℂ) : ComplexPoint X :=
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  (complexExponential X (dim X.left) v).toMul

example (v : Fin (dim X.left) → ℂ) (hv : v ∈ abelianPeriodLattice X) :
    abelianExp X v = 1 := by
  have h : complexExponential X (dim X.left) v = 0 := hv
  simp only [abelianExp, h]
  rfl

/-- The exponential is invariant under translation by the period lattice.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1; S12
`complexExponentialHom`, `complexExponentialLattice`. -/
theorem abelianExp_add_lattice (v : Fin (dim X.left) → ℂ) (l : abelianPeriodLattice X) :
    abelianExp X (v + l) = abelianExp X v := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  have hl : complexExponentialHom X (dim X.left) (l : Fin (dim X.left) → ℂ) = 0 := l.2
  change (complexExponentialHom X (dim X.left) (v + l)).toMul =
    (complexExponentialHom X (dim X.left) v).toMul
  rw [map_add, hl, add_zero]

example (v : Fin (dim X.left) → ℂ) (l : abelianPeriodLattice X) :
    abelianExp X (v + l) = abelianExp X v := abelianExp_add_lattice X v l

/-- The sections over `U ⊆ X(ℂ)` of the line bundle `L(a)` of a factor of automorphy
`a : Λ → ℂ^g → ℂ`: functions on `exp⁻¹(U)` that are restrictions of a function holomorphic on
`exp⁻¹(U)` and satisfy `f (x + l) = a l x * f x` for every `l ∈ Λ`.

Source: Mumford, *Abelian Varieties*, 2nd ed., Ch. I, §2, and Birkenhake–Lange, *Complex Abelian
Varieties*, 2nd ed., §1.1 and §2.1; `AutomorphyLineBundle.sectionsOn`. -/
def sectionsOnX (a : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (U : Set (ComplexPoint X)) : Submodule ℂ (abelianExp X ⁻¹' U → ℂ) where
  carrier := {f | f ∈ AutomorphyLineBundle.holomorphicOn (abelianExp X ⁻¹' U) ∧
    ∀ (l : abelianPeriodLattice X) (x : abelianExp X ⁻¹' U),
      f ⟨(x : Fin (dim X.left) → ℂ) + l, by
        change abelianExp X _ ∈ U
        rw [abelianExp_add_lattice]; exact x.2⟩ = a l x * f x}
  zero_mem' := ⟨(AutomorphyLineBundle.holomorphicOn _).zero_mem, fun _ _ ↦ by simp⟩
  add_mem' := fun {f g} hf hg ↦ ⟨(AutomorphyLineBundle.holomorphicOn _).add_mem hf.1 hg.1,
    fun l x ↦ by simp only [Pi.add_apply, hf.2 l x, hg.2 l x, mul_add]⟩
  smul_mem' := fun c f hf ↦ ⟨(AutomorphyLineBundle.holomorphicOn _).smul_mem c hf.1,
    fun l x ↦ by simp only [Pi.smul_apply, smul_eq_mul, hf.2 l x]; ring⟩

example (U : Set (ComplexPoint X)) :
    (0 : abelianExp X ⁻¹' U → ℂ) ∈ sectionsOnX X (fun _ _ ↦ 2) U :=
  (sectionsOnX X _ U).zero_mem

/-- Restriction of sections of `L(a)` on `X(ℂ)` from `U` to a subset `U' ⊆ U`.

Source: Mumford, *Abelian Varieties*, 2nd ed., Ch. I, §2. -/
def restrictX (a : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    {U U' : Set (ComplexPoint X)} (h : U' ⊆ U) :
    sectionsOnX X a U →ₗ[ℂ] sectionsOnX X a U' :=
  (LinearMap.funLeft ℂ ℂ (Set.inclusion (Set.preimage_mono h))).restrict fun f hf ↦ by
    obtain ⟨⟨F, hF, hfF⟩, heq⟩ := hf
    exact ⟨⟨F, hF.mono (Set.preimage_mono h), fun x ↦ hfF _⟩,
      fun l x ↦ heq l (Set.inclusion _ x)⟩

example (a : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    {U U' : Set (ComplexPoint X)} (h : U' ⊆ U) (f : sectionsOnX X a U)
    (x : abelianExp X ⁻¹' U') :
    (restrictX X a h f : abelianExp X ⁻¹' U' → ℂ) x =
      (f : abelianExp X ⁻¹' U → ℂ) ⟨x, Set.preimage_mono h x.2⟩ :=
  rfl

/-- The presheaf of sets `U ↦ L(a)(U)` on `X(ℂ)`, with restriction of functions.

Source: Mumford, *Abelian Varieties*, 2nd ed., Ch. I, §2. -/
def presheafX (a : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ) :
    TopCat.Presheaf Type (TopCat.of (ComplexPoint X)) where
  obj U := sectionsOnX X a (U.unop : Set (ComplexPoint X))
  map i := TypeCat.ofHom (restrictX X a (leOfHom i.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

example (a : abelianPeriodLattice X → (Fin (dim X.left) → ℂ) → ℂ)
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    (presheafX X a).obj U = sectionsOnX X a (U.unop : Set (ComplexPoint X)) := rfl

/-- The holomorphic functions on `U ⊆ X(ℂ)` for upstream's complex-manifold structure (charts
from algebraic étale coordinates): restrictions to `U` of functions `X(ℂ) → ℂ` that are complex
differentiable on `U` in those charts.

Source: Huybrechts, *Complex Geometry*, §1.1 and §2.1; upstream `ChartedSpace (Fin d → ℂ)
(ComplexPoint X)` (`Lemmas/AlgebraicGeometry/ComplexPoint/Manifold.lean`). -/
def holomorphicOnX (U : Set (ComplexPoint X)) : Submodule ℂ (U → ℂ) where
  carrier := {g | ∃ G : ComplexPoint X → ℂ,
    MDifferentiableOn 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, ℂ) G U ∧ ∀ x : U, g x = G x}
  zero_mem' := ⟨0, mdifferentiableOn_const, fun _ ↦ rfl⟩
  add_mem' := fun {f g} ⟨F, hF, hf⟩ ⟨G, hG, hg⟩ ↦
    ⟨F + G, hF.add hG, fun x ↦ by simp [hf x, hg x]⟩
  smul_mem' := fun c f ⟨F, hF, hf⟩ ↦
    ⟨c • F, hF.const_smul c, fun x ↦ by simp [hf x]⟩

example (U : Set (ComplexPoint X)) (c : ℂ) : (fun _ ↦ c : U → ℂ) ∈ holomorphicOnX X U :=
  ⟨fun _ ↦ c, mdifferentiableOn_const, fun _ ↦ rfl⟩

/-- The zero locus on `X(ℂ)` of a function `θ` on `ℂ^g`: the image under `exp` of `{θ = 0}`. For a
theta function it is the support of the divisor `(θ)`; no multiplicities are recorded and no
property is built in.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1. -/
def thetaZeroLocusX (θ : (Fin (dim X.left) → ℂ) → ℂ) : Set (ComplexPoint X) :=
  abelianExp X '' {v | θ v = 0}

example (θ : (Fin (dim X.left) → ℂ) → ℂ) (v : Fin (dim X.left) → ℂ) (hv : θ v = 0) :
    abelianExp X v ∈ thetaZeroLocusX X θ :=
  ⟨v, hv, rfl⟩

end HodgeLean.Adapters
