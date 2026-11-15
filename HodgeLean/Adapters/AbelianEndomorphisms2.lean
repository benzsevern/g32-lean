import HodgeLean.Adapters.AbelianEndomorphisms2Proofs

/-! # Endomorphisms of an abelian variety, stage 2: representations and lattice maps (FROZEN)

Stage 2 of the geometric commutant `End⁰(X) = End_HS(H¹(X, ℚ))`, after `AbelianEndomorphisms`
(stage 1). Notation: `X` is an abelian variety (a group object of `Over (Spec ℂ)` that is
integral, smooth and projective), `g = dim X.left`, `exp = complexExponential X g` (S12),
`Λ = abelianPeriodLattice X`, `ρ = abelianEndAction X`.

Claimed:
* the analytic representation is unique: two complex-linear maps of `ℂ^g` with the same
  exponential are equal; and it determines the endomorphism;
* the analytic representation `f ↦ A_f` is a ring homomorphism `AbelianEnd X → End_ℂ(ℂ^g)`;
* the lattice map `φ` of stage 1 (`spec_abelianEndAction_period`) is unique, it is the
  restriction of the analytic representation to `Λ`, and `f ↦ φ_f` is a ring homomorphism
  `AbelianEnd X → End_ℤ(Λ)` (the rational representation);
* every complex-linear `A` with `A Λ ⊆ Λ` descends, through the uniformization
  (`UniformizationBiholomorphic`), to a unique holomorphic self-map `F` of `X(ℂ)` with
  `F ∘ exp = exp ∘ A`, and every such `F` is a group homomorphism; falsification: `A = ½ · id`
  has no descent when `g ≥ 1`;
* a morphism `h : X ⟶ X` is a morphism of group objects if and only if its map of complex points
  is multiplicative;
* as an implication from the algebraization of holomorphic self-maps of `X(ℂ)` (an explicit
  binder `hAlg`: every holomorphic `F : X(ℂ) → X(ℂ)` is `Point.map h` of some `h : X ⟶ X`, a
  consequence of Chow's theorem and GAGA): every complex-linear `A` with `A Λ ⊆ Λ` is the analytic
  representation of an endomorphism, so the analytic representation identifies `End(X)` with the
  ring of complex-linear maps preserving `Λ`.

Not claimed: the algebraization `hAlg` itself (Chow/GAGA lane), the converse
`End_HS(H¹) ⊆ End⁰(X)` on cohomology (a rational Hodge endomorphism gives, after clearing
denominators, a complex-linear lattice map: deferred to stage 3), the commutant equation, any
computation of `End⁰(X)` for a specific `X`, homomorphisms between different abelian varieties,
and anything about de Rham cohomology. `[IsCommMonObj X]` is a binder only so that the ring
structure on `AbelianEnd X` and the additivity of `exp` are instances; it follows from the other
binders (`isCommMonObj_of_complexSelfProductIntegral`, `complexSelfProductIntegral_of_isIntegral`).
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open scoped Manifold ContDiff CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- Uniqueness of the analytic representation: two complex-linear maps of `ℂ^g` with the same
exponential are equal. `(A - A') v` lies in the discrete `Λ` for every `v`, and the image of the
connected `ℂ^g` under a continuous map into a discrete space is a point.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (the analytic
representation is well defined); S12 `discrete_complexExponentialLattice`,
`complexExponentialHom`. -/
theorem spec_analyticRepresentation_unique
    (A A' : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (h : ∀ v, complexExponential X (dim X.left) (A v) =
      complexExponential X (dim X.left) (A' v)) :
    A = A' :=
  spec_analyticRepresentation_unique_aux X A A' h

example (f : AbelianEnd X) :
    ∃! A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ), ∀ v,
      Additive.toMul (complexExponential X (dim X.left) (A v)) =
        Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)) := by
  obtain ⟨A, hA⟩ := spec_abelianEnd_analyticRepresentation X f
  refine ⟨A, hA, fun A' hA' => spec_analyticRepresentation_unique X A' A fun v => ?_⟩
  exact Additive.toMul.injective ((hA' v).trans (hA v).symm)

/-- The analytic representation determines the endomorphism: if one complex-linear `A` lifts
both `f` and `f'`, then `f(ℂ) = f'(ℂ)` because `exp` is surjective, and morphisms of the reduced
scheme `X`, of finite type over `ℂ`, are determined by their complex points.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (`ρ_a` is injective);
S12 `surjective_complexExponential`; Mathlib `AlgebraicGeometry.ext_of_apply_eq`. -/
theorem spec_eq_of_analyticRepresentation (f f' : AbelianEnd X)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)))
    (hA' : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f'.hom (Additive.toMul (complexExponential X (dim X.left) v))) :
    f = f' :=
  spec_eq_of_analyticRepresentation_aux X f f' A hA hA'

/-- Falsification check "nonzero endomorphisms have nonzero analytic representation": an
endomorphism lifted by `A = 0` is zero, since `0` (the constant map to the identity) is lifted
by `0`. -/
example (f : AbelianEnd X)
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left)
      ((0 : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ)) v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v))) :
    f = 0 := by
  refine spec_eq_of_analyticRepresentation X f 0 0 hA fun v => ?_
  change Additive.toMul (complexExponential X (dim X.left) 0) =
    Additive.toMul (complexExponential X (dim X.left) v) ≫ (1 : X ⟶ X)
  rw [MonObj.comp_one, complexExponential_zero]
  rfl

/-- The analytic representation is a ring homomorphism: `A_{f ∘ g} = A_f A_g`,
`A_{f + g} = A_f + A_g`, `A_1 = 1`, `A_0 = 0`, by uniqueness
(`spec_analyticRepresentation_unique`) and the additivity of `exp`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (analytic representation
`ρ_a : End(X) → M_g(ℂ)`); `spec_abelianEnd_analyticRepresentation`. -/
theorem spec_analyticRepresentation_ringHom :
    ∃ ρa : AbelianEnd X →+* Module.End ℂ (Fin (dim X.left) → ℂ), ∀ f v,
      Additive.toMul (complexExponential X (dim X.left) (ρa f v)) =
        Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)) :=
  spec_analyticRepresentation_ringHom_aux X

/-- The analytic representation is covariant: composition `f * g = f ∘ g` goes to the product
`A_f A_g` in this order. -/
example : ∃ ρa : AbelianEnd X →+* Module.End ℂ (Fin (dim X.left) → ℂ),
    ∀ f g v, ρa (f * g) v = ρa f (ρa g v) := by
  obtain ⟨ρa, -⟩ := spec_analyticRepresentation_ringHom X
  exact ⟨ρa, fun f g v => by rw [map_mul, Module.End.mul_apply]⟩

/-- Uniqueness of the lattice map of `spec_abelianEndAction_period`: the S12 periods of `HQ X 1`
separate the points of `Λ` (`HQ X 1 ≅ Hom(Λ, ℚ)`, `spec_abelianPeriod_equiv`, and `Λ` is free).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (rational representation
`ρ_r`); Hatcher, *Algebraic Topology*, §3.1 (universal coefficients). -/
theorem spec_latticeRepresentation_unique (f : AbelianEnd X)
    (φ φ' : abelianPeriodLattice X →+ abelianPeriodLattice X)
    (hφ : ∀ x l, abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ l))
    (hφ' : ∀ x l, abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ' l)) :
    φ = φ' :=
  spec_latticeRepresentation_unique_aux X f φ φ' hφ hφ'

example (f : AbelianEnd X) :
    ∃! φ : abelianPeriodLattice X →+ abelianPeriodLattice X, ∀ x l,
      abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ l) := by
  obtain ⟨φ, hφ⟩ := spec_abelianEndAction_period X f
  exact ⟨φ, hφ, fun φ' hφ' => spec_latticeRepresentation_unique X f φ' φ hφ' hφ⟩

/-- The lattice map is the restriction of the analytic representation: `φ l = A l` in `ℂ^g` for
`l ∈ Λ`. The image of the S12 loop of `l` under `f` is the S12 loop of `A l`, so `φ l` and
`A l` have the same periods, hence are equal (`spec_latticeRepresentation_unique`'s argument).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (`ρ_r ⊗ ℂ = ρ_a ⊕ ρ̄_a`, the
rational representation is the restriction of the analytic one to `Λ`); `loopPeriod_comp`. -/
theorem spec_latticeRepresentation_eq_analytic (f : AbelianEnd X)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)))
    (φ : abelianPeriodLattice X →+ abelianPeriodLattice X)
    (hφ : ∀ x l, abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ l))
    (l : abelianPeriodLattice X) :
    ((φ l : abelianPeriodLattice X) : Fin (dim X.left) → ℂ) = A l :=
  spec_latticeRepresentation_eq_analytic_aux X f A hA φ hφ l

-- The analytic representation of an endomorphism preserves the period lattice.
example (f : AbelianEnd X) : ∃ A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ),
    ∀ l ∈ abelianPeriodLattice X, A l ∈ abelianPeriodLattice X := by
  obtain ⟨A, hA⟩ := spec_abelianEnd_analyticRepresentation X f
  obtain ⟨φ, hφ⟩ := spec_abelianEndAction_period X f
  refine ⟨A, fun l hl => ?_⟩
  rw [← spec_latticeRepresentation_eq_analytic X f A hA φ hφ ⟨l, hl⟩]
  exact (φ ⟨l, hl⟩).2

/-- The rational representation is a ring homomorphism `AbelianEnd X → End_ℤ(Λ)`, dual to the
action on `HQ X 1` through the S12 periods. It is covariant (`φ_{f ∘ g} = φ_f ∘ φ_g`) while `ρ`
is contravariant: periods transpose.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (rational representation
`ρ_r : End(X) → End_ℤ(Λ)`); `spec_abelianEndAction_period`, `spec_abelianEndAction_ringHom`,
`spec_latticeRepresentation_unique`. -/
theorem spec_rationalRepresentation_ringHom :
    ∃ ρr : AbelianEnd X →+* Module.End ℤ (abelianPeriodLattice X), ∀ f x l,
      abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (ρr f l) :=
  spec_rationalRepresentation_ringHom_aux X

/-- Falsification check for the variance: the action of the composite `f * g = f ∘ g` on a class
reads its periods through `ρr f ∘ ρr g`, in this order. -/
example (f g : AbelianEnd X) (x : HQ X 1) (l : abelianPeriodLattice X) :
    ∃ ρr : AbelianEnd X →+* Module.End ℤ (abelianPeriodLattice X),
      abelianPeriod X (abelianEndAction X (f * g) x) l =
        abelianPeriod X x (ρr f (ρr g l)) := by
  obtain ⟨ρr, hρr⟩ := spec_rationalRepresentation_ringHom X
  exact ⟨ρr, by rw [hρr, map_mul, Module.End.mul_apply]⟩

/-- Descent of lattice maps: a complex-linear `A` with `A Λ ⊆ Λ` induces a unique holomorphic
self-map `F` of `X(ℂ)` with `F ∘ exp = exp ∘ A`. `exp ∘ A` is holomorphic (stage 4e) and
`Λ`-periodic, so it descends by the uniformization (`spec_existsUnique_contMDiff_descent_manifold`
with target `X(ℂ)`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Proposition 1.2.1 (a complex-linear
map with `A Λ ⊆ Λ'` induces a homomorphism `V/Λ → V'/Λ'`); `UniformizationBiholomorphic`,
`spec_contMDiff_complexExponential`. -/
theorem spec_existsUnique_holomorphic_descent
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ l ∈ abelianPeriodLattice X, A l ∈ abelianPeriodLattice X) :
    ∃! F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F ∧
        ∀ v, F (Additive.toMul (complexExponential X (dim X.left) v)) =
          Additive.toMul (complexExponential X (dim X.left) (A v)) :=
  spec_existsUnique_holomorphic_descent_aux X A hA

-- The descent of the identity is the identity.
example (F : ComplexPoint X → ComplexPoint X)
    (hF : ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F ∧
      ∀ v, F (Additive.toMul (complexExponential X (dim X.left) v)) =
        Additive.toMul (complexExponential X (dim X.left)
          ((LinearMap.id : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ)) v))) :
    F = id :=
  (spec_existsUnique_holomorphic_descent X LinearMap.id fun _ hl => hl).unique hF
    ⟨contMDiff_id, fun _ => rfl⟩

/-- A map of complex points lifted by a complex-linear `A` is a group homomorphism: every point is
some `exp v` (S12), and `exp` is a homomorphism.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Proposition 1.2.1; S12
`surjective_complexExponential`, `complexExponentialHom`. -/
theorem spec_descent_map_mul
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (F : ComplexPoint X → ComplexPoint X)
    (hF : ∀ v, F (Additive.toMul (complexExponential X (dim X.left) v)) =
      Additive.toMul (complexExponential X (dim X.left) (A v))) :
    F 1 = 1 ∧ ∀ x y, F (x * y) = F x * F y :=
  spec_descent_map_mul_aux X A F hF

example (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (F : ComplexPoint X → ComplexPoint X)
    (hF : ∀ v, F (Additive.toMul (complexExponential X (dim X.left) v)) =
      Additive.toMul (complexExponential X (dim X.left) (A v))) :
    ComplexPoint X →* ComplexPoint X :=
  ⟨⟨F, (spec_descent_map_mul X A F hF).1⟩, (spec_descent_map_mul X A F hF).2⟩

/-- Falsification check for the lattice hypothesis of `spec_existsUnique_holomorphic_descent`:
for `g ≥ 1`, the complex-linear map `½ · id` lifts no map of `X(ℂ)`. Such an `F` would give
`exp (l / 2) = F (exp l) = F 1 = exp 0`, so `l / 2 ∈ Λ` for every `l ∈ Λ`; a vector of an integer
basis of the rank-`2g` lattice `Λ` (`finrank_complexExponentialLattice`) is not divisible by `2`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`Λ ≅ ℤ^{2g}`); S12
`complexExponentialLatticeBasis`. -/
theorem spec_not_exists_descent_half (hg : 0 < dim X.left) :
    ¬ ∃ F : ComplexPoint X → ComplexPoint X, ∀ v,
      F (Additive.toMul (complexExponential X (dim X.left) v)) =
        Additive.toMul (complexExponential X (dim X.left) ((1 / 2 : ℂ) • v)) :=
  spec_not_exists_descent_half_aux X hg

example (hg : 0 < dim X.left) :
    ¬ ∀ l ∈ abelianPeriodLattice X, (1 / 2 : ℂ) • l ∈ abelianPeriodLattice X := fun h => by
  obtain ⟨F, ⟨-, hF⟩, -⟩ := spec_existsUnique_holomorphic_descent X
    ((1 / 2 : ℂ) • LinearMap.id) fun l hl => by simpa using h l hl
  exact spec_not_exists_descent_half X hg ⟨F, fun v => by simpa using hF v⟩

omit [IsCommMonObj X] in
/-- A morphism `h : X ⟶ X` is a morphism of group objects if and only if its map of complex
points is multiplicative. Forward, `IsMonHom.mul_hom`. Backward, the two composites
`μ ≫ h`, `(h ⊗ h) ≫ μ : X ⊗ X ⟶ X` agree on complex points (those of `X ⊗ X` are pairs), and
`X ⊗ X` is integral (`complexSelfProductIntegral_of_isIntegral`) and of finite type over `ℂ`, so
morphisms out of it are determined by complex points; `h 1 = 1` holds in any group.
Source: Mumford, *Abelian Varieties*, §4; Milne, *Abelian Varieties* (2008), §I.1; Mathlib
`AlgebraicGeometry.ext_of_apply_eq`, `IsMonHom`. -/
theorem spec_isMonHom_iff_pointMap_mul (h : X ⟶ X) :
    IsMonHom h ↔ ∀ x y : ComplexPoint X, Point.map h (x * y) = Point.map h x * Point.map h y :=
  spec_isMonHom_iff_pointMap_mul_aux X h

omit [IsCommMonObj X] in
-- An endomorphism maps the identity point to the identity point.
example (f : AbelianEnd X) : Point.map f.hom 1 = 1 := by
  have h := (spec_isMonHom_iff_pointMap_mul X f.hom).1 f.isMonHom 1 1
  rw [mul_one] at h
  exact left_eq_mul.mp h

/-- The converse direction at lattice level, as an implication from the algebraization of
holomorphic self-maps of `X(ℂ)` (`hAlg`, an explicit binder; true by Chow's theorem and GAGA):
every complex-linear `A` with `A Λ ⊆ Λ` is the analytic representation of an endomorphism.
Descend `A` (`spec_existsUnique_holomorphic_descent`), algebraize the descent (`hAlg`), and the
algebraic map is a morphism of group objects (`spec_descent_map_mul`,
`spec_isMonHom_iff_pointMap_mul`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Proposition 1.2.1 and §1.2;
for `hAlg`, Serre, *Géométrie algébrique et géométrie analytique* (GAGA), Ann. Inst. Fourier 6
(1956), §3, Proposition 13 and Chow, *On compact complex analytic varieties*, Amer. J. Math. 71
(1949). -/
theorem spec_exists_abelianEnd_of_lattice
    (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ l ∈ abelianPeriodLattice X, A l ∈ abelianPeriodLattice X) :
    ∃ f : AbelianEnd X, ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)) :=
  spec_exists_abelianEnd_of_lattice_aux X hAlg A hA

-- Under `hAlg`, the endomorphism lifted by a lattice-preserving `A` is unique.
example (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ l ∈ abelianPeriodLattice X, A l ∈ abelianPeriodLattice X) :
    ∃! f : AbelianEnd X, ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)) := by
  obtain ⟨f, hf⟩ := spec_exists_abelianEnd_of_lattice X hAlg A hA
  exact ⟨f, hf, fun f' hf' => spec_eq_of_analyticRepresentation X f' f A hf' hf⟩

/-- As an implication from the algebraization of holomorphic self-maps (`hAlg`), the analytic
representation identifies `End(X)` with the ring of complex-linear maps of `ℂ^g` preserving `Λ`:
it is an injective ring homomorphism whose image is exactly that set.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Proposition 1.2.1 and §1.2
(`End(X) ≅ {A ∈ M_g(ℂ) | A Λ ⊆ Λ}`); for `hAlg`, Serre, GAGA (1956), and Chow (1949). -/
theorem spec_analyticRepresentation_range
    (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F) :
    ∃ ρa : AbelianEnd X →+* Module.End ℂ (Fin (dim X.left) → ℂ),
      (∀ f v, Additive.toMul (complexExponential X (dim X.left) (ρa f v)) =
        Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v))) ∧
      Function.Injective ρa ∧
      Set.range ρa = {A | ∀ l ∈ abelianPeriodLattice X, A l ∈ abelianPeriodLattice X} :=
  spec_analyticRepresentation_range_aux X hAlg

/-- Under `hAlg`, multiplication by `½` is not an endomorphism when `g ≥ 1`: the range of the
analytic representation is a proper subset of `End_ℂ(ℂ^g)`. -/
example (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F) (hg : 0 < dim X.left) :
    ∃ ρa : AbelianEnd X →+* Module.End ℂ (Fin (dim X.left) → ℂ),
      (1 / 2 : ℂ) • LinearMap.id ∉ Set.range ρa := by
  obtain ⟨ρa, -, -, hrange⟩ := spec_analyticRepresentation_range X hAlg
  refine ⟨ρa, fun hmem => ?_⟩
  rw [hrange] at hmem
  obtain ⟨F, ⟨-, hF⟩, -⟩ := spec_existsUnique_holomorphic_descent X _ hmem
  exact spec_not_exists_descent_half X hg ⟨F, fun v => by simpa using hF v⟩

end HodgeLean.Adapters
