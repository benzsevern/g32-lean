import HodgeLean.Adapters.AbelianEndomorphismsProofs

/-! # Endomorphisms of an abelian variety acting on `HQ X 1` (FROZEN)

Stage 1 of the geometric commutant: the ring `AbelianEnd X` of group-scheme endomorphisms of an
abelian variety `X` (a group object of `Over (Spec ℂ)` that is integral, smooth and projective)
acts on `HQ X 1` by pullback along the map of complex points (`abelianEndAction`, defined in
`AbelianEndomorphismsDefs`).

Claimed:
* the action is an anti-homomorphism of rings `AbelianEnd X → Module.End ℚ (HQ X 1)`
  (unit, composition, zero, addition, and the packaged ring map into the opposite ring);
* multiplication by `n ∈ ℤ` (`𝟙 X ^ n` in the group `X ⟶ X`) acts on `HQ X 1` as `n`;
* every endomorphism has a complex-linear analytic representation `A` on `ℂ^g`,
  `g = dim X.left`, intertwining the S12 exponential: `exp (A v) = f (exp v)`;
* through the S12 periods, the action is dual to an additive endomorphism of the period lattice
  `Λ = abelianPeriodLattice X`;
* the action preserves the transported degree-one Hodge decomposition
  `ℂ ⊗[ℚ] HQ X 1 = Hol ⊕ Anti` of `DegreeOneLattice` (`complexHolomorphicH1`,
  `complexAntiholomorphicH1`): as an implication from a complex-linear analytic representation,
  and unconditionally;
* nonzero endomorphisms act nonzero (`abelianEndAction` is injective), and the `ℚ`-linear
  extension to `End⁰(X) = ℚ ⊗[ℤ] End(X)` is an injective `ℚ`-algebra map into the opposite of
  `Module.End ℚ (HQ X 1)`.

Not claimed: the converse `End_HS(H¹) ⊆ End⁰(X)` (Appell–Humbert-type algebraization), any
computation of `End⁰(X)` for a specific `X`, a comparison of `abelianEndAction` with a pullback of
sheaf cohomology or of de Rham cohomology, preservation of upstream's de Rham Hodge filtration,
and anything in degrees other than one. `[IsCommMonObj X]` is a binder only so that the ring
structure on `AbelianEnd X` is an instance; it follows from the other binders
(`isCommMonObj_of_complexSelfProductIntegral`, `complexSelfProductIntegral_of_isIntegral`), and
the statements that do not use the ring structure omit it.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- The identity endomorphism acts as the identity.
Source: Hatcher, *Algebraic Topology*, §3.1 (functoriality: `id^* = id`). -/
theorem spec_abelianEndAction_one : abelianEndAction X 1 = 1 :=
  spec_abelianEndAction_one_aux X

example (x : HQ X 1) : abelianEndAction X 1 x = x := by
  rw [spec_abelianEndAction_one X, Module.End.one_apply]

/-- The action is contravariant: `(f ∘ g)^* = g^* ∘ f^*`, with `f * g = f ∘ g` in
`AbelianEnd X`.
Source: Hatcher, *Algebraic Topology*, §3.1 (functoriality: `(f g)^* = g^* f^*`). -/
theorem spec_abelianEndAction_mul (f g : AbelianEnd X) :
    abelianEndAction X (f * g) = abelianEndAction X g * abelianEndAction X f :=
  spec_abelianEndAction_mul_aux X f g

/-- Documentary, not a falsification: the composite `f ∘ g` pulls back by `f` first, then by
`g`. No abelian variety with a computed noncommutative `End(X)` exists in the repository, so the
order is checked at ring level by the next `example`. -/
example (f g : AbelianEnd X) (x : HQ X 1) :
    abelianEndAction X (f * g) x = abelianEndAction X g (abelianEndAction X f x) := by
  rw [spec_abelianEndAction_mul X, Module.End.mul_apply]

/-- Falsification check for the order in `spec_abelianEndAction_mul`, at ring level: on the
noncommutative ring `Matrix (Fin 2) (Fin 2) ℚ`, transposition (the shape of the action on
`HQ X 1 ≅ Hom(Λ, ℚ)`, statement 8) satisfies the reversed law `ρ (a * b) = ρ b * ρ a` and fails the
covariant law `ρ (a * b) = ρ a * ρ b` on the elementary matrices `E₁₂`, `E₂₁`. So the two laws are
distinguishable, and an anti-homomorphism is not a homomorphism. -/
example :
    (∀ a b : Matrix (Fin 2) (Fin 2) ℚ, (a * b).transpose = b.transpose * a.transpose) ∧
      ¬ ∀ a b : Matrix (Fin 2) (Fin 2) ℚ, (a * b).transpose = a.transpose * b.transpose := by
  refine ⟨Matrix.transpose_mul, fun h => ?_⟩
  have h₀ := congrFun (congrFun (h !![0, 1; 0, 0] !![0, 0; 1, 0]) 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h₀

/-- The zero endomorphism (the constant map to the identity point) acts as zero: it factors
through a point, whose degree-one cohomology vanishes.
Source: Hatcher, *Algebraic Topology*, §3.1 (cohomology of a point). -/
theorem spec_abelianEndAction_zero : abelianEndAction X 0 = 0 :=
  spec_abelianEndAction_zero_aux X

example (x : HQ X 1) : abelianEndAction X 0 x = 0 := by
  rw [spec_abelianEndAction_zero X, LinearMap.zero_apply]

/-- The action is additive: on degree-one cohomology of the connected topological group `X(ℂ)`,
the pullback along a pointwise product of maps is the sum of the pullbacks (degree-one classes
of a connected H-space are primitive).
Source: Hatcher, *Algebraic Topology*, §3.C (H-spaces, primitive classes); Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., §1.2 (the rational representation is additive). -/
theorem spec_abelianEndAction_add (f g : AbelianEnd X) :
    abelianEndAction X (f + g) = abelianEndAction X f + abelianEndAction X g :=
  spec_abelianEndAction_add_aux X f g

example (f : AbelianEnd X) : abelianEndAction X (f + f) = 2 • abelianEndAction X f := by
  rw [spec_abelianEndAction_add X, two_nsmul]

/-- The action packaged as a ring homomorphism into the opposite ring of `Module.End ℚ (HQ X 1)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (rational representation
`ρ_r`, here contravariant); `spec_abelianEndAction_one`, `_mul`, `_zero`, `_add`. -/
theorem spec_abelianEndAction_ringHom :
    ∃ ρ : AbelianEnd X →+* (Module.End ℚ (HQ X 1))ᵐᵒᵖ,
      ∀ f, ρ f = MulOpposite.op (abelianEndAction X f) :=
  spec_abelianEndAction_ringHom_aux X

example (n : ℕ) : abelianEndAction X n = n := by
  obtain ⟨ρ, hρ⟩ := spec_abelianEndAction_ringHom X
  apply MulOpposite.op_injective
  rw [← hρ, map_natCast, MulOpposite.op_natCast]

omit [IsCommMonObj X] in
/-- Falsification check: multiplication by `n`, the `n`-th power of `𝟙 X` in the group
`X ⟶ X`, acts on `HQ X 1` as multiplication by `n`. A zero action, or the identity for every
`n`, fails it for `g ≥ 1`.
Source: Mumford, *Abelian Varieties*, §4 (multiplication by `n`); Birkenhake–Lange, *Complex
Abelian Varieties*, 2nd ed., §1.2 (its analytic representation is `n · id`). -/
theorem spec_complexPointPullback_zpow (n : ℤ) :
    complexPointPullback X (𝟙 X ^ n) 1 = (n : ℚ) • LinearMap.id :=
  spec_complexPointPullback_zpow_aux X n

omit [IsCommMonObj X] in
example (x : HQ X 1) : complexPointPullback X (𝟙 X ^ (-1 : ℤ)) 1 x = -x := by
  rw [spec_complexPointPullback_zpow X]
  simp

omit [IsCommMonObj X] in
/-- The analytic representation: every endomorphism lifts along the S12 exponential to a
complex-linear map of `ℂ^g`. The map of complex points is a holomorphic group homomorphism
(upstream `analyticAt_localChart_symm_map`), and a one-parameter subgroup is determined by its
velocity at the identity, so `A` is the derivative at the identity.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (analytic representation
`ρ_a`); Mumford, *Abelian Varieties*, §1; upstream
`Lemmas/AlgebraicGeometry/ComplexPoint/AnalyticMap.lean` at `2ead713`. -/
theorem spec_abelianEnd_analyticRepresentation (f : AbelianEnd X) :
    ∃ A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ), ∀ v,
      Additive.toMul (complexExponential X (dim X.left) (A v)) =
        Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)) :=
  spec_abelianEnd_analyticRepresentation_aux X f

omit [IsCommMonObj X] in
/-- Falsification check for complex linearity: the proof uses `A (i • v) = i • A v`, so it fails
for the alternative with `A` only `ℝ`-linear (statement 9's conjugation example on `ℂ/ℤ[i]`).
The intertwining `exp ∘ A = f ∘ exp` itself is only used here, not falsified. -/
example (f : AbelianEnd X) :
    ∃ A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ), ∀ v,
      Additive.toMul (complexExponential X (dim X.left) (Complex.I • A v)) =
        Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) (Complex.I • v))) := by
  obtain ⟨A, hA⟩ := spec_abelianEnd_analyticRepresentation X f
  exact ⟨A, fun v => by rw [← A.map_smul]; exact hA _⟩

omit [IsCommMonObj X] in
/-- Through the S12 periods, the action is dual to an additive endomorphism `φ` of the period
lattice: the image under `f` of the S12 loop of `l` is the S12 loop of `φ l` (with `φ` the
restriction of the analytic representation).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (rational representation
`ρ_r : End(X) → End_ℤ(Λ)`); `loopPeriod_comp`, `spec_abelianEnd_analyticRepresentation`. -/
theorem spec_abelianEndAction_period (f : AbelianEnd X) :
    ∃ φ : abelianPeriodLattice X →+ abelianPeriodLattice X, ∀ x l,
      abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ l) :=
  spec_abelianEndAction_period_aux X f

omit [IsCommMonObj X] in
example (f : AbelianEnd X) :
    ∃ φ : abelianPeriodLattice X →+ abelianPeriodLattice X, ∀ x,
      abelianPeriodEquiv X (abelianEndAction X f x) = (abelianPeriodEquiv X x).comp φ := by
  obtain ⟨φ, hφ⟩ := spec_abelianEndAction_period X f
  refine ⟨φ, fun x => AddMonoidHom.ext fun l => ?_⟩
  have h := Classical.choose_spec (spec_abelianPeriod_equiv X)
  exact (h _ l).trans ((hφ x l).trans (h x (φ l)).symm)

omit [IsCommMonObj X] in
/-- Hodge preservation, as an implication from a complex-linear analytic representation: the
complexified action preserves the classes with complex-linear periods and the classes with
conjugate-linear periods, because their period functionals compose with `A`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (`ρ_r ⊗ ℂ = ρ_a ⊕ ρ̄_a`) and
Theorem 1.4.1. -/
theorem spec_abelianEndAction_hodge_of_analyticRepresentation (f : AbelianEnd X)
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v))) :
    (complexHolomorphicH1 X).map ((abelianEndAction X f).baseChange ℂ) ≤
        complexHolomorphicH1 X ∧
      (complexAntiholomorphicH1 X).map ((abelianEndAction X f).baseChange ℂ) ≤
        complexAntiholomorphicH1 X :=
  spec_abelianEndAction_hodge_of_analyticRepresentation_aux X f A hA

omit [IsCommMonObj X] in
example (f : AbelianEnd X) (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)))
    (ω : ℂ ⊗[ℚ] HQ X 1) (hω : ω ∈ complexHolomorphicH1 X) :
    (abelianEndAction X f).baseChange ℂ ω ∈ complexHolomorphicH1 X :=
  (spec_abelianEndAction_hodge_of_analyticRepresentation X f A hA).1
    (Submodule.mem_map_of_mem hω)

omit [IsCommMonObj X] in
/-- Every endomorphism preserves the transported degree-one Hodge decomposition of
`ℂ ⊗[ℚ] HQ X 1`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 and Theorem 1.4.1;
`spec_abelianEnd_analyticRepresentation`,
`spec_abelianEndAction_hodge_of_analyticRepresentation`. -/
theorem spec_abelianEndAction_hodge (f : AbelianEnd X) :
    (complexHolomorphicH1 X).map ((abelianEndAction X f).baseChange ℂ) ≤
        complexHolomorphicH1 X ∧
      (complexAntiholomorphicH1 X).map ((abelianEndAction X f).baseChange ℂ) ≤
        complexAntiholomorphicH1 X :=
  spec_abelianEndAction_hodge_aux X f

omit [IsCommMonObj X] in
example (f : AbelianEnd X) (ω : ℂ ⊗[ℚ] HQ X 1) (hω : ω ∈ complexAntiholomorphicH1 X) :
    (abelianEndAction X f).baseChange ℂ ω ∈ complexAntiholomorphicH1 X :=
  (spec_abelianEndAction_hodge X f).2 (Submodule.mem_map_of_mem hω)

omit [IsCommMonObj X] in
/-- Falsification check: distinct endomorphisms act differently. If `f^* = g^*` on `HQ X 1`,
their lattice maps agree (`Λ` is free and `HQ X 1 = Hom(Λ, ℚ)`), hence their analytic
representations agree (`Λ` spans `ℂ^g` over `ℝ`), so `f` and `g` agree on `X(ℂ)` (the exponential
is surjective), hence as morphisms of the reduced scheme `X` of finite type over `ℂ`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (`ρ_r` is injective);
Mumford, *Abelian Varieties*, §19, Theorem 3. -/
theorem spec_abelianEndAction_injective : Function.Injective (abelianEndAction X) :=
  spec_abelianEndAction_injective_aux X

example (f : AbelianEnd X) (h : abelianEndAction X f = 0) : f = 0 :=
  spec_abelianEndAction_injective X (h.trans (spec_abelianEndAction_zero X).symm)

/-- The `ℚ`-linear extension of the action to `End⁰(X) = ℚ ⊗[ℤ] End(X)` is an injective
`ℚ`-algebra map into the opposite of `Module.End ℚ (HQ X 1)`. Injectivity uses that `End(X)` embeds
in the free finite-rank `ℤ`-module `End_ℤ(Λ)` and that `ℚ` is flat over `ℤ`.
Source: Mumford, *Abelian Varieties*, §19, Theorem 3 and Corollary 2 (`End⁰(X)` acts faithfully on
`H₁(X, ℚ)`); Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2. -/
theorem spec_abelianEnd0Action :
    ∃ ρ : AbelianEnd0 X →ₐ[ℚ] (Module.End ℚ (HQ X 1))ᵐᵒᵖ,
      (∀ f, ρ (1 ⊗ₜ f) = MulOpposite.op (abelianEndAction X f)) ∧ Function.Injective ρ :=
  spec_abelianEnd0Action_aux X

example : ∃ ρ : AbelianEnd0 X →ₐ[ℚ] (Module.End ℚ (HQ X 1))ᵐᵒᵖ,
    ρ (1 ⊗ₜ 1) = 1 ∧ Function.Injective ρ := by
  obtain ⟨ρ, -, hinj⟩ := spec_abelianEnd0Action X
  exact ⟨ρ, by rw [← Algebra.TensorProduct.one_def, map_one], hinj⟩

end HodgeLean.Adapters
