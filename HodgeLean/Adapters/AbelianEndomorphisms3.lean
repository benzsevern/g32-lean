import HodgeLean.Adapters.AbelianEndomorphisms3Proofs

/-! # Endomorphisms of an abelian variety, stage 3: the converse on `HQ X 1` (FROZEN)

Stage 3 of the geometric commutant `End⁰(X) = End_HS(H¹(X, ℚ))`, after `AbelianEndomorphisms`
(stage 1: `End⁰(X)` acts faithfully on `HQ X 1` by Hodge endomorphisms) and
`AbelianEndomorphisms2` (stage 2: under the algebraization binder `hAlg`, the analytic
representation identifies `End(X)` with `{A ∈ End_ℂ(ℂ^g) | A Λ ⊆ Λ}`). Notation: `X` is an abelian
variety (a group object of `Over (Spec ℂ)` that is integral, smooth and projective),
`g = dim X.left`, `Λ = abelianPeriodLattice X`, `Hol = complexHolomorphicH1 X`,
`Anti = complexAntiholomorphicH1 X` (the lattice-side split of `ℂ ⊗[ℚ] HQ X 1`), and `hAlg` is
stage 2's binder: every holomorphic self-map of `X(ℂ)` is `Point.map` of a morphism `X ⟶ X`.

Claimed, unconditionally:
* every rational endomorphism `T` of `HQ X 1 ≅ Hom(Λ, ℚ)`, after multiplication by some
  `N > 0`, is dual through the periods to an additive endomorphism of `Λ`; `N = 1` fails for
  `T = ½` when `g ≥ 1`;
* a rational `T` dual to `φ : Λ → Λ` preserves `Hol` if and only if `φ` extends to a complex-linear
  map of `ℂ^g`; so a `T` preserving `Hol` gives, after clearing denominators, a complex-linear `A`
  with `A Λ ⊆ Λ` dual to `N • T`;
* a rational `T` preserving `Hol` preserves `Anti` (conjugation exchanges them); for `g ≥ 1` some
  rational `T` does not preserve `Hol`;
* the split, as the bigraded family `latticeHodgePieces X` (`Hol` in type `(1, 0)`, `Anti` in type
  `(0, 1)`), is an internal direct sum, and the rational commutant of its Hodge Lie algebra
  (`hodgeLieAlgebra`, as in `EQWCore`) is `hodgeEndH1 X`, the endomorphisms of the lattice-side
  Hodge structure.

Claimed as implications from `hAlg`:
* every `T` preserving `Hol` has a multiple `N • T`, `N > 0`, equal to `abelianEndAction X f` for
  some endomorphism `f`;
* the action `End⁰(X) → End_ℚ(HQ X 1)ᵐᵒᵖ` of stage 1 is injective with range exactly
  `hodgeEndH1 X`, so `End⁰(X) ≃ End_HS(HQ X 1)ᵐᵒᵖ` as `ℚ`-algebras;
* the commutant equation: the rational commutant of the Hodge Lie algebra of `latticeHodgePieces X`
  is the image of `End⁰(X)`; and in the form `EQWCore`'s binder `hcomm` consumes: if
  `End⁰(X) = ℚ[j]` for one endomorphism `j`, the commutant is `Algebra.adjoin ℚ {j^*}`.

Not claimed: `hAlg` itself (Chow/GAGA lane); `End⁰(X) = K` for any specific `X`; the reductivity
or classification binders of `EQWCore`; any statement about the de Rham Hodge decomposition
(`latticeHodgePieces` is the lattice-side split; its identification with `F^1 H_dR^1` is the open
stage 4b/4c input of `HodgeFilterLattice`); the Rosati involution; homomorphisms between different
abelian varieties. `[IsCommMonObj X]` is a binder only where the ring structure on `AbelianEnd X`
is used; it follows from the other binders. HC no distance; AV milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open scoped Manifold ContDiff CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The rational transpose, after clearing denominators: for every rational endomorphism `T` of
`HQ X 1 ≅ Hom(Λ, ℚ)` there are `N > 0` and an additive `φ : Λ → Λ` with
`period (N • T x) = period x ∘ φ`. Dualize `T` through `spec_abelianPeriod_equiv`, write the
transpose in the S12 basis of `Λ` as a rational matrix, and multiply by a common denominator.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`H¹(X, ℤ) = Hom(Λ, ℤ)`)
and §1.2; Bourbaki, *Algèbre*, II §2 (transpose); `spec_abelianPeriod_equiv`,
`abelianLatticeBasis`. -/
theorem spec_abelianPeriod_transpose (T : Module.End ℚ (HQ X 1)) :
    ∃ N : ℕ, 0 < N ∧ ∃ φ : abelianPeriodLattice X →+ abelianPeriodLattice X, ∀ x l,
      abelianPeriod X ((N : ℚ) • T x) l = abelianPeriod X x (φ l) :=
  spec_abelianPeriod_transpose_aux X T

-- The periods of `T x` are those of `x` along `φ`, divided by `N`.
example (T : Module.End ℚ (HQ X 1)) :
    ∃ N : ℕ, 0 < N ∧ ∃ φ : abelianPeriodLattice X →+ abelianPeriodLattice X, ∀ x l,
      abelianPeriod X (T x) l = (N : ℚ)⁻¹ * abelianPeriod X x (φ l) := by
  obtain ⟨N, hN, φ, hφ⟩ := spec_abelianPeriod_transpose X T
  refine ⟨N, hN, φ, fun x l => ?_⟩
  have h := hφ x l
  rw [map_smul, Pi.smul_apply, smul_eq_mul] at h
  rw [← h, inv_mul_cancel_left₀ (by exact_mod_cast hN.ne')]

/-- Falsification check for the denominator `N` of `spec_abelianPeriod_transpose`: for `g ≥ 1`,
`T = ½` is dual to no additive endomorphism of `Λ`. Such `φ` would satisfy `φ l + φ l = l`, because
the periods separate the points of `Λ` (`spec_abelianPeriod_equiv`), and a vector of the integer
basis of the rank-`2g` lattice `Λ` is not divisible by `2`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`Λ ≅ ℤ^{2g}`); S12
`complexExponentialLatticeBasis`, `finrank_complexExponentialLattice`. -/
theorem spec_not_exists_latticeTranspose_half (hg : 0 < dim X.left) :
    ¬ ∃ φ : abelianPeriodLattice X →+ abelianPeriodLattice X, ∀ x l,
      abelianPeriod X ((1 / 2 : ℚ) • x) l = abelianPeriod X x (φ l) :=
  spec_not_exists_latticeTranspose_half_aux X hg

-- So `N = 1` cannot be required in `spec_abelianPeriod_transpose`.
example (hg : 0 < dim X.left) :
    ¬ ∀ T : Module.End ℚ (HQ X 1), ∃ φ : abelianPeriodLattice X →+ abelianPeriodLattice X,
      ∀ x l, abelianPeriod X (T x) l = abelianPeriod X x (φ l) := fun h => by
  obtain ⟨φ, hφ⟩ := h ((1 / 2 : ℚ) • LinearMap.id)
  exact spec_not_exists_latticeTranspose_half X hg ⟨φ, fun x l => hφ x l⟩

/-- Hodge criterion on the lattice: a rational `T` dual to `φ : Λ → Λ` preserves the holomorphic
summand if and only if `φ` extends to a complex-linear map of `ℂ^g`. Backward, the periods of
`T_ℂ ω` are `f ∘ A` for `ω` with periods `f`. Forward, `φ` extends `ℝ`-linearly to `B` (`Λ` spans
`ℂ^g` over `ℝ`); for every complex-linear `f`, the class with periods `f|_Λ`
(`spec_complexAbelianPeriod_restriction`) is sent to a class with complex-linear periods `f'`, so
`f ∘ B = f'` on `Λ`, hence everywhere, and `B (i v) = i B v` follows by testing on coordinates.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (`ρ_r ⊗ ℂ = ρ_a ⊕ ρ̄_a`) and
Theorem 1.4.1; `spec_complexAbelianPeriod_restriction`, S12
`isZLattice_complexExponentialLattice`. -/
theorem spec_hodge_iff_complexLinear (T : Module.End ℚ (HQ X 1))
    (φ : abelianPeriodLattice X →+ abelianPeriodLattice X)
    (hφ : ∀ x l, abelianPeriod X (T x) l = abelianPeriod X x (φ l)) :
    (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X ↔
      ∃ A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ), ∀ l,
        ((φ l : abelianPeriodLattice X) : Fin (dim X.left) → ℂ) = A l :=
  spec_hodge_iff_complexLinear_aux X T φ hφ

-- The identity is dual to the identity of `Λ`, which extends complex-linearly.
example : (complexHolomorphicH1 X).map ((LinearMap.id : Module.End ℚ (HQ X 1)).baseChange ℂ) ≤
    complexHolomorphicH1 X :=
  (spec_hodge_iff_complexLinear X LinearMap.id (AddMonoidHom.id _) fun _ _ => rfl).2
    ⟨LinearMap.id, fun _ => rfl⟩

/-- Rational Hodge endomorphisms to lattice maps: a rational `T` preserving the holomorphic summand
has a multiple `N • T`, `N > 0`, dual to the restriction to `Λ` of a complex-linear `A` (so
`A Λ ⊆ Λ`). This is `spec_abelianPeriod_transpose` followed by `spec_hodge_iff_complexLinear`
for `N • T`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 and Theorem 1.4.1. -/
theorem spec_exists_lattice_of_hodge (T : Module.End ℚ (HQ X 1))
    (hT : (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X) :
    ∃ N : ℕ, 0 < N ∧ ∃ φ : abelianPeriodLattice X →+ abelianPeriodLattice X,
      ∃ A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ),
        (∀ x l, abelianPeriod X ((N : ℚ) • T x) l = abelianPeriod X x (φ l)) ∧
          ∀ l, ((φ l : abelianPeriodLattice X) : Fin (dim X.left) → ℂ) = A l :=
  spec_exists_lattice_of_hodge_aux X T hT

-- The complex-linear map preserves the period lattice, the hypothesis of stage 2's
-- `spec_exists_abelianEnd_of_lattice`.
example (T : Module.End ℚ (HQ X 1))
    (hT : (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X) :
    ∃ A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ),
      ∀ l ∈ abelianPeriodLattice X, A l ∈ abelianPeriodLattice X := by
  obtain ⟨-, -, φ, A, -, hA⟩ := spec_exists_lattice_of_hodge X T hT
  exact ⟨A, fun l hl => hA ⟨l, hl⟩ ▸ (φ ⟨l, hl⟩).2⟩

/-- A rational endomorphism preserving the holomorphic summand preserves the antiholomorphic one:
`T_ℂ` commutes with the rational conjugation `sigmaQ`, which exchanges the two summands
(`spec_complexH1_conjugation_exchanges`) and is an involution.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §2.1 (a rational map preserving
`H^{1,0}` preserves its conjugate `H^{0,1}`); Birkenhake–Lange, *Complex Abelian Varieties*, 2nd
ed., Theorem 1.4.1. -/
theorem spec_map_antiholomorphic_le_of_holomorphic (T : Module.End ℚ (HQ X 1))
    (hT : (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X) :
    (complexAntiholomorphicH1 X).map (T.baseChange ℂ) ≤ complexAntiholomorphicH1 X :=
  spec_map_antiholomorphic_le_of_holomorphic_aux X T hT

-- Membership in `hodgeEndH1 X` needs only the holomorphic summand.
example (T : Module.End ℚ (HQ X 1)) :
    T ∈ hodgeEndH1 X ↔
      (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X :=
  ⟨fun h => h.1, fun h => ⟨h, spec_map_antiholomorphic_le_of_holomorphic X T h⟩⟩

/-- Falsification check for the Hodge hypothesis of `spec_hodge_iff_complexLinear`,
`spec_exists_lattice_of_hodge` and `spec_exists_abelianEnd_of_hodge`: for `g ≥ 1`, some rational
endomorphism of `HQ X 1` does not preserve the holomorphic summand. Otherwise `Hol` would be stable
under every elementary rational endomorphism, hence contain `1 ⊗ b` for every vector `b` of a
rational basis, so `Hol = ⊤`; but `Hol` and `Anti` are disjoint and `Anti ≠ 0`
(`spec_complexH1_split`, `spec_complexH1_dimension`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1. -/
theorem spec_exists_not_hodge (hg : 0 < dim X.left) :
    ∃ T : Module.End ℚ (HQ X 1),
      ¬ (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X :=
  spec_exists_not_hodge_aux X hg

example (hg : 0 < dim X.left) : hodgeEndH1 X ≠ ⊤ := fun h => by
  obtain ⟨T, hT⟩ := spec_exists_not_hodge X hg
  exact hT (h ▸ Algebra.mem_top : T ∈ hodgeEndH1 X).1

/-- The converse on `HQ X 1`, as an implication from the algebraization of holomorphic self-maps
of `X(ℂ)` (`hAlg`, an explicit binder; true by Chow's theorem and GAGA): every rational `T`
preserving the holomorphic summand has a multiple `N • T`, `N > 0`, induced by an endomorphism.
`spec_exists_lattice_of_hodge` gives a complex-linear `A` with `A Λ ⊆ Λ` dual to `N • T`;
stage 2's `spec_exists_abelianEnd_of_lattice` gives `f` lifted by `A`; its lattice map is
`A|_Λ` (`spec_latticeRepresentation_eq_analytic`), so `f^*` and `N • T` have the same periods,
hence are equal (`spec_abelianPeriod_equiv`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Proposition 1.2.1, §1.2 and
Theorem 1.4.1; Mumford, *Abelian Varieties*, §19 (`End⁰(X) ⊗ ℚ` and `End_HS`); for `hAlg`,
Serre, *Géométrie algébrique et géométrie analytique* (GAGA), Ann. Inst. Fourier 6 (1956), §3,
Proposition 13 and Chow, *On compact complex analytic varieties*, Amer. J. Math. 71 (1949). -/
theorem spec_exists_abelianEnd_of_hodge [IsCommMonObj X]
    (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F)
    (T : Module.End ℚ (HQ X 1))
    (hT : (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X) :
    ∃ N : ℕ, 0 < N ∧ ∃ f : AbelianEnd X, abelianEndAction X f = (N : ℚ) • T :=
  spec_exists_abelianEnd_of_hodge_aux X hAlg T hT

-- Under `hAlg`, a Hodge endomorphism lies in the `ℚ`-span of the endomorphism actions.
example [IsCommMonObj X]
    (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F)
    (T : Module.End ℚ (HQ X 1)) (hT : T ∈ hodgeEndH1 X) :
    ∃ q : ℚ, ∃ f : AbelianEnd X, T = q • abelianEndAction X f := by
  obtain ⟨N, hN, f, hf⟩ := spec_exists_abelianEnd_of_hodge X hAlg T hT.1
  refine ⟨(N : ℚ)⁻¹, f, ?_⟩
  rw [hf, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hN.ne'), one_smul]

/-- `End⁰(X) = End_HS(HQ X 1)`, as an implication from `hAlg`: the `ℚ`-linear extension of the
action to `End⁰(X)` (stage 1's `spec_abelianEnd0Action`, contravariant, hence into the opposite
ring) is injective with range exactly the endomorphisms of the lattice-side Hodge structure.
Range `⊆`: stage 1's `spec_abelianEndAction_hodge`; range `⊇`:
`spec_exists_abelianEnd_of_hodge`, dividing by `N` in `End⁰(X)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Proposition 1.2.1, §1.2 and
Theorem 1.4.1; Mumford, *Abelian Varieties*, §19 and §22 (`End⁰(X) = End_HS(H¹(X, ℚ))` over `ℂ`);
for `hAlg`, Serre, GAGA (1956), and Chow (1949). -/
theorem spec_abelianEnd0Action_range [IsCommMonObj X]
    (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F) :
    ∃ ρ : AbelianEnd0 X →ₐ[ℚ] (Module.End ℚ (HQ X 1))ᵐᵒᵖ,
      (∀ f, ρ (1 ⊗ₜ f) = MulOpposite.op (abelianEndAction X f)) ∧ Function.Injective ρ ∧
        ρ.range = (hodgeEndH1 X).op :=
  spec_abelianEnd0Action_range_aux X hAlg

-- Under `hAlg`, `End⁰(X)` is isomorphic to the opposite of `End_HS(HQ X 1)` as a `ℚ`-algebra.
example [IsCommMonObj X]
    (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F) :
    Nonempty (AbelianEnd0 X ≃ₐ[ℚ] (hodgeEndH1 X).op) := by
  obtain ⟨ρ, -, hinj, hrange⟩ := spec_abelianEnd0Action_range X hAlg
  exact ⟨(AlgEquiv.ofInjective ρ hinj).trans (Subalgebra.equivOfEq _ _ hrange)⟩

/-- The lattice-side split, as the bigraded family `latticeHodgePieces X`, is an internal direct
sum: `Hol ⊕ Anti = ℂ ⊗[ℚ] HQ X 1` (`spec_complexH1_split`) and the other pieces are `⊥`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1;
`spec_complexH1_split`. -/
theorem spec_latticeHodgePieces_isInternal : DirectSum.IsInternal (latticeHodgePieces X) :=
  spec_latticeHodgePieces_isInternal_aux X

example : LieSubalgebra ℚ (Module.End ℚ (HQ X 1)) :=
  hodgeLieAlgebra (latticeHodgePieces X) (spec_latticeHodgePieces_isInternal X)

/-- The rational commutant of the Hodge Lie algebra of the lattice-side split is the algebra of
its Hodge endomorphisms, unconditionally. By `EQWCore`'s
`spec_eqw_mem_centralizer_hodgeLieAlgebra_iff`, `T` commutes with the Hodge Lie algebra iff `T_ℂ`
commutes with the grading operator, which acts by `i` on `Hol` and by `-i` on `Anti`; since
`i ≠ -i` and the split is internal, that holds iff `T_ℂ` preserves both summands.
Source: Moonen, *An introduction to Mumford–Tate groups* (2004), §1–2; Deligne, *Théorie de
Hodge II*, Publ. Math. IHÉS 40 (1971), §2.1; `spec_eqw_mem_centralizer_hodgeLieAlgebra_iff`,
`gradingOperator_apply_of_mem`. -/
theorem spec_mem_centralizer_hodgeLieAlgebra_iff
    (hH : DirectSum.IsInternal (latticeHodgePieces X)) (T : Module.End ℚ (HQ X 1)) :
    T ∈ Subalgebra.centralizer ℚ
        (hodgeLieAlgebra (latticeHodgePieces X) hH : Set (Module.End ℚ (HQ X 1))) ↔
      T ∈ hodgeEndH1 X :=
  spec_mem_centralizer_hodgeLieAlgebra_iff_aux X hH T

-- Every endomorphism of `X` commutes with the Hodge Lie algebra.
example (hH : DirectSum.IsInternal (latticeHodgePieces X)) (f : AbelianEnd X) :
    abelianEndAction X f ∈ Subalgebra.centralizer ℚ
      (hodgeLieAlgebra (latticeHodgePieces X) hH : Set (Module.End ℚ (HQ X 1))) :=
  (spec_mem_centralizer_hodgeLieAlgebra_iff X hH _).2 (spec_abelianEndAction_hodge X f)

/-- The commutant equation, as an implication from `hAlg`: the rational commutant of the Hodge Lie
algebra of the lattice-side split is the image of `End⁰(X)` under its action on `HQ X 1`.
`spec_mem_centralizer_hodgeLieAlgebra_iff` and `spec_abelianEnd0Action_range`.
Source: Mumford, *Abelian Varieties*, §19 and §22; Moonen, *An introduction to Mumford–Tate
groups* (2004), §1–2 (`End⁰(A)` is the commutant of the Hodge group); for `hAlg`, Serre, GAGA
(1956), and Chow (1949). -/
theorem spec_centralizer_hodgeLieAlgebra_eq [IsCommMonObj X]
    (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F)
    (hH : DirectSum.IsInternal (latticeHodgePieces X)) :
    ∃ ρ : AbelianEnd0 X →ₐ[ℚ] (Module.End ℚ (HQ X 1))ᵐᵒᵖ,
      (∀ f, ρ (1 ⊗ₜ f) = MulOpposite.op (abelianEndAction X f)) ∧
        Subalgebra.centralizer ℚ
            (hodgeLieAlgebra (latticeHodgePieces X) hH : Set (Module.End ℚ (HQ X 1))) =
          ρ.range.unop :=
  spec_centralizer_hodgeLieAlgebra_eq_aux X hAlg hH

/-- Falsification check for the shape of the commutant: for `g ≥ 1` the commutant is a proper
subalgebra, so the commutant equation cannot be replaced by "the commutant is `End_ℚ(HQ X 1)`". -/
example (hH : DirectSum.IsInternal (latticeHodgePieces X)) (hg : 0 < dim X.left) :
    Subalgebra.centralizer ℚ
        (hodgeLieAlgebra (latticeHodgePieces X) hH : Set (Module.End ℚ (HQ X 1))) ≠ ⊤ :=
  fun h => by
  obtain ⟨T, hT⟩ := spec_exists_not_hodge X hg
  have hmem : T ∈ Subalgebra.centralizer ℚ
      (hodgeLieAlgebra (latticeHodgePieces X) hH : Set (Module.End ℚ (HQ X 1))) :=
    h ▸ Algebra.mem_top
  exact hT ((spec_mem_centralizer_hodgeLieAlgebra_iff X hH T).1 hmem).1

/-- The commutant equation in the form of `EQWCore`'s bridge binder `hcomm`, as an implication
from `hAlg`: if `End⁰(X) = ℚ[j]` for one endomorphism `j` (for the EQW route, `End⁰(X) = K` with
`j` a generator of `K`), the rational commutant of the Hodge Lie algebra of the lattice-side split
is `Algebra.adjoin ℚ {j^*}`. `⊇`: `j^*` is a Hodge endomorphism (stage 1) and the commutant is a
subalgebra; `⊆`: by `spec_exists_abelianEnd_of_hodge`, a commuting `T` has `N • T = f^*`, and
`1 ⊗ f` is a polynomial in `1 ⊗ j`, so `f^*` is the same polynomial in `j^*` (polynomials in one
element commute, so the order reversal of the action does not matter).
Source: F-1770 (EQW), the bridge `End⁰(A) = K`; Moonen, *An introduction to Mumford–Tate groups*
(2004), §1–2; Mumford, *Abelian Varieties*, §19; for `hAlg`, Serre, GAGA (1956), and Chow
(1949). -/
theorem spec_centralizer_eq_adjoin_of_adjoin_eq_top [IsCommMonObj X]
    (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F)
    (hH : DirectSum.IsInternal (latticeHodgePieces X)) (j : AbelianEnd X)
    (hK : Algebra.adjoin ℚ {(1 : ℚ) ⊗ₜ[ℤ] j} = (⊤ : Subalgebra ℚ (AbelianEnd0 X))) :
    Subalgebra.centralizer ℚ
        (hodgeLieAlgebra (latticeHodgePieces X) hH : Set (Module.End ℚ (HQ X 1))) =
      Algebra.adjoin ℚ {abelianEndAction X j} :=
  spec_centralizer_eq_adjoin_of_adjoin_eq_top_aux X hAlg hH j hK

/-- Falsification check for the hypothesis that the generator acts by an endomorphism of `X`:
for `g ≥ 1` some rational `T` (one that is not a Hodge endomorphism) has
`commutant ≠ Algebra.adjoin ℚ {T}`, since `T` lies in the right side and not in the left. -/
example (hH : DirectSum.IsInternal (latticeHodgePieces X)) (hg : 0 < dim X.left) :
    ∃ T : Module.End ℚ (HQ X 1), Subalgebra.centralizer ℚ
        (hodgeLieAlgebra (latticeHodgePieces X) hH : Set (Module.End ℚ (HQ X 1))) ≠
      Algebra.adjoin ℚ {T} := by
  obtain ⟨T, hT⟩ := spec_exists_not_hodge X hg
  refine ⟨T, fun h => hT ?_⟩
  have hmem : T ∈ Subalgebra.centralizer ℚ
      (hodgeLieAlgebra (latticeHodgePieces X) hH : Set (Module.End ℚ (HQ X 1))) :=
    h ▸ Algebra.self_mem_adjoin_singleton ℚ T
  exact ((spec_mem_centralizer_hodgeLieAlgebra_iff X hH T).1 hmem).1

/-- The consumer: with `HQ X 1` in the role of `V`, the lattice-side split in the role of `H`, and
`J = j^*`, the bridge binder `hcomm` of `EQWCore`'s assembly `spec_eqw_hSU_of_centralizer_eq` is
supplied by `spec_centralizer_eq_adjoin_of_adjoin_eq_top` under `hAlg` and `End⁰(X) = ℚ[j]`. The
remaining binders of the assembly stay open here. -/
example [IsCommMonObj X] [FiniteDimensional ℚ (HQ X 1)]
    (hAlg : ∀ F : ComplexPoint X → ComplexPoint X,
      ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω F →
        ∃ h : X ⟶ X, Point.map h = F)
    (hH : DirectSum.IsInternal (latticeHodgePieces X)) (j : AbelianEnd X)
    (hK : Algebra.adjoin ℚ {(1 : ℚ) ⊗ₜ[ℤ] j} = (⊤ : Subalgebra ℚ (AbelianEnd0 X)))
    (hdim : Module.finrank ℚ (HQ X 1) = 12 ∨ Module.finrank ℚ (HQ X 1) = 16)
    (E : LinearMap.BilinForm ℚ (HQ X 1)) (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hJ : (abelianEndAction X j).comp (abelianEndAction X j) = (-3 : ℚ) • LinearMap.id)
    (hskew : ∀ x y, E (abelianEndAction X j x) y = -E x (abelianEndAction X j y))
    (hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → latticeHodgePieces X pq = ⊥)
    (hJH : ∀ pq, ∀ x ∈ latticeHodgePieces X pq,
      (abelianEndAction X j).baseChange ℂ x ∈ latticeHodgePieces X pq)
    (hiso₁₀ : ∀ x ∈ latticeHodgePieces X (1, 0), ∀ y ∈ latticeHodgePieces X (1, 0),
      E.baseChange ℂ x y = 0)
    (hiso₀₁ : ∀ x ∈ latticeHodgePieces X (0, 1), ∀ y ∈ latticeHodgePieces X (0, 1),
      E.baseChange ℂ x y = 0)
    (hbalPos : Module.finrank ℂ ↥(latticeHodgePieces X (1, 0) ⊓
        Module.End.eigenspace ((abelianEndAction X j).baseChange ℂ) WeilPower.root) =
      Module.finrank ℂ ↥(latticeHodgePieces X (0, 1) ⊓
        Module.End.eigenspace ((abelianEndAction X j).baseChange ℂ) WeilPower.root))
    (hbalNeg : Module.finrank ℂ ↥(latticeHodgePieces X (1, 0) ⊓
        Module.End.eigenspace ((abelianEndAction X j).baseChange ℂ) (-WeilPower.root)) =
      Module.finrank ℂ ↥(latticeHodgePieces X (0, 1) ⊓
        Module.End.eigenspace ((abelianEndAction X j).baseChange ℂ) (-WeilPower.root)))
    (hred : LieAlgebra.radical ℚ (hodgeLieAlgebra (latticeHodgePieces X) hH) =
      LieAlgebra.center ℚ (hodgeLieAlgebra (latticeHodgePieces X) hH))
    (hclass : EQWClassification E hE (abelianEndAction X j) hJ hskew) :
    complexSpan (hodgeLieAlgebra (latticeHodgePieces X) hH).toSubmodule =
      (WeilPower.complexSU E hE (abelianEndAction X j) hJ hskew).toSubmodule :=
  spec_eqw_hSU_of_centralizer_eq hdim E hE hAlt (abelianEndAction X j) hJ hskew hsupp hJH
    hiso₁₀ hiso₀₁ hbalPos hbalNeg hred
    (spec_centralizer_eq_adjoin_of_adjoin_eq_top X hAlg hH j hK) hclass

end HodgeLean.Adapters
