import Mathlib

/-!
# The Hodge Lie algebra of a rational Hodge structure

Foundations target T6 (`docs/roadmap/foundations.md` §4 T6, §6 Rank 5).

## Setting

`V` is a finite-dimensional `ℚ`-vector space and `H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)` a raw
Hodge decomposition: `DirectSum.IsInternal H`. Conjugation symmetry (`complexConj` maps `H (p, q)`
into `H (q, p)`) and purity (`H (p, q) = ⊥` unless `p + q = n`) are hypotheses only of the
statements that use them; the characterization of the invariants needs neither.

## Main definitions

* `gradingOperator H hH : Module.End ℂ (ℂ ⊗[ℚ] V)`: the grading operator `C`, acting by
  `i (p - q)` on `H (p, q)` (the derivative of Deligne's `h` along the unit circle).
* `rationalLieHull c`: the smallest `ℚ`-Lie subalgebra of `End_ℚ V` whose complexification (the
  `ℂ`-span `complexSpan` of the base changes `X_ℂ` of its elements) contains `c`.
* `hodgeLieAlgebra H hH := rationalLieHull (gradingOperator H hH)`, the Lie-algebra substitute
  for the Hodge group (special Mumford–Tate group).
* `complexAction N : End_ℂ (ℂ ⊗ V) →ₗ[ℂ] End_ℂ (ℂ ⊗ N)`: the complexification of a Lie module `N`
  over `End_ℚ V` (for `V`, `V ⊗ V`, `Module.Dual ℚ V`, ...).
* `tensorHodge H`: the Hodge decomposition of `V ⊗ V`.

## Main results

* `gradingOperator_complexConj`: `C` commutes with conjugation (it is defined over `ℝ`).
* `gradingOperator_mem_span_hodgeLieAlgebra`, `hodgeLieAlgebra_le`: the minimum is attained
  (base change to `ℂ` commutes with intersections, `baseChange_inf`, and
  `ℂ ⊗ End_ℚ V ≃ End_ℂ (ℂ ⊗ V)`, `endBaseChangeEquiv`).
* `mem_maxTrivSubmodule_hodgeLieAlgebra_iff`: for any Lie module `N` over `End_ℚ V`, `v ∈ N` is
  killed by the Hodge Lie algebra iff `complexAction N C` kills `1 ⊗ v`.
* `mem_maxTrivSubmodule_hodgeLieAlgebra_iff_mem_iSup`, `..._iff_of_pure`: the invariants in `V`
  are the Hodge classes.
* `isInternal_tensorHodge`, `gradingOperator_tensorHodge`,
  `mem_maxTrivSubmodule_hodgeLieAlgebra_tensor_iff`: the tensor pieces form a Hodge
  decomposition of `V ⊗ V` whose grading operator is the derivation `C ⊗ 1 + 1 ⊗ C`, and its
  Hodge classes are the invariants of the Hodge Lie algebra acting by derivations.
* Examples: `hodgeLieAlgebra_trivialHodge` (`ℚ(0)` gives `⊥`), `hodgeLieAlgebra_rotation` (CM by
  `ℚ(i)` on `ℚ²` gives the line through the rotation), `weightTwo_single_zero` (a rational class
  of type `(2, 0) + (0, 2)` is rejected).

## The choice of `complexAction`

`complexAction N` is `LinearMap.tensorProduct ∘ (ρ.baseChange ℂ) ∘ endBaseChangeEquiv.symm`, with
`ρ = LieModule.toEnd`: it goes through the isomorphism `End_ℂ (ℂ ⊗ V) ≃ ℂ ⊗ End_ℚ V` (finite
dimension), so it is defined on all of `End_ℂ (ℂ ⊗ V)` with no compatibility hypothesis, and
`complexAction_baseChange` says it extends `X ↦ (ρ X)_ℂ`. On `V` it is the identity
(`complexAction_self`); on `V ⊗ V` it is the derivation (`complexAction_tensor_complexTensorMul`).

## Not formalized

The comparison with the Hodge group: `Hg` is connected, so `Hg` fixes `v` iff `Lie(Hg)` kills `v`
iff (by minimality, `Lie(Hg)` being the algebraic hull of `hodgeLieAlgebra`) the Hodge Lie
algebra kills `v`. Algebraic groups are absent from Mathlib, so this file never mentions `Hg`;
the statement about invariants is proved directly for the Lie algebra.

Relation to the goal: HC no distance; AV milestone no distance; F-1575 step 2 and "the Hodge ring
is the invariant ring" become statable.
-/

open TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

namespace HodgeLean.Foundations

section Grading

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Complex conjugation on the `ℂ` factor of `ℂ ⊗[ℚ] V`, a `ℚ`-linear map.

Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §2.1 (the complex conjugation
of `V_ℂ = V ⊗ ℂ` with respect to the real structure `V_ℝ`). -/
def complexConj (V : Type*) [AddCommGroup V] [Module ℚ V] : ℂ ⊗[ℚ] V →ₗ[ℚ] ℂ ⊗[ℚ] V :=
  LinearMap.rTensor V (starRingEnd ℂ).toRatAlgHom.toLinearMap

@[simp]
theorem complexConj_tmul (z : ℂ) (v : V) :
    complexConj V (z ⊗ₜ v) = (starRingEnd ℂ z) ⊗ₜ v := rfl

theorem complexConj_smul (z : ℂ) (x : ℂ ⊗[ℚ] V) :
    complexConj V (z • x) = starRingEnd ℂ z • complexConj V x := by
  induction x using TensorProduct.inductionOn with
  | tmul w v => simp [smul_tmul']
  | add x y hx hy => simp [smul_add, hx, hy]

example (v : V) : complexConj V (Complex.I ⊗ₜ v) = -(Complex.I ⊗ₜ v) := by
  simp [neg_tmul]

variable (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)

/-- The grading operator `C` of a Hodge decomposition `ℂ ⊗[ℚ] V = ⨁ H (p, q)`: it acts on
`H (p, q)` by multiplication by `i (p - q)`. It is the derivative at `1` of the Deligne torus
action restricted to the unit circle, `z ↦ z^p z̄^q` on `H (p, q)`, so it generates the Lie algebra
of the circle `U(1) ⊆ 𝕊`, whose `ℚ`-Zariski closure is the Hodge group. It does not see the
weight: the Mumford–Tate group also contains the weight homothety, the Hodge group does not.

Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §2.1 (the Hodge structure as
an action of `𝕊`; the operator here is its derivative `dh`, acting by `i (p - q)`, not the Weil
operator `h(i)`, which acts by `i ^ (p - q)`); Moonen, *An introduction to Mumford–Tate
groups* (lecture notes, 2004), §1–2 (the Hodge group as the `ℚ`-Zariski closure of `h(U(1))`). -/
def gradingOperator : Module.End ℂ (ℂ ⊗[ℚ] V) :=
  DirectSum.toModule ℂ (ℤ × ℤ) _
      (fun pq => (Complex.I * ((pq.1 : ℂ) - pq.2)) • (H pq).subtype) ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap H) hH).symm.toLinearMap

theorem gradingOperator_apply_of_mem {p q : ℤ} {x : ℂ ⊗[ℚ] V} (hx : x ∈ H (p, q)) :
    gradingOperator H hH x = (Complex.I * ((p : ℂ) - q)) • x := by
  have h : (LinearEquiv.ofBijective (DirectSum.coeLinearMap H) hH).symm x =
      DirectSum.lof ℂ (ℤ × ℤ) (fun i => H i) (p, q) ⟨x, hx⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    exact (DirectSum.coeLinearMap_of H (p, q) ⟨x, hx⟩).symm
  simp only [gradingOperator, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h,
    DirectSum.toModule_lof, LinearMap.smul_apply, Submodule.subtype_apply]

/-- Two endomorphisms that agree on every piece of an internal decomposition are equal. -/
theorem linearMap_ext_of_isInternal {ι R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [DecidableEq ι]
    {A : ι → Submodule R M} (hA : DirectSum.IsInternal A) {f g : M →ₗ[R] N}
    (h : ∀ i, ∀ x ∈ A i, f x = g x) : f = g := by
  ext x
  have hx : x ∈ ⨆ i, A i := by rw [hA.submodule_iSup_eq_top]; trivial
  induction hx using Submodule.iSup_induction' with
  | mem i x hx => exact h i x hx
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]

/-- The grading operator commutes with complex conjugation, given the conjugation symmetry
`conj (H (p, q)) ⊆ H (q, p)` of the Hodge decomposition. So `C` is defined over `ℝ` (not over
`ℚ` in general).

Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §2.1 (`h` is defined over
`ℝ`). -/
theorem gradingOperator_complexConj
    (hconj : ∀ p q : ℤ, ∀ x ∈ H (p, q), complexConj V x ∈ H (q, p)) (x : ℂ ⊗[ℚ] V) :
    gradingOperator H hH (complexConj V x) = complexConj V (gradingOperator H hH x) := by
  have hx : x ∈ ⨆ i, H i := by rw [hH.submodule_iSup_eq_top]; trivial
  induction hx using Submodule.iSup_induction' with
  | mem i x hx =>
    obtain ⟨p, q⟩ := i
    rw [gradingOperator_apply_of_mem H hH (hconj p q x hx), gradingOperator_apply_of_mem H hH hx,
      complexConj_smul]
    congr 1
    simp only [map_mul, Complex.conj_I, map_sub, map_intCast]
    ring
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]

end Grading

section BaseChange

/-- Over a field, base change to `ℂ` commutes with kernels (flatness). -/
theorem ker_baseChange_eq {M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (f : M →ₗ[ℚ] N) : LinearMap.ker (f.baseChange ℂ) = (LinearMap.ker f).baseChange ℂ :=
  Module.Flat.ker_lTensor_eq (S := ℂ) (M := ℂ) f

/-- Base change to `ℂ` commutes with binary intersections of `ℚ`-subspaces. -/
theorem baseChange_inf {M : Type*} [AddCommGroup M] [Module ℚ M] (A B : Submodule ℚ M) :
    (A ⊓ B).baseChange ℂ = A.baseChange ℂ ⊓ B.baseChange ℂ := by
  refine le_antisymm (le_inf (Submodule.baseChange_mono ℂ inf_le_left)
    (Submodule.baseChange_mono ℂ inf_le_right)) ?_
  intro x hx
  obtain ⟨hA, hB⟩ := Submodule.mem_inf.mp hx
  have hAB : A ⊓ B = LinearMap.ker (A.mkQ.prod B.mkQ) := by
    rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  have hprod : A.mkQ.prod B.mkQ = (LinearMap.inl ℚ _ _).comp A.mkQ +
      (LinearMap.inr ℚ _ _).comp B.mkQ :=
    LinearMap.ext fun y => Prod.ext (by simp) (by simp)
  rw [← Submodule.ker_mkQ A, ← ker_baseChange_eq, LinearMap.mem_ker] at hA
  rw [← Submodule.ker_mkQ B, ← ker_baseChange_eq, LinearMap.mem_ker] at hB
  rw [hAB, ← ker_baseChange_eq, LinearMap.mem_ker, hprod, LinearMap.baseChange_add,
    LinearMap.baseChange_comp, LinearMap.baseChange_comp]
  simp [hA, hB]

variable (V : Type*) [AddCommGroup V] [Module ℚ V]

theorem tensorProductEnd_tmul (z : ℂ) (X : Module.End ℚ V) :
    LinearMap.tensorProductEnd ℚ ℂ V (z ⊗ₜ X) = z • X.baseChange ℂ := rfl

theorem tensorProductEnd_one_tmul (X : Module.End ℚ V) :
    LinearMap.tensorProductEnd ℚ ℂ V (1 ⊗ₜ X) = X.baseChange ℂ := by
  rw [tensorProductEnd_tmul, one_smul]

/-- For finite-dimensional `V`, the natural map `ℂ ⊗[ℚ] End_ℚ V → End_ℂ (ℂ ⊗[ℚ] V)` is
bijective. -/
theorem tensorProductEnd_bijective [FiniteDimensional ℚ V] :
    Function.Bijective (LinearMap.tensorProductEnd ℚ ℂ V) := by
  classical
  let b := Module.finBasis ℚ V
  let bC := Algebra.TensorProduct.basis ℂ b
  let e₁ := LinearEquiv.baseChange ℚ ℂ _ _ (LinearMap.toMatrix b b)
  let e₂ := (matrixEquivTensor (Fin (Module.finrank ℚ V)) ℚ ℂ).symm
  have key : ∀ y, LinearMap.toMatrix bC bC (LinearMap.tensorProductEnd ℚ ℂ V y) = e₂ (e₁ y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul z X =>
      rw [tensorProductEnd_tmul, map_smul]
      simp [e₁, e₂, bC, LinearMap.toMatrix_baseChange]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  have h : ⇑(LinearMap.tensorProductEnd ℚ ℂ V) =
      (LinearMap.toMatrix bC bC).symm ∘ e₂ ∘ e₁ := by
    funext y
    simp [← key]
  rw [h]
  exact (LinearMap.toMatrix bC bC).symm.bijective.comp (e₂.bijective.comp e₁.bijective)

/-- The `ℂ`-linear isomorphism `ℂ ⊗[ℚ] End_ℚ V ≃ End_ℂ (ℂ ⊗[ℚ] V)`, `z ⊗ X ↦ z • X_ℂ`, for `V`
finite-dimensional.

Source: Bourbaki, *Algèbre*, ch. II (extension of the ring of scalars; `Hom` of finite free
modules commutes with it). -/
def endBaseChangeEquiv [FiniteDimensional ℚ V] :
    ℂ ⊗[ℚ] Module.End ℚ V ≃ₗ[ℂ] Module.End ℂ (ℂ ⊗[ℚ] V) :=
  LinearEquiv.ofBijective (LinearMap.tensorProductEnd ℚ ℂ V).toLinearMap
    (tensorProductEnd_bijective V)

@[simp]
theorem endBaseChangeEquiv_apply [FiniteDimensional ℚ V] (y : ℂ ⊗[ℚ] Module.End ℚ V) :
    endBaseChangeEquiv V y = LinearMap.tensorProductEnd ℚ ℂ V y := rfl

variable {V}

/-- The complexification `W ⊗ ℂ` of a `ℚ`-subspace `W ⊆ End_ℚ V`, as the `ℂ`-span of the base
changes `X_ℂ` of its elements inside `End_ℂ (ℂ ⊗[ℚ] V)`.

Source: Bourbaki, *Algèbre*, ch. II (extension of the ring of scalars). -/
def complexSpan (W : Submodule ℚ (Module.End ℚ V)) : Submodule ℂ (Module.End ℂ (ℂ ⊗[ℚ] V)) :=
  Submodule.span ℂ ((fun X : Module.End ℚ V => X.baseChange ℂ) '' W)

theorem complexSpan_eq_map (W : Submodule ℚ (Module.End ℚ V)) :
    complexSpan W = (W.baseChange ℂ).map (LinearMap.tensorProductEnd ℚ ℂ V).toLinearMap := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span, complexSpan, Submodule.map_coe,
    ← Set.image_comp]
  congr 2
  funext X
  simp only [Function.comp_apply, TensorProduct.mk_apply, AlgHom.toLinearMap_apply,
    tensorProductEnd_one_tmul]

theorem mem_complexSpan_iff [FiniteDimensional ℚ V] (W : Submodule ℚ (Module.End ℚ V))
    (c : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    c ∈ complexSpan W ↔ (endBaseChangeEquiv V).symm c ∈ W.baseChange ℂ := by
  rw [complexSpan_eq_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : (endBaseChangeEquiv V).symm (LinearMap.tensorProductEnd ℚ ℂ V y) = y :=
      (endBaseChangeEquiv V).symm_apply_apply y
    rw [AlgHom.toLinearMap_apply, this]
    exact hy
  · intro h
    exact ⟨_, h, (endBaseChangeEquiv V).apply_symm_apply c⟩

theorem complexSpan_top [FiniteDimensional ℚ V] :
    complexSpan (⊤ : Submodule ℚ (Module.End ℚ V)) = ⊤ := by
  rw [eq_top_iff]
  intro c _
  rw [mem_complexSpan_iff, Submodule.baseChange_top]
  trivial

theorem complexSpan_inf [FiniteDimensional ℚ V] (W W' : Submodule ℚ (Module.End ℚ V)) :
    complexSpan (W ⊓ W') = complexSpan W ⊓ complexSpan W' := by
  ext c
  simp only [Submodule.mem_inf, mem_complexSpan_iff, baseChange_inf]

end BaseChange

section Hull

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The smallest `ℚ`-Lie subalgebra `L` of `End_ℚ V` whose complexification contains a given
complex endomorphism `c` of `ℂ ⊗[ℚ] V`.

Source: Moonen, *An introduction to Mumford–Tate groups* (lecture notes, 2004), §1–2 (the
Mumford–Tate and Hodge groups as the smallest `ℚ`-algebraic subgroups through whose real points
`h` factors; this is the Lie-algebra analogue). -/
def rationalLieHull (c : Module.End ℂ (ℂ ⊗[ℚ] V)) : LieSubalgebra ℚ (Module.End ℚ V) :=
  sInf {L | c ∈ complexSpan L.toSubmodule}

theorem rationalLieHull_le {c : Module.End ℂ (ℂ ⊗[ℚ] V)} {L : LieSubalgebra ℚ (Module.End ℚ V)}
    (h : c ∈ complexSpan L.toSubmodule) : rationalLieHull c ≤ L :=
  sInf_le h

/-- The minimum defining `rationalLieHull` is attained: `c` lies in the complexification of
`rationalLieHull c`. -/
theorem mem_complexSpan_rationalLieHull [FiniteDimensional ℚ V] (c : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    c ∈ complexSpan (rationalLieHull c).toSubmodule := by
  let S : Set (LieSubalgebra ℚ (Module.End ℚ V)) := {L | c ∈ complexSpan L.toSubmodule}
  have hS : S.Nonempty := ⟨⊤, by simp [S, complexSpan_top]⟩
  let f : LieSubalgebra ℚ (Module.End ℚ V) → ℕ := fun L => Module.finrank ℚ L.toSubmodule
  let L₀ := Function.argminOn f S hS
  have hL₀ : L₀ ∈ S := Function.argminOn_mem f S hS
  have hle : ∀ L ∈ S, L₀ ≤ L := by
    intro L hL
    have hinf : L ⊓ L₀ ∈ S := by
      change c ∈ complexSpan (L ⊓ L₀).toSubmodule
      rw [LieSubalgebra.inf_toSubmodule, complexSpan_inf]
      exact ⟨hL, hL₀⟩
    have h1 : f L₀ ≤ f (L ⊓ L₀) := Function.argminOn_le f S hinf
    have h2 : (L ⊓ L₀).toSubmodule ≤ L₀.toSubmodule := by
      rw [LieSubalgebra.toSubmodule_le_toSubmodule]
      exact inf_le_right
    have h3 : (L ⊓ L₀).toSubmodule = L₀.toSubmodule :=
      Submodule.eq_of_le_of_finrank_le h2 h1
    have h4 : L ⊓ L₀ = L₀ := LieSubalgebra.toSubmodule_injective h3
    rw [← h4]
    exact inf_le_left
  have heq : rationalLieHull c = L₀ := le_antisymm (sInf_le hL₀) (le_sInf hle)
  rw [heq]
  exact hL₀

end Hull

section Invariants

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (N : Type*) [AddCommGroup N] [Module ℚ N] [LieRingModule (Module.End ℚ V) N]
  [LieModule ℚ (Module.End ℚ V) N]

/-- The complexification of a Lie module `N` over `End_ℚ V`: the `ℂ`-linear map
`End_ℂ (ℂ ⊗[ℚ] V) → End_ℂ (ℂ ⊗[ℚ] N)` sending `z • X_ℂ` to `z • (ρ X)_ℂ`, where `ρ X` is the action
of a rational endomorphism `X` on `N`. It is defined through the isomorphism
`End_ℂ (ℂ ⊗[ℚ] V) ≃ ℂ ⊗[ℚ] End_ℚ V` (finite dimension), so it needs no compatibility hypothesis;
`complexAction_baseChange` says it extends `ρ`.

Source: Bourbaki, *Groupes et algèbres de Lie*, ch. I (extension of scalars of a Lie algebra and
of its modules). -/
def complexAction [FiniteDimensional ℚ V] :
    Module.End ℂ (ℂ ⊗[ℚ] V) →ₗ[ℂ] Module.End ℂ (ℂ ⊗[ℚ] N) :=
  LinearMap.tensorProduct ℚ ℂ N N ∘ₗ
    ((LieModule.toEnd ℚ (Module.End ℚ V) N : Module.End ℚ V →ₗ[ℚ] Module.End ℚ N).baseChange ℂ) ∘ₗ
    (endBaseChangeEquiv V).symm.toLinearMap

theorem complexAction_baseChange [FiniteDimensional ℚ V] (X : Module.End ℚ V) :
    complexAction N (X.baseChange ℂ) = (LieModule.toEnd ℚ (Module.End ℚ V) N X).baseChange ℂ := by
  have h : (endBaseChangeEquiv V).symm (X.baseChange ℂ) = 1 ⊗ₜ X := by
    rw [LinearEquiv.symm_apply_eq, endBaseChangeEquiv_apply, tensorProductEnd_one_tmul]
  simp only [complexAction, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h,
    LinearMap.baseChange_tmul]
  exact one_smul ℂ _

/-- The action of `z ⊗ X` on `1 ⊗ v`, linearly in `z ⊗ X`. -/
theorem tensorProduct_baseChange_toEnd_one_tmul (y : ℂ ⊗[ℚ] Module.End ℚ V) (v : N) :
    LinearMap.tensorProduct ℚ ℂ N N
        ((LieModule.toEnd ℚ (Module.End ℚ V) N : Module.End ℚ V →ₗ[ℚ] Module.End ℚ N).baseChange
          ℂ y) (1 ⊗ₜ v) =
      ((LieModule.toEnd ℚ (Module.End ℚ V) N : Module.End ℚ V →ₗ[ℚ] Module.End ℚ N).flip
        v).baseChange ℂ y := by
  induction y using TensorProduct.inductionOn with
  | tmul z X =>
    change (z • ((LieModule.toEnd ℚ (Module.End ℚ V) N X).baseChange ℂ)) (1 ⊗ₜ v) = _
    simp [smul_tmul']
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']

/-- The annihilator `{X | X • v = 0}` of an element of a Lie module, a Lie subalgebra.

Source: Bourbaki, *Groupes et algèbres de Lie*, ch. I (Lie modules; the annihilator of an element
is a subalgebra). -/
def lieAnnihilator (v : N) : LieSubalgebra ℚ (Module.End ℚ V) :=
  { LinearMap.ker
      ((LieModule.toEnd ℚ (Module.End ℚ V) N : Module.End ℚ V →ₗ[ℚ] Module.End ℚ N).flip v) with
    lie_mem' := by
      intro X Y hX hY
      simp only [Submodule.carrier_eq_coe, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply,
        LieHom.coe_toLinearMap, LieModule.toEnd_apply_apply] at hX hY ⊢
      rw [lie_lie, hX, hY, lie_zero, lie_zero, sub_zero] }

theorem mem_lieAnnihilator {v : N} {X : Module.End ℚ V} :
    X ∈ lieAnnihilator N v ↔ ⁅X, v⁆ = 0 := by
  change X ∈ LinearMap.ker _ ↔ _
  simp

/-- **Invariants of the rational Lie hull.** An element `v` of a Lie module `N` over `End_ℚ V` is
killed by the rational Lie hull of `c` if and only if the complexified action of `c` kills
`1 ⊗ v`. -/
theorem mem_maxTrivSubmodule_rationalLieHull_iff [FiniteDimensional ℚ V]
    (c : Module.End ℂ (ℂ ⊗[ℚ] V)) (v : N) :
    v ∈ LieModule.maxTrivSubmodule ℚ (rationalLieHull c) N ↔ complexAction N c (1 ⊗ₜ v) = 0 := by
  have h1 : v ∈ LieModule.maxTrivSubmodule ℚ (rationalLieHull c) N ↔
      rationalLieHull c ≤ lieAnnihilator N v := by
    rw [LieModule.mem_maxTrivSubmodule]
    constructor
    · intro h X hX
      rw [mem_lieAnnihilator]
      simpa using h ⟨X, hX⟩
    · intro h X
      rw [LieSubalgebra.coe_bracket_of_module]
      exact (mem_lieAnnihilator N).mp (h X.2)
  have h2 : rationalLieHull c ≤ lieAnnihilator N v ↔
      c ∈ complexSpan (lieAnnihilator N v).toSubmodule := by
    constructor
    · intro h
      exact Submodule.span_mono (Set.image_mono h) (mem_complexSpan_rationalLieHull c)
    · exact rationalLieHull_le
  have h3 : complexAction N c (1 ⊗ₜ v) =
      ((LieModule.toEnd ℚ (Module.End ℚ V) N : Module.End ℚ V →ₗ[ℚ] Module.End ℚ N).flip
        v).baseChange ℂ ((endBaseChangeEquiv V).symm c) :=
    tensorProduct_baseChange_toEnd_one_tmul N _ v
  rw [h1, h2, mem_complexSpan_iff, h3, ← LinearMap.mem_ker, ker_baseChange_eq]
  rfl

/-- On `N = V` itself the complexified action is the identity. -/
theorem complexAction_self [FiniteDimensional ℚ V] (c : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    complexAction V c = c := by
  simp only [complexAction, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LieModule.toEnd_module_end]
  have : ((LieHom.id : Module.End ℚ V →ₗ⁅ℚ⁆ Module.End ℚ V) : Module.End ℚ V →ₗ[ℚ] _) =
      LinearMap.id := rfl
  rw [this, LinearMap.baseChange_id, LinearMap.id_apply]
  exact (endBaseChangeEquiv V).apply_symm_apply c

end Invariants

section Diagonal

/-- If `ℂ`-subspaces `G (p, q)` span `W` and `D` acts on `G (p, q)` by `i (p - q)`, the kernel of
`D` is the sum of the diagonal pieces `G (p, p)`. No independence of the `G (p, q)` is needed:
it comes from the independence of eigenspaces. -/
theorem ker_eq_iSup_diag {W : Type*} [AddCommGroup W] [Module ℂ W] (G : ℤ × ℤ → Submodule ℂ W)
    (hG : ⨆ i, G i = ⊤) (D : Module.End ℂ W)
    (hD : ∀ p q : ℤ, ∀ x ∈ G (p, q), D x = (Complex.I * ((p : ℂ) - q)) • x) :
    LinearMap.ker D = ⨆ p : ℤ, G (p, p) := by
  have hGle : ∀ i : ℤ × ℤ, G i ≤ D.eigenspace (Complex.I * ((i.1 - i.2 : ℤ) : ℂ)) := by
    rintro ⟨p, q⟩ x hx
    rw [Module.End.mem_eigenspace_iff, hD p q x hx]
    push_cast
    rfl
  refine le_antisymm ?_ (iSup_le fun p x hx => by simp [LinearMap.mem_ker, hD p p x hx])
  intro x hx
  let E : ℤ → Submodule ℂ W := fun d => ⨆ (i : ℤ × ℤ) (_ : i.1 - i.2 = d), G i
  have hE : ⨆ d, E d = ⊤ := by
    rw [eq_top_iff, ← hG]
    exact iSup_le fun i => le_iSup_of_le (i.1 - i.2)
      (le_iSup₂ (f := fun (j : ℤ × ℤ) (_ : j.1 - j.2 = i.1 - i.2) => G j) i rfl)
  have hxE : x ∈ E 0 ⊔ ⨆ (d) (_ : d ≠ 0), E d := by
    rw [← iSup_split_single E 0, hE]
    trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hxE
  have hEμ : ∀ d : ℤ, E d ≤ D.eigenspace (Complex.I * d) :=
    fun d => iSup₂_le fun i hi => hi ▸ hGle i
  have hb' : b ∈ ⨆ μ ∈ ({0}ᶜ : Set ℂ), D.eigenspace μ := by
    refine (iSup₂_le fun d hd => ?_ : ⨆ (d) (_ : d ≠ 0), E d ≤ _) hb
    refine le_trans (hEμ d) (le_iSup₂_of_le (Complex.I * d) ?_ le_rfl)
    simp [Complex.I_ne_zero, hd]
  have hb0 : b ∈ D.eigenspace 0 := by
    have hab : b = (a + b) - a := by abel
    rw [hab]
    refine sub_mem ?_ ?_
    · rw [Module.End.mem_eigenspace_iff, zero_smul]
      exact hx
    · simpa using hEμ 0 ha
  have hdis := (Module.End.eigenspaces_iSupIndep D).disjoint_biSup (x := (0 : ℂ))
    (y := ({0}ᶜ : Set ℂ)) (by simp)
  rw [Submodule.disjoint_def.mp hdis b hb0 hb', add_zero]
  refine (iSup₂_le fun i hi => ?_ : E 0 ≤ _) ha
  obtain ⟨p, q⟩ := i
  have hqp : q = p := by simp at hi; omega
  subst hqp
  exact le_iSup (fun r : ℤ => G (r, r)) q

end Diagonal

section HodgeLieAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)

/-- The **Hodge Lie algebra** of a rational Hodge decomposition: the smallest `ℚ`-Lie subalgebra
`𝔥` of `End_ℚ V` whose complexification `𝔥 ⊗ ℂ ⊆ End_ℂ (ℂ ⊗[ℚ] V)` contains the grading operator
`C` (acting by `i (p - q)` on `H (p, q)`). It plays the role of the Lie algebra of the Hodge
group (the *special* Mumford–Tate group), and its invariants are the classes of type `(p, p)` in
every weight, with no Tate twist. For a conjugation-symmetric decomposition of nonzero weight on
`V ≠ 0`, `C` has trace zero, so `𝔥 ⊆ 𝔰𝔩(V)` and `𝔥` does not contain the weight operator; that
is not proved here, and without conjugation symmetry it can fail (`V = ℚ`, `H (1, 0) = ⊤` gives
`𝔥 = ℚ · id`).

Source: Moonen, *An introduction to Mumford–Tate groups* (lecture notes, 2004), §1–2 (the Hodge
group `Hg`, the smallest `ℚ`-algebraic subgroup of `GL(V)` whose real points contain
`h(U(1))`); Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §2.1 (`h` and `C`). -/
def hodgeLieAlgebra : LieSubalgebra ℚ (Module.End ℚ V) :=
  rationalLieHull (gradingOperator H hH)

theorem hodgeLieAlgebra_eq_sInf :
    hodgeLieAlgebra H hH = sInf {L | gradingOperator H hH ∈
      Submodule.span ℂ ((fun X : Module.End ℚ V => X.baseChange ℂ) '' (L.toSubmodule : Set _))} :=
  rfl

/-- The minimum defining the Hodge Lie algebra is attained. -/
theorem gradingOperator_mem_span_hodgeLieAlgebra [FiniteDimensional ℚ V] :
    gradingOperator H hH ∈ Submodule.span ℂ
      ((fun X : Module.End ℚ V => X.baseChange ℂ) ''
        ((hodgeLieAlgebra H hH).toSubmodule : Set _)) :=
  mem_complexSpan_rationalLieHull _

/-- Minimality of the Hodge Lie algebra. -/
theorem hodgeLieAlgebra_le {L : LieSubalgebra ℚ (Module.End ℚ V)}
    (h : gradingOperator H hH ∈ Submodule.span ℂ
      ((fun X : Module.End ℚ V => X.baseChange ℂ) '' (L.toSubmodule : Set _))) :
    hodgeLieAlgebra H hH ≤ L :=
  rationalLieHull_le h

/-- **Invariants of the Hodge Lie algebra, general form.** For any Lie module `N` over
`End_ℚ V` (for example `V`, `V ⊗ V`, `Module.Dual ℚ V`), a rational `v ∈ N` is killed by the Hodge
Lie algebra if and only if the complexified grading operator kills `1 ⊗ v`. -/
theorem mem_maxTrivSubmodule_hodgeLieAlgebra_iff [FiniteDimensional ℚ V]
    (N : Type*) [AddCommGroup N] [Module ℚ N] [LieRingModule (Module.End ℚ V) N]
    [LieModule ℚ (Module.End ℚ V) N] (v : N) :
    v ∈ LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH) N ↔
      complexAction N (gradingOperator H hH) (1 ⊗ₜ v) = 0 :=
  mem_maxTrivSubmodule_rationalLieHull_iff N _ v

/-- The kernel of the grading operator is the sum of the pieces of type `(p, p)`. -/
theorem ker_gradingOperator : LinearMap.ker (gradingOperator H hH) = ⨆ p : ℤ, H (p, p) :=
  ker_eq_iSup_diag H hH.submodule_iSup_eq_top _ fun _ _ _ hx => gradingOperator_apply_of_mem H hH hx

/-- **Hodge classes are the invariants of the Hodge Lie algebra.** A rational vector `v ∈ V` is
killed by `hodgeLieAlgebra` if and only if `1 ⊗ v` lies in the sum of the pieces `H (p, p)`.

No register entry; it makes F-1575 step 2 statable. HC: no distance. AV milestone: no
distance. -/
theorem mem_maxTrivSubmodule_hodgeLieAlgebra_iff_mem_iSup [FiniteDimensional ℚ V] (v : V) :
    v ∈ LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH) V ↔ 1 ⊗ₜ v ∈ ⨆ p : ℤ, H (p, p) := by
  rw [mem_maxTrivSubmodule_hodgeLieAlgebra_iff, complexAction_self, ← LinearMap.mem_ker,
    ker_gradingOperator]

/-- **Hodge classes in a pure Hodge structure.** If the decomposition is pure of weight `n`, a
rational `v` is killed by the Hodge Lie algebra if and only if `v = 0`, or `n` is even and
`1 ⊗ v` has type `(n/2, n/2)`. -/
theorem mem_maxTrivSubmodule_hodgeLieAlgebra_iff_of_pure [FiniteDimensional ℚ V] {n : ℤ}
    (hpure : ∀ p q : ℤ, p + q ≠ n → H (p, q) = ⊥) (v : V) :
    v ∈ LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH) V ↔
      v = 0 ∨ (Even n ∧ 1 ⊗ₜ v ∈ H (n / 2, n / 2)) := by
  rw [mem_maxTrivSubmodule_hodgeLieAlgebra_iff_mem_iSup]
  have hle : ⨆ p : ℤ, H (p, p) ≤ H (n / 2, n / 2) := iSup_le fun p => by
    by_cases hp : p + p = n
    · have : p = n / 2 := by omega
      rw [this]
    · rw [hpure p p hp]
      exact bot_le
  constructor
  · intro hv
    have hv' := hle hv
    by_cases hn : Even n
    · exact Or.inr ⟨hn, hv'⟩
    · left
      have hb : H (n / 2, n / 2) = ⊥ := hpure _ _ fun h => hn ⟨n / 2, by omega⟩
      rw [hb, Submodule.mem_bot] at hv'
      exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff ℚ V (A := ℂ) v).mp hv'
  · rintro (rfl | ⟨-, hv⟩)
    · simp
    · exact le_iSup (fun p : ℤ => H (p, p)) (n / 2) hv

end HodgeLieAlgebra

section Examples

/-- A decomposition with two nonzero pieces `A` at `i` and `B` at `j`, complementary, is
internal. -/
theorem isInternal_pair {W : Type*} [AddCommGroup W] [Module ℂ W] {A B : Submodule ℂ W}
    (hAB : IsCompl A B) {i j : ℤ × ℤ} (hij : i ≠ j) :
    DirectSum.IsInternal (fun k => if k = i then A else if k = j then B else ⊥) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro k
    by_cases hk : k = i
    · subst hk
      simp only [↓reduceIte]
      refine hAB.disjoint.mono_right (iSup₂_le fun l hl => ?_)
      simp only [hl, ↓reduceIte]
      split_ifs <;> simp
    · by_cases hk' : k = j
      · subst hk'
        simp only [hk, ↓reduceIte]
        refine hAB.disjoint.symm.mono_right (iSup₂_le fun l hl => ?_)
        simp only [hl, ↓reduceIte]
        split_ifs <;> simp
      · simp [hk, hk']
  · rw [eq_top_iff, ← hAB.sup_eq_top]
    exact sup_le (le_iSup_of_le i (by simp)) (le_iSup_of_le j (by simp [hij.symm]))

section ComplexStructure

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (J : Module.End ℚ V)

/-- The line `ℚ ∙ J` spanned by one endomorphism, as an (abelian) Lie subalgebra.

Source: Bourbaki, *Groupes et algèbres de Lie*, ch. I (a one-dimensional subspace is an abelian
Lie subalgebra). -/
def lineLieSubalgebra : LieSubalgebra ℚ (Module.End ℚ V) :=
  { Submodule.span ℚ {J} with
    lie_mem' := by
      intro x y hx hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp [smul_lie, lie_smul] }

theorem lineLieSubalgebra_toSubmodule : (lineLieSubalgebra J).toSubmodule = ℚ ∙ J := rfl

/-- The Hodge decomposition of a rational complex structure `J`: `H (p, q)` is the `-i`
eigenspace of `J_ℂ`, `H (q, p)` the `i` eigenspace, all other pieces are `0`. For `(p, q) = (1, 0)`
this is the weight-one structure of a complex torus with complex structure `-J` in the convention
where the Weil operator acts by `i^{p-q}` (`C = -J` here).

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., ch. 1 (a complex structure on
`V_ℝ` and the decomposition `V_ℂ = V^{1,0} ⊕ V^{0,1}` into eigenspaces of `J`). -/
def complexStructureHodge (p q : ℤ) : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V) :=
  fun k => if k = (p, q) then Module.End.eigenspace (J.baseChange ℂ) (-Complex.I)
    else if k = (q, p) then Module.End.eigenspace (J.baseChange ℂ) Complex.I else ⊥

theorem complexStructureHodge_def (p q : ℤ) :
    complexStructureHodge J p q = fun k =>
      if k = (p, q) then Module.End.eigenspace (J.baseChange ℂ) (-Complex.I)
      else if k = (q, p) then Module.End.eigenspace (J.baseChange ℂ) Complex.I else ⊥ := rfl

variable {J} (hJ : J * J = -1)
include hJ

theorem baseChange_baseChange_of_sq (x : ℂ ⊗[ℚ] V) :
    J.baseChange ℂ (J.baseChange ℂ x) = -x := by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp, hJ]
  simp [LinearMap.baseChange_neg, Module.End.one_eq_id, LinearMap.baseChange_id]

/-- For a rational complex structure `J` (`J² = -1`), the `-i` and `i` eigenspaces of `J_ℂ` are
complementary. -/
theorem isCompl_eigenspace_of_sq :
    IsCompl (Module.End.eigenspace (J.baseChange ℂ) (-Complex.I))
      (Module.End.eigenspace (J.baseChange ℂ) Complex.I) := by
  constructor
  · rw [disjoint_iff]
    exact ((Module.End.eigenspaces_iSupIndep (J.baseChange ℂ)).pairwiseDisjoint
      (show -Complex.I ≠ Complex.I by
        intro h
        have : (2 : ℂ) * Complex.I = 0 := by linear_combination -h
        simp [Complex.I_ne_zero] at this)).eq_bot
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hJC := baseChange_baseChange_of_sq hJ
    refine Submodule.mem_sup.mpr ⟨(1 / 2 : ℂ) • (x + Complex.I • J.baseChange ℂ x), ?_,
      (1 / 2 : ℂ) • (x - Complex.I • J.baseChange ℂ x), ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      simp only [map_smul, map_add, hJC, smul_add, smul_neg, smul_smul]
      rw [show -Complex.I * (1 / 2 * Complex.I) = 1 / 2 by
        ring_nf; rw [Complex.I_sq]; ring]
      module
    · rw [Module.End.mem_eigenspace_iff]
      simp only [map_smul, map_sub, hJC, smul_sub, smul_neg, smul_smul]
      rw [show Complex.I * (1 / 2 * Complex.I) = -(1 / 2) by
        ring_nf; rw [Complex.I_sq]; ring]
      module
    · module

theorem isInternal_complexStructureHodge {p q : ℤ} (hpq : p ≠ q) :
    DirectSum.IsInternal (complexStructureHodge J p q) :=
  isInternal_pair (isCompl_eigenspace_of_sq hJ) (by simp [hpq])

/-- The grading operator of the structure defined by `J` is `-(p - q) J_ℂ`. -/
theorem gradingOperator_complexStructureHodge {p q : ℤ} (hpq : p ≠ q) :
    gradingOperator _ (isInternal_complexStructureHodge hJ hpq) =
      (-((p : ℂ) - q)) • J.baseChange ℂ := by
  refine linearMap_ext_of_isInternal (isInternal_complexStructureHodge hJ hpq) fun k x hx => ?_
  rw [gradingOperator_apply_of_mem _ _ hx, LinearMap.smul_apply]
  simp only [complexStructureHodge] at hx
  split_ifs at hx with h1 h2
  · subst h1
    rw [Module.End.mem_eigenspace_iff.mp hx, smul_smul]
    congr 1
    ring
  · subst h2
    rw [Module.End.mem_eigenspace_iff.mp hx, smul_smul]
    congr 1
    ring
  · rw [(Submodule.mem_bot ℂ).mp hx]
    simp

/-- **The Hodge Lie algebra of a rational complex structure** (CM by `ℚ(i)` in dimension 2) is
the line `ℚ ∙ J`. -/
theorem hodgeLieAlgebra_complexStructureHodge [FiniteDimensional ℚ V] [Nontrivial V] {p q : ℤ}
    (hpq : p ≠ q) :
    (hodgeLieAlgebra _ (isInternal_complexStructureHodge hJ hpq)).toSubmodule = ℚ ∙ J := by
  have hC := gradingOperator_complexStructureHodge hJ hpq
  have hpq' : -((p : ℂ) - q) ≠ 0 := by
    rw [neg_ne_zero, sub_ne_zero]
    exact_mod_cast hpq
  have hle : hodgeLieAlgebra _ (isInternal_complexStructureHodge hJ hpq) ≤ lineLieSubalgebra J := by
    refine hodgeLieAlgebra_le _ _ ?_
    rw [hC]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨J, Submodule.mem_span_singleton_self J, rfl⟩)
  have hJ0 : J ≠ 0 := by
    rintro rfl
    simp at hJ
  have hne : (hodgeLieAlgebra _ (isInternal_complexStructureHodge hJ hpq)).toSubmodule ≠ ⊥ := by
    intro hbot
    have hmem :=
      gradingOperator_mem_span_hodgeLieAlgebra _ (isInternal_complexStructureHodge hJ hpq)
    rw [hbot, Submodule.bot_coe, Set.image_singleton, LinearMap.baseChange_zero,
      Submodule.span_zero_singleton, Submodule.mem_bot, hC, smul_eq_zero] at hmem
    rcases hmem with h | h
    · exact hpq' h
    · exact hJ0 (LinearMap.baseChangeHom_injective (R := ℚ) (S := ℂ) (M := V) (N := V)
        (by simpa using h))
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  rw [finrank_span_singleton hJ0]
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  exact hne (Submodule.finrank_eq_zero.mp h0)

omit hJ in
/-- Base change of a rational endomorphism commutes with complex conjugation. -/
theorem complexConj_baseChange (x : ℂ ⊗[ℚ] V) :
    complexConj V (J.baseChange ℂ x) = J.baseChange ℂ (complexConj V x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z v => simp
  | add x y hx hy => simp only [map_add, hx, hy]

omit hJ in
theorem complexConj_mem_eigenspace {μ : ℂ} {x : ℂ ⊗[ℚ] V}
    (hx : x ∈ Module.End.eigenspace (J.baseChange ℂ) μ) :
    complexConj V x ∈ Module.End.eigenspace (J.baseChange ℂ) (starRingEnd ℂ μ) := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  rw [← complexConj_baseChange, hx, complexConj_smul]

omit hJ in
/-- The structure defined by `J` is conjugation-symmetric: a genuine Hodge structure. -/
theorem complexStructureHodge_conj {p q : ℤ} (hpq : p ≠ q) (a b : ℤ) (x : ℂ ⊗[ℚ] V)
    (hx : x ∈ complexStructureHodge J p q (a, b)) :
    complexConj V x ∈ complexStructureHodge J p q (b, a) := by
  have hqp : ((q, p) : ℤ × ℤ) ≠ (p, q) := by simp [Prod.ext_iff, hpq.symm]
  simp only [complexStructureHodge] at hx ⊢
  by_cases h1 : ((a, b) : ℤ × ℤ) = (p, q)
  · simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simp only [↓reduceIte] at hx
    simp only [hqp, ↓reduceIte]
    simpa using complexConj_mem_eigenspace hx
  · by_cases h2 : ((a, b) : ℤ × ℤ) = (q, p)
    · simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      simp only [hqp, ↓reduceIte] at hx
      simp only [↓reduceIte]
      simpa using complexConj_mem_eigenspace hx
    · simp only [h1, h2, ↓reduceIte, Submodule.mem_bot] at hx
      rw [hx, map_zero]
      exact Submodule.zero_mem _

omit hJ in
/-- The structure defined by `J` is pure of weight `p + q`. -/
theorem complexStructureHodge_pure {p q : ℤ} (a b : ℤ) (hab : a + b ≠ p + q) :
    complexStructureHodge J p q (a, b) = ⊥ := by
  have h1 : (a, b) ≠ (p, q) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  have h2 : (a, b) ≠ (q, p) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  simp [complexStructureHodge, h1, h2]

end ComplexStructure

section Trivial

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem isInternal_single (i : ℤ × ℤ) :
    DirectSum.IsInternal (fun k => if k = i then (⊤ : Submodule ℂ W) else ⊥) := by
  have h := isInternal_pair (W := W) isCompl_top_bot (i := i) (j := (i.1 + 1, i.2))
    (by simp [Prod.ext_iff])
  convert h using 2 with k
  split_ifs <;> rfl

/-- The trivial Hodge structure `ℚ(0)`: `V = ℚ` with `H (0, 0) = ⊤`.

Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §2.1 (the Tate structures
`ℚ(n)`, here `n = 0`). -/
def trivialHodge : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] ℚ) := fun k => if k = (0, 0) then ⊤ else ⊥

theorem isInternal_trivialHodge : DirectSum.IsInternal trivialHodge :=
  isInternal_single (0, 0)

theorem gradingOperator_trivialHodge :
    gradingOperator trivialHodge isInternal_trivialHodge = 0 := by
  refine linearMap_ext_of_isInternal isInternal_trivialHodge fun k x hx => ?_
  rw [gradingOperator_apply_of_mem _ _ hx, LinearMap.zero_apply]
  simp only [trivialHodge] at hx
  split_ifs at hx with h
  · subst h
    simp
  · rw [(Submodule.mem_bot ℂ).mp hx, smul_zero]

/-- **Example.** The Hodge Lie algebra of the trivial structure `ℚ(0)` is `0`. -/
theorem hodgeLieAlgebra_trivialHodge :
    hodgeLieAlgebra trivialHodge isInternal_trivialHodge = ⊥ := by
  rw [eq_bot_iff]
  refine hodgeLieAlgebra_le _ _ ?_
  rw [gradingOperator_trivialHodge]
  exact Submodule.zero_mem _

/-- **Example.** Every vector of `ℚ(0)` is a Hodge class. -/
theorem mem_maxTrivSubmodule_trivialHodge (v : ℚ) :
    v ∈ LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra trivialHodge isInternal_trivialHodge) ℚ := by
  rw [mem_maxTrivSubmodule_hodgeLieAlgebra_iff_mem_iSup]
  exact le_iSup (fun p : ℤ => trivialHodge (p, p)) 0 (by simp [trivialHodge])

example : (1 : ℚ) ∈
    LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra trivialHodge isInternal_trivialHodge) ℚ :=
  mem_maxTrivSubmodule_trivialHodge 1

end Trivial

section Rotation

theorem one_ne_neg_one : (1 : ℤ) ≠ -1 := by decide

/-- The rotation `[[0, -1], [1, 0]]` of `ℚ²`, a rational complex structure: multiplication by `i`
on `ℚ(i) ≅ ℚ²`, the complex multiplication of the elliptic curve `ℂ / ℤ[i]`.

Source: Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, ch. II (complex
multiplication). -/
def rotation : Module.End ℚ (Fin 2 → ℚ) := Matrix.toLinAlgEquiv' !![0, -1; 1, 0]

theorem rotation_mul_rotation : rotation * rotation = -1 := by
  rw [rotation, ← map_mul, ← map_one (Matrix.toLinAlgEquiv' (R := ℚ) (n := Fin 2)), ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem rotation_single_zero : rotation (Pi.single 0 1) = Pi.single 1 1 := by
  ext i
  fin_cases i <;> simp [rotation, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct]

theorem rotation_single_one : rotation (Pi.single 1 1) = -Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [rotation, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct]

/-- The vector `(1, i) = 1 ⊗ e₀ + i ⊗ e₁` lies in `H (p, q)`, the `-i` eigenspace of the rotation:
for `(p, q) = (1, 0)` this is the elliptic curve `ℂ / ℤ[i]` with complex multiplication by
`ℚ(i)`. -/
theorem one_I_mem_complexStructureHodge (p q : ℤ) :
    (1 : ℂ) ⊗ₜ[ℚ] (Pi.single 0 1 : Fin 2 → ℚ) + Complex.I ⊗ₜ[ℚ] (Pi.single 1 1 : Fin 2 → ℚ) ∈
      complexStructureHodge rotation p q (p, q) := by
  simp only [complexStructureHodge, Module.End.mem_eigenspace_iff, map_add,
    LinearMap.baseChange_tmul, rotation_single_zero, rotation_single_one, smul_add, smul_tmul',
    smul_eq_mul, tmul_neg, ↓reduceIte]
  rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], mul_one,
    neg_tmul]
  abel

theorem one_negI_mem_complexStructureHodge (p q : ℤ) (hpq : p ≠ q) :
    (1 : ℂ) ⊗ₜ[ℚ] (Pi.single 0 1 : Fin 2 → ℚ) - Complex.I ⊗ₜ[ℚ] (Pi.single 1 1 : Fin 2 → ℚ) ∈
      complexStructureHodge rotation p q (q, p) := by
  have h : ((q, p) : ℤ × ℤ) ≠ (p, q) := by simp [Prod.ext_iff, hpq.symm]
  simp only [complexStructureHodge, h, Module.End.mem_eigenspace_iff, map_sub,
    LinearMap.baseChange_tmul, rotation_single_zero, rotation_single_one, smul_sub, smul_tmul',
    smul_eq_mul, tmul_neg, ↓reduceIte]
  rw [Complex.I_mul_I, mul_one, neg_tmul]
  abel

/-- `1 ⊗ e₀ ± i ⊗ e₁ ≠ 0`: the first coordinate is `1`. -/
theorem one_add_smul_ne_zero (z : ℂ) :
    (1 : ℂ) ⊗ₜ[ℚ] (Pi.single 0 1 : Fin 2 → ℚ) + z ⊗ₜ[ℚ] (Pi.single 1 1 : Fin 2 → ℚ) ≠ 0 := by
  intro h
  have := congrArg (fun x => TensorProduct.rid ℚ ℂ
    ((LinearMap.proj 0 : (Fin 2 → ℚ) →ₗ[ℚ] ℚ).baseChange ℂ x)) h
  simp at this

/-- In the CM example, `H (p, q)` is exactly the line spanned by `(1, i)`. -/
theorem complexStructureHodge_rotation_eq_span {p q : ℤ} (hpq : p ≠ q) :
    complexStructureHodge rotation p q (p, q) = ℂ ∙ ((1 : ℂ) ⊗ₜ[ℚ] (Pi.single 0 1 : Fin 2 → ℚ) +
      Complex.I ⊗ₜ[ℚ] (Pi.single 1 1 : Fin 2 → ℚ)) := by
  have hA : complexStructureHodge rotation p q (p, q) =
      Module.End.eigenspace (rotation.baseChange ℂ) (-Complex.I) := by
    simp [complexStructureHodge]
  have hB : complexStructureHodge rotation p q (q, p) =
      Module.End.eigenspace (rotation.baseChange ℂ) Complex.I := by
    have h : ((q, p) : ℤ × ℤ) ≠ (p, q) := by simp [Prod.ext_iff, hpq.symm]
    simp [complexStructureHodge, h]
  have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_eigenspace_of_sq rotation_mul_rotation)
  rw [Module.finrank_baseChange, Module.finrank_fin_fun] at hsum
  have hw := one_I_mem_complexStructureHodge p q
  have hw' := one_negI_mem_complexStructureHodge p q hpq
  rw [hA] at hw
  rw [hB] at hw'
  have h1 : 1 ≤ Module.finrank ℂ (Module.End.eigenspace (rotation.baseChange ℂ) (-Complex.I)) :=
    Submodule.one_le_finrank_iff.mpr
      ((Submodule.ne_bot_iff _).mpr ⟨_, hw, one_add_smul_ne_zero _⟩)
  have h2 : 1 ≤ Module.finrank ℂ (Module.End.eigenspace (rotation.baseChange ℂ) Complex.I) := by
    refine Submodule.one_le_finrank_iff.mpr ((Submodule.ne_bot_iff _).mpr ⟨_, hw', ?_⟩)
    rw [sub_eq_add_neg, ← neg_tmul]
    exact one_add_smul_ne_zero _
  rw [hA]
  refine (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr hw)
    ?_).symm
  rw [finrank_span_singleton (one_add_smul_ne_zero _)]
  omega

/-- **Example (CM by `ℚ(i)`).** For `V = ℚ²` with `H (1, 0)` the `-i` eigenspace of the rotation
(the line through `(1, i)`, `complexStructureHodge_rotation_eq_span`) and `H (0, 1)` its
conjugate, the Hodge Lie algebra is the line spanned by the rotation. -/
theorem hodgeLieAlgebra_rotation :
    (hodgeLieAlgebra _ (isInternal_complexStructureHodge rotation_mul_rotation
      one_ne_zero)).toSubmodule = ℚ ∙ rotation :=
  hodgeLieAlgebra_complexStructureHodge rotation_mul_rotation one_ne_zero

/-- The rational class `e₀` is not killed by the Hodge Lie algebra of the structure of type
`(p, q) + (q, p)` defined by the rotation, for any `p ≠ q`. -/
theorem single_zero_not_mem_maxTrivSubmodule {p q : ℤ} (hpq : p ≠ q) :
    (Pi.single 0 1 : Fin 2 → ℚ) ∉ LieModule.maxTrivSubmodule ℚ
      (hodgeLieAlgebra _ (isInternal_complexStructureHodge rotation_mul_rotation hpq))
      (Fin 2 → ℚ) := by
  rw [mem_maxTrivSubmodule_hodgeLieAlgebra_iff, complexAction_self,
    gradingOperator_complexStructureHodge rotation_mul_rotation hpq, LinearMap.smul_apply,
    LinearMap.baseChange_tmul, rotation_single_zero, smul_eq_zero, not_or]
  refine ⟨?_, ?_⟩
  · simp only [neg_eq_zero, sub_eq_zero]
    exact_mod_cast hpq
  · rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff ℚ (Fin 2 → ℚ) (A := ℂ)]
    simp

/-- **Falsification.** In the weight-two structure `V = ℚ²`, `H (2, 0)` and `H (0, 2)` the
conjugate eigenlines of the rotation, the rational class `e₀` has type `(2, 0) + (0, 2)`, and the
Hodge Lie algebra does not kill it: it is not a Hodge class. (With the weight operator in place of
`C`, a weight-zero structure such as type `(1, -1) + (-1, 1)` would have every class invariant,
see `rationalLieHull_zero`.) -/
theorem weightTwo_single_zero :
    (1 : ℂ) ⊗ₜ[ℚ] (Pi.single 0 1 : Fin 2 → ℚ) ∈
        complexStructureHodge rotation 2 0 (2, 0) ⊔ complexStructureHodge rotation 2 0 (0, 2) ∧
      (Pi.single 0 1 : Fin 2 → ℚ) ∉ LieModule.maxTrivSubmodule ℚ
        (hodgeLieAlgebra _ (isInternal_complexStructureHodge rotation_mul_rotation
          two_ne_zero)) (Fin 2 → ℚ) := by
  refine ⟨?_, single_zero_not_mem_maxTrivSubmodule two_ne_zero⟩
  have h := (isCompl_eigenspace_of_sq rotation_mul_rotation).sup_eq_top
  have e1 : complexStructureHodge rotation 2 0 (2, 0) =
      Module.End.eigenspace (rotation.baseChange ℂ) (-Complex.I) := by
    simp [complexStructureHodge]
  have e2 : complexStructureHodge rotation 2 0 (0, 2) =
      Module.End.eigenspace (rotation.baseChange ℂ) Complex.I := by
    simp [complexStructureHodge]
  rw [e1, e2, h]
  trivial

/-- With `0` in place of the grading operator (the weight operator of a weight-zero structure),
the hull is `0` and kills everything. -/
theorem rationalLieHull_zero {V : Type*} [AddCommGroup V] [Module ℚ V] :
    rationalLieHull (0 : Module.End ℂ (ℂ ⊗[ℚ] V)) = ⊥ :=
  eq_bot_iff.mpr (rationalLieHull_le (Submodule.zero_mem _))

example : (Pi.single 0 1 : Fin 2 → ℚ) ∈
      LieModule.maxTrivSubmodule ℚ (rationalLieHull (0 : Module.End ℂ (ℂ ⊗[ℚ] (Fin 2 → ℚ))))
        (Fin 2 → ℚ) ∧
    (Pi.single 0 1 : Fin 2 → ℚ) ∉ LieModule.maxTrivSubmodule ℚ
      (hodgeLieAlgebra _ (isInternal_complexStructureHodge rotation_mul_rotation
        one_ne_neg_one)) (Fin 2 → ℚ) := by
  refine ⟨?_, single_zero_not_mem_maxTrivSubmodule one_ne_neg_one⟩
  rw [mem_maxTrivSubmodule_rationalLieHull_iff, map_zero, LinearMap.zero_apply]

end Rotation

end Examples

section Tensor

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The `ℂ`-bilinear product `(ℂ ⊗ V) × (ℂ ⊗ V) → ℂ ⊗ (V ⊗ V)`, `(a ⊗ v, b ⊗ u) ↦ ab ⊗ (v ⊗ u)`,
through which `(ℂ ⊗ V) ⊗_ℂ (ℂ ⊗ V) ≃ ℂ ⊗ (V ⊗ V)` (Mathlib's `distribBaseChange`).

Source: Bourbaki, *Algèbre*, ch. II (extension of scalars commutes with tensor products). -/
def complexTensorMul : (ℂ ⊗[ℚ] V) →ₗ[ℂ] (ℂ ⊗[ℚ] V) →ₗ[ℂ] ℂ ⊗[ℚ] (V ⊗[ℚ] V) :=
  (TensorProduct.mk ℂ (ℂ ⊗[ℚ] V) (ℂ ⊗[ℚ] V)).compr₂
    (TensorProduct.AlgebraTensorModule.distribBaseChange ℚ ℂ V V).symm.toLinearMap

@[simp]
theorem complexTensorMul_tmul (a b : ℂ) (v u : V) :
    complexTensorMul (a ⊗ₜ[ℚ] v) (b ⊗ₜ[ℚ] u) = (a * b) ⊗ₜ[ℚ] (v ⊗ₜ[ℚ] u) := by
  simp [complexTensorMul]

theorem map₂_complexTensorMul_top :
    Submodule.map₂ complexTensorMul ⊤ ⊤ = (⊤ : Submodule ℂ (ℂ ⊗[ℚ] (V ⊗[ℚ] V))) := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ :=
    (TensorProduct.AlgebraTensorModule.distribBaseChange ℚ ℂ V V).symm.surjective x
  induction y using TensorProduct.inductionOn with
  | tmul a b => exact Submodule.apply_mem_map₂ complexTensorMul (m := a) (n := b) trivial trivial
  | add y y' hy hy' => rw [map_add]; exact add_mem hy hy'

variable (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)

/-- The Hodge decomposition of `V ⊗ V`: `(V ⊗ V)^{r,s} = ⨁_{p + p' = r, q + q' = s}
V^{p,q} ⊗ V^{p',q'}`, as subspaces of `ℂ ⊗[ℚ] (V ⊗[ℚ] V)`.

Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §§1–2 (the tensor
product of Hodge structures); Moonen, *An introduction to Mumford–Tate groups* (lecture notes,
2004), §1 (tensor constructions). -/
def tensorHodge : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] (V ⊗[ℚ] V)) :=
  fun k => ⨆ (ij : (ℤ × ℤ) × (ℤ × ℤ)) (_ : ij.1 + ij.2 = k),
    Submodule.map₂ complexTensorMul (H ij.1) (H ij.2)

theorem map₂_le_tensorHodge (i j : ℤ × ℤ) :
    Submodule.map₂ complexTensorMul (H i) (H j) ≤ tensorHodge H (i + j) :=
  le_iSup₂_of_le (f := fun (ij : (ℤ × ℤ) × (ℤ × ℤ)) (_ : ij.1 + ij.2 = i + j) =>
    Submodule.map₂ complexTensorMul (H ij.1) (H ij.2)) (i, j) rfl le_rfl

include hH in
theorem iSup_tensorHodge : ⨆ k, tensorHodge H k = ⊤ := by
  rw [eq_top_iff, ← map₂_complexTensorMul_top, ← hH.submodule_iSup_eq_top,
    Submodule.map₂_iSup_left]
  refine iSup_le fun i => ?_
  rw [Submodule.map₂_iSup_right]
  exact iSup_le fun j => le_iSup_of_le (i + j) (map₂_le_tensorHodge H i j)

omit H in
/-- A rational endomorphism acts on `V ⊗ V` as a derivation, also after base change. -/
theorem baseChange_toEnd_complexTensorMul (X : Module.End ℚ V) (x y : ℂ ⊗[ℚ] V) :
    (LieModule.toEnd ℚ (Module.End ℚ V) (V ⊗[ℚ] V) X).baseChange ℂ (complexTensorMul x y) =
      complexTensorMul (X.baseChange ℂ x) y + complexTensorMul x (X.baseChange ℂ y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    induction y using TensorProduct.inductionOn with
    | tmul b u =>
      simp [LieModule.toEnd_apply_apply, TensorProduct.LieModule.lie_tmul_right, tmul_add]
    | add y y' hy hy' =>
      simp only [map_add, hy, hy']
      abel
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx']
    abel

omit H in
/-- The complexified action on `V ⊗ V` is the derivation `Y ⊗ 1 + 1 ⊗ Y`. -/
theorem complexAction_tensor_complexTensorMul [FiniteDimensional ℚ V]
    (Y : Module.End ℂ (ℂ ⊗[ℚ] V)) (x y : ℂ ⊗[ℚ] V) :
    complexAction (V ⊗[ℚ] V) Y (complexTensorMul x y) =
      complexTensorMul (Y x) y + complexTensorMul x (Y y) := by
  obtain ⟨t, rfl⟩ := (endBaseChangeEquiv V).surjective Y
  simp only [complexAction, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply]
  induction t using TensorProduct.inductionOn with
  | tmul z X =>
    change (z • ((LieModule.toEnd ℚ (Module.End ℚ V) (V ⊗[ℚ] V) X).baseChange ℂ))
      (complexTensorMul x y) = _
    rw [endBaseChangeEquiv_apply, tensorProductEnd_tmul, LinearMap.smul_apply,
      baseChange_toEnd_complexTensorMul]
    simp only [LinearMap.smul_apply, map_smul, smul_add]
  | add t t' ht ht' =>
    simp only [map_add, LinearMap.add_apply, ht, ht']
    abel

omit hH in
/-- If `Y` acts on each `H i` by a scalar `f i` with `f` additive, its derivation on `V ⊗ V` acts on
the tensor piece `k` by `f k`. -/
theorem tensorHodge_le_eigenspace_of [FiniteDimensional ℚ V] {Y : Module.End ℂ (ℂ ⊗[ℚ] V)}
    {f : ℤ × ℤ → ℂ} (hf : ∀ i j, f (i + j) = f i + f j) (hY : ∀ i, ∀ x ∈ H i, Y x = f i • x)
    (k : ℤ × ℤ) :
    tensorHodge H k ≤ Module.End.eigenspace (complexAction (V ⊗[ℚ] V) Y) (f k) := by
  refine iSup₂_le fun ij hij => Submodule.map₂_le.mpr fun x hx y hy => ?_
  subst hij
  rw [Module.End.mem_eigenspace_iff, complexAction_tensor_complexTensorMul, hY _ x hx, hY _ y hy,
    LinearMap.map_smul₂, map_smul, ← add_smul, hf]

/-- The complexified grading operator acts on the tensor piece `(r, s)` by `i (r - s)`. -/
theorem tensorHodge_le_eigenspace [FiniteDimensional ℚ V] (k : ℤ × ℤ) :
    tensorHodge H k ≤ Module.End.eigenspace (complexAction (V ⊗[ℚ] V) (gradingOperator H hH))
      (Complex.I * ((k.1 : ℂ) - k.2)) :=
  tensorHodge_le_eigenspace_of H (f := fun k : ℤ × ℤ => Complex.I * ((k.1 : ℂ) - k.2))
    (fun i j => by simp only [Prod.fst_add, Prod.snd_add]; push_cast; ring)
    (fun i x hx => gradingOperator_apply_of_mem H hH (p := i.1) (q := i.2) hx) k

/-- The operator acting on `H (p, q)` by `(p + q) + i (p - q)`; its eigenvalues separate the
pairs `(p, q)`. It is the derivative of `z ↦ z^p z̄^q` at `1` in the direction `1 + i`, as `C` is
the derivative in the direction `i` and the weight operator the one in the direction `1`. An
auxiliary operator, used to prove that tensor pieces are independent.

Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §2.1 (the action `h` of the
Deligne torus `𝕊`). -/
def separatingOperator : Module.End ℂ (ℂ ⊗[ℚ] V) :=
  DirectSum.toModule ℂ (ℤ × ℤ) _
      (fun pq => (((pq.1 + pq.2 : ℤ) : ℂ) + Complex.I * ((pq.1 : ℂ) - pq.2)) • (H pq).subtype) ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap H) hH).symm.toLinearMap

theorem separatingOperator_apply_of_mem {i : ℤ × ℤ} {x : ℂ ⊗[ℚ] V} (hx : x ∈ H i) :
    separatingOperator H hH x = (((i.1 + i.2 : ℤ) : ℂ) + Complex.I * ((i.1 : ℂ) - i.2)) • x := by
  have h : (LinearEquiv.ofBijective (DirectSum.coeLinearMap H) hH).symm x =
      DirectSum.lof ℂ (ℤ × ℤ) (fun i => H i) i ⟨x, hx⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    exact (DirectSum.coeLinearMap_of H i ⟨x, hx⟩).symm
  simp only [separatingOperator, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h,
    DirectSum.toModule_lof, LinearMap.smul_apply, Submodule.subtype_apply]

theorem separating_injective :
    Function.Injective fun k : ℤ × ℤ => ((k.1 + k.2 : ℤ) : ℂ) + Complex.I * ((k.1 : ℂ) - k.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.sub_re, Complex.sub_im, Complex.intCast_im, Complex.add_im, Complex.mul_im] at hre him
  simp only [zero_mul, one_mul, add_zero, zero_add, sub_self, mul_zero] at hre him
  have h1 : a + b = c + d := by exact_mod_cast hre
  have h2 : (a : ℝ) - b = c - d := by linarith
  have h2' : a - b = c - d := by exact_mod_cast h2
  simp only [Prod.mk.injEq]
  omega

include hH in
/-- The tensor pieces form an internal direct sum decomposition of `ℂ ⊗[ℚ] (V ⊗[ℚ] V)`: they
are a Hodge decomposition. -/
theorem isInternal_tensorHodge [FiniteDimensional ℚ V] : DirectSum.IsInternal (tensorHodge H) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, iSup_tensorHodge H hH⟩
  have hind := (Module.End.eigenspaces_iSupIndep
    (complexAction (V ⊗[ℚ] V) (separatingOperator H hH))).comp separating_injective
  refine hind.mono fun k => ?_
  refine tensorHodge_le_eigenspace_of H (fun i j => ?_)
    (fun i x hx => separatingOperator_apply_of_mem H hH hx) k
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  ring

/-- **The grading operator of the tensor Hodge structure is the derivation `C ⊗ 1 + 1 ⊗ C`**, i.e.
the complexified action of `C` on `V ⊗ V`. -/
theorem gradingOperator_tensorHodge [FiniteDimensional ℚ V] :
    gradingOperator (tensorHodge H) (isInternal_tensorHodge H hH) =
      complexAction (V ⊗[ℚ] V) (gradingOperator H hH) := by
  refine linearMap_ext_of_isInternal (isInternal_tensorHodge H hH) fun k x hx => ?_
  rw [gradingOperator_apply_of_mem _ _ (p := k.1) (q := k.2) hx,
    Module.End.mem_eigenspace_iff.mp (tensorHodge_le_eigenspace H hH k hx)]

/-- **Hodge classes in `V ⊗ V` are the invariants of the Hodge Lie algebra.** A rational tensor
`w ∈ V ⊗ V` is killed by `hodgeLieAlgebra` (acting by derivations, `X • (v ⊗ u) = Xv ⊗ u + v ⊗ Xu`)
if and only if `1 ⊗ w` lies in the sum of the tensor pieces of type `(r, r)`.

No register entry; with F-1575 step 2 it is the statement "the Hodge ring is the invariant ring"
in degree two. HC: no distance. AV milestone: no distance. -/
theorem mem_maxTrivSubmodule_hodgeLieAlgebra_tensor_iff [FiniteDimensional ℚ V]
    (w : V ⊗[ℚ] V) :
    w ∈ LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH) (V ⊗[ℚ] V) ↔
      1 ⊗ₜ w ∈ ⨆ r : ℤ, tensorHodge H (r, r) := by
  rw [mem_maxTrivSubmodule_hodgeLieAlgebra_iff, ← LinearMap.mem_ker,
    ker_eq_iSup_diag (tensorHodge H) (iSup_tensorHodge H hH) _ fun p q x hx =>
      Module.End.mem_eigenspace_iff.mp (tensorHodge_le_eigenspace H hH (p, q) hx)]

end Tensor

section DefinitionExamples

/-! One `example` for each definition of this file, on a concrete case. -/

example : gradingOperator _ (isInternal_complexStructureHodge rotation_mul_rotation one_ne_zero) =
    (-1 : ℂ) • rotation.baseChange ℂ := by
  rw [gradingOperator_complexStructureHodge rotation_mul_rotation one_ne_zero]
  norm_num

example (X : Module.End ℚ (Fin 2 → ℚ)) : endBaseChangeEquiv (Fin 2 → ℚ) (1 ⊗ₜ X) = X.baseChange ℂ :=
  tensorProductEnd_one_tmul _ X

example : complexSpan (⊤ : Submodule ℚ (Module.End ℚ (Fin 2 → ℚ))) = ⊤ := complexSpan_top

example : rationalLieHull (0 : Module.End ℂ (ℂ ⊗[ℚ] (Fin 2 → ℚ))) = ⊥ := rationalLieHull_zero

example (c : Module.End ℂ (ℂ ⊗[ℚ] (Fin 2 → ℚ))) : complexAction (Fin 2 → ℚ) c = c :=
  complexAction_self c

example : rotation ∉ lieAnnihilator (Fin 2 → ℚ) (Pi.single 0 1) := by
  rw [mem_lieAnnihilator, Module.End.lie_apply, rotation_single_zero]
  simp

example : hodgeLieAlgebra trivialHodge isInternal_trivialHodge = ⊥ := hodgeLieAlgebra_trivialHodge

example : rotation ∈ lineLieSubalgebra rotation := Submodule.mem_span_singleton_self rotation

example : (1 : ℂ) ⊗ₜ[ℚ] (Pi.single 0 1 : Fin 2 → ℚ) + Complex.I ⊗ₜ[ℚ] (Pi.single 1 1 : Fin 2 → ℚ) ∈
    complexStructureHodge rotation 1 0 (1, 0) :=
  one_I_mem_complexStructureHodge 1 0

example : trivialHodge (0, 0) = ⊤ := by simp [trivialHodge]

example : rotation * rotation = -1 := rotation_mul_rotation

example (v u : ℚ) :
    complexTensorMul ((1 : ℂ) ⊗ₜ[ℚ] v) ((1 : ℂ) ⊗ₜ[ℚ] u) = (1 : ℂ) ⊗ₜ[ℚ] (v ⊗ₜ[ℚ] u) := by
  simp

example (v u : ℚ) : (1 : ℂ) ⊗ₜ[ℚ] (v ⊗ₜ[ℚ] u) ∈ tensorHodge trivialHodge (0, 0) := by
  have h := map₂_le_tensorHodge trivialHodge (0, 0) (0, 0)
    (Submodule.apply_mem_map₂ complexTensorMul (m := (1 : ℂ) ⊗ₜ[ℚ] v) (n := (1 : ℂ) ⊗ₜ[ℚ] u)
      (by simp [trivialHodge]) (by simp [trivialHodge]))
  simpa using h

example (x : ℂ ⊗[ℚ] ℚ) (hx : x ∈ trivialHodge (0, 0)) :
    separatingOperator trivialHodge isInternal_trivialHodge x = 0 := by
  rw [separatingOperator_apply_of_mem _ _ hx]
  simp

end DefinitionExamples

end HodgeLean.Foundations
