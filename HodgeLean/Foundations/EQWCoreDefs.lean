import HodgeLean.Foundations.HSUCandidateHodge

/-! # The representation-theoretic core of EQW, stage 1 (FROZEN DEFINITIONS)

Definitions for `EQWCore`, the first stage of formalizing F-1770 (EQW, "exact endomorphisms
force the generic Hodge group"):

* `weilSU E J`, the rational special unitary Lie algebra of a Weil-type datum: endomorphisms
  commuting with `J`, infinitesimally preserving `E`, with `tr X = 0` and `tr (J X) = 0`. It is
  defined for any `J`, in particular for `J² = -d` and every imaginary quadratic `ℚ(√-d)`; for
  `d = 3` its complexification is `WeilPower.complexSU`.
* `HasPlusMinusIntertwiner L J μ`: a nonzero complex endomorphism commuting with `L`, carrying
  the `μ`-eigenspace of `J_ℂ` into the `-μ`-eigenspace and killing the `-μ`-eigenspace, i.e. a
  nonzero `L`-map `V₊ → V₋` (part (c) of F-1770).
* `EQWClassification E hE J hJ hskew`, the explicit classification binder: parts (b) and the
  descent half of (d) of F-1770 in dimensions `12` and `16` (abelian sixfolds and eightfolds).
  It is a hypothesis, never proved here.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

namespace HodgeLean.Foundations

open WeilPower
open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The rational special unitary Lie algebra `𝔰𝔲(V, h)` of a Weil-type datum `(E, J)`, written
with rational equations: `X J = J X`, `E (X x) y = -E x (X y)`, `tr X = 0` and `tr (J X) = 0`.
For `X` commuting with `J`, the two trace conditions say that the `K`-linear trace of `X`
vanishes, `K = ℚ(J)`.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5–6 (the
special unitary group of the Hermitian form `h`); Bourbaki, *Groupes et algèbres de Lie*, ch. I,
§6 (the Lie algebras of the classical groups). -/
def weilSU (E : LinearMap.BilinForm ℚ V) (J : Module.End ℚ V) :
    LieSubalgebra ℚ (Module.End ℚ V) where
  carrier := {X | X * J = J * X ∧ (∀ x y, E (X x) y = -E x (X y)) ∧
    LinearMap.trace ℚ V X = 0 ∧ LinearMap.trace ℚ V (J * X) = 0}
  add_mem' := by
    rintro X Y ⟨hX1, hX2, hX3, hX4⟩ ⟨hY1, hY2, hY3, hY4⟩
    refine ⟨by rw [add_mul, mul_add, hX1, hY1], fun x y => ?_, by simp [hX3, hY3],
      by simp [mul_add, hX4, hY4]⟩
    simp only [LinearMap.add_apply, map_add, LinearMap.add_apply, hX2, hY2]
    ring
  zero_mem' := by simp
  smul_mem' := by
    rintro c X ⟨hX1, hX2, hX3, hX4⟩
    refine ⟨by rw [smul_mul_assoc, hX1, mul_smul_comm], fun x y => ?_, by simp [hX3],
      by simp [hX4]⟩
    simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hX2, smul_eq_mul]
    ring
  lie_mem' := by
    rintro X Y ⟨hX1, hX2, hX3, hX4⟩ ⟨hY1, hY2, hY3, hY4⟩
    rw [Ring.lie_def]
    refine ⟨?_, fun x y => ?_, ?_, ?_⟩
    · have h1 : X * Y * J = J * (X * Y) := by
        rw [mul_assoc, hY1, ← mul_assoc, hX1, mul_assoc]
      have h2 : Y * X * J = J * (Y * X) := by
        rw [mul_assoc, hX1, ← mul_assoc, hY1, mul_assoc]
      rw [sub_mul, mul_sub, h1, h2]
    · simp only [LinearMap.sub_apply, map_sub, LinearMap.sub_apply, Module.End.mul_apply, hX2,
        hY2]
      ring
    · rw [map_sub, LinearMap.trace_mul_comm, sub_self]
    · rw [mul_sub, map_sub, ← mul_assoc J Y X, LinearMap.trace_mul_comm ℚ (J * Y) X,
        ← mul_assoc X J Y, hX1, mul_assoc, sub_self]

example (E : LinearMap.BilinForm ℚ V) (J : Module.End ℚ V) :
    (0 : Module.End ℚ V) ∈ weilSU E J :=
  (weilSU E J).zero_mem

/-- A nonzero `L`-equivariant map from the `μ`-eigenspace `V₊` of `J_ℂ` to the `-μ`-eigenspace
`V₋`, extended by zero on `V₋`: a complex endomorphism `Φ ≠ 0` commuting with every `X_ℂ`,
`X ∈ L`, with `Φ (V₊) ⊆ V₋` and `Φ (V₋) = 0`. An isomorphism `V₊ ≅ V₋` of `L_ℂ`-modules gives
one.
Source: F-1770 part (c) (the two `K`-eigenspaces as Hodge-group modules); van Geemen,
*An introduction to the Hodge conjecture for abelian varieties*, §5 (the eigenspace splitting
`V_ℂ = V₊ ⊕ V₋` of a Weil-type structure). -/
def HasPlusMinusIntertwiner (L : LieSubalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V)
    (μ : ℂ) : Prop :=
  ∃ Φ : Module.End ℂ (ℂ ⊗[ℚ] V), Φ ≠ 0 ∧
    (∀ X ∈ L, Φ * X.baseChange ℂ = X.baseChange ℂ * Φ) ∧
    (∀ v ∈ Module.End.eigenspace (J.baseChange ℂ) μ,
      Φ v ∈ Module.End.eigenspace (J.baseChange ℂ) (-μ)) ∧
    (∀ v ∈ Module.End.eigenspace (J.baseChange ℂ) (-μ), Φ v = 0)

example (L : LieSubalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V) (μ : ℂ) :
    HasPlusMinusIntertwiner L J μ ↔ ∃ Φ : Module.End ℂ (ℂ ⊗[ℚ] V), Φ ≠ 0 ∧
      (∀ X ∈ L, Φ * X.baseChange ℂ = X.baseChange ℂ * Φ) ∧
      (∀ v ∈ Module.End.eigenspace (J.baseChange ℂ) μ,
        Φ v ∈ Module.End.eigenspace (J.baseChange ℂ) (-μ)) ∧
      (∀ v ∈ Module.End.eigenspace (J.baseChange ℂ) (-μ), Φ v = 0) :=
  Iff.rfl

variable [FiniteDimensional ℚ V]

/-- **The EQW classification binder** (F-1770 part (b), with the descent half of part (d)), for
`K = ℚ(√-3)` and `V` of dimension `12` or `16`: let `L` be a rational Lie subalgebra of
`weilSU E J` with trivial radical (semisimple), whose rational commutant is exactly `ℚ[J]`, with
no nonzero `L`-map `V₊ → V₋`, and which is the rational Lie hull of an element `c` with
`c² = -1`. Then the complexification of `L` is `complexSU`. This is the finite list of
semisimple Lie algebras with a faithful irreducible non-self-dual minuscule representation of
dimension `6` or `8` (compact factors included), followed by Lemma TENSOR and the descent of the
idle ideal to `ℚ`, which contradicts minimality. It is a hypothesis; nothing here proves it.
Source: F-1770 (EQW), parts (b) and (d), refereed CORRECT (hodge-EQWR); Deligne, *Variétés de
Shimura*, Proc. Symp. Pure Math. 33 (1979), §1.3 (minuscule representations from Hodge
structures of weight one); Bourbaki, *Groupes et algèbres de Lie*, ch. VIII, §7.3 (the minuscule
weights). -/
def EQWClassification (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (J : Module.End ℚ V) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id)
    (hskew : ∀ x y, E (J x) y = -E x (J y)) : Prop :=
  E.IsAlt → (Module.finrank ℚ V = 12 ∨ Module.finrank ℚ V = 16) →
    ∀ (L : LieSubalgebra ℚ (Module.End ℚ V)) (c : Module.End ℂ (ℂ ⊗[ℚ] V)),
      rationalLieHull c = L → c * c = -1 → L ≤ weilSU E J →
      LieAlgebra.HasTrivialRadical ℚ L →
      Subalgebra.centralizer ℚ (L : Set (Module.End ℚ V)) = Algebra.adjoin ℚ {J} →
      ¬ HasPlusMinusIntertwiner L J root →
      complexSpan L.toSubmodule = (complexSU E hE J hJ hskew).toSubmodule

example (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (J : Module.End ℚ V)
    (hJ : J.comp J = (-3 : ℚ) • LinearMap.id) (hskew : ∀ x y, E (J x) y = -E x (J y))
    (h : EQWClassification E hE J hJ hskew) (hAlt : E.IsAlt)
    (hdim : Module.finrank ℚ V = 12 ∨ Module.finrank ℚ V = 16)
    (L : LieSubalgebra ℚ (Module.End ℚ V)) (c : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hc : rationalLieHull c = L) (hcc : c * c = -1) (hL : L ≤ weilSU E J)
    (hrad : LieAlgebra.HasTrivialRadical ℚ L)
    (hcomm : Subalgebra.centralizer ℚ (L : Set (Module.End ℚ V)) = Algebra.adjoin ℚ {J})
    (hint : ¬ HasPlusMinusIntertwiner L J root) :
    complexSpan L.toSubmodule = (complexSU E hE J hJ hskew).toSubmodule :=
  h hAlt hdim L c hc hcc hL hrad hcomm hint

end HodgeLean.Foundations
