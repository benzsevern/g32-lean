import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.RingTheory.Trace.Basic
import HodgeLean.Blocks.Weil.Basic

/-! # CM splitting of `ℂ ⊗ V`, stage A2a (FROZEN DEFINITIONS)

Definitions for `CMSplitting`, stage A2a of the Powers flagship (PW v0.3, Theorem 4.2,
doi:10.5281/zenodo.23570103; plan `docs/roadmap/pw-flagship-plan.md`, §4.2 row A2a). They concern a
`ℚ`-space `V` with a `ℚ`-algebra map `ι : L →ₐ[ℚ] Module.End ℚ V` from a commutative `ℚ`-algebra
`L` (in the application a CM field):

* `cmEigenspace ι τ`, for a `ℚ`-algebra map `τ : L →ₐ[ℚ] ℂ`, the joint `τ`-eigenspace
  `W_τ = {x ∈ ℂ ⊗ V | ι(a)_ℂ x = τ(a) x for every a ∈ L}`;
* `cmConjEmbedding τ`, the conjugate embedding `τ̄ = conj ∘ τ`;
* `cmPlusPart ι u d`, the sum of the `W_τ` with `τ(u) = i√d`, the space the plan writes `V₊`;
* `a2a_fstAction`, `a2a_diagAction L` and `a2a_traceSymplectic L`, the concrete data of the two
  falsification statements.

No definition asserts a decomposition, dimension, orthogonality or duality. HC no distance; AV
milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable {L : Type*} [CommRing L] [Algebra ℚ L]

/-- The joint `τ`-eigenspace of the complexified action: the vectors `x ∈ ℂ ⊗ V` with
`ι(a)_ℂ x = τ(a) x` for every `a ∈ L`. For a CM field `L` these are the spaces `W_τ`
(`W_v`, `W̄_v`) of the paper.
Source: PW v0.3, Subsection 2.1 (Conventions: "the subscript denotes the `τ`-eigenspace of `M`")
and Subsection 2.3 (`V_ℂ = ⊕_v (W_v ⊕ W̄_v)`, `W_v` the `σ_v`-eigenspace). -/
def cmEigenspace (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ) :
    Submodule ℂ (ℂ ⊗[ℚ] V) :=
  ⨅ a : L, Module.End.eigenspace ((ι a).baseChange ℂ) (τ a)

example (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ) (x : ℂ ⊗[ℚ] V) :
    x ∈ cmEigenspace ι τ ↔ ∀ a : L, (ι a).baseChange ℂ x = τ a • x := by
  simp [cmEigenspace]

/-- The conjugate embedding `τ̄ = conj ∘ τ`.
Source: PW v0.3, Subsection 2.1 (`q_τ = p_τ̄`) and Subsection 2.3 (`W̄_v`, the
`σ̄_v`-eigenspace). -/
def cmConjEmbedding (τ : L →ₐ[ℚ] ℂ) : L →ₐ[ℚ] ℂ :=
  (starRingEnd ℂ).toRatAlgHom.comp τ

example (τ : L →ₐ[ℚ] ℂ) (a : L) : cmConjEmbedding τ a = starRingEnd ℂ (τ a) := rfl

/-- The sum of the `W_τ` over the embeddings `τ` with `τ(u) = i√d`: for `k = ℚ(u) ⊆ L`,
`u² = -d`, it is the space `V₊ = ⊕_{τ(u) = i√d} W_τ` of the plan, and the paper's
`W = ⊕_v W_v` for the embedding `σ(u) = i√d` of `k`.
Source: PW v0.3, Subsection 2.2 (`V_ℂ = W ⊕ W̄`, `W` for a fixed embedding `σ` of `k`) and
Subsection 2.3 (each real place `v` has a unique extension `σ_v` of `σ`). -/
def cmPlusPart (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ) : Submodule ℂ (ℂ ⊗[ℚ] V) :=
  ⨆ (τ : L →ₐ[ℚ] ℂ) (_ : τ u = HodgeBlocks.WeilAction.omegaC d), cmEigenspace ι τ

example (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ) (τ : L →ₐ[ℚ] ℂ)
    (hτ : τ u = HodgeBlocks.WeilAction.omegaC d) :
    cmEigenspace ι τ ≤ cmPlusPart ι u d :=
  le_iSup₂_of_le τ hτ le_rfl

/-- A non-faithful action of `ℚ × ℚ` on `ℚ`: `(a, b)` acts by `a`. Its kernel is `0 × ℚ`.
Source: constructed here, for the falsification of the dimension statement. -/
def a2a_fstAction : ℚ × ℚ →ₐ[ℚ] Module.End ℚ ℚ :=
  (Algebra.ofId ℚ (Module.End ℚ ℚ)).comp (AlgHom.fst ℚ ℚ ℚ)

example (a b x : ℚ) : a2a_fstAction (a, b) x = a * x := by
  simp [a2a_fstAction, Algebra.algebraMap_eq_smul_one]

/-- The diagonal action of `L` on `L × L` by multiplication.
Source: constructed here, for the falsification of the orthogonality statement. -/
def a2a_diagAction (L : Type*) [CommRing L] [Algebra ℚ L] :
    L →ₐ[ℚ] Module.End ℚ (L × L) :=
  (Algebra.lmul ℚ (L × L)).comp ((AlgHom.id ℚ L).prod (AlgHom.id ℚ L))

example (a x y : L) : a2a_diagAction L a (x, y) = (a * x, a * y) := by
  simp [a2a_diagAction]

/-- The alternating trace form `((x₁, x₂), (y₁, y₂)) ↦ Tr(x₁ y₂) - Tr(x₂ y₁)` on `L × L`.
It is `L`-compatible for the identity, `E(a x, y) = E(x, a y)`, not for complex conjugation.
Source: constructed here, for the falsification of the orthogonality statement. -/
def a2a_traceSymplectic (L : Type*) [CommRing L] [Algebra ℚ L] :
    LinearMap.BilinForm ℚ (L × L) :=
  LinearMap.mk₂ ℚ
    (fun x y => Algebra.trace ℚ L (x.1 * y.2) - Algebra.trace ℚ L (x.2 * y.1))
    (fun x x' y => by simp only [Prod.fst_add, Prod.snd_add, add_mul, map_add]; ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_mul_assoc, map_smul, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Prod.fst_add, Prod.snd_add, mul_add, map_add]; ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, mul_smul_comm, map_smul, smul_eq_mul]; ring)

example (x y : L × L) :
    a2a_traceSymplectic L x y = Algebra.trace ℚ L (x.1 * y.2) - Algebra.trace ℚ L (x.2 * y.1) :=
  rfl

end HodgeLean.Foundations
