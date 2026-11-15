import HodgeLean.Foundations.CMSplitting
import HodgeLean.Foundations.PowersVocabularyDefs
import HodgeLean.Foundations.WeilPowerTransport

/-! # `Lie(G_k)_ℂ` in block form, stage A2b (FROZEN DEFINITIONS)

Definitions for `CMLieBlocks`, stage A2b of the Powers flagship (PW v0.3, Theorem 4.2,
doi:10.5281/zenodo.23570103; plan `docs/roadmap/pw-flagship-plan.md`, §4.2 row A2b). They concern
a finite-dimensional `ℚ`-space `V` with a `ℚ`-algebra map `ι : L →ₐ[ℚ] Module.End ℚ V` from a
number field `L`, so that `ℂ ⊗ V = ⊕_τ W_τ` (A2a, `spec_a2a_iSupIndep`, `spec_a2a_iSup_eq_top`):

* `cmPlusEmb L u d`, the type of embeddings `v : L → ℂ` with `v(u) = i√d`, which index the
  blocks `W_v` (the paper's `σ_v`, one for each real place of `F`);
* `cmProjection ι τ`, the projection `ℂ ⊗ V → W_τ` along the other `W_σ`;
* `cmBlock ι τ X`, the diagonal block `π_τ ∘ X ∘ incl_τ` of an endomorphism `X` of `ℂ ⊗ V`, the
  multi-block form of `WeilPower.firstBlock`;
* `cmBlockTraceZero ι u d`, the tuples `(X_v)_v ∈ ⊕_v 𝔤𝔩(W_v)` with `Σ_v tr X_v = 0`;
* `a2b_cmSymplectic L`, the form `((x₁, x₂), (y₁, y₂)) ↦ Tr(x₁ ȳ₂) - Tr(x₂ ȳ₁)` on `L × L`, the
  concrete model used to show that the binders of the block statements can be met.

No definition asserts a block decomposition of `gkLie`, a dimension, an intertwining or a trace
identity. HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations

open scoped TensorProduct
open NumberField

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The embeddings `v : L → ℂ` with `v(u) = i√d`. For `k = ℚ(u) ⊆ L`, `u² = -d`, `d > 0`, they are
the extensions `σ_v` of the fixed embedding `σ(u) = i√d` of `k`, one for each real place `v` of
the maximal totally real subfield `F` (A2a's S5: there are `[L : ℚ] / 2` of them).
Source: PW v0.3, Subsection 2.3 ("Each real place `v` of `F` has a unique extension `σ_v` of
`σ` to `L`"). -/
abbrev cmPlusEmb (L : Type*) [CommRing L] [Algebra ℚ L] (u : L) (d : ℚ) : Type _ :=
  {τ : L →ₐ[ℚ] ℂ // τ u = HodgeBlocks.WeilAction.omegaC d}

example {L : Type*} [CommRing L] [Algebra ℚ L] (u : L) (d : ℚ) (v : cmPlusEmb L u d) :
    v.1 u = HodgeBlocks.WeilAction.omegaC d :=
  v.2

/-- The two normalizations of `i√3` agree: A2b states everything with `omegaC d`, and the
`d = 3` files `Foundations/WeilPower*.lean` use `WeilPower.root`.
Source: `HodgeBlocks.WeilAction.omegaC` (`Blocks/Weil/Basic.lean`), `WeilPower.root`
(`Foundations/WeilPower.lean`). -/
example : HodgeBlocks.WeilAction.omegaC 3 = WeilPower.root := by
  simp [HodgeBlocks.WeilAction.omegaC, WeilPower.root]

section NumberField

variable {L : Type*} [Field L] [NumberField L] [FiniteDimensional ℚ V]

/-- The projection `ℂ ⊗ V → W_τ` along the other joint eigenspaces, read off from the internal
direct sum `ℂ ⊗ V = ⊕_τ W_τ` of A2a (S1 and S2).
Source: PW v0.3, Subsection 2.3 (`V_ℂ = ⊕_v (W_v ⊕ W̄_v)`); `spec_a2a_iSupIndep`,
`spec_a2a_iSup_eq_top` (`Foundations/CMSplitting.lean`). -/
def cmProjection (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ) :
    (ℂ ⊗[ℚ] V) →ₗ[ℂ] cmEigenspace ι τ :=
  haveI := Classical.decEq (L →ₐ[ℚ] ℂ)
  (DirectSum.component ℂ (L →ₐ[ℚ] ℂ) (fun σ => cmEigenspace ι σ) τ).comp
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap (cmEigenspace ι))
      ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
        ⟨spec_a2a_iSupIndep ι, spec_a2a_iSup_eq_top ι⟩)).symm.toLinearMap

example (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ) (x : cmEigenspace ι τ) :
    cmProjection ι τ x = x := by
  classical
  exact DirectSum.IsInternal.ofBijective_coeLinearMap_same
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨spec_a2a_iSupIndep ι, spec_a2a_iSup_eq_top ι⟩) x

/-- The diagonal block `X_τ = π_τ ∘ X ∘ incl_τ ∈ 𝔤𝔩(W_τ)` of an endomorphism `X` of `ℂ ⊗ V`. For
`X` commuting with `ι(L)_ℂ` it is the restriction of `X` to `W_τ`. At `L = k`, `d = 3` it plays
the role of `WeilPower.firstBlock`.
Source: PW v0.3, Subsection 2.3 (`Lef(A)_ℂ = ∏_v GL(W_v)`, an element acting on `W_v` through its
`v`-component); `WeilPower.firstBlock` (`Foundations/WeilPowerLie.lean`). -/
def cmBlock (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ) :
    Module.End ℂ (ℂ ⊗[ℚ] V) →ₗ[ℂ] Module.End ℂ (cmEigenspace ι τ) where
  toFun X := cmProjection ι τ ∘ₗ X ∘ₗ (cmEigenspace ι τ).subtype
  map_add' X Y := by ext; simp
  map_smul' c X := by ext; simp

example (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ) (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (x : cmEigenspace ι τ) :
    cmBlock ι τ X x = cmProjection ι τ (X x) :=
  rfl

/-- The tuples `(X_v)_v ∈ ⊕_v 𝔤𝔩(W_v)`, indexed by the embeddings `v` with `v(u) = i√d`, whose
traces sum to zero: `Σ_v tr X_v = 0`. This is the target of the block form of
`Lie(G_k(A))_ℂ`.
Source: PW v0.3, Subsection 2.3 (`G_k(A)_ℂ = {(g_v) : ∏_v det g_v = 1}`, whose Lie algebra is
`{(X_v) : Σ_v tr X_v = 0}`). -/
def cmBlockTraceZero (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ) :
    Submodule ℂ (∀ v : cmPlusEmb L u d, Module.End ℂ (cmEigenspace ι v.1)) :=
  LinearMap.ker (∑ v : cmPlusEmb L u d,
    (LinearMap.trace ℂ (cmEigenspace ι v.1)).comp
      (LinearMap.proj (R := ℂ) (φ := fun w : cmPlusEmb L u d => Module.End ℂ (cmEigenspace ι w.1))
        v))

example (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ)
    (Y : ∀ v : cmPlusEmb L u d, Module.End ℂ (cmEigenspace ι v.1)) :
    Y ∈ cmBlockTraceZero ι u d ↔ ∑ v, LinearMap.trace ℂ _ (Y v) = 0 := by
  simp [cmBlockTraceZero]

variable (L) in
/-- The alternating form `((x₁, x₂), (y₁, y₂)) ↦ Tr(x₁ c(y₂)) - Tr(x₂ c(y₁))` on `L × L`, for a CM
field `L` with complex conjugation `c`. With the diagonal action it satisfies the Rosati
condition `E(a x, y) = E(x, c(a) y)`, the binder of the block statements, so those binders can
be met for every CM field.
Source: constructed here; compare Shimura, *Abelian varieties with complex multiplication and
modular functions*, §4–6 (CM polarizations `Tr(ξ x c(y))` on `L`). -/
def a2b_cmSymplectic [IsCMField L] : LinearMap.BilinForm ℚ (L × L) :=
  LinearMap.mk₂ ℚ
    (fun x y => Algebra.trace ℚ L (x.1 * IsCMField.complexConj L y.2) -
      Algebra.trace ℚ L (x.2 * IsCMField.complexConj L y.1))
    (fun x x' y => by simp only [Prod.fst_add, Prod.snd_add, add_mul, map_add]; ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_mul_assoc, map_smul, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Prod.fst_add, Prod.snd_add, map_add, mul_add]; ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_rat_smul, map_smul, mul_smul_comm,
        smul_eq_mul]; ring)

example [IsCMField L] (x y : L × L) :
    a2b_cmSymplectic L x y = Algebra.trace ℚ L (x.1 * IsCMField.complexConj L y.2) -
      Algebra.trace ℚ L (x.2 * IsCMField.complexConj L y.1) :=
  rfl

end NumberField

end HodgeLean.Foundations
