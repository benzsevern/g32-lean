import HodgeLean.Foundations.DirectSumInvariantsProofs

/-! # The Powers flagship, stage A3a: invariants of a direct sum of Lie algebras, and the exterior algebra of a direct sum (FROZEN SPEC)

Stage A3a of formalizing PW v0.3, Theorem 4.2 (`thm:gen`), "Hodge classes on powers of abelian
varieties of Weil type and of type IV with exact endomorphism algebra"
(doi:10.5281/zenodo.23570103), in the plan's algebra track (`docs/roadmap/pw-flagship-plan.md`,
§3.1 item 2 and §4.2 row A3a). Each theorem is proved by the matching `_aux` theorem in
`DirectSumInvariantsProofs.lean`. The definitions `exteriorProdMul` and `exteriorProdDegree` are
in `DirectSumInvariantsDefs.lean`. Everything is pure linear algebra over a field `K`; the
"Derived group" step of Theorem 4.2's proof computes the invariants of `∏_v SL(W_v)` on
`⋀ (⊕_v Space_v)` block by block, and needs these abstract statements (stage A3b does the
induction over blocks).

Setting: Lie algebras `𝔤₁`, `𝔤₂` over `K`, acting through Lie maps `ρᵢ : 𝔤ᵢ → End Mᵢ` (or through
`LieModule` instances of `𝔤₁ × 𝔤₂`); spaces `S₁`, `S₂`; the repository's `⋀[K]^k` (Mathlib's
`exteriorPower`) with the derivation action `InvariantsExterior.exteriorDer`. It claims:

* invariants of a tensor product: the joint kernel of `ρ₁(x) ⊗ 1 + 1 ⊗ ρ₂(y)` on `M₁ ⊗ M₂` is
  `M₁^{𝔤₁} ⊗ M₂^{𝔤₂}` (S1), and the same for Mathlib's `LieModule` structure on `M₁ ⊗ M₂` when
  `𝔤₁ × 𝔤₂` acts on `M₁` through `𝔤₁` and on `M₂` through `𝔤₂` (S2), over any field and finite-
  dimensional `Mᵢ`; over `ℤ` the shape of S1 fails (S12);
* the exterior algebra of a direct sum: `exteriorProdMul` is Mathlib's
  `ExteriorAlgebra.prodEquivTensor` (the graded tensor product `⋀S₁ ᵍ⊗ ⋀S₂`) on pure tensors (S3);
  in degree `k`, `⊕_{i+j=k} ⋀^i S₁ ⊗ ⋀^j S₂ → ⋀^k (S₁ × S₂)` is bijective (S4), and
  `prodEquivTensor` carries `⋀^k (S₁ × S₂)` onto the degree-`k` part (S5); the multiplication
  carries the graded sign `(-1)^{j i'}` (S6), and with `2 ≠ 0` no algebra map from the ungraded
  tensor product does what `prodEquivTensor` does on generators (S11);
* equivariance: `exteriorProdMul` intertwines `exteriorDer (f₁ × f₂)` with
  `exteriorDer f₁ ⊗ 1 + 1 ⊗ exteriorDer f₂`, in characteristic `0` (S7);
* invariants of the exterior algebra of a direct sum: in characteristic `0`,
  `(⋀^k (S₁ × S₂))^{𝔤₁ ⊕ 𝔤₂}` is the image of `⊕_{i+j=k} (⋀^i S₁)^{𝔤₁} ⊗ (⋀^j S₂)^{𝔤₂}` (S8),
  and the map is injective by S4;
* degenerate checks: `S₂ = 0` (S9) and `k = 0` (S10). S1 and S2 hold over every field, while
  S7 and S8 carry `CharZero K` because `exteriorDer` is defined only in characteristic `0`.

It does not claim: any statement about `SL(W)` or `GL(W)` as groups; the multi-block first
fundamental theorem (stage A3b); the weights and the centre (stage A4); anything about an abelian
variety, its cohomology or its Hodge classes. The results are unconditional linear algebra; the
flagship uses them in an implication from `HodgeLieIsGk`. HC no distance; AV milestone no
distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations
open InvariantsExterior

variable {K : Type*} [Field K]

section Tensor

variable {𝔤₁ 𝔤₂ M₁ M₂ : Type*} [LieRing 𝔤₁] [LieAlgebra K 𝔤₁] [LieRing 𝔤₂] [LieAlgebra K 𝔤₂]
  [AddCommGroup M₁] [Module K M₁] [AddCommGroup M₂] [Module K M₂]

/-- **S1, invariants of a tensor product.** Let `𝔤₁ ⊕ 𝔤₂` act on `M₁ ⊗ M₂` by
`(x, y) ↦ ρ₁(x) ⊗ 1 + 1 ⊗ ρ₂(y)`. Its invariants are `M₁^{𝔤₁} ⊗ M₂^{𝔤₂}`, the image of the
tensor product of the two kernels. Over any field; no characteristic hypothesis.
Source: Bourbaki, *Algèbre*, ch. II, §3, no. 7 (over a field, `ker (u ⊗ 1) = ker u ⊗ N`, and
`(P ⊗ N) ∩ (M ⊗ Q) = P ⊗ Q`); PW v0.3, proof of Theorem 4.2, "Derived group" step (the
invariants are computed block by block). -/
theorem spec_a3a_tensor_invariants [FiniteDimensional K M₁] [FiniteDimensional K M₂]
    (ρ₁ : 𝔤₁ →ₗ⁅K⁆ Module.End K M₁) (ρ₂ : 𝔤₂ →ₗ⁅K⁆ Module.End K M₂) :
    (⨅ x : 𝔤₁ × 𝔤₂, LinearMap.ker ((ρ₁ x.1).rTensor M₂ + (ρ₂ x.2).lTensor M₁)) =
      LinearMap.range (TensorProduct.map (⨅ x, LinearMap.ker (ρ₁ x)).subtype
        (⨅ y, LinearMap.ker (ρ₂ y)).subtype) :=
  spec_a3a_tensor_invariants_aux ρ₁ ρ₂

example [FiniteDimensional K M₁] [FiniteDimensional K M₂]
    (ρ₁ : 𝔤₁ →ₗ⁅K⁆ Module.End K M₁) (ρ₂ : 𝔤₂ →ₗ⁅K⁆ Module.End K M₂) (m : M₁) (n : M₂)
    (hm : m ∈ ⨅ x, LinearMap.ker (ρ₁ x)) (hn : n ∈ ⨅ y, LinearMap.ker (ρ₂ y)) (x : 𝔤₁ × 𝔤₂) :
    ((ρ₁ x.1).rTensor M₂ + (ρ₂ x.2).lTensor M₁) (m ⊗ₜ[K] n) = 0 := by
  have h : m ⊗ₜ[K] n ∈ LinearMap.range (TensorProduct.map (⨅ x, LinearMap.ker (ρ₁ x)).subtype
      (⨅ y, LinearMap.ker (ρ₂ y)).subtype) := ⟨⟨m, hm⟩ ⊗ₜ[K] ⟨n, hn⟩, rfl⟩
  rw [← spec_a3a_tensor_invariants ρ₁ ρ₂] at h
  exact (Submodule.mem_iInf _).mp h x

/-- S1 needs no characteristic hypothesis: it applies over `ZMod 2`. -/
example {N₁ N₂ : Type*} [AddCommGroup N₁] [Module (ZMod 2) N₁] [FiniteDimensional (ZMod 2) N₁]
    [AddCommGroup N₂] [Module (ZMod 2) N₂] [FiniteDimensional (ZMod 2) N₂]
    (ρ₁ : Module.End (ZMod 2) N₁ →ₗ⁅ZMod 2⁆ Module.End (ZMod 2) N₁)
    (ρ₂ : Module.End (ZMod 2) N₂ →ₗ⁅ZMod 2⁆ Module.End (ZMod 2) N₂) :
    (⨅ x : Module.End (ZMod 2) N₁ × Module.End (ZMod 2) N₂,
        LinearMap.ker ((ρ₁ x.1).rTensor N₂ + (ρ₂ x.2).lTensor N₁)) =
      LinearMap.range (TensorProduct.map (⨅ x, LinearMap.ker (ρ₁ x)).subtype
        (⨅ y, LinearMap.ker (ρ₂ y)).subtype) :=
  spec_a3a_tensor_invariants ρ₁ ρ₂

/-- **S2, invariants of a tensor product, `LieModule` form.** Let `𝔤₁ × 𝔤₂` act on `M₁` and `M₂`,
with `𝔤₂` acting trivially on `M₁` and `𝔤₁` trivially on `M₂`. Then the invariants of Mathlib's
`LieModule` structure on `M₁ ⊗ M₂` (`⁅z, m ⊗ n⁆ = ⁅z, m⁆ ⊗ n + m ⊗ ⁅z, n⁆`) are
`M₁^{𝔤₁ × 𝔤₂} ⊗ M₂^{𝔤₁ × 𝔤₂}`, that is `M₁^{𝔤₁} ⊗ M₂^{𝔤₂}`.
Source: as S1 (Bourbaki, *Algèbre*, ch. II, §3, no. 7); Mathlib's `TensorProduct.LieModule`
(`Mathlib/Algebra/Lie/TensorProduct.lean`, `lie_tmul_right`). -/
theorem spec_a3a_maxTrivSubmodule_tensor [FiniteDimensional K M₁] [FiniteDimensional K M₂]
    [LieRingModule (𝔤₁ × 𝔤₂) M₁] [LieModule K (𝔤₁ × 𝔤₂) M₁]
    [LieRingModule (𝔤₁ × 𝔤₂) M₂] [LieModule K (𝔤₁ × 𝔤₂) M₂]
    (h₁ : ∀ (y : 𝔤₂) (m : M₁), ⁅((0 : 𝔤₁), y), m⁆ = 0)
    (h₂ : ∀ (x : 𝔤₁) (n : M₂), ⁅(x, (0 : 𝔤₂)), n⁆ = 0) :
    (LieModule.maxTrivSubmodule K (𝔤₁ × 𝔤₂) (M₁ ⊗[K] M₂) : Submodule K (M₁ ⊗[K] M₂)) =
      LinearMap.range (TensorProduct.map
        (LieModule.maxTrivSubmodule K (𝔤₁ × 𝔤₂) M₁ : Submodule K M₁).subtype
        (LieModule.maxTrivSubmodule K (𝔤₁ × 𝔤₂) M₂ : Submodule K M₂).subtype) :=
  spec_a3a_maxTrivSubmodule_tensor_aux h₁ h₂

example [FiniteDimensional K M₁] [FiniteDimensional K M₂]
    [LieRingModule (𝔤₁ × 𝔤₂) M₁] [LieModule K (𝔤₁ × 𝔤₂) M₁]
    [LieRingModule (𝔤₁ × 𝔤₂) M₂] [LieModule K (𝔤₁ × 𝔤₂) M₂]
    (h₁ : ∀ (y : 𝔤₂) (m : M₁), ⁅((0 : 𝔤₁), y), m⁆ = 0)
    (h₂ : ∀ (x : 𝔤₁) (n : M₂), ⁅(x, (0 : 𝔤₂)), n⁆ = 0)
    (m : LieModule.maxTrivSubmodule K (𝔤₁ × 𝔤₂) M₁)
    (n : LieModule.maxTrivSubmodule K (𝔤₁ × 𝔤₂) M₂) :
    (m : M₁) ⊗ₜ[K] (n : M₂) ∈ LieModule.maxTrivSubmodule K (𝔤₁ × 𝔤₂) (M₁ ⊗[K] M₂) := by
  have h : (m : M₁) ⊗ₜ[K] (n : M₂) ∈ (LieModule.maxTrivSubmodule K (𝔤₁ × 𝔤₂) (M₁ ⊗[K] M₂) :
      Submodule K (M₁ ⊗[K] M₂)) := by
    rw [spec_a3a_maxTrivSubmodule_tensor h₁ h₂]
    exact ⟨m ⊗ₜ[K] n, rfl⟩
  exact h

/-- **S12, falsification: S1 needs a field.** Over `ℤ`, let the abelian Lie algebra `ℤ` act on
`ℤ` by multiplication by `2` and trivially on `ZMod 2`. On `ℤ ⊗ ZMod 2 ≅ ZMod 2` the operator
`2 ⊗ 1` is zero, so every element is invariant, while `ker 2 = 0` on `ℤ`, so the right side of
S1 is `0`: the kernel of `2 ⊗ 1` is not the image of `ker 2 ⊗ ZMod 2`.
Source: constructed here; compare Bourbaki, *Algèbre*, ch. II, §3, no. 7 (exactness of `⊗ N`
needs `N` flat, which `ZMod 2` is not over `ℤ`). -/
theorem spec_a3a_ker_rTensor_ne_over_int :
    LinearMap.ker ((2 : Module.End ℤ ℤ).rTensor (ZMod 2)) ≠
      LinearMap.range ((LinearMap.ker (2 : Module.End ℤ ℤ)).subtype.rTensor (ZMod 2)) :=
  spec_a3a_ker_rTensor_ne_over_int_aux

example :
    LinearMap.range ((LinearMap.ker (2 : Module.End ℤ ℤ)).subtype.rTensor (ZMod 2)) ≠
      LinearMap.ker ((2 : Module.End ℤ ℤ).rTensor (ZMod 2)) :=
  spec_a3a_ker_rTensor_ne_over_int.symm

end Tensor

section Exterior

variable {S₁ S₂ : Type*} [AddCommGroup S₁] [Module K S₁] [AddCommGroup S₂] [Module K S₂]

/-- **S3, bridge to Mathlib's graded tensor product.** In `⋀ (S₁ × S₂)`, `exteriorProdMul i j`
of `a ⊗ b` is the inverse of Mathlib's `ExteriorAlgebra.prodEquivTensor` applied to the graded
pure tensor `a ᵍ⊗ₜ b` of `⋀S₁ ᵍ⊗ ⋀S₂`.
Source: Bourbaki, *Algèbre*, ch. III, §7, no. 7, Proposition 10; Mathlib's
`ExteriorAlgebra.prodEquivTensor` (`Mathlib/LinearAlgebra/ExteriorAlgebra/Product.lean`), the
`Q = 0` analogue of `CliffordAlgebra.prodEquiv` with the `ℕ`-grading. -/
theorem spec_a3a_exteriorProdMul_tmul (i j : ℕ) (a : ⋀[K]^i S₁) (b : ⋀[K]^j S₂) :
    ((exteriorProdMul i j (a ⊗ₜ[K] b) : ⋀[K]^(i + j) (S₁ × S₂)) : ExteriorAlgebra K (S₁ × S₂)) =
      (ExteriorAlgebra.prodEquivTensor K S₁ S₂).symm
        ((a : ExteriorAlgebra K S₁) ᵍ⊗ₜ[K] (b : ExteriorAlgebra K S₂)) :=
  spec_a3a_exteriorProdMul_tmul_aux i j a b

example (i j : ℕ) (a : ⋀[K]^i S₁) (b : ⋀[K]^j S₂) :
    ExteriorAlgebra.prodEquivTensor K S₁ S₂ (exteriorProdMul i j (a ⊗ₜ[K] b) : _) =
      (a : ExteriorAlgebra K S₁) ᵍ⊗ₜ[K] (b : ExteriorAlgebra K S₂) := by
  rw [spec_a3a_exteriorProdMul_tmul i j a b, AlgEquiv.apply_symm_apply]

/-- **S4, the exterior algebra of a direct sum in degree `k`.** The map
`⊕_{i+j=k} ⋀^i S₁ ⊗ ⋀^j S₂ → ⋀^k (S₁ × S₂)`, `a ⊗ b ↦ a ∧ b`, is bijective; so
`⋀^k (S₁ × S₂) ≅ ⊕_{i+j=k} ⋀^i S₁ ⊗ ⋀^j S₂` as `K`-modules.
Source: Bourbaki, *Algèbre*, ch. III, §7, no. 7, Proposition 10 and its corollary in each
degree. -/
theorem spec_a3a_exteriorProdDegree_bijective (k : ℕ) :
    Function.Bijective (exteriorProdDegree (K := K) (S₁ := S₁) (S₂ := S₂) k) :=
  spec_a3a_exteriorProdDegree_bijective_aux k

example (k : ℕ) :
    Nonempty (⋀[K]^k (S₁ × S₂) ≃ₗ[K]
      ⨁ p : {p : ℕ × ℕ // p.1 + p.2 = k}, ⋀[K]^p.1.1 S₁ ⊗[K] ⋀[K]^p.1.2 S₂) :=
  ⟨(LinearEquiv.ofBijective _ (spec_a3a_exteriorProdDegree_bijective k)).symm⟩

/-- **S5, `prodEquivTensor` is degree-wise.** An element `x` of `⋀ (S₁ × S₂)` has degree `k`
exactly when its image under Mathlib's `prodEquivTensor`, read in `⋀S₁ ⊗ ⋀S₂`, lies in the sum of
the images of `⋀^i S₁ ⊗ ⋀^j S₂` over `i + j = k`.
Source: Bourbaki, *Algèbre*, ch. III, §7, no. 7, Proposition 10 (the isomorphism is graded);
Mathlib's `ExteriorAlgebra.prodEquivTensor`. -/
theorem spec_a3a_mem_exteriorPower_iff (k : ℕ) (x : ExteriorAlgebra K (S₁ × S₂)) :
    x ∈ ⋀[K]^k (S₁ × S₂) ↔
      (GradedTensorProduct.of K (fun i : ℕ => ⋀[K]^i S₁) (fun i : ℕ => ⋀[K]^i S₂)).symm
          (ExteriorAlgebra.prodEquivTensor K S₁ S₂ x) ∈
        ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = k},
          LinearMap.range (TensorProduct.map (⋀[K]^p.1.1 S₁).subtype (⋀[K]^p.1.2 S₂).subtype) :=
  spec_a3a_mem_exteriorPower_iff_aux k x

example (k : ℕ) (y : ⋀[K]^k (S₁ × S₂)) :
    (GradedTensorProduct.of K (fun i : ℕ => ⋀[K]^i S₁) (fun i : ℕ => ⋀[K]^i S₂)).symm
        (ExteriorAlgebra.prodEquivTensor K S₁ S₂ y) ∈
      ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = k},
        LinearMap.range (TensorProduct.map (⋀[K]^p.1.1 S₁).subtype (⋀[K]^p.1.2 S₂).subtype) :=
  (spec_a3a_mem_exteriorPower_iff k (y : ExteriorAlgebra K (S₁ × S₂))).mp y.2

/-- **S6, the sign of the graded tensor product.** For `a ∈ ⋀^i S₁`, `b ∈ ⋀^j S₂`,
`a' ∈ ⋀^i' S₁`, `b' ∈ ⋀^j' S₂`: `(a ∧ b) ∧ (a' ∧ b') = (-1)^{j i'} (a ∧ a') ∧ (b ∧ b')` in
`⋀ (S₁ × S₂)`, the multiplication `(a ⊗ b)(a' ⊗ b') = (-1)^{|b||a'|} aa' ⊗ bb'` of `⋀S₁ ᵍ⊗ ⋀S₂`.
Source: Bourbaki, *Algèbre*, ch. III, §4, no. 7 (the skew tensor product of graded algebras) and
§7, no. 7, Proposition 10; Mathlib's `ExteriorAlgebra.map_inl_inr_anticomm`. -/
theorem spec_a3a_exteriorProdMul_mul (i j i' j' : ℕ) (a : ⋀[K]^i S₁) (b : ⋀[K]^j S₂)
    (a' : ⋀[K]^i' S₁) (b' : ⋀[K]^j' S₂) :
    ((exteriorProdMul i j (a ⊗ₜ[K] b) : ⋀[K]^(i + j) (S₁ × S₂)) : ExteriorAlgebra K (S₁ × S₂)) *
        (exteriorProdMul i' j' (a' ⊗ₜ[K] b') : ⋀[K]^(i' + j') (S₁ × S₂)) =
      (-1 : K) ^ (j * i') •
        ((exteriorProdMul (i + i') (j + j')
          (exteriorPower.wedge K S₁ i i' a a' ⊗ₜ[K] exteriorPower.wedge K S₂ j j' b b') :
            ⋀[K]^(i + i' + (j + j')) (S₁ × S₂)) : ExteriorAlgebra K (S₁ × S₂)) :=
  spec_a3a_exteriorProdMul_mul_aux i j i' j' a b a' b'

example (i j' : ℕ) (a : ⋀[K]^i S₁) (b : ⋀[K]^1 S₂) (a' : ⋀[K]^1 S₁) (b' : ⋀[K]^j' S₂) :
    ((exteriorProdMul i 1 (a ⊗ₜ[K] b) : ⋀[K]^(i + 1) (S₁ × S₂)) : ExteriorAlgebra K (S₁ × S₂)) *
        (exteriorProdMul 1 j' (a' ⊗ₜ[K] b') : ⋀[K]^(1 + j') (S₁ × S₂)) =
      -((exteriorProdMul (i + 1) (1 + j')
          (exteriorPower.wedge K S₁ i 1 a a' ⊗ₜ[K] exteriorPower.wedge K S₂ 1 j' b b') :
            ⋀[K]^(i + 1 + (1 + j')) (S₁ × S₂)) : ExteriorAlgebra K (S₁ × S₂)) := by
  rw [spec_a3a_exteriorProdMul_mul, mul_one, pow_one, neg_one_smul]

/-- **S9, degenerate check `S₂ = 0`.** If `S₂ = 0`, then `a ⊗ c ↦ a ∧ c` from
`⋀^k S₁ ⊗ ⋀^0 S₂ = ⋀^k S₁ ⊗ K` to `⋀^k (S₁ × S₂)` is already bijective: the other summands of S4
vanish.
Source: constructed here; Bourbaki, *Algèbre*, ch. III, §7, no. 7, Proposition 10, with
`⋀ 0 = K`. -/
theorem spec_a3a_exteriorProdMul_bijective_of_subsingleton [Subsingleton S₂] (k : ℕ) :
    Function.Bijective (exteriorProdMul (K := K) (S₁ := S₁) (S₂ := S₂) k 0) :=
  spec_a3a_exteriorProdMul_bijective_of_subsingleton_aux k

example [Subsingleton S₂] (k : ℕ) :
    Nonempty (⋀[K]^k S₁ ⊗[K] ⋀[K]^0 S₂ ≃ₗ[K] ⋀[K]^(k + 0) (S₁ × S₂)) :=
  ⟨LinearEquiv.ofBijective _ (spec_a3a_exteriorProdMul_bijective_of_subsingleton k)⟩

/-- **S10, degenerate check `k = 0`.** The derivation action on `⋀^0 = K` is zero, so in degree
`0` every element is invariant, and S8 at `k = 0` says the image of `K ⊗ K` is everything (the
`example`).
Source: constructed here; Fulton–Harris, *Representation Theory*, §8.1 (a Lie algebra acts on
`⋀^0 = K` trivially). -/
theorem spec_a3a_exteriorDer_zero {M : Type*} [AddCommGroup M] [Module K M]
    (f : Module.End K M) : exteriorDer 0 f = 0 :=
  spec_a3a_exteriorDer_zero_aux f

/-- **S11, falsification: the ungraded tensor product.** If `2 ≠ 0` in `K`, there is no algebra
map from the ungraded tensor product `⋀K ⊗ ⋀K` to `⋀ (K × K)` sending `ι 1 ⊗ 1 ↦ ι (1, 0)` and
`1 ⊗ ι 1 ↦ ι (0, 1)`, as `prodEquivTensor.symm` does for the graded one: the ungraded product
makes the two images commute, while in `⋀ (K × K)` they anticommute and their product is not `0`.
In characteristic `2` the sign `-1 = 1` disappears and the hypothesis `2 ≠ 0` cannot be dropped.
Source: constructed here; Bourbaki, *Algèbre*, ch. III, §7, no. 7, Proposition 10 (the
isomorphism is with the skew tensor product, not the ordinary one). -/
theorem spec_a3a_not_exists_ungraded_algHom (h2 : (2 : K) ≠ 0) :
    ¬ ∃ φ : ExteriorAlgebra K K ⊗[K] ExteriorAlgebra K K →ₐ[K] ExteriorAlgebra K (K × K),
      φ (ExteriorAlgebra.ι K 1 ⊗ₜ[K] 1) = ExteriorAlgebra.ι K (1, 0) ∧
        φ (1 ⊗ₜ[K] ExteriorAlgebra.ι K 1) = ExteriorAlgebra.ι K (0, 1) :=
  spec_a3a_not_exists_ungraded_algHom_aux h2

example :
    ¬ ∃ φ : ExteriorAlgebra ℚ ℚ ⊗[ℚ] ExteriorAlgebra ℚ ℚ →ₐ[ℚ] ExteriorAlgebra ℚ (ℚ × ℚ),
      φ (ExteriorAlgebra.ι ℚ 1 ⊗ₜ[ℚ] 1) = ExteriorAlgebra.ι ℚ (1, 0) ∧
        φ (1 ⊗ₜ[ℚ] ExteriorAlgebra.ι ℚ 1) = ExteriorAlgebra.ι ℚ (0, 1) :=
  spec_a3a_not_exists_ungraded_algHom two_ne_zero

variable [CharZero K]

/-- **S7, equivariance.** For `f₁ ∈ End S₁` and `f₂ ∈ End S₂`, `exteriorProdMul i j` intertwines
`exteriorDer f₁ ⊗ 1 + 1 ⊗ exteriorDer f₂` on `⋀^i S₁ ⊗ ⋀^j S₂` with `exteriorDer (f₁ × f₂)` on
`⋀^(i+j) (S₁ × S₂)`. So the isomorphism of S4 intertwines the actions of `𝔤₁ ⊕ 𝔤₂` whenever
`𝔤ᵢ` acts on `Sᵢ`. The derivations have degree `0`, so no sign appears here; the graded sign is
in the multiplication (S6, S11).
Source: Fulton–Harris, *Representation Theory*, §8.1 (a Lie algebra acts on `⋀` by derivations);
Bourbaki, *Algèbre*, ch. III, §7, no. 7, Proposition 10; the repository's `exteriorDer_wedge` and
`exteriorDer_map` (`Foundations/InvariantsExterior.lean`). -/
theorem spec_a3a_exteriorDer_comp_exteriorProdMul (i j : ℕ) (f₁ : Module.End K S₁)
    (f₂ : Module.End K S₂) :
    exteriorDer (i + j) (f₁.prodMap f₂) ∘ₗ exteriorProdMul i j =
      exteriorProdMul i j ∘ₗ
        ((exteriorDer i f₁).rTensor (⋀[K]^j S₂) + (exteriorDer j f₂).lTensor (⋀[K]^i S₁)) :=
  spec_a3a_exteriorDer_comp_exteriorProdMul_aux i j f₁ f₂

example (i j : ℕ) (f₁ : Module.End K S₁) (f₂ : Module.End K S₂) (a : ⋀[K]^i S₁)
    (b : ⋀[K]^j S₂) :
    exteriorDer (i + j) (f₁.prodMap f₂) (exteriorProdMul i j (a ⊗ₜ[K] b)) =
      exteriorProdMul i j (exteriorDer i f₁ a ⊗ₜ[K] b + a ⊗ₜ[K] exteriorDer j f₂ b) := by
  have := LinearMap.congr_fun (spec_a3a_exteriorDer_comp_exteriorProdMul i j f₁ f₂) (a ⊗ₜ[K] b)
  simpa using this

/-- **S8, invariants of the exterior algebra of a direct sum.** Let `𝔤₁ ⊕ 𝔤₂` act on `S₁ × S₂` by
`(x, y) ↦ ρ₁(x) × ρ₂(y)`, and on `⋀^k (S₁ × S₂)` by `exteriorDer`. In characteristic `0` its
invariants are the image under the isomorphism of S4 of
`⊕_{i+j=k} (⋀^i S₁)^{𝔤₁} ⊗ (⋀^j S₂)^{𝔤₂}`.
Source: PW v0.3, proof of Theorem 4.2, "Derived group" step (the `∏_v SL(W_v)`-invariants of
`⊗_v Λ_v` are `⊗_v Λ_v^{SL(W_v)}`); from S1, S4 and S7. -/
theorem spec_a3a_exterior_invariants {𝔤₁ 𝔤₂ : Type*} [LieRing 𝔤₁] [LieAlgebra K 𝔤₁]
    [LieRing 𝔤₂] [LieAlgebra K 𝔤₂] [FiniteDimensional K S₁] [FiniteDimensional K S₂]
    (ρ₁ : 𝔤₁ →ₗ⁅K⁆ Module.End K S₁) (ρ₂ : 𝔤₂ →ₗ⁅K⁆ Module.End K S₂) (k : ℕ) :
    (⨅ x : 𝔤₁ × 𝔤₂, LinearMap.ker (exteriorDer k ((ρ₁ x.1).prodMap (ρ₂ x.2)))) =
      ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = k},
        LinearMap.range (exteriorProdDegree k ∘ₗ
          DirectSum.lof K _ (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} =>
            ⋀[K]^p.1.1 S₁ ⊗[K] ⋀[K]^p.1.2 S₂) p ∘ₗ
          TensorProduct.map (⨅ x, LinearMap.ker (exteriorDer p.1.1 (ρ₁ x))).subtype
            (⨅ y, LinearMap.ker (exteriorDer p.1.2 (ρ₂ y))).subtype) :=
  spec_a3a_exterior_invariants_aux ρ₁ ρ₂ k

/-- S8 at `k = 0`, with S10: the image of `(⋀^0 S₁)^{𝔤₁} ⊗ (⋀^0 S₂)^{𝔤₂}` is all of `⋀^0`. -/
example {𝔤₁ 𝔤₂ : Type*} [LieRing 𝔤₁] [LieAlgebra K 𝔤₁] [LieRing 𝔤₂] [LieAlgebra K 𝔤₂]
    [FiniteDimensional K S₁] [FiniteDimensional K S₂]
    (ρ₁ : 𝔤₁ →ₗ⁅K⁆ Module.End K S₁) (ρ₂ : 𝔤₂ →ₗ⁅K⁆ Module.End K S₂) :
    (⨆ p : {p : ℕ × ℕ // p.1 + p.2 = 0},
        LinearMap.range (exteriorProdDegree 0 ∘ₗ
          DirectSum.lof K _ (fun p : {p : ℕ × ℕ // p.1 + p.2 = 0} =>
            ⋀[K]^p.1.1 S₁ ⊗[K] ⋀[K]^p.1.2 S₂) p ∘ₗ
          TensorProduct.map (⨅ x, LinearMap.ker (exteriorDer p.1.1 (ρ₁ x))).subtype
            (⨅ y, LinearMap.ker (exteriorDer p.1.2 (ρ₂ y))).subtype)) = ⊤ := by
  rw [← spec_a3a_exterior_invariants ρ₁ ρ₂ 0]
  simp [spec_a3a_exteriorDer_zero]

end Exterior

end HodgeLean.Foundations
