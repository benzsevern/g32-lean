import HodgeLean.Foundations.InvariantsExterior

/-! # The exterior algebra of a direct sum, degree by degree (FROZEN DEFINITIONS)

Stage A3a of the Powers flagship (`docs/roadmap/pw-flagship-plan.md`, §4.2 row A3a). Two maps:

* `exteriorProdMul i j : ⋀^i S₁ ⊗ ⋀^j S₂ → ⋀^(i+j) (S₁ × S₂)`, `a ⊗ b ↦ a ∧ b`, with `S₁` and `S₂`
  included in `S₁ × S₂` as the two factors;
* `exteriorProdDegree k : ⨁_{i+j=k} ⋀^i S₁ ⊗ ⋀^j S₂ → ⋀^k (S₁ × S₂)`, the sum of the maps
  `exteriorProdMul i j` over `i + j = k`, cast to degree `k`.

Both are maps into the repository's `⋀[K]^k` submodules (Mathlib's `exteriorPower`), on which
`InvariantsExterior.exteriorDer` acts. That they are isomorphisms and agree with Mathlib's
`ExteriorAlgebra.prodEquivTensor` is claimed in `DirectSumInvariants.lean`, not here.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations

variable {K : Type*} [Field K]
variable {S₁ S₂ : Type*} [AddCommGroup S₁] [Module K S₁] [AddCommGroup S₂] [Module K S₂]

/-- The wedge of the two factors: `a ⊗ b ↦ ι₁(a) ∧ ι₂(b)`, where `ι₁ = LinearMap.inl` and
`ι₂ = LinearMap.inr` include `S₁` and `S₂` in `S₁ × S₂`.
Source: Bourbaki, *Algèbre*, ch. III, §7, no. 7, Proposition 10 (the exterior algebra of a direct
sum is the skew tensor product of the exterior algebras). -/
def exteriorProdMul (i j : ℕ) :
    ⋀[K]^i S₁ ⊗[K] ⋀[K]^j S₂ →ₗ[K] ⋀[K]^(i + j) (S₁ × S₂) :=
  TensorProduct.lift
    (((exteriorPower.wedge K (S₁ × S₂) i j).compl₂
        (exteriorPower.map j (LinearMap.inr K S₁ S₂))).comp
      (exteriorPower.map i (LinearMap.inl K S₁ S₂)))

example (i j : ℕ) (a : Fin i → S₁) (b : Fin j → S₂) :
    exteriorProdMul i j
        (exteriorPower.ιMulti K i a ⊗ₜ[K] exteriorPower.ιMulti K j b) =
      exteriorPower.ιMulti K (i + j)
        (Fin.append (LinearMap.inl K S₁ S₂ ∘ a) (LinearMap.inr K S₁ S₂ ∘ b)) := by
  simp only [exteriorProdMul, TensorProduct.lift.tmul, LinearMap.comp_apply,
    LinearMap.compl₂_apply, exteriorPower.map_apply_ιMulti]
  exact InvariantsExterior.wedge_ιMulti _ _

/-- The degree-`k` part: the sum over `i + j = k` of `exteriorProdMul i j`, composed with the
identification `⋀^(i+j) = ⋀^k`.
Source: Bourbaki, *Algèbre*, ch. III, §7, no. 7, Proposition 10, in degree `k`
(`⋀^k (S₁ ⊕ S₂) ≅ ⊕_{i+j=k} ⋀^i S₁ ⊗ ⋀^j S₂`). -/
def exteriorProdDegree (k : ℕ) :
    (⨁ p : {p : ℕ × ℕ // p.1 + p.2 = k}, ⋀[K]^p.1.1 S₁ ⊗[K] ⋀[K]^p.1.2 S₂) →ₗ[K]
      ⋀[K]^k (S₁ × S₂) :=
  DirectSum.toModule K _ _ fun p =>
    (LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[K]^n (S₁ × S₂)) p.2)).toLinearMap ∘ₗ
      exteriorProdMul p.1.1 p.1.2

example (k : ℕ) (p : {p : ℕ × ℕ // p.1 + p.2 = k})
    (x : ⋀[K]^p.1.1 S₁ ⊗[K] ⋀[K]^p.1.2 S₂) :
    ((exteriorProdDegree k (DirectSum.lof K _ _ p x) : ⋀[K]^k (S₁ × S₂)) :
        ExteriorAlgebra K (S₁ × S₂)) =
      (exteriorProdMul p.1.1 p.1.2 x : ExteriorAlgebra K (S₁ × S₂)) := by
  simp [exteriorProdDegree, DirectSum.toModule_lof]

end HodgeLean.Foundations
