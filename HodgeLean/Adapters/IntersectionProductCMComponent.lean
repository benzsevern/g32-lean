import HodgeLean.Adapters.IntersectionProductCMStalk
import HodgeLean.Adapters.KleimanProductLocal

/-! # The local ring at a component of a proper intersection

Let `X` be a smooth integral complex variety, `u`, `v` points of `X` whose closures meet properly,
`y` a component of `(I_u ⊔ I_v).subscheme` and `z` its image, with `A = 𝒪_{X,z}`,
`𝔭 = a3i_stalkIdeal X z u` and `𝔮 = a3i_stalkIdeal X z v`. This file records
* `Tor_0(A/𝔭, A/𝔮) ≅ A/(𝔭 + 𝔮)`, so that the lengths agree (`a3c_length_tor_zero`);
* `dim A = dim A/𝔭 + dim A/𝔮`, all finite (`a3c_component_dims`), from the dimension formula
  `codim u + dim A/𝔭 = codim z` and properness `codim z = codim u + codim v`.

Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, B.6; Fulton, *Intersection Theory*,
second edition, §7.1 and §20.4. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped TensorProduct

namespace HodgeLean.Adapters
universe u

/-- `(A ⧸ 𝔮) ⧸ 𝔭 (A ⧸ 𝔮) ≃ A ⧸ (𝔭 + 𝔮)`. -/
def a3c_quotSMulEquiv {A : Type*} [CommRing A] (𝔭 𝔮 : Ideal A) :
    ((A ⧸ 𝔮) ⧸ (𝔭 • ⊤ : Submodule A (A ⧸ 𝔮))) ≃ₗ[A] A ⧸ (𝔭 ⊔ 𝔮) :=
  Submodule.quotEquivOfEq _ (Submodule.map (Submodule.mkQ 𝔮) (𝔭 ⊔ 𝔮 : Submodule A A)) (by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
    have : (⊤ : Submodule A (A ⧸ 𝔮)) = (⊤ : Submodule A A).map (Submodule.mkQ 𝔮) := by
      rw [Submodule.map_top, Submodule.range_mkQ]
    rw [this, ← Submodule.map_smul'']
    congr 1
    change 𝔭 • (⊤ : Ideal A) = 𝔭
    rw [Ideal.smul_eq_mul, Ideal.mul_top]) ≪≫ₗ
    Submodule.quotientQuotientEquivQuotient 𝔮 (𝔭 ⊔ 𝔮) le_sup_right

/-- `Tor_0(A/𝔭, A/𝔮)` has the length of `A/(𝔭 + 𝔮)`. -/
theorem a3c_length_tor_zero {A : Type u} [CommRing A] (𝔭 𝔮 : Ideal A) :
    Module.length A (((Tor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ 𝔭))).obj
      (ModuleCat.of A (A ⧸ 𝔮))) = Module.length A (A ⧸ (𝔭 ⊔ 𝔮)) := by
  let e1 : (((Tor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ 𝔭))).obj
      (ModuleCat.of A (A ⧸ 𝔮))) ≃ₗ[A] (A ⧸ 𝔭) ⊗[A] (A ⧸ 𝔮) :=
    (a3c_tor0Iso (ModuleCat.of A (A ⧸ 𝔭)) (ModuleCat.of A (A ⧸ 𝔮))).toLinearEquiv
  exact (e1 ≪≫ₗ TensorProduct.quotTensorEquivQuotSMul (A ⧸ 𝔮) 𝔭 ≪≫ₗ
    a3c_quotSMulEquiv 𝔭 𝔮).length_eq

/-- At a component `z` of a proper intersection on a smooth complex variety,
`dim 𝒪_{X,z} = dim 𝒪_{X,z}/𝔭_u + dim 𝒪_{X,z}/𝔭_v`, all three finite. -/
theorem a3c_component_dims (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (u v : X.left) (hp : a3i_MeetProperly X.left u v)
    (y : (ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subscheme)
    (hy : closure ({y} : Set (ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subscheme) ∈
      irreducibleComponents (ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subscheme) :
    u ⤳ (ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subschemeι y ∧
      v ⤳ (ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subschemeι y ∧
      ∃ n a b : ℕ,
        ringKrullDim (X.left.presheaf.stalk
          ((ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subschemeι y)) = n ∧
        ringKrullDim (X.left.presheaf.stalk
            ((ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subschemeι y) ⧸
          a3i_stalkIdeal X.left
            ((ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subschemeι y) u) = a ∧
        ringKrullDim (X.left.presheaf.stalk
            ((ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subschemeι y) ⧸
          a3i_stalkIdeal X.left
            ((ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subschemeι y) v) = b ∧
        n = a + b := by
  set z := (ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subschemeι y with hzdef
  have hzuv : z ∈ closure ({u} : Set X.left) ∩ closure ({v} : Set X.left) := by
    rw [← hc9k_range_subschemeι X u v]
    exact ⟨y, rfl⟩
  have huz : u ⤳ z := specializes_iff_mem_closure.mpr hzuv.1
  have hvz : v ⤳ z := specializes_iff_mem_closure.mpr hzuv.2
  refine ⟨huz, hvz, ?_⟩
  have : IsRegularLocalRing (X.left.presheaf.stalk z) := a3c_isRegularLocalRing_stalk X z
  obtain ⟨xs, hxs, -⟩ := a3c_exists_regular_sop (X.left.presheaf.stalk z)
  set n := xs.length
  have hcz : Order.coheight z = n := by
    have h := ringKrullDim_stalk_eq_coheight z
    rw [← hxs] at h
    exact_mod_cast h.symm
  have hdu := a3c_coheight_add_ringKrullDim_stalkIdeal X z u huz
  have hdv := a3c_coheight_add_ringKrullDim_stalkIdeal X z v hvz
  rw [hcz] at hdu hdv
  obtain ⟨cu, a, hcu, ha, hua⟩ := a3c_split_nat hdu
  obtain ⟨cv, b, hcv, hb, hvb⟩ := a3c_split_nat hdv
  have hprop := hp y hy
  rw [hcz, hcu, hcv] at hprop
  have hprop' : n = cu + cv := by exact_mod_cast hprop
  exact ⟨n, a, b, hxs.symm, ha, hb, by omega⟩

end HodgeLean.Adapters
