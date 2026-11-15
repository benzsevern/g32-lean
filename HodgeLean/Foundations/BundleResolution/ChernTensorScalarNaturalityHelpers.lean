import HodgeLean.Foundations.Singular.TensorScalarCochain
import HodgeLean.Foundations.Singular.TensorDegreeMaps

/-! # Scalar tensor cochains under an actual chain map

Pullback through the actual total tensor map acts on the corresponding
factor cochain in each bidegree.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory
open HodgeLean.Foundations.Singular
open scoped TensorProduct
namespace HodgeLean.Foundations.BundleResolution

theorem i1_tensorScalarCochain_mapLeft {K K' : ChainComplex (ModuleCat ℚ) ℕ}
    (f : K ⟶ K') (L : ChainComplex (ModuleCat ℚ) ℕ) (p q : ℕ)
    (φ : Module.Dual ℚ (K'.X p)) (ψ : Module.Dual ℚ (L.X q)) :
    (tensorScalarCochain K' L p q φ ψ).comp ((f ▷ L).f (p + q)).hom =
      tensorScalarCochain K L p q (φ.comp (f.f p).hom) ψ := by
  suffices h : ModuleCat.ofHom ((tensorScalarCochain K' L p q φ ψ).comp
      ((f ▷ L).f (p + q)).hom) =
      ModuleCat.ofHom (tensorScalarCochain K L p q (φ.comp (f.f p).hom) ψ) from
    congrArg ModuleCat.Hom.hom h
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro r s hrs
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro u v
  have hn := ConcreteCategory.congr_hom
    (tensorDegreeInclusion_naturality f (𝟙 L) r s (p + q) hrs) (u ⊗ₜ[ℚ] v)
  change ((f ▷ L).f (p + q)).hom
    ((HomologicalComplex.ιTensorObj K L r s (p + q) hrs).hom (u ⊗ₜ[ℚ] v)) =
      (HomologicalComplex.ιTensorObj K' L r s (p + q) hrs).hom
        (((f.f r) ⊗ₘ 𝟙 (L.X s)).hom (u ⊗ₜ[ℚ] v)) at hn
  erw [ModuleCat.MonoidalCategory.tensorHom_tmul] at hn
  change tensorScalarCochain K' L p q φ ψ
    (((f ▷ L).f (p + q)).hom
      ((HomologicalComplex.ιTensorObj K L r s (p + q) hrs).hom (u ⊗ₜ[ℚ] v))) =
    tensorScalarCochain K L p q (φ.comp (f.f p).hom) ψ
      ((HomologicalComplex.ιTensorObj K L r s (p + q) hrs).hom (u ⊗ₜ[ℚ] v))
  rw [hn]
  by_cases h : r = p ∧ s = q
  · rcases h with ⟨rfl, rfl⟩
    rw [tensorScalarCochain_self, tensorScalarCochain_self]
    rfl
  · rw [tensorScalarCochain_other K' L p q r s hrs h,
      tensorScalarCochain_other K L p q r s hrs h]

end HodgeLean.Foundations.BundleResolution
