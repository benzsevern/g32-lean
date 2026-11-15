import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Cap.Relative
import HodgeLean.Foundations.Singular.Cup

/-! # Actual relative cochain cup action

The same-pair relative cap product defines a relative cup cochain by duality.
It uses the actual relative-chain cokernel and the Alexander–Whitney product.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.BundleResolution

variable (P : TopPair) (p q : ℕ)

def i1_relativeCupCochain :
    RelativeCochain ℚ P p →ₗ[ℚ]
      Cochain ℚ (TopCat.toSSet.obj P.fst) q →ₗ[ℚ] RelativeCochain ℚ P (p + q) where
  toFun φ := (relativeCap ℚ P p q φ).dualMap
  map_add' φ ψ := by
    ext η c
    change η (relativeCapLinear ℚ P p q (φ + ψ) c) =
      η (relativeCapLinear ℚ P p q φ c) + η (relativeCapLinear ℚ P p q ψ c)
    simp only [map_add, LinearMap.add_apply]
  map_smul' a φ := by
    ext η c
    change η (relativeCapLinear ℚ P p q (a • φ) c) =
      a • η (relativeCapLinear ℚ P p q φ c)
    simp only [map_smul, LinearMap.smul_apply]

theorem i1_relativeCupCochain_toAbsolute
    (φ : RelativeCochain ℚ P p) (ψ : Cochain ℚ (TopCat.toSSet.obj P.fst) q) :
    relativeCochainToAbsolute ℚ P (p + q) (i1_relativeCupCochain P p q φ ψ) =
      HodgeLean.Foundations.Singular.cupCochain P.fst p q
        (relativeCochainToAbsolute ℚ P p φ) ψ := by
  ext c
  change ψ (relativeCap ℚ P p q φ (((relativeChainProjection ℚ P).f (p + q)).hom c)) = _
  rw [relativeCap_projection_apply]
  rfl

theorem i1_relativeCochainToAbsolute_injective (n : ℕ) :
    Function.Injective (relativeCochainToAbsolute ℚ P n) := by
  haveI : Epi ((relativeChainProjection ℚ P).f n) :=
    Cofork.IsColimit.epi (relativeChainProjectionComponentIsCokernelForCap ℚ P n)
  exact LinearMap.dualMap_injective_of_surjective
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

theorem i1_relativeCupCochain_closed
    (φ : RelativeCochain ℚ P p) (ψ : Cochain ℚ (TopCat.toSSet.obj P.fst) q)
    (hφ : relativeCoboundary ℚ P p φ = 0) (hψ : coboundary ℚ q ψ = 0) :
    relativeCoboundary ℚ P (p + q) (i1_relativeCupCochain P p q φ ψ) = 0 := by
  apply i1_relativeCochainToAbsolute_injective P (p + q + 1)
  have ha := congrArg (relativeCochainToAbsolute ℚ P (p + 1)) hφ
  rw [relativeCochainToAbsolute_coboundary, map_zero] at ha
  rw [relativeCochainToAbsolute_coboundary, i1_relativeCupCochain_toAbsolute,
    HodgeLean.Foundations.Singular.coboundary_cupCochain, ha, hψ]
  simp only [map_zero, LinearMap.zero_apply, LinearMap.zero_comp, smul_zero, add_zero]

theorem i1_relativeCupCochain_one (φ : RelativeCochain ℚ P p) :
    i1_relativeCupCochain P p 0 φ (HodgeLean.Foundations.Singular.unitCochain P.fst) = φ := by
  apply i1_relativeCochainToAbsolute_injective P p
  exact (i1_relativeCupCochain_toAbsolute P p 0 φ _).trans
    (HodgeLean.Foundations.Singular.cupCochain_one P.fst p _)

end HodgeLean.Foundations.BundleResolution
