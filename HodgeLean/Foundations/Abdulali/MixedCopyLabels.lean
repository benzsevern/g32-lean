import HodgeLean.Foundations.Abdulali.MixedCopyContraction

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Compatible copy labels turn the enlarged contraction into a labeled base contraction. -/
theorem mixedTensorContraction_copyTensorIn_compatible (r n d : ℕ)
    (ℓ : (⨂[ℂ]^d V) →ₗ[ℂ] ℂ)
    (c : Fin (n + d) → Fin (r + 1)) (a : Fin n → Fin r)
    (ha : ∀ i, c (Fin.castAdd d i) = (a i).succ)
    (he : ∀ j, c (Fin.natAdd n j) = 0) (t : ⨂[ℂ]^(n + d) V) :
    mixedTensorContraction r n d ℓ (m1b_copyTensorIn (r + 1) (n + d) c t) =
      m1b_copyTensorIn r n a (baseTensorContraction n d ℓ t) := by
  classical
  have htail (i : Fin r) (v : V) :
      mixedCopiesOut r (Pi.single i.succ v) = Pi.single i v := by
    ext j
    change (Pi.single i.succ v : Fin (r + 1) → V) j.succ = (Pi.single i v : Fin r → V) j
    simp only [Pi.single_apply, Fin.succ_inj]
  have hhead (v : V) : mixedExtraOut r (Pi.single 0 v) = v := by
    simp only [mixedExtraOut, LinearMap.proj_apply, Pi.single_eq_same]
  have hc : (mixedTensorContraction r n d ℓ).comp
      (m1b_copyTensorIn (r + 1) (n + d) c) =
      (m1b_copyTensorIn r n a).comp (baseTensorContraction n d ℓ) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change mixedTensorContraction r n d ℓ
        (m1b_copyTensorIn (r + 1) (n + d) c (PiTensorProduct.tprod ℂ v)) =
      m1b_copyTensorIn r n a (baseTensorContraction n d ℓ (PiTensorProduct.tprod ℂ v))
    simp only [m1b_copyTensorIn, PiTensorProduct.map_tprod,
      mixedTensorContraction_tprod, baseTensorContraction_tprod, map_smul,
      LinearMap.single_apply, ha, he, htail, hhead]
  exact LinearMap.congr_fun hc t

end HodgeLean.Foundations.Abdulali
