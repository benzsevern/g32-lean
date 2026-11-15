import HodgeLean.Foundations.Abdulali.MixedCopyContraction

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- An original slot placed in the distinguished extra copy is killed by the retained projection. -/
theorem mixedTensorContraction_copyTensorIn_eq_zero_of_original (r n d : ℕ)
    (ℓ : (⨂[ℂ]^d V) →ₗ[ℂ] ℂ) (c : Fin (n + d) → Fin (r + 1))
    (i : Fin n) (hi : c (Fin.castAdd d i) = 0) (t : ⨂[ℂ]^(n + d) V) :
    mixedTensorContraction r n d ℓ (m1b_copyTensorIn (r + 1) (n + d) c t) = 0 := by
  classical
  have hc : (mixedTensorContraction r n d ℓ).comp
      (m1b_copyTensorIn (r + 1) (n + d) c) = 0 := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change mixedTensorContraction r n d ℓ
      (m1b_copyTensorIn (r + 1) (n + d) c (PiTensorProduct.tprod ℂ v)) = 0
    simp only [m1b_copyTensorIn, PiTensorProduct.map_tprod,
      mixedTensorContraction_tprod, LinearMap.single_apply]
    have hz : PiTensorProduct.tprod ℂ (fun k : Fin n =>
        mixedCopiesOut r (Pi.single (c (Fin.castAdd d k)) (v (Fin.castAdd d k)))) = 0 := by
      apply (PiTensorProduct.tprod ℂ).map_coord_zero i
      rw [hi]
      ext j
      change (Pi.single 0 (v (Fin.castAdd d i)) : Fin (r + 1) → V) j.succ = 0
      simp only [Pi.single_apply, Fin.succ_ne_zero, if_false]
    rw [hz, smul_zero]
  exact LinearMap.congr_fun hc t

/-- An extra slot placed in an original copy is killed by the extra-block projection. -/
theorem mixedTensorContraction_copyTensorIn_eq_zero_of_extra (r n d : ℕ)
    (ℓ : (⨂[ℂ]^d V) →ₗ[ℂ] ℂ) (c : Fin (n + d) → Fin (r + 1))
    (j : Fin d) (hj : c (Fin.natAdd n j) ≠ 0) (t : ⨂[ℂ]^(n + d) V) :
    mixedTensorContraction r n d ℓ (m1b_copyTensorIn (r + 1) (n + d) c t) = 0 := by
  classical
  have hc : (mixedTensorContraction r n d ℓ).comp
      (m1b_copyTensorIn (r + 1) (n + d) c) = 0 := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change mixedTensorContraction r n d ℓ
      (m1b_copyTensorIn (r + 1) (n + d) c (PiTensorProduct.tprod ℂ v)) = 0
    simp only [m1b_copyTensorIn, PiTensorProduct.map_tprod,
      mixedTensorContraction_tprod, LinearMap.single_apply]
    have hz : PiTensorProduct.tprod ℂ (fun k : Fin d =>
        mixedExtraOut r (Pi.single (c (Fin.natAdd n k)) (v (Fin.natAdd n k)))) = 0 := by
      apply (PiTensorProduct.tprod ℂ).map_coord_zero j
      change (Pi.single (c (Fin.natAdd n j)) (v (Fin.natAdd n j)) : Fin (r + 1) → V) 0 = 0
      simp only [Pi.single_apply, Ne.symm hj, if_false]
    rw [hz, map_zero, zero_smul]
  exact LinearMap.congr_fun hc t

end HodgeLean.Foundations.Abdulali
