import HodgeLean.Foundations.Program.MilneTensorFamilyMaps

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def m1b_copyTensorIn (r n : ℕ) (a : Fin n → Fin r) :
    (⨂[ℂ]^n V) →ₗ[ℂ] (⨂[ℂ]^n (Fin r → V)) :=
  PiTensorProduct.map (fun i => LinearMap.single ℂ (fun _ : Fin r => V) (a i))

def m1b_copyTensorOut (r n : ℕ) (a : Fin n → Fin r) :
    (⨂[ℂ]^n (Fin r → V)) →ₗ[ℂ] (⨂[ℂ]^n V) :=
  PiTensorProduct.map (fun i => LinearMap.proj (a i))

theorem m1b_sum_copyTensorIn_out (r n : ℕ) (t : ⨂[ℂ]^n (Fin r → V)) :
    (∑ a : Fin n → Fin r, m1b_copyTensorIn r n a (m1b_copyTensorOut r n a t)) = t := by
  have h : (∑ a : Fin n → Fin r, (m1b_copyTensorIn (V := V) r n a).comp
      (m1b_copyTensorOut r n a)) = LinearMap.id := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.id_apply, m1b_copyTensorIn, m1b_copyTensorOut, PiTensorProduct.map_tprod,
      LinearMap.single_apply, LinearMap.proj_apply]
    rw [← (PiTensorProduct.tprod ℂ).map_sum (fun i j => Pi.single j (v i j))]
    congr 1
    funext i
    exact LinearMap.sum_single_apply (fun _ : Fin r => V) (v i)
  simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] using
    LinearMap.congr_fun h t

end HodgeLean.Foundations.Program
