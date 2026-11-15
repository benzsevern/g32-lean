import HodgeLean.Foundations.Program.MilneTensorContractions

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem m1b_tensorMap_perm (n : ℕ) (f : Fin n → V →ₗ[ℂ] W)
    (σ : Equiv.Perm (Fin n)) (t : ⨂[ℂ]^n V) :
    PiTensorProduct.map f (SchurWeyl.permRep ℂ V (Fin n) σ t) =
      SchurWeyl.permRep ℂ W (Fin n) σ (PiTensorProduct.map (fun i => f (σ i)) t) := by
  have h : (PiTensorProduct.map f).comp (SchurWeyl.permRep ℂ V (Fin n) σ) =
      (SchurWeyl.permRep ℂ W (Fin n) σ).comp (PiTensorProduct.map (fun i => f (σ i))) := by
    ext v
    change PiTensorProduct.map f (SchurWeyl.permRep ℂ V (Fin n) σ (PiTensorProduct.tprod ℂ v)) =
      SchurWeyl.permRep ℂ W (Fin n) σ
        (PiTensorProduct.map (fun i => f (σ i)) (PiTensorProduct.tprod ℂ v))
    simp only [LinearMap.comp_apply, SchurWeyl.permRep_tprod, PiTensorProduct.map_tprod]
    congr 1
    funext i
    simp only [Equiv.apply_symm_apply]
  exact LinearMap.congr_fun h t

theorem m1b_tensorMap_append (k l : ℕ) (f : Fin (k + l) → V →ₗ[ℂ] W)
    (a : ⨂[ℂ]^k V) (b : ⨂[ℂ]^l V) :
    PiTensorProduct.map f (InvariantsExterior.tensorAppend k l (a ⊗ₜ[ℂ] b)) =
      InvariantsExterior.tensorAppend k l
        (PiTensorProduct.map (fun i => f (Fin.castAdd l i)) a ⊗ₜ[ℂ]
          PiTensorProduct.map (fun i => f (Fin.natAdd k i)) b) := by
  have h : (PiTensorProduct.map f).comp (InvariantsExterior.tensorAppend k l).toLinearMap =
      (InvariantsExterior.tensorAppend k l).toLinearMap.comp
        (TensorProduct.map (PiTensorProduct.map (fun i => f (Fin.castAdd l i)))
          (PiTensorProduct.map (fun i => f (Fin.natAdd k i)))) := by
    ext x y
    change PiTensorProduct.map f (InvariantsExterior.tensorAppend k l
      (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y)) =
        InvariantsExterior.tensorAppend k l (TensorProduct.map
          (PiTensorProduct.map (fun i => f (Fin.castAdd l i)))
          (PiTensorProduct.map (fun i => f (Fin.natAdd k i)))
          (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y))
    simp only [TensorProduct.map_tmul, InvariantsExterior.tensorAppend_tprod,
      PiTensorProduct.map_tprod]
    congr 1
    funext i
    exact Fin.addCases (fun j => by simp) (fun j => by simp) i
  exact LinearMap.congr_fun h (a ⊗ₜ[ℂ] b)

end HodgeLean.Foundations.Program
