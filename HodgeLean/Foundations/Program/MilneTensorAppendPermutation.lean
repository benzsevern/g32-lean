import HodgeLean.Foundations.Program.MilneTensorAppendProducts

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def m1b_rightPermutation (k l : ℕ) (σ : Equiv.Perm (Fin l)) :
    Equiv.Perm (Fin (k + l)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl (Fin k)) σ).trans finSumFinEquiv)

theorem m1b_tensorAppend_perm_right (k l : ℕ) (σ : Equiv.Perm (Fin l))
    (a : ⨂[ℂ]^k V) (b : ⨂[ℂ]^l V) :
    InvariantsExterior.tensorAppend k l (a ⊗ₜ[ℂ] SchurWeyl.permRep ℂ V (Fin l) σ b) =
      SchurWeyl.permRep ℂ V (Fin (k + l)) (m1b_rightPermutation k l σ)
        (InvariantsExterior.tensorAppend k l (a ⊗ₜ[ℂ] b)) := by
  have h : (InvariantsExterior.tensorAppend k l).toLinearMap.comp
      (TensorProduct.map LinearMap.id (SchurWeyl.permRep ℂ V (Fin l) σ)) =
      (SchurWeyl.permRep ℂ V (Fin (k + l)) (m1b_rightPermutation k l σ)).comp
        (InvariantsExterior.tensorAppend k l).toLinearMap := by
    apply TensorProduct.ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro w
    change InvariantsExterior.tensorAppend k l
        ((⨂ₜ[ℂ] i, v i) ⊗ₜ[ℂ] SchurWeyl.permRep ℂ V (Fin l) σ (⨂ₜ[ℂ] i, w i)) =
      SchurWeyl.permRep ℂ V (Fin (k + l)) (m1b_rightPermutation k l σ)
        (InvariantsExterior.tensorAppend k l ((⨂ₜ[ℂ] i, v i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, w i)))
    simp only [SchurWeyl.permRep_tprod, InvariantsExterior.tensorAppend_tprod]
    congr 1
    funext j
    obtain ⟨z, rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k + l)).surjective j
    cases z <;> simp [m1b_rightPermutation, Fin.append]
  exact LinearMap.congr_fun h (a ⊗ₜ[ℂ] b)

end HodgeLean.Foundations.Program
