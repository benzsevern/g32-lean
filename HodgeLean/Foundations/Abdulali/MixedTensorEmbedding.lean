import HodgeLean.Foundations.Abdulali.VolumeContraction

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Put the original copies after the distinguished extra copy. -/
def mixedCopiesIn (r : ℕ) : (Fin r → V) →ₗ[ℂ] (Fin (r + 1) → V) where
  toFun x := Fin.cons 0 x
  map_add' x y := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp only [Fin.cons_zero, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, zero_add, smul_zero, RingHom.id_apply]
  map_smul' c x := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp only [Fin.cons_zero, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, zero_add, smul_zero, RingHom.id_apply]

/-- Forget the distinguished extra copy. -/
def mixedCopiesOut (r : ℕ) : (Fin (r + 1) → V) →ₗ[ℂ] (Fin r → V) :=
  LinearMap.pi (fun i => LinearMap.proj i.succ)

/-- Include the factor to be contracted in the distinguished copy. -/
def mixedExtraIn (r : ℕ) : V →ₗ[ℂ] (Fin (r + 1) → V) :=
  LinearMap.single ℂ (fun _ => V) 0

/-- Evaluate at the distinguished copy. -/
def mixedExtraOut (r : ℕ) : (Fin (r + 1) → V) →ₗ[ℂ] V :=
  LinearMap.proj 0

/-- Embed a mixed tensor in one tensor power on the enlarged copy space. -/
def mixedTensorIn (r n d : ℕ) :
    (⨂[ℂ]^n (Fin r → V)) ⊗[ℂ] (⨂[ℂ]^d V) →ₗ[ℂ]
      (⨂[ℂ]^(n + d) (Fin (r + 1) → V)) :=
  (InvariantsExterior.tensorAppend n d).toLinearMap.comp
    (TensorProduct.map (PiTensorProduct.map (fun _ : Fin n => mixedCopiesIn r))
      (PiTensorProduct.map (fun _ : Fin d => mixedExtraIn r)))

end HodgeLean.Foundations.Abdulali
