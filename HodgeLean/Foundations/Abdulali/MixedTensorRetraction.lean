import HodgeLean.Foundations.Abdulali.MixedTensorEmbedding

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Recover the two designated blocks from the enlarged tensor power. -/
def mixedTensorOut (r n d : ℕ) :
    (⨂[ℂ]^(n + d) (Fin (r + 1) → V)) →ₗ[ℂ]
      (⨂[ℂ]^n (Fin r → V)) ⊗[ℂ] (⨂[ℂ]^d V) :=
  (TensorProduct.map (PiTensorProduct.map (fun _ : Fin n => mixedCopiesOut r))
    (PiTensorProduct.map (fun _ : Fin d => mixedExtraOut r))).comp
      (InvariantsExterior.tensorAppend n d).symm.toLinearMap

/-- The block maps retain the original copy index. -/
theorem mixedCopiesOut_in (r : ℕ) (x : Fin r → V) :
    mixedCopiesOut r (mixedCopiesIn r x) = x := by
  ext i
  rfl

/-- The distinguished copy retains its coefficient. -/
theorem mixedExtraOut_in (r : ℕ) (x : V) :
    mixedExtraOut r (mixedExtraIn r x) = x := by
  classical
  simp only [mixedExtraOut, mixedExtraIn, LinearMap.proj_apply,
    LinearMap.single_apply, Pi.single_eq_same]

/-- Recovering an embedded mixed tensor gives the original tensor. -/
theorem mixedTensorOut_in (r n d : ℕ)
    (z : (⨂[ℂ]^n (Fin r → V)) ⊗[ℂ] (⨂[ℂ]^d V)) :
    mixedTensorOut r n d (mixedTensorIn r n d z) = z := by
  have h₁ : (mixedCopiesOut (V := V) r).comp (mixedCopiesIn r) = LinearMap.id :=
    LinearMap.ext (mixedCopiesOut_in r)
  have h₂ : (mixedExtraOut (V := V) r).comp (mixedExtraIn r) = LinearMap.id :=
    LinearMap.ext (mixedExtraOut_in r)
  have ht₁ : (PiTensorProduct.map (fun _ : Fin n => mixedCopiesOut (V := V) r)).comp
      (PiTensorProduct.map (fun _ : Fin n => mixedCopiesIn r)) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [h₁, PiTensorProduct.map_id]
  have ht₂ : (PiTensorProduct.map (fun _ : Fin d => mixedExtraOut (V := V) r)).comp
      (PiTensorProduct.map (fun _ : Fin d => mixedExtraIn r)) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [h₂, PiTensorProduct.map_id]
  have hc : (mixedTensorOut (V := V) r n d).comp (mixedTensorIn r n d) =
      LinearMap.id := by
    apply TensorProduct.ext'
    intro a b
    change TensorProduct.map _ _ ((InvariantsExterior.tensorAppend n d).symm
      ((InvariantsExterior.tensorAppend n d) (TensorProduct.map _ _ (a ⊗ₜ[ℂ] b)))) = _
    rw [LinearEquiv.symm_apply_apply]
    simp only [TensorProduct.map_tmul, ← LinearMap.comp_apply, ht₁, ht₂,
      LinearMap.id_apply]
  exact LinearMap.congr_fun hc z

/-- No mixed tensor is lost by adjoining the extra copy. -/
theorem mixedTensorIn_injective (r n d : ℕ) :
    Function.Injective (mixedTensorIn (V := V) r n d) :=
  Function.LeftInverse.injective (mixedTensorOut_in r n d)

end HodgeLean.Foundations.Abdulali
