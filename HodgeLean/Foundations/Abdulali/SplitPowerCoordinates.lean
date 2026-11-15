import HodgeLean.Foundations.WeilPowerClasses
import HodgeLean.Foundations.Program.MilneTensorDefs

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

variable {U : Type*} [AddCommGroup U] [Module ℂ U]

/-- Coordinates of the two-dimensional trivial multiplicity factor.
Source: the matrix-unit decomposition of the split quaternion module. -/
def splitRowCoordinates : ((Fin 2 → ℂ) ⊗[ℂ] U) ≃ₗ[ℂ] (Fin 2 → U) :=
  TensorProduct.comm ℂ _ _ ≪≫ₗ TensorProduct.piScalarRight ℂ ℂ U (Fin 2)

/-- Flatten the pair consisting of the power index and the quaternion row.
Source: the biproduct indexing convention in Abdulali, Annals 155 (2002), Remark 4.2. -/
def flattenSplitCopies (r : ℕ) : (Fin r → Fin 2 → U) ≃ₗ[ℂ] (Fin (r*2) → U) where
  toFun x j := x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  invFun x i k := x (finProdFinEquiv (i,k))
  left_inv x := by ext i k; simp only [Equiv.symm_apply_apply]
  right_inv x := by
    ext j
    exact congrArg x (finProdFinEquiv.apply_symm_apply j)
  map_add' x y := rfl
  map_smul' c x := rfl

/-- The split rational power has `2*r` copies of the orthogonal standard module.
Source: Abdulali, Annals 155 (2002), §4 and Remark 4.2. -/
def splitPowerCoordinates {V : Type*} [AddCommGroup V] [Module ℚ V] (r : ℕ)
    (e : ((Fin 2 → ℂ) ⊗[ℂ] U) ≃ₗ[ℂ] (ℂ ⊗[ℚ] V)) :
    (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) ≃ₗ[ℂ] (Fin (r*2) → U) :=
  powerBaseChange r ≪≫ₗ TensorProduct.congr e.symm (LinearEquiv.refl ℂ _) ≪≫ₗ
    TensorProduct.piScalarRight ℂ ℂ _ (Fin r) ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ => splitRowCoordinates) ≪≫ₗ flattenSplitCopies r

/-- The orthogonal operator acts on each of the retained power and row labels.
Source: functoriality of the split quaternion module, Abdulali, §4. -/
theorem splitPowerCoordinates_intertwines {V : Type*} [AddCommGroup V] [Module ℚ V]
    (r : ℕ) (e : ((Fin 2 → ℂ) ⊗[ℂ] U) ≃ₗ[ℂ] (ℂ ⊗[ℚ] V))
    (X : Module.End ℂ (ℂ ⊗[ℚ] V)) (T : Module.End ℂ U)
    (h : e.symm.conj X = T.lTensor (Fin 2 → ℂ))
    (z : ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) :
    splitPowerCoordinates r e (powerAction r X z) =
      m1b_copies (r*2) T (splitPowerCoordinates r e z) := by
  obtain ⟨z, rfl⟩ := (powerBaseChange (V := V) r).symm.surjective z
  induction z using TensorProduct.inductionOn with
  | tmul v c =>
    obtain ⟨v, rfl⟩ := e.surjective v
    have hx : X (e v) = e (T.lTensor (Fin 2 → ℂ) v) := by
      have hh := LinearMap.congr_fun h v
      change e.symm (X (e v)) = _ at hh
      exact e.symm.injective (by rw [hh, e.symm_apply_apply])
    rw [show powerAction r X ((powerBaseChange r).symm (e v ⊗ₜ[ℂ] c)) =
      (powerBaseChange r).symm (X (e v) ⊗ₜ[ℂ] c) by simp only [powerAction,
        LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, LinearMap.rTensor_tmul]]
    rw [hx]
    clear hx
    induction v using TensorProduct.inductionOn with
    | tmul x u =>
      ext j
      simp [splitPowerCoordinates, splitRowCoordinates, flattenSplitCopies,
        TensorProduct.piScalarRight, TensorProduct.piScalarRightHom,
        TensorProduct.piScalarRightHomBil, LinearMap.lTensor_tmul, m1b_copies]
    | add v w hv hw =>
      simpa only [map_add, TensorProduct.add_tmul, Pi.add_apply] using congrArg₂ (· + ·) hv hw
  | add z w hz hw =>
    simpa only [map_add] using congrArg₂ (· + ·) hz hw

end HodgeLean.Foundations.Abdulali
