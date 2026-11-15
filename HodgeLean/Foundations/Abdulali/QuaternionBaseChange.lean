import HodgeLean.Foundations.Abdulali.QuaternionInvolution
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section
open scoped Quaternion TensorProduct
namespace HodgeLean.Foundations.Abdulali

/-- Coefficientwise rational inclusion of the quaternion presentation.
Source: scalar extension of the presentation in Abdulali, Annals of Mathematics
155 (2002), §3.1–3.2. -/
def quaternionRationalInclusion (b : ℚ) :
    ℍ[ℚ, -3, 0, b] →ₐ[ℚ] ℍ[ℂ, -3, 0, (b : ℂ)] where
  toFun q := ⟨q.re, q.imI, q.imJ, q.imK⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' q r := by ext <;> simp
  map_mul' q r := by ext <;> simp <;> push_cast <;> ring
  commutes' q := by
    rw [IsScalarTower.algebraMap_apply ℚ ℂ ℍ[ℂ, -3, 0, (b : ℂ)]]
    ext <;> simp [QuaternionAlgebra.algebraMap_eq]

example (b : ℚ) (q : ℍ[ℚ, -3, 0, b]) :
    (quaternionRationalInclusion b q).imI = (q.imI : ℂ) := rfl

private lemma quaternionBasis_apply {R : Type*} [CommRing R]
    (c₁ c₂ c₃ : R) (i : Fin 4) :
    QuaternionAlgebra.basisOneIJK c₁ c₂ c₃ i =
      (QuaternionAlgebra.linearEquivTuple c₁ c₂ c₃).symm (Pi.single i 1) :=
  congrFun (Module.Basis.coe_ofEquivFun _) i

/-- The coefficient inclusion retains all four quaternion basis vectors.
Source: the scalar-extension presentation in Abdulali, Annals of Mathematics
155 (2002), §3.1–3.2. -/
theorem quaternionRationalInclusion_basis (b : ℚ) (i : Fin 4) :
    quaternionRationalInclusion b (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b i) =
      QuaternionAlgebra.basisOneIJK (-3 : ℂ) 0 (b : ℂ) i := by
  simp only [quaternionBasis_apply]
  fin_cases i <;> ext <;>
    simp [quaternionRationalInclusion, QuaternionAlgebra.coe_linearEquivTuple_symm,
      QuaternionAlgebra.equivTuple]

/-- Complexification of the rational quaternion presentation, with the
canonical map specified on every pure tensor. No splitting or involution
is chosen by this scalar-extension equivalence.
Source: scalar extension of the quaternion presentation in Abdulali,
Annals of Mathematics 155 (2002), §3.1–3.2. -/
theorem quaternion_base_change (b : ℚ) :
    ∃ e : (ℂ ⊗[ℚ] ℍ[ℚ, -3, 0, b]) ≃ₐ[ℂ] ℍ[ℂ, -3, 0, (b : ℂ)],
      ∀ c q, e (c ⊗ₜ[ℚ] q) = c • (⟨(q.re : ℂ), (q.imI : ℂ), (q.imJ : ℂ), (q.imK : ℂ)⟩ : ℍ[ℂ, -3, 0, (b : ℂ)]) := by
  let f := (AlgHom.liftEquiv ℚ ℂ _ _) (quaternionRationalInclusion b)
  let B := (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b).baseChange ℂ
  let C := QuaternionAlgebra.basisOneIJK (-3 : ℂ) 0 (b : ℂ)
  let E := B.equivFun ≪≫ₗ C.equivFun.symm
  have h (i : Fin 4) : f (B i) = C i := by
    simp only [f, B, C, Module.Basis.baseChange_apply, AlgHom.liftEquiv_tmul,
      quaternionBasis_apply, one_smul]
    fin_cases i <;> ext <;>
      simp [quaternionRationalInclusion, QuaternionAlgebra.coe_linearEquivTuple_symm,
        QuaternionAlgebra.equivTuple, Pi.single_apply]
  have hf : f.toLinearMap = E.toLinearMap := by
    apply B.ext
    intro i
    change f (B i) = C.equivFun.symm (B.equivFun (B i))
    rw [show B.equivFun (B i) = Pi.single i 1 by ext j; simp [Pi.single_apply, eq_comm]]
    rw [h i]
    apply C.equivFun.injective
    ext j
    simp only [Module.Basis.equivFun_self, LinearEquiv.apply_symm_apply]
    simp [Pi.single_apply, eq_comm]
  refine ⟨AlgEquiv.ofBijective f ?_, ?_⟩
  · change Function.Bijective f.toLinearMap
    rw [hf]
    exact E.bijective
  · intro c q
    exact AlgHom.liftEquiv_tmul _ c q

end HodgeLean.Foundations.Abdulali
