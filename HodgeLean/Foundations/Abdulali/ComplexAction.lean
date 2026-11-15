import HodgeLean.Foundations.Abdulali.QuaternionBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

noncomputable section
open scoped TensorProduct Quaternion
namespace HodgeLean.Foundations.Abdulali

/-- Scalar extension of a rational quaternion action, using the coefficientwise
quaternion scalar-extension equivalence.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.1–3.2. -/
def quaternionComplexAction {V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : ℚ) (ρ : ℍ[ℚ, -3, 0, b] →ₐ[ℚ] Module.End ℚ V) :
    ℍ[ℂ, -3, 0, (b : ℂ)] →ₐ[ℂ] Module.End ℂ (ℂ ⊗[ℚ] V) :=
  ((AlgHom.liftEquiv ℚ ℂ _ _) ((Module.End.baseChangeHom ℚ ℂ V).comp ρ)).comp
    (Classical.choose (quaternion_base_change b)).symm.toAlgHom

example {V : Type*} [AddCommGroup V] [Module ℚ V] (b : ℚ)
    (ρ : ℍ[ℚ, -3, 0, b] →ₐ[ℚ] Module.End ℚ V) :
    quaternionComplexAction b ρ 1 = 1 := map_one _

/-- The extended action agrees with the original action on every rational
quaternion, after scalar extension on the representation space.
Source: scalar extension of representations, Abdulali, Annals of Mathematics
155 (2002), §3.1–3.2. -/
theorem quaternionComplexAction_rational {V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : ℚ) (ρ : ℍ[ℚ, -3, 0, b] →ₐ[ℚ] Module.End ℚ V) (q : ℍ[ℚ, -3, 0, b]) :
    quaternionComplexAction b ρ (quaternionRationalInclusion b q) = (ρ q).baseChange ℂ := by
  let e := Classical.choose (quaternion_base_change b)
  have he := Classical.choose_spec (quaternion_base_change b)
  have hi : e.symm (quaternionRationalInclusion b q) = 1 ⊗ₜ[ℚ] q := by
    apply e.injective
    rw [e.apply_symm_apply]
    have hh : e (1 ⊗ₜ[ℚ] q) = quaternionRationalInclusion b q := by
      simpa [e, quaternionRationalInclusion] using he 1 q
    exact hh.symm
  change (AlgHom.liftEquiv ℚ ℂ _ _ ((Module.End.baseChangeHom ℚ ℂ V).comp ρ))
    (e.symm (quaternionRationalInclusion b q)) = _
  rw [hi, AlgHom.liftEquiv_tmul, one_smul]
  rfl

/-- The Rosati equation survives extension of both the quaternion action and
the alternating form. Quaternion conjugation is linear in the complex
coefficients here; it is not the complex conjugation of a Hermitian form.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.1–3.2. -/
theorem quaternionComplexAction_rosati {V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : ℚ) (ρ : ℍ[ℚ, -3, 0, b] →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V)
    (hadj : ∀ q x y, E (ρ q x) y = E x (ρ (star q) y))
    (q : ℍ[ℂ, -3, 0, (b : ℂ)]) (z w : ℂ ⊗[ℚ] V) :
    E.baseChange ℂ (quaternionComplexAction b ρ q z) w =
      E.baseChange ℂ z (quaternionComplexAction b ρ (star q) w) := by
  have hR (q : ℍ[ℚ, -3, 0, b]) (z w : ℂ ⊗[ℚ] V) :
      E.baseChange ℂ ((ρ q).baseChange ℂ z) w =
        E.baseChange ℂ z ((ρ (star q)).baseChange ℂ w) := by
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']
    | tmul c x =>
      induction w using TensorProduct.inductionOn with
      | add w w' hw hw' => simp only [map_add, hw, hw']
      | tmul d y => simp [LinearMap.BilinForm.baseChange_tmul, hadj]
  have hstar (r : ℍ[ℚ, -3, 0, b]) :
      star (quaternionRationalInclusion b r) = quaternionRationalInclusion b (star r) := by
    ext <;> simp [quaternionRationalInclusion]
  have hq : q = q.re • quaternionRationalInclusion b ⟨1, 0, 0, 0⟩ +
      q.imI • quaternionRationalInclusion b ⟨0, 1, 0, 0⟩ +
      q.imJ • quaternionRationalInclusion b ⟨0, 0, 1, 0⟩ +
      q.imK • quaternionRationalInclusion b ⟨0, 0, 0, 1⟩ := by
    ext <;> simp [quaternionRationalInclusion]
  conv_lhs => rw [hq]
  conv_rhs => rw [hq]
  simp only [map_add, map_smul, star_add, QuaternionAlgebra.star_smul',
    hstar, quaternionComplexAction_rational, LinearMap.add_apply, LinearMap.smul_apply, hR]

end HodgeLean.Foundations.Abdulali
