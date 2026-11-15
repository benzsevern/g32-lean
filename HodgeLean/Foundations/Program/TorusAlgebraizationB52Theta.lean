import HodgeLean.Foundations.Program.TorusAlgebraizationDefs

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- The pointwise product of three theta sections is a section of the cubed factor. -/
def b5_cubeSection (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)
    (s t u : b5_sections Λ F hF Q 1) : b5_sections Λ F hF Q 3 := by
  refine ⟨fun z ↦ s.val z * t.val z * u.val z, ?_, ?_⟩
  · exact (s.property.1.mul t.property.1).mul u.property.1
  · intro l z
    change s.val (z + b5_lattice Λ F l) * t.val (z + b5_lattice Λ F l) *
      u.val (z + b5_lattice Λ F l) =
        b5_factor Λ F hF Q l z ^ 3 * (s.val z * t.val z * u.val z)
    rw [s.property.2 l z, t.property.2 l z, u.property.2 l z]
    ring

@[simp]
theorem b5_cubeSection_apply (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (s t u : b5_sections Λ F hF Q 1)
    (z : b5_V Λ F) :
    (b5_cubeSection Λ F hF Q s t u).val z = s.val z * t.val z * u.val z := rfl

theorem b5_H_add_right (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (x y z : b5_V Λ F) :
    b5_H Λ F hF Q x (y + z) = b5_H Λ F hF Q x y + b5_H Λ F hF Q x z := by
  simp only [b5_H, map_add, LinearMap.add_apply]
  ring

theorem b5_factor_add_right (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (l : Λ) (z a : b5_V Λ F) :
    b5_factor Λ F hF Q l (z + a) = b5_factor Λ F hF Q l z *
      Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) a) := by
  unfold b5_factor
  rw [b5_H_add_right]
  have he :
      Real.pi * (b5_H Λ F hF Q (b5_lattice Λ F l) z +
          b5_H Λ F hF Q (b5_lattice Λ F l) a) +
          (Real.pi / 2) * b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F l) =
        (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) z +
          (Real.pi / 2) * b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F l)) +
            Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) a := by ring
  rw [he, Complex.exp_add, mul_assoc]

/-- Three translates whose translation vectors sum to zero satisfy the cubed automorphy law. -/
def b5_balancedCubeSection (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (s t u : b5_sections Λ F hF Q 1)
    (a b c : b5_V Λ F) (habc : a + b + c = 0) : b5_sections Λ F hF Q 3 := by
  refine ⟨fun z ↦ s.val (z + a) * t.val (z + b) * u.val (z + c), ?_, ?_⟩
  · exact ((s.property.1.comp (differentiable_id.add (differentiable_const a))).mul
      (t.property.1.comp (differentiable_id.add (differentiable_const b)))).mul
        (u.property.1.comp (differentiable_id.add (differentiable_const c)))
  · intro l z
    change s.val (z + b5_lattice Λ F l + a) * t.val (z + b5_lattice Λ F l + b) *
      u.val (z + b5_lattice Λ F l + c) = b5_factor Λ F hF Q l z ^ 3 *
        (s.val (z + a) * t.val (z + b) * u.val (z + c))
    rw [add_right_comm z (b5_lattice Λ F l) a,
      add_right_comm z (b5_lattice Λ F l) b,
      add_right_comm z (b5_lattice Λ F l) c,
      s.property.2 l (z + a), t.property.2 l (z + b), u.property.2 l (z + c),
      b5_factor_add_right, b5_factor_add_right, b5_factor_add_right]
    simp only [pow_one]
    have hexp :
        Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) a) *
          Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) b) *
            Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) c) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← mul_add, ← mul_add,
        ← b5_H_add_right, ← b5_H_add_right, habc]
      simp [b5_H]
    calc
      _ = b5_factor Λ F hF Q l z ^ 3 *
          (Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) a) *
            Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) b) *
              Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) c)) *
            (s.val (z + a) * t.val (z + b) * u.val (z + c)) := by ring
      _ = _ := by rw [hexp]; ring

@[simp]
theorem b5_balancedCubeSection_apply (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (s t u : b5_sections Λ F hF Q 1)
    (a b c : b5_V Λ F) (habc : a + b + c = 0) (z : b5_V Λ F) :
    (b5_balancedCubeSection Λ F hF Q s t u a b c habc).val z =
      s.val (z + a) * t.val (z + b) * u.val (z + c) := rfl

end HodgeLean.Foundations.Program
