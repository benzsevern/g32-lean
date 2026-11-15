import HodgeLean.Foundations.Program.MilneTensorHelpers
import HodgeLean.Foundations.Abdulali.SignCharacterDecomposition

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The full bilinear orthogonal group as a subgroup of invertible endomorphisms.
Source: Weyl, The Classical Groups, Chapter II, §9, the group preserving a symmetric
bilinear form; this definition also makes sense for an arbitrary bilinear form. -/
def orthogonalUnits (B : LinearMap.BilinForm ℂ V) :
    Subgroup (Module.End ℂ V)ˣ where
  carrier := {u | ∀ x y, B (u.val x) (u.val y) = B x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro u v hu hv x y
    change B (u.val (v.val x)) (u.val (v.val y)) = B x y
    rw [hu, hv]
  inv_mem' := by
    intro u hu x y
    have hh := hu ((↑u⁻¹ : Module.End ℂ V) x) ((↑u⁻¹ : Module.End ℂ V) y)
    simpa only [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Module.End.one_apply] using hh.symm

/-- The tensor representation on an arbitrary number of standard copies.
Source: Weyl, The Classical Groups, Chapter II, §17, polarized tensor representations. -/
def orthogonalTensorRepresentation (B : LinearMap.BilinForm ℂ V) (r n : ℕ) :
    orthogonalUnits B →* Module.End ℂ (⨂[ℂ]^n (Fin r → V)) where
  toFun u := SchurWeyl.tensorPow (Fin n) (m1b_copies r u.val.val)
  map_one' := by
    have hc : m1b_copies (V := V) r 1 = 1 := by ext x i; rfl
    exact hc ▸ SchurWeyl.tensorPow_one
  map_mul' u v := by
    have hc : m1b_copies r (u.val.val * v.val.val) =
        m1b_copies r u.val.val * m1b_copies r v.val.val := by ext x i; rfl
    change SchurWeyl.tensorPow (Fin n) (m1b_copies r (u.val.val * v.val.val)) = _
    rw [hc, SchurWeyl.tensorPow_mul]

variable [FiniteDimensional ℂ V]

/-- The determinant character of the bilinear orthogonal group.
Source: Weyl, The Classical Groups, Chapter II, §9, determinant character. -/
def orthogonalDeterminant (B : LinearMap.BilinForm ℂ V) : orthogonalUnits B →* ℂ where
  toFun u := LinearMap.det u.val.val
  map_one' := map_one LinearMap.det
  map_mul' u v := map_mul LinearMap.det u.val.val v.val.val

/-- Every isometry of a nondegenerate bilinear form has determinant one or minus one.
Source: Weyl, The Classical Groups, Chapter II, §9; take determinants in the Gram
matrix equation. Symmetry is unnecessary for this particular identity. -/
theorem orthogonalDeterminant_sign (B : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (u : orthogonalUnits B) :
    orthogonalDeterminant B u = 1 ∨ orthogonalDeterminant B u = -1 := by
  classical
  let b := Module.finBasis ℂ V
  let M := LinearMap.toMatrix b b u.val.val
  let Q := LinearMap.BilinForm.toMatrix b B
  have hQ : Q.det ≠ 0 := by
    exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB
  have heq : B.comp u.val.val u.val.val = B := by
    ext x y
    exact u.property x y
  have hm : M.transpose * Q * M = Q := by
    have hh := congrArg (LinearMap.BilinForm.toMatrix b) heq
    rw [LinearMap.BilinForm.toMatrix_comp b b] at hh
    exact hh
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hsq : M.det * M.det = 1 := by
    apply mul_right_cancel₀ hQ
    calc M.det * M.det * Q.det = M.det * Q.det * M.det := by ring
         _ = 1 * Q.det := by rw [hd, one_mul]
  have hfactor : (M.det - 1) * (M.det + 1) = 0 := by
    calc (M.det - 1) * (M.det + 1) = M.det * M.det - 1 := by ring
         _ = 0 := by rw [hsq, sub_self]
  have hdet : orthogonalDeterminant B u = M.det := by
    exact (LinearMap.det_toMatrix b u.val.val).symm
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (hdet.trans (sub_eq_zero.mp h))
  · exact Or.inr (hdet.trans (eq_neg_iff_add_eq_zero.mpr h))

/-- On every tensor power of every repeated standard representation, special-orthogonal
fixed vectors split into the trivial and determinant character sectors for the full group.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17, the index-two decomposition.
The case of a trivial determinant character is included. -/
theorem orthogonal_tensor_character_decomposition
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate) (r n : ℕ) :
    (⨅ g : orthogonalUnits B, ⨅ (_ : orthogonalDeterminant B g = 1),
      LinearMap.ker (orthogonalTensorRepresentation B r n g - LinearMap.id)) =
    (⨅ g : orthogonalUnits B,
      LinearMap.ker (orthogonalTensorRepresentation B r n g - LinearMap.id)) ⊔
    (⨅ g : orthogonalUnits B,
      LinearMap.ker (orthogonalTensorRepresentation B r n g -
        orthogonalDeterminant B g • LinearMap.id)) := by
  classical
  by_cases hex : ∃ s : orthogonalUnits B, orthogonalDeterminant B s = -1
  · obtain ⟨s, hs⟩ := hex
    exact sign_character_fixed_decomposition (orthogonalTensorRepresentation B r n)
      (orthogonalDeterminant B) (orthogonalDeterminant_sign B hB) s hs
  · have hdet (g : orthogonalUnits B) : orthogonalDeterminant B g = 1 := by
      rcases orthogonalDeterminant_sign B hB g with h | h
      · exact h
      · exact False.elim (hex ⟨g, h⟩)
    simp only [hdet, one_smul, iInf_true, sup_idem]

/-- The units-based full orthogonal action has exactly the fixed tensors of the
existing bilinear-isometry formulation.
Source: Weyl, The Classical Groups, Chapter II, §9, the full orthogonal group. -/
theorem orthogonal_tensor_fixed_eq (B : LinearMap.BilinForm ℂ V) (r n : ℕ) :
    (⨅ g : orthogonalUnits B,
      LinearMap.ker (orthogonalTensorRepresentation B r n g - LinearMap.id)) =
      m1b_fixed (m1b_copies r '' m1b_isometries B) n := by
  apply le_antisymm
  · intro t ht
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at ht
    simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    rintro _ ⟨u, ⟨⟨w, rfl⟩, hu⟩, rfl⟩
    exact ht ⟨w, hu⟩
  · intro t ht
    simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at ht
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    exact ht _ ⟨g.val.val, ⟨g.val.isUnit, g.property⟩, rfl⟩

/-- The kernel of the determinant character acts as the bilinear special orthogonal group.
Source: Weyl, The Classical Groups, Chapter II, §9, the determinant-one subgroup. -/
theorem special_orthogonal_tensor_fixed_eq (B : LinearMap.BilinForm ℂ V) (r n : ℕ) :
    (⨅ g : orthogonalUnits B, ⨅ (_ : orthogonalDeterminant B g = 1),
      LinearMap.ker (orthogonalTensorRepresentation B r n g - LinearMap.id)) =
      m1b_fixed (m1b_copies r '' {u ∈ m1b_isometries B | LinearMap.det u = 1}) n := by
  apply le_antisymm
  · intro t ht
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at ht
    simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    rintro _ ⟨u, ⟨⟨⟨w, rfl⟩, hu⟩, hd⟩, rfl⟩
    exact ht ⟨w, hu⟩ hd
  · intro t ht
    simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at ht
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g hg
    exact ht _ ⟨g.val.val, ⟨⟨g.val.isUnit, g.property⟩, hg⟩, rfl⟩

end HodgeLean.Foundations.Abdulali
