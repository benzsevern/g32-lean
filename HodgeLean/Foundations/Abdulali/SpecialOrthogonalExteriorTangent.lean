import HodgeLean.Foundations.Abdulali.ExteriorGroupTangent
import HodgeLean.Foundations.Abdulali.ExteriorFixedTensorLift
import HodgeLean.Foundations.Abdulali.SpecialOrthogonalBilinearLie

noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

/-- In any finite basis, the intrinsic skew equation gives the tangent vector
of the determinant-one isometry group. -/
theorem bilinear_skew_mem_specialOrthogonal_tangent
    {V : Type*} [AddCommGroup V] [Module ℂ V] {d : ℕ}
    (b : Module.Basis (Fin d) ℂ V) (B : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (X : Module.End ℂ V)
    (hX : ∀ x y, B (X x) y + B x (X y) = 0) :
    LinearMap.toMatrix b b X ∈
      g1_lieAlgebra (specialOrthogonalMatrixGroup (LinearMap.toMatrix₂ b b B)) := by
  rw [lie_specialOrthogonalMatrixGroup]
  have hf : B.compl₁₂ X LinearMap.id + B.compl₁₂ LinearMap.id X = 0 := by
    ext x y
    exact hX x y
  have hm := congrArg (LinearMap.toMatrix₂ b b) hf
  simp only [map_add, map_zero, LinearMap.toMatrix₂_compl₁₂ b b b b,
    LinearMap.toMatrix_id, Matrix.transpose_one, mul_one, one_mul] at hm
  refine ⟨hm, trace_eq_zero_of_skew _ _ ?_ hm⟩
  exact isUnit_iff_ne_zero.mpr ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB)

/-- An actual matrix point of the special orthogonal group acts as an intrinsic
bilinear isometry with determinant one. -/
theorem specialOrthogonal_matrix_point_isometry
    {V : Type*} [AddCommGroup V] [Module ℂ V] {d : ℕ}
    (b : Module.Basis (Fin d) ℂ V) (B : LinearMap.BilinForm ℂ V)
    (g : Matrix.GeneralLinearGroup (Fin d) ℂ)
    (hg : g ∈ (specialOrthogonalMatrixGroup (LinearMap.toMatrix₂ b b B)).carrier) :
    Matrix.toLin b b (g : Matrix (Fin d) (Fin d) ℂ) ∈ m1b_isometries B ∧
      LinearMap.det (Matrix.toLin b b (g : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
  have h := (mem_specialOrthogonalMatrixGroup _ g).mp hg
  refine ⟨⟨g.isUnit.map (Matrix.toLinAlgEquiv b).toMonoidHom, ?_⟩, ?_⟩
  · have he : B.compl₁₂ (Matrix.toLin b b ↑g) (Matrix.toLin b b ↑g) = B := by
      apply (LinearMap.toMatrix₂ b b).injective
      rw [LinearMap.toMatrix₂_compl₁₂ b b b b, LinearMap.toMatrix_toLin]
      exact h.1
    intro x y
    exact congrArg (fun F : LinearMap.BilinForm ℂ V => F x y) he
  · rw [LinearMap.det_toLin]
    exact h.2

/-- SO-fixed exterior vectors are killed by every intrinsic skew operator. -/
theorem special_orthogonal_exterior_fixed_killed
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (r n : ℕ) (v : ⋀[ℂ]^n (Fin r → V))
    (hv : ∀ u ∈ m1b_isometries B, LinearMap.det u = 1 →
      exteriorPower.map n (m1b_copies r u) v = v)
    (X : Module.End ℂ V) (hX : ∀ x y, B (X x) y + B x (X y) = 0) :
    InvariantsExterior.exteriorDer n (m1b_copies r X) v = 0 := by
  let b := Module.finBasis ℂ V
  have hm := bilinear_skew_mem_specialOrthogonal_tangent b B hB X hX
  have hf : ∀ g ∈ (specialOrthogonalMatrixGroup (LinearMap.toMatrix₂ b b B)).carrier,
      exteriorPower.map n (m2_diagonalEnd r (Matrix.toLin b b ↑g)) v = v := by
    intro g hg
    obtain ⟨hi, hd⟩ := specialOrthogonal_matrix_point_isometry b B g hg
    exact hv _ hi hd
  have hz := exterior_fixed_killed_by_matrix_tangent b _ r n v hf _ hm
  rw [Matrix.toLin_toMatrix] at hz
  exact hz

/-- Alternating images of SO-fixed tensors are killed by intrinsic skew
operators, with no symmetry assumption needed in this direction. -/
theorem special_orthogonal_tensor_image_killed
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (r n : ℕ) (v : ⋀[ℂ]^n (Fin r → V))
    (hv : v ∈ (m1b_fixed (m1b_copies r ''
      {u ∈ m1b_isometries B | LinearMap.det u = 1}) n).map
        (InvariantsExterior.wedgeQuotient n)) :
    ∀ X : Module.End ℂ V, (∀ x y, B (X x) y + B x (X y) = 0) →
      InvariantsExterior.exteriorDer n (m1b_copies r X) v = 0 := by
  have hf := (exterior_fixed_iff_mem_fixed_tensor_image _ n v).mpr hv
  apply special_orthogonal_exterior_fixed_killed B hB r n v
  intro u hu hd
  exact hf _ ⟨u, ⟨hu, hd⟩, rfl⟩

end HodgeLean.Foundations.Abdulali
