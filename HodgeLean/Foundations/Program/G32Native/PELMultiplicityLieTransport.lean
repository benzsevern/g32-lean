import Mathlib.RingTheory.TensorProduct.Maps
import HodgeLean.Foundations.Program.G32Native.PELMultiplicityCenter
import HodgeLean.Foundations.Program.G32Native.PELOrthogonalSimple
import HodgeLean.Foundations.Program.G32Native.PELLieSimpleTransport

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.GeneralTypeIII
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The bilinear skew equation in a chosen matrix marking. -/
theorem pel_skew_matrix_iff {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℂ V) (B : LinearMap.BilinForm ℂ V)
    (X : Module.End ℂ V) :
    (LinearMap.toMatrix b b X).transpose * LinearMap.toMatrix₂ b b B +
      LinearMap.toMatrix₂ b b B * LinearMap.toMatrix b b X = 0 ↔
      ∀ x y, B (X x) y + B x (X y) = 0 := by
  have hm : LinearMap.toMatrix₂ b b
      (B.compl₁₂ X LinearMap.id + B.compl₁₂ LinearMap.id X) =
      (LinearMap.toMatrix b b X).transpose * LinearMap.toMatrix₂ b b B +
      LinearMap.toMatrix₂ b b B * LinearMap.toMatrix b b X := by
    simp only [map_add, LinearMap.toMatrix₂_compl₁₂ b b b b,
      LinearMap.toMatrix_id, Matrix.transpose_one, mul_one, one_mul]
  rw [← hm, map_eq_zero_iff _ (LinearMap.toMatrix₂ b b).injective]
  constructor
  · intro h x y; exact LinearMap.congr_fun₂ h x y
  · intro h; ext x y; exact h x y

/-- A retained orthogonal multiplicity normal form gives a Lie equivalence,
including the commutator, with the six-dimensional orthogonal algebra. -/
theorem pel_multiplicity_lie_equiv
    {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (c : Module.Basis (Fin n) ℂ V)
    (L : LieSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] V)
    (B : LinearMap.BilinForm ℂ (Fin 6 → ℂ)) (hs : B.IsSymm) (hnd : B.Nondegenerate)
    (normal : ∀ X : Module.End ℂ V, LinearMap.toMatrix c c X ∈ L ↔
      ∃! T : Module.End ℂ (Fin 6 → ℂ),
        (∀ u v, B (T u) v + B u (T v) = 0) ∧
        e.symm.conj X = T.lTensor (Fin 2 → ℂ)) :
    Nonempty (LieAlgebra.Orthogonal.so (Fin 6) ℂ ≃ₗ⁅ℂ⁆ L) := by
  obtain ⟨b, hb⟩ := HodgeLean.Foundations.Abdulali.symmetric_bilinear_orthonormal_basis B hnd hs
  have hdim : Module.finrank ℂ (Fin 6 → ℂ) = 6 := by simp
  let b6 := b.reindex (finCongr hdim)
  have hb6 : LinearMap.toMatrix₂ b6 b6 B = 1 := by
    ext i j
    have hh := congrArg (fun M => M ((finCongr hdim).symm i) ((finCongr hdim).symm j)) hb
    simpa [b6, LinearMap.toMatrix₂_apply, Matrix.one_apply] using hh
  let t : Matrix (Fin 6) (Fin 6) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin 6 → ℂ) :=
    (LinearMap.toMatrixAlgEquiv b6).symm
  let f : Matrix (Fin 6) (Fin 6) ℂ →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    (LinearMap.toMatrixAlgEquiv c).toAlgHom.comp
      ((e.conjAlgEquiv ℂ).toAlgHom.comp
        ((Module.End.lTensorAlgHom ℂ (Fin 6 → ℂ) (Fin 2 → ℂ)).comp t.toAlgHom))
  have hf_apply (M : Matrix (Fin 6) (Fin 6) ℂ) :
      f M = LinearMap.toMatrix c c (e.conj ((t M).lTensor (Fin 2 → ℂ))) := rfl
  have hf (M : LieAlgebra.Orthogonal.so (Fin 6) ℂ) : f M ∈ L := by
    apply (normal _).mpr
    refine ⟨t M, ⟨?_, ?_⟩, ?_⟩
    · apply (pel_skew_matrix_iff b6 B (t M)).mp
      rw [hb6]
      have ht : LinearMap.toMatrix b6 b6 (t M) = M := (LinearMap.toMatrix b6 b6).apply_symm_apply M
      rw [ht, Matrix.mul_one, Matrix.one_mul]
      exact add_eq_zero_iff_eq_neg.mpr ((LieAlgebra.Orthogonal.mem_so (Fin 6) ℂ _).mp M.property)
    · exact LinearEquiv.conj_symm_conj e _
    · intro S hS
      apply pel_lTensor_two_injective
      have hh : e.symm.conj (e.conj ((t M).lTensor (Fin 2 → ℂ))) =
          S.lTensor (Fin 2 → ℂ) := hS.2
      simpa only [LinearEquiv.conj_symm_conj] using hh.symm
  let F : LieAlgebra.Orthogonal.so (Fin 6) ℂ →ₗ⁅ℂ⁆ L :=
    { toLinearMap := (f.toLinearMap.comp
        (LieAlgebra.Orthogonal.so (Fin 6) ℂ).toSubmodule.subtype).codRestrict L.toSubmodule hf
      map_lie' := by
        intro X Y
        apply Subtype.ext
        change f ((X : Matrix (Fin 6) (Fin 6) ℂ) * Y - Y * X) =
          f X * f Y - f Y * f X
        rw [map_sub, map_mul, map_mul] }
  refine ⟨LieEquiv.ofBijective F ⟨?_, ?_⟩⟩
  · intro X Y h
    have hh : f X = f Y := congrArg Subtype.val h
    rw [hf_apply, hf_apply] at hh
    exact Subtype.ext (t.injective (pel_lTensor_two_injective
      (e.conj.injective ((LinearMap.toMatrix c c).injective hh))))
  · intro X
    obtain ⟨T, ⟨hT, heT⟩, _⟩ := (normal ((LinearMap.toMatrix c c).symm X.val)).mp
      (by simpa only [LinearEquiv.apply_symm_apply] using X.property)
    have hM : LinearMap.toMatrix b6 b6 T ∈ LieAlgebra.Orthogonal.so (Fin 6) ℂ := by
      rw [LieAlgebra.Orthogonal.mem_so]
      have hz := (pel_skew_matrix_iff b6 B T).mpr hT
      rw [hb6, Matrix.mul_one, Matrix.one_mul] at hz
      exact add_eq_zero_iff_eq_neg.mp hz
    refine ⟨⟨_, hM⟩, ?_⟩
    apply Subtype.ext
    change f (LinearMap.toMatrix b6 b6 T) = X.val
    have hh := congrArg e.conj heT
    have hh' : (LinearMap.toMatrix c c).symm X.val = e.conj (T.lTensor (Fin 2 → ℂ)) := by
      simpa only [LinearEquiv.conj_conj_symm] using hh
    rw [hf_apply]
    have ht : t (LinearMap.toMatrix b6 b6 T) = T :=
      (LinearMap.toMatrixAlgEquiv b6).symm_apply_apply T
    rw [ht, ← hh', LinearEquiv.apply_symm_apply]

#print axioms pel_multiplicity_lie_equiv
end HodgeLean.Foundations.Program.GeneralTypeIII
