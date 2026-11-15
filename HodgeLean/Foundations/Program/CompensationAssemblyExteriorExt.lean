import HodgeLean.Foundations.Program.CompensationAssemblyExterior

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem cq_exterior_product_linear_ext (R V T N : Type*) [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup T] [Module R T]
    [AddCommGroup N] [Module R N]
    (L S : ExteriorAlgebra R (V × T) →ₗ[R] N)
    (h : ∀ (i j : ℕ) (a : ⋀[R]^i V) (b : ⋀[R]^j T),
      L (ExteriorAlgebra.map (LinearMap.inl R V T) a *
        ExteriorAlgebra.map (LinearMap.inr R V T) b) =
      S (ExteriorAlgebra.map (LinearMap.inl R V T) a *
        ExteriorAlgebra.map (LinearMap.inr R V T) b)) : L = S := by
  have hp (a : ExteriorAlgebra R V) (b : ExteriorAlgebra R T) :
      L (ExteriorAlgebra.map (LinearMap.inl R V T) a *
        ExteriorAlgebra.map (LinearMap.inr R V T) b) =
      S (ExteriorAlgebra.map (LinearMap.inl R V T) a *
        ExteriorAlgebra.map (LinearMap.inr R V T) b) := by
    induction a using DirectSum.Decomposition.inductionOn (fun i => ⋀[R]^i V) with
    | zero => simp only [map_zero, zero_mul]
    | add a a' ha ha' => simp only [map_add, add_mul, ha, ha']
    | @homogeneous i a =>
      induction b using DirectSum.Decomposition.inductionOn (fun j => ⋀[R]^j T) with
      | zero => simp only [map_zero, mul_zero]
      | add b b' hb hb' => simp only [map_add, mul_add, hb, hb']
      | @homogeneous j b => exact h i j a b
  let E : ExteriorAlgebra R (V × T) ≃ₗ[R]
      ExteriorAlgebra R V ⊗[R] ExteriorAlgebra R T :=
    (ExteriorAlgebra.prodEquivTensor R V T).toLinearEquiv.trans
      (GradedTensorProduct.of R (fun i : ℕ => ⋀[R]^i V)
        (fun j : ℕ => ⋀[R]^j T)).symm
  have hE : L.comp E.symm.toLinearMap = S.comp E.symm.toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    exact hp a b
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hE (E x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hx

theorem cq_exterior_map_symm_apply (R V T : Type*) [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup T] [Module R T]
    (e : V ≃ₗ[R] T) (a : ExteriorAlgebra R T) :
    ExteriorAlgebra.map e.toLinearMap (ExteriorAlgebra.map e.symm.toLinearMap a) = a := by
  have hcomp : e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    exact e.apply_symm_apply
  change ((ExteriorAlgebra.map e.toLinearMap).comp
    (ExteriorAlgebra.map e.symm.toLinearMap)) a = a
  rw [ExteriorAlgebra.map_comp_map, hcomp, ExteriorAlgebra.map_id]
  rfl

end HodgeLean.Foundations.Program
