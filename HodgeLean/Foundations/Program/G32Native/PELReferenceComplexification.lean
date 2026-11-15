import HodgeLean.Foundations.Program.G32Native.PELReferenceLinear

noncomputable section
open scoped TensorProduct
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.GeneralTypeIII
variable {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [DecidableEq ι]

/-- Coordinates commute with cancellation of the iterated scalar extension. -/
theorem pel_repr_cancel_real (b : Module.Basis ι ℚ V) (x : ℝ ⊗[ℚ] V) (i : ι) :
    (Algebra.TensorProduct.basis ℂ b).repr
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V)
        ((1 : ℂ) ⊗ₜ[ℝ] x)) i =
      ((Algebra.TensorProduct.basis ℝ b).repr x i : ℂ) := by
  induction x using TensorProduct.inductionOn with
  | tmul r v => simp [Algebra.smul_def]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply,
      hx, hy, Complex.ofReal_add]

/-- Complexification of a real operator is entrywise inclusion of its real matrix. -/
theorem pel_matrix_complexification (b : Module.Basis ι ℚ V)
    (I : Module.End ℝ (ℝ ⊗[ℚ] V)) :
    LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
      (Algebra.TensorProduct.basis ℂ b) (complexifyRealEnd I) =
      (LinearMap.toMatrix (Algebra.TensorProduct.basis ℝ b)
        (Algebra.TensorProduct.basis ℝ b) I).map (algebraMap ℝ ℂ) := by
  ext i j
  simpa [LinearMap.toMatrix_apply, complexifyRealEnd] using
    pel_repr_cancel_real b (I ((1 : ℝ) ⊗ₜ[ℚ] b j)) i

/-- The minus-i kernel in coordinates transports to the corresponding eigenspace. -/
theorem pel_matrix_negative_eigenspace (b : Module.Basis ι ℂ (ℂ ⊗[ℚ] V))
    (T : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    (LinearMap.ker (Matrix.toLin' (LinearMap.toMatrix b b T) +
      Complex.I • (LinearMap.id : Module.End ℂ (ι → ℂ)))).map
        b.equivFun.symm.toLinearMap = Module.End.eigenspace T (-Complex.I) := by
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Module.End.mem_eigenspace_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change T (b.equivFun.symm y) = -Complex.I • b.equivFun.symm y
    have he : T (b.equivFun.symm y) = b.equivFun.symm
        (Matrix.toLin' (LinearMap.toMatrix b b T) y) := by
      apply b.equivFun.injective
      change b.equivFun (T (b.equivFun.symm y)) =
        b.equivFun (b.equivFun.symm (Matrix.toLin' (LinearMap.toMatrix b b T) y))
      rw [b.equivFun.apply_symm_apply]
      have hm := LinearMap.toMatrix_mulVec_repr b b T (b.equivFun.symm y)
      change Matrix.toLin' (LinearMap.toMatrix b b T)
        (b.equivFun (b.equivFun.symm y)) = b.equivFun (T (b.equivFun.symm y)) at hm
      rw [b.equivFun.apply_symm_apply] at hm
      exact hm.symm
    rw [he, add_eq_zero_iff_eq_neg.mp hy, map_neg, map_smul, neg_smul]
  · intro hx
    refine ⟨b.equivFun x, ?_, b.equivFun.symm_apply_apply x⟩
    have he : Matrix.toLin' (LinearMap.toMatrix b b T) (b.equivFun x) =
        b.equivFun (T x) := by
      exact LinearMap.toMatrix_mulVec_repr b b T x
    rw [he, hx, map_smul]
    module

/-- Two complementary scalar eigenspaces determine the negative-i eigenspace. -/
theorem pel_negative_eigenspace_of_split {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : Module.End ℂ W) (U V : Submodule ℂ W) (hUV : U ⊔ V = ⊤)
    (hU : ∀ x ∈ U, T x = -Complex.I • x)
    (hV : ∀ x ∈ V, T x = Complex.I • x) :
    Module.End.eigenspace T (-Complex.I) = U := by
  ext z
  rw [Module.End.mem_eigenspace_iff]
  constructor
  · intro hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp
      (show z ∈ U ⊔ V by rw [hUV]; trivial)
    have hv0 : (2 * Complex.I) • v = 0 := by
      calc
        _ = T (u + v) + Complex.I • (u + v) := by
          rw [map_add, hU u hu, hV v hv]
          module
        _ = 0 := by rw [hz]; module
    have hvzero : v = 0 := (smul_eq_zero.mp hv0).resolve_left
      (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    simpa only [hvzero, add_zero] using hu
  · exact hU z

#print axioms pel_repr_cancel_real
#print axioms pel_matrix_complexification
#print axioms pel_matrix_negative_eigenspace
#print axioms pel_negative_eigenspace_of_split
end HodgeLean.Foundations.Program.GeneralTypeIII
