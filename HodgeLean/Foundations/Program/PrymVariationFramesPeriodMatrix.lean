import HodgeLean.Foundations.Program.PrymVariationFramesDefs
import HodgeLean.Foundations.Program.PrymVariationFramesHolomorphic

noncomputable section
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem b63e_periodF_iff_frame (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {ι : Type*} (θ : ι → b3_HolForm ℂ C)
    (hθ : Submodule.span ℂ (Set.range θ) = ⊤) (v : ℂ ⊗[ℤ] b3_periodLattice ℂ C) :
    v ∈ b3_periodF ℂ C ↔ ∀ i, b3_cplxPeriod ℂ C v (θ i) = 0 := by
  change b3_cplxPeriod ℂ C v = 0 ↔ _
  constructor
  · intro h i
    exact congrFun h (θ i)
  · intro h
    let f := b3A_toDual ⟨b3_cplxPeriod ℂ C v, b3A_cplxPeriod_mem_linearDual v⟩
    have hf : f = 0 := LinearMap.ext_on_range hθ h
    exact funext fun x ↦ LinearMap.congr_fun hf x

set_option backward.isDefEq.respectTransparency false in
theorem b63e_period_matrix_kernel (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {M : Type} [AddCommGroup M]
    {m n : ℕ} (B : Module.Basis (Fin n) ℤ M) (T : M →ₗ[ℤ] b3_periodLattice ℂ C)
    (θ : Fin m → b3_HolForm ℂ C) (hθ : Submodule.span ℂ (Set.range θ) = ⊤)
    (c : Fin n → ℂ) :
    b63e_coordVector B c ∈ (b3_periodF ℂ C).comap (T.baseChange ℂ) ↔
      (Matrix.mulVecLin (fun i j ↦ (T (B j)).val (θ i))) c = 0 := by
  rw [Submodule.mem_comap, b63e_periodF_iff_frame C θ hθ]
  simp only [b63e_coordVector, map_sum, LinearMap.baseChange_tmul,
    b3_cplxPeriod, LinearMap.liftBaseChange_tmul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, funext_iff, Pi.zero_apply]
  simp only [mul_comm]
  rfl

theorem b63e_coordVector_reindex {ι κ : Type} [Fintype ι] [Fintype κ]
    {M : Type*} [AddCommGroup M] (B : Module.Basis ι ℤ M) (e : ι ≃ κ) (c : κ → ℂ) :
    b63e_coordVector (B.reindex e) c = b63e_coordVector B (c ∘ e) := by
  classical
  simp only [b63e_coordVector, Module.Basis.reindex_apply, Function.comp_apply]
  exact (Fintype.sum_equiv e _ _ (fun i ↦ by rw [e.symm_apply_apply])).symm

end HodgeLean.Foundations.Program
