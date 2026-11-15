import HodgeLean.Adapters.F1575Products
import HodgeLean.Foundations.DualForm

/-! # Normalization of the single-copy quadratic generator

The split-basis bivector has the same contraction as the complexification
of the rational polarization bivector. Injectivity of contraction identifies
them, fixing the coefficient and sign before transport to cohomology.
-/

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Adapters
open Foundations Foundations.WeilPower

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

theorem f1575_contract_complexify (E : LinearMap.BilinForm ℚ V)
    (ω : ⋀[ℚ]^2 V) (x : V) :
    Symplectic.contract (HodgeBlocks.complexifyWedge 2 ω)
      ((E.baseChange ℂ) ((1 : ℂ) ⊗ₜ[ℚ] x)) =
      (1 : ℂ) ⊗ₜ[ℚ] Symplectic.contract ω (E x) := by
  let φ := (E.baseChange ℂ) ((1 : ℂ) ⊗ₜ[ℚ] x)
  have hh : (((LinearMap.applyₗ φ).comp
      Symplectic.contract).restrictScalars ℚ).comp (HodgeBlocks.complexifyWedge 2) =
      (TensorProduct.mk ℚ ℂ V 1).comp
        ((LinearMap.applyₗ (E x)).comp Symplectic.contract) := by
    ext v
    simp [φ, HodgeBlocks.complexifyWedge_ιMulti,
      LinearMap.BilinForm.baseChange_tmul, TensorProduct.tmul_sub,
      TensorProduct.tmul_smul, Algebra.smul_def]
    simp only [TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul, mul_one]
    rfl
  exact LinearMap.congr_fun hh ω

theorem f1575_contract_dualForm {ω : ⋀[ℚ]^2 V} (hω : Symplectic.IsNondegenerate ω)
    (x : V) : Symplectic.contract ω (Symplectic.dualForm hω x) = -x := by
  have hh : Symplectic.dualForm hω x = -(Symplectic.contractEquiv hω).symm x := by
    ext y
    exact (LinearMap.BilinForm.IsAlt.neg_eq (Symplectic.isAlt_dualForm hω) y x).symm
  rw [hh, map_neg, Symplectic.contract_contractEquiv_symm]

theorem f1575_contract_complex_dualForm {ω : ⋀[ℚ]^2 V}
    (hω : Symplectic.IsNondegenerate ω) (x : ℂ ⊗[ℚ] V) :
    Symplectic.contract (HodgeBlocks.complexifyWedge 2 ω)
      (((Symplectic.dualForm hω).baseChange ℂ) x) = -x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [show a ⊗ₜ[ℚ] x = a • ((1 : ℂ) ⊗ₜ[ℚ] x) by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    rw [map_smul, map_smul, f1575_contract_complexify, f1575_contract_dualForm]
    simp only [TensorProduct.tmul_neg, smul_neg]
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]

section Split
variable {Z W : Type*} [AddCommGroup Z] [Module ℂ Z]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]

theorem f1575_contract_split_sum (E : LinearMap.BilinForm ℂ Z)
    (e : Z ≃ₗ[ℂ] (W × Module.Dual ℂ W))
    (he : ∀ x y, E x y = splitForm W (e x) (e y))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ W) (x : Z) :
    Symplectic.contract
      (∑ i, exteriorPower.ιMulti ℂ 2 ![e.symm (b i, 0), e.symm (0, b.dualBasis i)])
        (E x) = -x := by
  apply e.injective
  simp only [map_sum, LinearMap.sum_apply, Symplectic.contract_ιMulti,
    Matrix.cons_val_zero, Matrix.cons_val_one, he, LinearEquiv.apply_symm_apply,
    splitForm, LinearMap.mk₂_apply, map_zero, zero_sub, sub_zero,
    map_sub, map_smul, map_neg]
  apply Prod.ext
  · simp [← prod_mk_sum, Finset.sum_neg_distrib]
  · simp [← prod_mk_sum, Finset.sum_neg_distrib]

end Split

theorem f1575_complex_dualForm_surjective {ω : ⋀[ℚ]^2 V}
    (hω : Symplectic.IsNondegenerate ω) :
    Function.Surjective ((Symplectic.dualForm hω).baseChange ℂ) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank ℂ (ℂ ⊗[ℚ] V) =
      Module.finrank ℂ (Module.Dual ℂ (ℂ ⊗[ℚ] V)) by
      rw [Subspace.dual_finrank_eq])).mp
  intro x y h
  have hh := congrArg (Symplectic.contract (HodgeBlocks.complexifyWedge 2 ω)) h
  simpa only [f1575_contract_complex_dualForm, neg_inj] using hh

theorem f1575_split_sum_eq_complexify {ω : ⋀[ℚ]^2 V}
    (hω : Symplectic.IsNondegenerate ω)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    (e : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (W × Module.Dual ℂ W))
    (he : ∀ x y, (Symplectic.dualForm hω).baseChange ℂ x y =
      splitForm W (e x) (e y))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ W) :
    (∑ i, exteriorPower.ιMulti ℂ 2 ![e.symm (b i, 0), e.symm (0, b.dualBasis i)]) =
      HodgeBlocks.complexifyWedge 2 ω := by
  apply Symplectic.contract_injective
  ext φ
  obtain ⟨x, rfl⟩ := f1575_complex_dualForm_surjective hω φ
  rw [f1575_contract_split_sum _ e he b x, f1575_contract_complex_dualForm]

theorem f1575_singleCopy_theta {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] (e : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (W × Module.Dual ℂ W))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ W) :
    exteriorPower.map 2 ((powerModel 1 e).symm.trans f1575SingleCopyComplex).toLinearMap
      (InvariantsExterior.theta (1 : Fin 1 → ℂ) (1 : Fin 1 → ℂ)) =
      ∑ i, exteriorPower.ιMulti ℂ 2 ![e.symm (b i, 0), e.symm (0, b.dualBasis i)] := by
  rw [InvariantsExterior.theta_eq_sum b, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [InvariantsExterior.wedgePair_apply, exteriorPower.map_apply_ιMulti]
  congr 1
  funext j
  fin_cases j
  · change f1575SingleCopyComplex ((powerModel 1 e).symm
      (InvariantsExterior.vectorIn (1 : Fin 1 → ℂ) (b i))) = _
    rw [f1575_singleCopyModel_symm_vector]
    simp only [Pi.one_apply, one_smul]
    rfl
  · change f1575SingleCopyComplex ((powerModel 1 e).symm
      (InvariantsExterior.dualIn (1 : Fin 1 → ℂ) (b.dualBasis i))) = _
    rw [f1575_singleCopyModel_symm_dual]
    simp only [Pi.one_apply, one_smul]
    rfl

end HodgeLean.Adapters
