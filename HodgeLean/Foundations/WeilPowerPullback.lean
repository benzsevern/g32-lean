import HodgeLean.Foundations.WeilPowerSpan

/-! # Pullbacks in polarized power coordinates -/

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.WeilPower

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem exteriorBaseChange_map {V' : Type*} [AddCommGroup V'] [Module ℚ V']
    [Module.Finite ℚ V] [Module.Finite ℚ V'] (k : ℕ) (f : V →ₗ[ℚ] V') :
    (exteriorBaseChange k).toLinearMap.comp ((exteriorPower.map k f).baseChange ℂ) =
      (exteriorPower.map k (f.baseChange ℂ)).comp (exteriorBaseChange k).toLinearMap := by
  apply (((Module.finBasis ℚ V).exteriorPower k).baseChange ℂ).ext
  intro s
  simp only [Module.Basis.baseChange_apply, LinearMap.comp_apply,
    LinearMap.baseChange_tmul, LinearEquiv.coe_coe, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti,
    exteriorBaseChange_one_ιMulti]
  rfl

theorem powerBaseChange_pullback (J : Module.End ℚ V) {m : ℕ}
    (r s : Fin m → ℚ) (z : ℂ ⊗[ℚ] V) :
    powerBaseChange m ((weilPowerPullback J r s).baseChange ℂ z) =
      z ⊗ₜ[ℂ] multiplicityEquiv m (1 ⊗ₜ[ℚ] r) +
        J.baseChange ℂ z ⊗ₜ[ℂ] multiplicityEquiv m (1 ⊗ₜ[ℚ] s) := by
  induction z using TensorProduct.inductionOn with
  | tmul c x =>
    simp [weilPowerPullback, powerBaseChange, TensorProduct.tmul_add]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.add_tmul, hx, hy]
    abel

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The two split multiplicities of a rational `r + sJ` pullback are conjugate. -/
theorem powerModel_pullback (J : Module.End ℚ V) {m : ℕ}
    (e : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (W × Module.Dual ℂ W))
    (hJe : ∀ z, e (J.baseChange ℂ z) = splitJ W (e z))
    (r s : Fin m → ℚ) (z : ℂ ⊗[ℚ] V) :
    powerModel m e ((weilPowerPullback J r s).baseChange ℂ z) =
      ((e z).1 ⊗ₜ[ℂ] (multiplicityEquiv m (1 ⊗ₜ[ℚ] r) +
          root • multiplicityEquiv m (1 ⊗ₜ[ℚ] s)),
        (e z).2 ⊗ₜ[ℂ] (multiplicityEquiv m (1 ⊗ₜ[ℚ] r) -
          root • multiplicityEquiv m (1 ⊗ₜ[ℚ] s))) := by
  unfold powerModel
  simp only [LinearEquiv.trans_apply, powerBaseChange_pullback, map_add,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, hJe]
  simp [TensorProduct.prodLeft, splitJ, TensorProduct.tmul_add,
    TensorProduct.tmul_sub, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    TensorProduct.neg_tmul, sub_eq_add_neg]
  simp only [← neg_smul, TensorProduct.neg_tmul, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul]

theorem powerModel_pullback_vector (J : Module.End ℚ V) {m : ℕ}
    (e : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (W × Module.Dual ℂ W))
    (hJe : ∀ z, e (J.baseChange ℂ z) = splitJ W (e z))
    (r s : Fin m → ℚ) (w : W) :
    powerModel m e ((weilPowerPullback J r s).baseChange ℂ (e.symm (w, 0))) =
      InvariantsExterior.vectorIn (multiplicityEquiv m (1 ⊗ₜ[ℚ] r) +
        root • multiplicityEquiv m (1 ⊗ₜ[ℚ] s)) w := by
  rw [powerModel_pullback J e hJe, e.apply_symm_apply]
  simp [InvariantsExterior.vectorIn, TensorProduct.tmul_add, TensorProduct.tmul_smul]

theorem powerModel_pullback_dual (J : Module.End ℚ V) {m : ℕ}
    (e : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (W × Module.Dual ℂ W))
    (hJe : ∀ z, e (J.baseChange ℂ z) = splitJ W (e z))
    (r s : Fin m → ℚ) (w : Module.Dual ℂ W) :
    powerModel m e ((weilPowerPullback J r s).baseChange ℂ (e.symm (0, w))) =
      InvariantsExterior.dualIn (multiplicityEquiv m (1 ⊗ₜ[ℚ] r) -
        root • multiplicityEquiv m (1 ⊗ₜ[ℚ] s)) w := by
  rw [powerModel_pullback J e hJe, e.apply_symm_apply]
  simp [InvariantsExterior.dualIn, TensorProduct.tmul_sub, TensorProduct.tmul_smul]

theorem powerModel_pullback_exterior_vector [Module.Finite ℂ W]
    (J : Module.End ℚ V) {m : ℕ}
    (e : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (W × Module.Dual ℂ W))
    (hJe : ∀ z, e (J.baseChange ℂ z) = splitJ W (e z))
    (r s : Fin m → ℚ) (t : ⋀[ℂ]^(Module.finrank ℂ W) W) :
    exteriorPower.map (Module.finrank ℂ W)
        ((powerModel m e).toLinearMap.comp ((weilPowerPullback J r s).baseChange ℂ))
      (exteriorPower.map (Module.finrank ℂ W)
        (e.symm.toLinearMap.comp (LinearMap.inl ℂ W (Module.Dual ℂ W))) t) =
      InvariantsExterior.detWOf t (multiplicityEquiv m (1 ⊗ₜ[ℚ] r) +
        root • multiplicityEquiv m (1 ⊗ₜ[ℚ] s)) := by
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  unfold InvariantsExterior.detWOf
  apply congrArg (fun f => exteriorPower.map (Module.finrank ℂ W) f t)
  apply LinearMap.ext
  intro w
  exact powerModel_pullback_vector J e hJe r s w

theorem powerModel_pullback_exterior_dual [Module.Finite ℂ W]
    (J : Module.End ℚ V) {m : ℕ}
    (e : (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (W × Module.Dual ℂ W))
    (hJe : ∀ z, e (J.baseChange ℂ z) = splitJ W (e z))
    (r s : Fin m → ℚ) (t : ⋀[ℂ]^(Module.finrank ℂ W) (Module.Dual ℂ W)) :
    exteriorPower.map (Module.finrank ℂ W)
        ((powerModel m e).toLinearMap.comp ((weilPowerPullback J r s).baseChange ℂ))
      (exteriorPower.map (Module.finrank ℂ W)
        (e.symm.toLinearMap.comp (LinearMap.inr ℂ W (Module.Dual ℂ W))) t) =
      InvariantsExterior.detWDualOf t (multiplicityEquiv m (1 ⊗ₜ[ℚ] r) -
        root • multiplicityEquiv m (1 ⊗ₜ[ℚ] s)) := by
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  unfold InvariantsExterior.detWDualOf
  apply congrArg (fun f => exteriorPower.map (Module.finrank ℂ W) f t)
  apply LinearMap.ext
  intro w
  exact powerModel_pullback_dual J e hJe r s w

end HodgeLean.Foundations.WeilPower
