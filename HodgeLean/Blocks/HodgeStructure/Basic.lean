import Mathlib

/-! # Pure rational Hodge structures -/

open scoped TensorProduct

noncomputable section

namespace HodgeBlocks

/-- `Complex.conjAe` (`Mathlib/LinearAlgebra/Complex/Module.lean:249`) supplies complex
conjugation as a real-algebra equivalence; restricting its linear map gives a rational map. -/
def conjQ : ℂ →ₗ[ℚ] ℂ :=
  Complex.conjAe.toLinearMap.restrictScalars ℚ

@[simp] theorem conjQ_apply (z : ℂ) : conjQ z = (starRingEnd ℂ) z := rfl

variable (V : Type*) [AddCommGroup V] [Module ℚ V]

/-- `TensorProduct.map` (`Mathlib/LinearAlgebra/TensorProduct/Map.lean:53`) maps two
linear maps over tensor factors.  Here it constructs `conj ⊗ id`. -/
def sigmaQR : ℂ ⊗[ℚ] V →ₗ[ℚ] ℂ ⊗[ℚ] V :=
  TensorProduct.map conjQ LinearMap.id

@[simp] theorem sigmaQ_tmul (c : ℂ) (v : V) :
    sigmaQR V (c ⊗ₜ[ℚ] v) = (starRingEnd ℂ) c ⊗ₜ[ℚ] v := by
  simp [sigmaQR, TensorProduct.map_tmul]

/-- Rational conjugation on the complexification is involutive. -/
@[simp] theorem sigmaQR_involutive (x : ℂ ⊗[ℚ] V) : sigmaQR V (sigmaQR V x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The linear-map form of involutivity. -/
theorem sigmaQR_comp_sigmaQR : (sigmaQR V).comp (sigmaQR V) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact sigmaQR_involutive V x

/-- The rational map `sigmaQR`, bundled as a conjugate-semilinear map so it maps complex
submodules. -/
def sigmaQ : (ℂ ⊗[ℚ] V) →ₛₗ[starRingEnd ℂ] (ℂ ⊗[ℚ] V) where
  toFun := sigmaQR V
  map_add' := map_add (sigmaQR V)
  map_smul' := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul d v => simp [TensorProduct.smul_tmul', mul_comm]
    | add x y hx hy => simp [smul_add, hx, hy]

@[simp] theorem sigmaQ_involutive (x : ℂ ⊗[ℚ] V) : sigmaQ V (sigmaQ V x) = x :=
  sigmaQR_involutive V x

/-- A pure rational Hodge structure of weight `n`, expressed by its Hodge decomposition. -/
structure QHodgeStructure (n : ℤ) (V : Type*) [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] where
  H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)
  supported : ∀ pq, pq.1 + pq.2 ≠ n → H pq = ⊥
  /-- `DirectSum.IsInternal` (`Mathlib/Algebra/DirectSum/Module.lean`) says the canonical
  map from the external direct sum of the pieces is an equivalence. -/
  isInternal : DirectSum.IsInternal H
  conj_symm : ∀ p q : ℤ, (H (p, q)).map (sigmaQ V) = H (q, p)

namespace QHodgeStructure

variable {n : ℤ} [Module.Finite ℚ V] (M : QHodgeStructure n V)

variable {W : Type*} [AddCommGroup W] [Module ℚ W] [Module.Finite ℚ W]

/-- Complexification of a rational linear equivalence. -/
def complexificationCongr (e : V ≃ₗ[ℚ] W) :
    (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (ℂ ⊗[ℚ] W) :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ) e

@[simp] theorem complexificationCongr_tmul (e : V ≃ₗ[ℚ] W) (c : ℂ) (v : V) :
    complexificationCongr (V := V) (W := W) e (c ⊗ₜ[ℚ] v) = c ⊗ₜ[ℚ] e v := by
  simp [complexificationCongr]

theorem complexificationCongr_sigmaQR (e : V ≃ₗ[ℚ] W) (x : ℂ ⊗[ℚ] V) :
    complexificationCongr (V := V) (W := W) e (sigmaQR V x) =
      sigmaQR W (complexificationCongr (V := V) (W := W) e x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp
  | add x y hx hy => simp [map_add, hx, hy]

theorem map_sigma_complexificationCongr (e : V ≃ₗ[ℚ] W)
    (P : Submodule ℂ (ℂ ⊗[ℚ] V)) :
    (P.map (complexificationCongr (V := V) (W := W) e).toLinearMap).map (sigmaQ W) =
      (P.map (sigmaQ V)).map
        (complexificationCongr (V := V) (W := W) e).toLinearMap := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨sigmaQ V y, Submodule.mem_map_of_mem hy,
      complexificationCongr_sigmaQR (V := V) (W := W) e y⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨complexificationCongr (V := V) (W := W) e y, ⟨y, hy, rfl⟩,
      (complexificationCongr_sigmaQR (V := V) (W := W) e y).symm⟩

/-- Transport a rational Hodge structure across a rational linear equivalence. -/
def congr (e : V ≃ₗ[ℚ] W) : QHodgeStructure n W where
  H pq := (M.H pq).map (complexificationCongr (V := V) (W := W) e).toLinearMap
  supported pq h := by rw [M.supported pq h, Submodule.map_bot]
  isInternal := by
    have hM := M.isInternal
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hM ⊢
    refine ⟨?_, ?_⟩
    · have hm := hM.1.map_orderIso
          (Submodule.orderIsoMapComap
            (complexificationCongr (V := V) (W := W) e))
      simpa [Function.comp_def, Submodule.orderIsoMapComap_apply] using hm
    · rw [← Submodule.map_iSup, hM.2, Submodule.map_top,
        LinearEquiv.range]
  conj_symm p q := by
    rw [map_sigma_complexificationCongr, M.conj_symm]

/-- Conjugation symmetry with the two indices reversed. -/
theorem conj_symm_reverse (p q : ℤ) :
    (M.H (q, p)).map (sigmaQ V) = M.H (p, q) :=
  M.conj_symm q p

#print axioms complexificationCongr
#print axioms complexificationCongr_tmul
#print axioms complexificationCongr_sigmaQR
#print axioms map_sigma_complexificationCongr
#print axioms congr

end QHodgeStructure
end HodgeBlocks
