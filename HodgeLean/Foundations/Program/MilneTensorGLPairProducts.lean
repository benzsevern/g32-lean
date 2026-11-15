import HodgeLean.Foundations.Program.MilneTensorPairSums

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def m1b_vectorDualAction (g : LinearMap.GeneralLinearGroup ℂ W) :
    Module.End ℂ (W × Module.Dual ℂ W) :=
  (g : Module.End ℂ W).prodMap
    ((g⁻¹ : LinearMap.GeneralLinearGroup ℂ W) : Module.End ℂ W).dualMap

def m1b_glPairSlots (k : ℕ) : (Fin k ⊕ Fin k) ≃ Fin (k * 2) :=
  finSumFinEquiv.trans (finCongr (by omega))

def m1b_glPairIn (k : ℕ) : SchurWeyl.MixedTensor ℂ W (Fin k) (Fin k) →ₗ[ℂ]
    ⨂[ℂ]^(k * 2) (W × Module.Dual ℂ W) :=
  (PiTensorProduct.reindex ℂ (fun _ => W × Module.Dual ℂ W)
    (m1b_glPairSlots k)).toLinearMap.comp InvariantsExterior.orderedWordIn

theorem m1b_glPairIn_tprod (k : ℕ) (v : Fin k → W) (φ : Fin k → Module.Dual ℂ W) :
    m1b_glPairIn k ((⨂ₜ[ℂ] i, v i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, φ i)) =
      ⨂ₜ[ℂ] i, Sum.elim (fun j => (v j, 0)) (fun j => (0, φ j))
        ((m1b_glPairSlots k).symm i) := by
  simp only [m1b_glPairIn, LinearMap.comp_apply, InvariantsExterior.orderedWordIn,
    TensorProduct.map_tmul, PiTensorProduct.map_tprod, LinearEquiv.coe_coe,
    PiTensorProduct.tmulEquiv_apply, PiTensorProduct.reindex_tprod]
  rfl

theorem m1b_glPairIn_intertwines (k : ℕ) (g : LinearMap.GeneralLinearGroup ℂ W)
    (t : SchurWeyl.MixedTensor ℂ W (Fin k) (Fin k)) :
    SchurWeyl.tensorPow (Fin (k * 2)) (m1b_vectorDualAction g) (m1b_glPairIn k t) =
      m1b_glPairIn k (SchurWeyl.mixedRep ℂ W (Fin k) (Fin k) g t) := by
  suffices h : (SchurWeyl.tensorPow (Fin (k * 2)) (m1b_vectorDualAction g)).comp
      (m1b_glPairIn k) = (m1b_glPairIn k).comp
        (SchurWeyl.mixedRep ℂ W (Fin k) (Fin k) g) from LinearMap.congr_fun h t
  apply TensorProduct.ext
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro φ
  change SchurWeyl.tensorPow (Fin (k * 2)) (m1b_vectorDualAction g)
      (m1b_glPairIn k ((⨂ₜ[ℂ] i, v i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, φ i))) =
    m1b_glPairIn k (SchurWeyl.mixedRep ℂ W (Fin k) (Fin k) g
      ((⨂ₜ[ℂ] i, v i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, φ i)))
  simp only [m1b_glPairIn_tprod, SchurWeyl.tensorPow_tprod, SchurWeyl.mixedRep_tmul_tprod]
  congr 1
  funext i
  cases h : (m1b_glPairSlots k).symm i with
  | inl j => simp only [Sum.elim_inl, m1b_vectorDualAction, LinearMap.prodMap_apply,
      LinearMap.map_zero]
  | inr j =>
    simp only [Sum.elim_inr, m1b_vectorDualAction, LinearMap.prodMap_apply, LinearMap.map_zero]
    rfl

variable [FiniteDimensional ℂ W]

theorem m1b_glPairIn_contraction_fixed (k : ℕ) (π : Equiv.Perm (Fin k)) :
    m1b_glPairIn k (SchurWeyl.contraction ℂ W (Fin k) π) ∈
      m1b_fixed (Set.range (m1b_vectorDualAction (W := W))) (k * 2) := by
  have hc : SchurWeyl.contraction ℂ W (Fin k) π ∈
      (SchurWeyl.mixedRep ℂ W (Fin k) (Fin k)).invariants := by
    rw [SchurWeyl.invariants_mixedRep_eq_span_contraction]
    exact Submodule.subset_span ⟨π, rfl⟩
  simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rintro _ ⟨g, rfl⟩
  rw [m1b_glPairIn_intertwines]
  exact congrArg (m1b_glPairIn k) (hc g)

def m1b_pairToSum (k : ℕ) : (Fin k × Fin 2) ≃ (Fin k ⊕ Fin k) where
  toFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  invFun := Sum.elim (fun i => (i, 0)) (fun i => (i, 1))
  left_inv p := by rcases p with ⟨i, j⟩; fin_cases j <;> simp
  right_inv p := by cases p <;> simp

theorem m1b_glPairIn_one_contraction {β : Type*} [Fintype β] [DecidableEq β]
    (b : Module.Basis β ℂ W) :
    m1b_glPairIn 1 (SchurWeyl.contraction ℂ W (Fin 1) 1) =
      ∑ j, ⨂ₜ[ℂ] i : Fin 2, if i = 0 then (b j, 0) else (0, b.coord j) := by
  rw [SchurWeyl.contraction_eq_sum b, map_sum]
  rw [← (Equiv.piUnique (fun _ : Fin 1 => β)).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [m1b_glPairIn_tprod]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem m1b_glPairIn_contraction_products (k : ℕ) (π : Equiv.Perm (Fin k)) :
    m1b_glPairIn k (SchurWeyl.contraction ℂ W (Fin k) π) ∈
      m1b_products (m1b_fixed (Set.range (m1b_vectorDualAction (W := W))) 2) (k * 2) := by
  classical
  let b := Module.finBasis ℂ W
  let e : (Fin k × Fin 2) ≃ Fin (k * 2) :=
    ((m1b_pairToSum k).trans (Equiv.sumCongr π (Equiv.refl _))).trans (m1b_glPairSlots k)
  have hq : (∑ j, ⨂ₜ[ℂ] i : Fin 2,
      if i = 0 then (b j, 0) else (0, b.coord j)) ∈
      m1b_fixed (Set.range (m1b_vectorDualAction (W := W))) 2 := by
    rw [← m1b_glPairIn_one_contraction b]
    exact m1b_glPairIn_contraction_fixed 1 1
  have hp := m1b_products_pairSums
    (m1b_fixed (Set.range (m1b_vectorDualAction (W := W))) 2) k
    (fun _ j (i : Fin 2) => if i = 0 then (b j, 0) else (0, b.coord j))
    (fun _ => hq) e
  convert hp using 1
  rw [SchurWeyl.contraction_eq_sum b, map_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [m1b_glPairIn_tprod]
  congr 1
  funext i
  obtain ⟨p, rfl⟩ := e.surjective i
  rcases p with ⟨j, s⟩
  fin_cases s <;>
    simp [e, m1b_pairToSum, Equiv.trans_apply]

end HodgeLean.Foundations.Program
