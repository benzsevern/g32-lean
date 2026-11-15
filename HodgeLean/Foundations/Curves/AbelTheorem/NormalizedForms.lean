import HodgeLean.Foundations.Curves.AbelTheorem.FrameConstruction
import HodgeLean.Foundations.Curves.AbelTheorem.PeriodLinearAlgebra

noncomputable section
open HodgeLean.Foundations.Program
open Module Manifold
open scoped ContDiff BigOperators TensorProduct
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

def latticeFunctional (ell : b3_periodLattice E C) : Dual ℂ (b3_HolForm E C) :=
  b3A_toDual ⟨ell.val, b3Forms_periodLattice_le_linearDual ell.property⟩

theorem complex_left_tensor_period {g : ℕ}
    (b : Basis (Fin g ⊕ Fin g) ℤ (b3_periodLattice E C))
    (c : Fin g → ℂ) (θ : b3_HolForm E C) :
    b3_cplxPeriod E C (complexLeftTensor b c) θ =
      ∑ i, c i * (b (.inl i)).val θ := by
  rw [complexLeftTensor, map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

theorem a_period_functionals_independent (h : finrank ℂ E = 1) {g : ℕ}
    (b : Basis (Fin g ⊕ Fin g) ℤ (b3_periodLattice E C))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C))
    (hQ : b3_IsIntersectionForm E Q)
    (haa : ∀ i j, Q (b (.inl i)) (b (.inl j)) = 0) :
    LinearIndependent ℂ (fun i => latticeFunctional (b (.inl i))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hmem : complexLeftTensor b c ∈ b3_periodF E C := by
    change b3_cplxPeriod E C (complexLeftTensor b c) = 0
    funext θ
    rw [complex_left_tensor_period]
    have he := LinearMap.congr_fun hc θ
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply] at he
    exact he
  have hz := complex_left_tensor_coefficients_zero b Q (b3_periodF E C)
    (b3_intersectionForm_isRiemannForm h Q hQ) haa c hmem
  intro i
  exact congrFun hz i

theorem exists_normalized_holomorphic_basis (h : finrank ℂ E = 1) {g : ℕ}
    (b : Basis (Fin g ⊕ Fin g) ℤ (b3_periodLattice E C))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C))
    (hQ : b3_IsIntersectionForm E Q)
    (haa : ∀ i j, Q (b (.inl i)) (b (.inl j)) = 0) :
    ∃ forms : Basis (Fin g) ℂ (b3_HolForm E C),
      ∀ i j, (b (.inl i)).val (forms j) = if i = j then 1 else 0 := by
  classical
  letI := b3_holForm_finiteDimensional (E := E) (C := C) h
  have hcard : Fintype.card (Fin g) = finrank ℂ (Dual ℂ (b3_HolForm E C)) := by
    rw [Fintype.card_fin, Subspace.dual_finrank_eq]
    exact curve_symplectic_genus h b
  let d := basisOfLinearIndependentOfCardEqFinrank'
    (fun i => latticeFunctional (b (.inl i)))
    (a_period_functionals_independent h b Q hQ haa) hcard
  let e := Module.evalEquiv ℂ (b3_HolForm E C)
  let forms := d.dualBasis.map e.symm
  refine ⟨forms, fun i j => ?_⟩
  have hdi : d i = latticeFunctional (b (.inl i)) := by
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) i
  change latticeFunctional (b (.inl i)) (e.symm (d.dualBasis j)) = _
  calc
    latticeFunctional (b (.inl i)) (e.symm (d.dualBasis j)) =
        e (e.symm (d.dualBasis j)) (latticeFunctional (b (.inl i))) := rfl
    _ = d.dualBasis j (latticeFunctional (b (.inl i))) := by rw [e.apply_symm_apply]
    _ = d.dualBasis j (d i) := by rw [hdi]
    _ = if i = j then 1 else 0 := by simp only [Basis.dualBasis_apply_self]

end HodgeLean.Foundations.Curves.AbelTheorem
