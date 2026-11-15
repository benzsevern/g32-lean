import HodgeLean.Foundations.Program.PrymVariationCentreScalar
import HodgeLean.Foundations.Program.PrymVariationCentreRange

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

theorem b63d_scalarElement_unique (g : b4b_Group) :
    b4b_toMatrix g = g32h_omega • (1 : Matrix (Fin 4) (Fin 4) ℂ) ↔
      g = b63d_scalarElement := by
  constructor
  · intro hg
    apply Subtype.val_injective
    exact hg.trans b63d_scalarElement_matrix.symm
  · rintro rfl
    exact b63d_scalarElement_matrix

theorem b63d_left_reindex {M : Type*} [AddCommGroup M] (a : b4b_Group → ℤ)
    (f : b4b_Group → M) :
    ∑ h : b4b_Group, a h • f (b63d_scalarElement * h) =
      ∑ k : b4b_Group, a (b63d_scalarElement⁻¹ * k) • f k := by
  refine Fintype.sum_equiv (Equiv.mulLeft b63d_scalarElement) _ _ fun h ↦ ?_
  change a h • f (b63d_scalarElement * h) =
    a (b63d_scalarElement⁻¹ * (b63d_scalarElement * h)) •
      f (b63d_scalarElement * h)
  congr 2
  congr 1
  group

set_option maxHeartbeats 400000 in
theorem b63d_sq_reindex {M : Type*} [AddCommGroup M] (f : b4b_Group → M) :
    ∑ h : b4b_Group, b4b_projectorCoeff h • f (b63d_scalarElement ^ 2 * h) =
      ∑ k : b4b_Group, b4b_projectorCoeff (b63d_scalarElement * k) • f k := by
  have h0 : (∑ h : b4b_Group, b4b_projectorCoeff h •
      f (b63d_scalarElement ^ 2 * h)) =
      ∑ h : b4b_Group, b4b_projectorCoeff h •
        f (b63d_scalarElement * (b63d_scalarElement * h)) := by
    apply Finset.sum_congr rfl
    intro h hh
    apply congrArg (fun q : b4b_Group ↦ b4b_projectorCoeff h • f q)
    rw [pow_two, mul_assoc]
  have h1 := b63d_left_reindex b4b_projectorCoeff
    (fun k ↦ f (b63d_scalarElement * k))
  have h2 := b63d_left_reindex
    (fun k ↦ b4b_projectorCoeff (b63d_scalarElement⁻¹ * k)) f
  rw [h0, h1, h2]
  apply Finset.sum_congr rfl
  intro k hk
  apply congrArg (fun n : ℤ ↦ n • f k)
  apply congrArg b4b_projectorCoeff
  have hzinv : b63d_scalarElement⁻¹ = b63d_scalarElement ^ 2 := by
    calc
      b63d_scalarElement⁻¹ = b63d_scalarElement⁻¹ * 1 := by simp
      _ = b63d_scalarElement⁻¹ * b63d_scalarElement ^ 3 := by
        rw [b63d_scalarElement_cube]
      _ = b63d_scalarElement ^ 2 := by group
  rw [hzinv]
  calc
    b63d_scalarElement ^ 2 * (b63d_scalarElement ^ 2 * k) =
        b63d_scalarElement * (b63d_scalarElement ^ 3 * k) := by group
    _ = b63d_scalarElement * k := by rw [b63d_scalarElement_cube, one_mul]

theorem b63d_one_reindex {M : Type*} [AddCommGroup M] (f : b4b_Group → M) :
    ∑ h : b4b_Group, b4b_projectorCoeff h • f (b63d_scalarElement * h) =
      ∑ k : b4b_Group, b4b_projectorCoeff (b63d_scalarElement⁻¹ * k) • f k := by
  exact b63d_left_reindex b4b_projectorCoeff f

set_option maxHeartbeats 400000 in
theorem b63d_homology_projector_polynomial (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x)) (x : b6m_H1 C) :
    let P := ∑ h : b4b_Group, b4b_projectorCoeff h • b63d_homologyAct C hC h
    let T := b63d_homologyAct C hC b63d_scalarElement
    T (T (P x)) + T (P x) + P x = 0 := by
  dsimp only
  simp only [LinearMap.sum_apply]
  change b63d_homologyAct C hC b63d_scalarElement
      (b63d_homologyAct C hC b63d_scalarElement
        (∑ h : b4b_Group, b4b_projectorCoeff h • b63d_homologyAct C hC h x)) +
    b63d_homologyAct C hC b63d_scalarElement
      (∑ h : b4b_Group, b4b_projectorCoeff h • b63d_homologyAct C hC h x) +
    (∑ h : b4b_Group, b4b_projectorCoeff h • b63d_homologyAct C hC h x) = 0
  simp only [map_sum, map_zsmul]
  simp_rw [b63d_homologyAct_mul]
  have hsq : ∑ h : b4b_Group, b4b_projectorCoeff h •
      b63d_homologyAct C hC (b63d_scalarElement * (b63d_scalarElement * h)) x =
      ∑ k : b4b_Group, b4b_projectorCoeff (b63d_scalarElement * k) •
        b63d_homologyAct C hC k x := by
    convert b63d_sq_reindex (fun k ↦ b63d_homologyAct C hC k x) using 1 <;>
      apply Finset.sum_congr rfl <;> intro h hh <;> congr 3 <;>
        simp only [pow_two, mul_assoc]
  have hone : ∑ h : b4b_Group, b4b_projectorCoeff h •
      b63d_homologyAct C hC (b63d_scalarElement * h) x =
      ∑ k : b4b_Group, b4b_projectorCoeff (b63d_scalarElement⁻¹ * k) •
        b63d_homologyAct C hC k x := by
    exact b63d_one_reindex (fun k ↦ b63d_homologyAct C hC k x)
  rw [hsq, hone, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro h hh
  let y := b63d_homologyAct C hC h x
  have hc : b4b_projectorCoeff (b63d_scalarElement * h) +
      b4b_projectorCoeff (b63d_scalarElement⁻¹ * h) + b4b_projectorCoeff h = 0 := by
    have := b63d_projectorCoeff_scalar h
    omega
  change b4b_projectorCoeff (b63d_scalarElement * h) • y +
      b4b_projectorCoeff (b63d_scalarElement⁻¹ * h) • y +
      b4b_projectorCoeff h • y = 0
  calc
    _ = (b4b_projectorCoeff (b63d_scalarElement * h) +
        b4b_projectorCoeff (b63d_scalarElement⁻¹ * h) + b4b_projectorCoeff h) • y := by
          rw [add_zsmul, add_zsmul]
    _ = 0 := by rw [hc, zero_smul]

theorem b63d_homology_saturation_polynomial (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (x : b6m_H1 C)
    (hx : x ∈ b63l_saturation (LinearMap.range
      (∑ h : b4b_Group, b4b_projectorCoeff h •
        b63d_homologyAct C (fun g ↦ (hG g).continuous) h))) :
    b63d_homologyAct C (fun g ↦ (hG g).continuous) b63d_scalarElement
        (b63d_homologyAct C (fun g ↦ (hG g).continuous) b63d_scalarElement x) +
      b63d_homologyAct C (fun g ↦ (hG g).continuous) b63d_scalarElement x + x = 0 := by
  let T := b63d_homologyAct C (fun g ↦ (hG g).continuous) b63d_scalarElement
  let P := ∑ h : b4b_Group, b4b_projectorCoeff h •
    b63d_homologyAct C (fun g ↦ (hG g).continuous) h
  rcases hx with ⟨n, hn, y, hy⟩
  have hP : T (T (P y)) + T (P y) + P y = 0 :=
    b63d_homology_projector_polynomial C (fun g ↦ (hG g).continuous) y
  have hy' : P y = n • x := by
    calc
      P y = (inferInstance : Module ℤ (b6m_H1 C)).smul n x := hy
      _ = n • x := int_smul_eq_zsmul (inferInstance : Module ℤ (b6m_H1 C)) n x
  have hnpoly : n • (T (T x) + T x + x) = 0 := by
    calc
      n • (T (T x) + T x + x) = T (T (n • x)) + T (n • x) + n • x := by
        simp only [zsmul_add, map_zsmul]
      _ = T (T (P y)) + T (P y) + P y := by rw [hy']
      _ = 0 := hP
  obtain ⟨E, hE⟩ := b6m_period_comparison C
  have hmapped := congrArg E hnpoly
  rw [map_zero, map_zsmul] at hmapped
  have hzero : E (T (T x) + T x + x) = 0 :=
    (smul_eq_zero.mp hmapped).resolve_left hn
  apply E.injective
  simpa using hzero

set_option maxHeartbeats 400000 in
theorem b63d_period_projector_polynomial (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (x : b3_periodLattice ℂ C) :
    let P := b4_groupEnd ℂ (C := C) b4b_projectorCoeff
    let T := b4_latticeAct ℂ (C := C) b63d_scalarElement
    T (T (P x)) + T (P x) + P x = 0 := by
  dsimp only
  simp only [b4_groupEnd, AddMonoidHom.finsetSum_apply, map_sum,
    AddMonoidHom.smul_apply, map_zsmul]
  simp_rw [← AddMonoidHom.comp_apply, ← b4_latticeAct_mul hG]
  have hsq : ∑ h : b4b_Group, b4b_projectorCoeff h •
      b4_latticeAct ℂ (b63d_scalarElement * (b63d_scalarElement * h)) x =
      ∑ k : b4b_Group, b4b_projectorCoeff (b63d_scalarElement * k) •
        b4_latticeAct ℂ k x := by
    convert b63d_sq_reindex (fun k ↦ b4_latticeAct ℂ k x) using 1 <;>
      apply Finset.sum_congr rfl <;> intro h hh <;> congr 3 <;>
        simp only [pow_two, mul_assoc]
  have hone : ∑ h : b4b_Group, b4b_projectorCoeff h •
      b4_latticeAct ℂ (b63d_scalarElement * h) x =
      ∑ k : b4b_Group, b4b_projectorCoeff (b63d_scalarElement⁻¹ * k) •
        b4_latticeAct ℂ k x := by
    exact b63d_one_reindex (fun k ↦ b4_latticeAct ℂ k x)
  rw [hsq, hone, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro h hh
  let y := b4_latticeAct ℂ h x
  have hc : b4b_projectorCoeff (b63d_scalarElement * h) +
      b4b_projectorCoeff (b63d_scalarElement⁻¹ * h) + b4b_projectorCoeff h = 0 := by
    have := b63d_projectorCoeff_scalar h
    omega
  change b4b_projectorCoeff (b63d_scalarElement * h) • y +
      b4b_projectorCoeff (b63d_scalarElement⁻¹ * h) • y +
      b4b_projectorCoeff h • y = 0
  calc
    _ = (b4b_projectorCoeff (b63d_scalarElement * h) +
        b4b_projectorCoeff (b63d_scalarElement⁻¹ * h) + b4b_projectorCoeff h) • y := by
          rw [add_zsmul, add_zsmul]
    _ = 0 := by rw [hc, zero_smul]

theorem b63d_period_saturation_polynomial (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (x : b3_periodLattice ℂ C)
    (hx : x ∈ b63l_saturation
      (b4_groupEnd ℂ (C := C) b4b_projectorCoeff).toIntLinearMap.range) :
    b4_latticeAct ℂ (C := C) b63d_scalarElement
        (b4_latticeAct ℂ (C := C) b63d_scalarElement x) +
      b4_latticeAct ℂ (C := C) b63d_scalarElement x + x = 0 := by
  let T := b4_latticeAct ℂ (C := C) b63d_scalarElement
  let P := (b4_groupEnd ℂ (C := C) b4b_projectorCoeff).toIntLinearMap
  rcases hx with ⟨n, hn, y, hy⟩
  have hP : T (T (P y)) + T (P y) + P y = 0 :=
    b63d_period_projector_polynomial C hG y
  have hy' : P y = n • x := by
    calc
      P y = (inferInstance : Module ℤ (b3_periodLattice ℂ C)).smul n x := hy
      _ = n • x := int_smul_eq_zsmul
        (inferInstance : Module ℤ (b3_periodLattice ℂ C)) n x
  have hnpoly : n • (T (T x) + T x + x) = 0 := by
    calc
      n • (T (T x) + T x + x) = T (T (n • x)) + T (n • x) + n • x := by
        simp only [zsmul_add, map_zsmul]
      _ = T (T (P y)) + T (P y) + P y := by rw [hy']
      _ = 0 := hP
  exact (smul_eq_zero.mp hnpoly).resolve_left hn

end HodgeLean.Foundations.Program
