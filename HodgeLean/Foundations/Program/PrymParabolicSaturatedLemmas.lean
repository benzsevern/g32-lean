import HodgeLean.Foundations.Program.PrymParabolicSaturatedDefs
import HodgeLean.Foundations.Program.PrymVariationCentrePolynomial
import HodgeLean.Foundations.Program.PrymVariationCentreSaturation

/-! # Lemmas for stage H5, first part: rank, the cyclotomic relation and transport

Helper lemmas for `PrymParabolicSaturatedProofs.lean`: the cyclotomic relation `1 + Z + Z² = 0`
on the image of the primitive operator of any multiplicative family, its extension to the
saturation in a torsion-free module, the rank of the saturated cellular lattice, and the
transport of saturated images along an intertwining equivalence.
HC no distance; AV milestone no distance.
-/

noncomputable section

open HodgeLean.Papers
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

/-! ## Group-ring operators and saturation, with the additive `ℤ`-action -/

theorem hg6_projOf_apply {M : Type*} [AddCommGroup M] [Module ℤ M]
    (ρ : b4b_Group → M →ₗ[ℤ] M) (x : M) :
    hg6_projOf ρ x = ∑ h, b4b_projectorCoeff h • ρ h x := by
  rw [hg6_projOf, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  let ev : (M →ₗ[ℤ] M) →+ M := ⟨⟨fun f => f x, rfl⟩, fun _ _ => rfl⟩
  exact map_zsmul ev _ _

theorem hg6_mem_saturation_iff {M : Type*} [AddCommGroup M] [Module ℤ M]
    (L : Submodule ℤ M) (x : M) :
    x ∈ b63l_saturation L ↔ ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ L := by
  constructor
  · rintro ⟨n, hn, h⟩
    refine ⟨n, hn, ?_⟩
    convert h using 1
    exact (int_smul_eq_zsmul _ _ _).symm
  · rintro ⟨n, hn, h⟩
    refine ⟨n, hn, ?_⟩
    convert h using 1
    exact int_smul_eq_zsmul _ _ _

theorem hg6_zsmul_eq_zero {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.IsTorsionFree ℤ M] {n : ℤ} (hn : n ≠ 0) {x : M} (h : n • x = 0) : x = 0 := by
  rw [← int_smul_eq_zsmul inferInstance] at h
  exact (smul_eq_zero.mp h).resolve_left hn

/-! ## The cyclotomic relation -/

set_option maxHeartbeats 400000 in
/-- For a multiplicative family `ρ`, the central element `z₀` satisfies
`ρ(z₀)² P + ρ(z₀) P + P = 0` on the image of the primitive operator `P = hg6_projOf ρ`. -/
theorem hg6_projector_polynomial {M : Type*} [AddCommGroup M] [Module ℤ M]
    (ρ : b4b_Group → M →ₗ[ℤ] M) (hmul : ∀ h k x, ρ h (ρ k x) = ρ (h * k) x) (x : M) :
    ρ b63d_scalarElement (ρ b63d_scalarElement (hg6_projOf ρ x)) +
      ρ b63d_scalarElement (hg6_projOf ρ x) + hg6_projOf ρ x = 0 := by
  simp only [hg6_projOf_apply, map_sum, map_zsmul, hmul]
  have hsq : ∑ h : b4b_Group, b4b_projectorCoeff h •
      ρ (b63d_scalarElement * (b63d_scalarElement * h)) x =
      ∑ k : b4b_Group, b4b_projectorCoeff (b63d_scalarElement * k) • ρ k x := by
    convert b63d_sq_reindex (fun k ↦ ρ k x) using 1
    apply Finset.sum_congr rfl
    intro h _
    rw [pow_two, mul_assoc]
  have hone : ∑ h : b4b_Group, b4b_projectorCoeff h • ρ (b63d_scalarElement * h) x =
      ∑ k : b4b_Group, b4b_projectorCoeff (b63d_scalarElement⁻¹ * k) • ρ k x :=
    b63d_one_reindex (fun k ↦ ρ k x)
  rw [hsq, hone, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro h _
  have hc : b4b_projectorCoeff (b63d_scalarElement * h) +
      b4b_projectorCoeff (b63d_scalarElement⁻¹ * h) + b4b_projectorCoeff h = 0 := by
    have := b63d_projectorCoeff_scalar h
    omega
  rw [← add_zsmul, ← add_zsmul, hc, zero_zsmul]

/-- The cyclotomic relation extends to the saturation of the image in a torsion-free module. -/
theorem hg6_saturation_polynomial {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.IsTorsionFree ℤ M]
    (ρ : b4b_Group → M →ₗ[ℤ] M) (hmul : ∀ h k x, ρ h (ρ k x) = ρ (h * k) x) (x : M)
    (hx : x ∈ b63l_saturation (LinearMap.range (hg6_projOf ρ))) :
    ρ b63d_scalarElement (ρ b63d_scalarElement x) + ρ b63d_scalarElement x + x = 0 := by
  obtain ⟨n, hn, y, hy⟩ := (hg6_mem_saturation_iff _ _).mp hx
  have hP := hg6_projector_polynomial ρ hmul y
  rw [hy] at hP
  refine hg6_zsmul_eq_zero hn ?_
  rw [← hP]
  simp only [map_zsmul, zsmul_add]

theorem hg6_H1act_mul_apply (h k : b4b_Group) (x : hg2_H1 ℤ b4b_root) :
    hg2_H1act ℤ b4b_root h (hg2_H1act ℤ b4b_root k x) = hg2_H1act ℤ b4b_root (h * k) x :=
  LinearMap.congr_fun (hg2_H1act_mul ℤ b4b_root h k) x

instance hg6_H1_free : Module.Free ℤ (hg2_H1 ℤ b4b_root) := (hg2_H1_finite_free b4b_root).1

instance hg6_H1_finite : Module.Finite ℤ (hg2_H1 ℤ b4b_root) := (hg2_H1_finite_free b4b_root).2

instance hg6_H1_torsionFree : Module.IsTorsionFree ℤ (hg2_H1 ℤ b4b_root) := inferInstance

/-! ## Statement 2 -/

theorem hg6_cellOperator_sq_lemma (x : hg6_cellLattice) :
    hg6_cellOperator (hg6_cellOperator x) = (-3 : ℤ) • x := by
  let T := hg2_H1act ℤ b4b_root b63d_scalarElement
  have hp : T (T x.val) + T x.val + x.val = 0 :=
    hg6_saturation_polynomial (hg2_H1act ℤ b4b_root) hg6_H1act_mul_apply x.val x.property
  have hJ (u : hg6_cellLattice) : (hg6_cellOperator u).val = u.val + 2 • T u.val := by
    change u.val + 2 • hg6_cellCentre u.val = _
    rw [hg6_cellCentre, hg6_centreOf_eq]
  apply Subtype.ext
  rw [hJ, hJ]
  change (x.val + 2 • T x.val) + 2 • T (x.val + 2 • T x.val) = (-3 : ℤ) • x.val
  rw [map_add, map_nsmul, ← sub_eq_zero]
  calc
    (x.val + 2 • T x.val + 2 • (T x.val + 2 • T (T x.val))) - (-3 : ℤ) • x.val =
        4 • (T (T x.val) + T x.val + x.val) := by
      simp only [smul_add, neg_smul, sub_neg_eq_add]
      module
    _ = 0 := by rw [hp, smul_zero]

/-! ## Statement 1 -/

theorem hg6_cellLattice_finrank : Module.finrank ℤ hg6_cellLattice = 12 := by
  obtain ⟨E, -⟩ := b63d_saturation_complex_equiv (LinearMap.range hg2_projector)
  have h1 := E.finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_baseChange, hg2_projector_rank] at h1
  exact h1.symm

theorem hg6_cellLattice_basis_lemma : Nonempty (Module.Basis (Fin 12) ℤ hg6_cellLattice) :=
  ⟨Module.finBasisOfFinrankEq ℤ hg6_cellLattice hg6_cellLattice_finrank⟩

/-! ## Statement 3 -/

theorem hg6_projOf_intertwine {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N]
    (ρ : b4b_Group → M →ₗ[ℤ] M) (ρ' : b4b_Group → N →ₗ[ℤ] N) (e : M →ₗ[ℤ] N)
    (he : ∀ h x, e (ρ h x) = ρ' h (e x)) (x : M) :
    e (hg6_projOf ρ x) = hg6_projOf ρ' (e x) := by
  simp only [hg6_projOf_apply, map_sum, map_zsmul, he]

theorem hg6_saturated_transport_lemma {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N]
    (ρ : b4b_Group → M →ₗ[ℤ] M) (ρ' : b4b_Group → N →ₗ[ℤ] N) (e : M ≃ₗ[ℤ] N)
    (he : ∀ h x, e (ρ h x) = ρ' h (e x)) :
    (b63l_saturation (LinearMap.range (hg6_projOf ρ))).map (e : M →ₗ[ℤ] N) =
        b63l_saturation (LinearMap.range (hg6_projOf ρ')) ∧
      ∀ x, e (hg6_centreOf ρ x) = hg6_centreOf ρ' (e x) := by
  have hP := hg6_projOf_intertwine ρ ρ' (e : M →ₗ[ℤ] N) he
  have he' : ∀ h y, e.symm (ρ' h y) = ρ h (e.symm y) := fun h y => by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
  have hP' := hg6_projOf_intertwine ρ' ρ (e.symm : N →ₗ[ℤ] M) he'
  refine ⟨?_, fun x => by rw [hg6_centreOf_eq, hg6_centreOf_eq, he]⟩
  ext y
  rw [Submodule.mem_map, hg6_mem_saturation_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨n, hn, u, hu⟩ := (hg6_mem_saturation_iff _ _).mp hx
    refine ⟨n, hn, e u, ?_⟩
    have := hP u
    simp only [LinearEquiv.coe_coe] at this
    rw [← this, hu, map_zsmul]
    rfl
  · rintro ⟨n, hn, v, hv⟩
    refine ⟨e.symm y, (hg6_mem_saturation_iff _ _).mpr ⟨n, hn, e.symm v, ?_⟩,
      e.apply_symm_apply y⟩
    have := hP' v
    simp only [LinearEquiv.coe_coe] at this
    rw [← this, hv, map_zsmul]

end HodgeLean.Foundations.Program
