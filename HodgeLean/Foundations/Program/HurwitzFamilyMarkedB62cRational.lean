import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cGeneration
import Mathlib.Algebra.Category.Grp.Injective

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters

theorem b6m_chainQuotient_rational_cocycle (Y : SSet.{0})
    (F : b6m_chainQuotient Y →+ ℚ) :
    ∃ ψ : Simplicial.Cocycle ℚ Y 1, ∀ σ : Y.obj (Opposite.op (SimplexCategory.mk 1)),
      ψ.1 (Simplicial.chainOfSimplex ℚ σ) =
        F (b6m_chainQuotientMap Y (Simplicial.chainOfSimplex ℤ σ)) := by
  let f := fun σ : Y.obj (Opposite.op (SimplexCategory.mk 1)) ↦
    F (b6m_chainQuotientMap Y (Simplicial.chainOfSimplex ℤ σ))
  have hf : ∀ τ : Y.obj (Opposite.op (SimplexCategory.mk 2)),
      f (Y.δ 0 τ) - f (Y.δ 1 τ) + f (Y.δ 2 τ) = 0 := by
    intro τ
    have h := congrArg F (b6m_chainQuotient_triangle Y τ)
    simpa only [map_add, map_sub, map_zero] using h
  refine ⟨⟨simplexCochain ℚ Y 1 f, ?_⟩, fun σ ↦
    spec_simplexCochain_chainOfSimplex_aux ℚ Y 1 f σ⟩
  refine LinearMap.mem_ker.mpr (cochain_ext_simplex_b3Rest2 _ _ fun τ ↦ ?_)
  rw [Simplicial.coboundary_chainOfSimplex, LinearMap.zero_apply]
  simpa [Fin.sum_univ_succ, spec_simplexCochain_chainOfSimplex_aux,
    sub_eq_add_neg, add_assoc] using hf τ

set_option backward.isDefEq.respectTransparency false in
theorem b6m_homology_rational_cocycle (T : Type) [TopologicalSpace T]
    (f : b6m_H1 T →ₗ[ℤ] ℚ) :
    ∃ ψ : Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of T)) 1,
      ∀ p : C(UnitAddCircle, T),
        ψ.1 (Simplicial.chainOfSimplex ℚ (loopSimplex p)) =
          f (((SingularChainComplex ℤ (TopCat.of T)).sc 1).moduleCatHomologyClass
            (loopCycle ℤ p)) := by
  obtain ⟨j, hj, hJ⟩ := b6m_homology_chain_embedding T
  obtain ⟨F, hF⟩ := (Module.Baer.of_divisible ℚ).extension_property j hj f
  obtain ⟨ψ, hψ⟩ := b6m_chainQuotient_rational_cocycle _ F.toAddMonoidHom
  refine ⟨ψ, fun p ↦ ?_⟩
  exact (hψ (loopSimplex p)).trans
    ((congrArg F (hJ (loopCycle ℤ p)).symm).trans
      (LinearMap.congr_fun hF _))

open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false in
theorem b6m_rational_functional_period (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (P : b6m_H1 C →ₗ[ℤ] (b3_HolForm ℂ C → ℂ))
    (hP : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_period ℂ C γ)
    (f : b6m_H1 C →ₗ[ℤ] ℚ) :
    ∃ θ : b3_HolForm ℂ C, ∀ x : b6m_H1 C, (f x : ℝ) = (P x θ).re := by
  obtain ⟨ψ, hψ⟩ := b6m_homology_rational_cocycle C f
  obtain ⟨θ, hθ⟩ := b3Rest2_cocycle_form (E := ℂ) (C := C) (by simp) ψ
  let r : b6m_H1 C →ₗ[ℤ] ℝ :=
    (Rat.castHom ℝ).toAddMonoidHom.toIntLinearMap.comp f
  let s : b6m_H1 C →ₗ[ℤ] ℝ :=
    Complex.reAddGroupHom.toIntLinearMap.comp ((LinearMap.proj θ).comp P)
  have hrs : r = s := by
    apply b6m_homology_linearMap_ext C
    intro γ
    change (f (b6m_loopClass C γ) : ℝ) = (P (b6m_loopClass C γ) θ).re
    rw [hP]
    have h := hθ γ (b3Rest2_circ γ) (b3Rest2_circ_apply γ)
    rw [hψ] at h
    exact h
  exact ⟨θ, fun x ↦ LinearMap.congr_fun hrs x⟩

set_option backward.isDefEq.respectTransparency false in
theorem b6m_torsion_of_rational_functionals_zero (M : Type*) [AddCommGroup M]
    (x : M) (hx : ∀ f : M →ₗ[ℤ] ℚ, f x = 0) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x = 0 := by
  by_contra h
  have hn : ∀ n : ℤ, n • x = 0 → n = 0 := by
    intro n hn
    by_contra hn0
    exact h ⟨n, hn0, hn⟩
  let i : ℤ →ₗ[ℤ] M := LinearMap.toSpanSingleton ℤ M x
  have hi : Function.Injective i := by
    intro a b hab
    apply sub_eq_zero.mp
    apply hn
    rw [sub_zsmul]
    simpa only [i, LinearMap.toSpanSingleton_apply, sub_eq_add_neg] using sub_eq_zero.mpr hab
  let g : ℤ →ₗ[ℤ] ℚ := (Int.castAddHom ℚ).toIntLinearMap
  obtain ⟨F, hF⟩ := (Module.Baer.of_divisible ℚ).extension_property i hi g
  have h1 : F x = 1 := by simpa [i, g] using LinearMap.congr_fun hF 1
  rw [hx F] at h1
  exact zero_ne_one h1

set_option backward.isDefEq.respectTransparency false in
theorem b6m_period_zero_iff_torsion (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (P : b6m_H1 C →ₗ[ℤ] (b3_HolForm ℂ C → ℂ))
    (hP : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_period ℂ C γ)
    (x : b6m_H1 C) : P x = 0 ↔ ∃ n : ℤ, n ≠ 0 ∧ n • x = 0 := by
  constructor
  · intro hx
    apply b6m_torsion_of_rational_functionals_zero
    intro f
    let f' : b6m_H1 C →ₗ[ℤ] ℚ :=
      { toFun := f
        map_add' := map_add f
        map_smul' := by
          intro n y
          change f ((b6m_H1 C).isModule.smul n y) = n • f y
          rw [int_smul_eq_zsmul]
          exact map_zsmul f n y }
    obtain ⟨θ, hθ⟩ := b6m_rational_functional_period C P hP f'
    have h := hθ x
    rw [hx] at h
    have hzero : (f x : ℝ) = 0 := h
    exact_mod_cast hzero
  · rintro ⟨n, hn, hx⟩
    have h : n • P x = 0 := (map_zsmul P n x).symm.trans
      ((congrArg P hx).trans (map_zero P))
    exact (smul_eq_zero.mp h).resolve_left hn

set_option backward.isDefEq.respectTransparency false in
theorem b6m_period_lattice_kernel (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (P : b6m_H1 C →ₗ[ℤ] b3_periodLattice ℂ C)
    (hP : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ) :
    LinearMap.ker P = Submodule.torsion ℤ (b6m_H1 C) := by
  let F : b6m_H1 C →ₗ[ℤ] (b3_HolForm ℂ C → ℂ) :=
    (b3_periodLattice ℂ C).toIntSubmodule.subtype.comp P
  have hF : ∀ γ : b3_SmoothLoop ℂ C, F (b6m_loopClass C γ) = b3_period ℂ C γ :=
    fun γ ↦ congrArg Subtype.val (hP γ)
  ext x
  have hzero : P x = 0 ↔ F x = 0 :=
    ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩
  rw [LinearMap.mem_ker, hzero, b6m_period_zero_iff_torsion C F hF x]
  constructor
  · rintro ⟨n, hn, hx⟩
    apply (Submodule.mem_torsion_iff x).mpr
    refine ⟨⟨n, mem_nonZeroDivisors_iff_ne_zero.mpr hn⟩, ?_⟩
    change (b6m_H1 C).isModule.smul n x = 0
    rw [int_smul_eq_zsmul]
    exact hx
  · intro hx
    obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff x).mp hx
    change (b6m_H1 C).isModule.smul n.1 x = 0 at hn
    rw [int_smul_eq_zsmul] at hn
    exact ⟨n.1, mem_nonZeroDivisors_iff_ne_zero.mp n.2, hn⟩

set_option backward.isDefEq.respectTransparency false in
theorem b6m_period_quotient_comparison (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] :
    ∃ P : (b6m_H1 C ⧸ Submodule.torsion ℤ (b6m_H1 C)) ≃ₗ[ℤ] b3_periodLattice ℂ C,
      ∀ γ : b3_SmoothLoop ℂ C,
        P (Submodule.Quotient.mk (b6m_loopClass C γ)) = b3_latticePeriod ℂ C γ := by
  obtain ⟨P, hsurj, hP⟩ := b6m_period_lattice_map_exists C
  have hk := b6m_period_lattice_kernel C P hP
  let e := (Submodule.quotEquivOfEq _ _ hk.symm).trans
    (P.quotKerEquivOfSurjective hsurj)
  let E : (b6m_H1 C ⧸ Submodule.torsion ℤ (b6m_H1 C)) ≃ₗ[ℤ] b3_periodLattice ℂ C :=
    { toFun := e
      invFun := e.symm
      left_inv := e.toEquiv.left_inv
      right_inv := e.toEquiv.right_inv
      map_add' := e.map_add
      map_smul' := fun n x ↦ map_zsmul e n x }
  refine ⟨E, fun γ ↦ ?_⟩
  change P.quotKerEquivOfSurjective hsurj
    (Submodule.Quotient.mk (b6m_loopClass C γ)) = b3_latticePeriod ℂ C γ
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]
  exact hP γ

set_option backward.isDefEq.respectTransparency false in
theorem b6m_period_comparison_of_torsionFree (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [Module.IsTorsionFree ℤ (b6m_H1 C)] :
    ∃ P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C,
      ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ := by
  obtain ⟨P, hsurj, hP⟩ := b6m_period_lattice_map_exists C
  have ht : Submodule.torsion ℤ (b6m_H1 C) = ⊥ :=
    Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance
  have hi : Function.Injective P := LinearMap.ker_eq_bot.mp
    ((b6m_period_lattice_kernel C P hP).trans ht)
  exact ⟨LinearEquiv.ofBijective P ⟨hi, hsurj⟩, hP⟩

end HodgeLean.Foundations.Program
