module

public import Mathlib

/-! # Local analytic Schur reduction at a Fredholm operator -/

@[expose] public noncomputable section

open Set Filter Topology Module

namespace HodgeLean.Foundations

open ContinuousLinearMap in
/-- Pointwise composition of analytic operator-valued maps is analytic.
Composition is a continuous bilinear map. -/
theorem b63r_schur_analyticOnNhd_comp {W X Y Z : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {f : W → Y →L[ℂ] Z} {g : W → X →L[ℂ] Y} {s : Set W}
    (hf : AnalyticOnNhd ℂ f s) (hg : AnalyticOnNhd ℂ g s) :
    AnalyticOnNhd ℂ (fun w => (f w).comp (g w)) s := fun x hx =>
  ((compL ℂ X Y Z).analyticAt_bilinear (f x, g x)).comp₂ (hf x hx) (hg x hx)

open ContinuousLinearMap in
/-- The Schur reduction with respect to a chosen Fredholm package. -/
theorem b63r_schur_pkg {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T₀ : E →L[ℂ] F} (pkg : T₀.FredholmPackage) :
    ∃ 𝒰 : Set (E →L[ℂ] F), IsOpen 𝒰 ∧ T₀ ∈ 𝒰 ∧
      ∃ (M : (E →L[ℂ] F) → pkg.decDom.X₀ →L[ℂ] pkg.decCodom.X₀)
        (L : (E →L[ℂ] F) → pkg.decDom.X₀ →L[ℂ] E),
        AnalyticOnNhd ℂ M 𝒰 ∧ AnalyticOnNhd ℂ L 𝒰 ∧ M T₀ = 0 ∧
        ∀ S ∈ 𝒰, Function.Injective (L S) ∧
          (M S).ker.map (L S).toLinearMap = S.ker := by
  set X₁ := pkg.decDom.X₁
  set K := pkg.decDom.X₀
  set R := pkg.decCodom.X₁
  set C := pkg.decCodom.X₀
  have hdom : Submodule.IsTopCompl X₁ K := pkg.decDom.isTopCompl
  have hcod : Submodule.IsTopCompl R C := pkg.decCodom.isTopCompl
  have : CompleteSpace X₁ := hdom.isClosed.isComplete.completeSpace_coe
  let Q : F →L[ℂ] R := R.projectionOntoL C hcod
  let P : F →L[ℂ] C := C.projectionOntoL R hcod.symm
  obtain ⟨e, he⟩ := pkg.eventually_nhds_isInvertible.self_of_nhds
  let A : (E →L[ℂ] F) → (X₁ →L[ℂ] X₁) := fun S =>
    (e.symm : R →L[ℂ] X₁) ∘L Q ∘L S ∘L X₁.subtypeL
  let G : (E →L[ℂ] F) → (F →L[ℂ] X₁) := fun S =>
    Ring.inverse (A S) ∘L (e.symm : R →L[ℂ] X₁) ∘L Q
  let L : (E →L[ℂ] F) → (K →L[ℂ] E) := fun S =>
    K.subtypeL - X₁.subtypeL ∘L G S ∘L S ∘L K.subtypeL
  let M : (E →L[ℂ] F) → (K →L[ℂ] C) := fun S => P ∘L S ∘L L S
  have hA : AnalyticOnNhd ℂ A univ :=
    b63r_schur_analyticOnNhd_comp analyticOnNhd_const
      (b63r_schur_analyticOnNhd_comp analyticOnNhd_const
        (b63r_schur_analyticOnNhd_comp analyticOnNhd_id analyticOnNhd_const))
  let 𝒰 : Set (E →L[ℂ] F) := {S | IsUnit (A S)}
  have hInv : AnalyticOnNhd ℂ (fun S => Ring.inverse (A S)) 𝒰 := by
    intro S hS
    have h := analyticAt_inverse (𝕜 := ℂ) hS.unit
    rw [hS.unit_spec] at h
    exact h.comp (hA S trivial)
  have hG : AnalyticOnNhd ℂ G 𝒰 :=
    b63r_schur_analyticOnNhd_comp hInv analyticOnNhd_const
  have hL : AnalyticOnNhd ℂ L 𝒰 :=
    analyticOnNhd_const.sub (b63r_schur_analyticOnNhd_comp analyticOnNhd_const
      (b63r_schur_analyticOnNhd_comp hG
        (b63r_schur_analyticOnNhd_comp analyticOnNhd_id analyticOnNhd_const)))
  have hM : AnalyticOnNhd ℂ M 𝒰 :=
    b63r_schur_analyticOnNhd_comp analyticOnNhd_const
      (b63r_schur_analyticOnNhd_comp analyticOnNhd_id hL)
  have hAT₀ : A T₀ = 1 := by
    refine ContinuousLinearMap.ext fun x => ?_
    have h : e x = Q (T₀ x) := congrArg (fun f : X₁ →L[ℂ] R => f x) he
    show e.symm (Q (T₀ x)) = x
    rw [← h, ContinuousLinearEquiv.symm_apply_apply]
  have h𝒰 : IsOpen 𝒰 :=
    Units.isOpen.preimage (continuousOn_univ.mp hA.continuousOn)
  refine ⟨𝒰, h𝒰, by simp [𝒰, hAT₀], M, L, hM, hL, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun k => ?_
    show P _ = 0
    have hR : T₀.range = R := pkg.range_eq
    rw [Submodule.projectionOntoL_apply_eq_zero_iff, ← hR]
    exact LinearMap.mem_range_self _ _
  intro S hS
  have hl : ∀ x : X₁, G S (S x) = x := fun x => by
    show Ring.inverse (A S) (A S x) = x
    rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hS]
    rfl
  have hr : ∀ y : F, Q (S (G S y)) = Q y := fun y => by
    have h : A S (Ring.inverse (A S) (e.symm (Q y))) = e.symm (Q y) := by
      rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel _ hS]
      rfl
    exact e.symm.injective h
  have hQP : ∀ w : F, Q w = 0 → P w = 0 → w = 0 := fun w h1 h2 => by
    have h := Submodule.projectionL_add_projectionL_eq_self hcod w
    rw [← Submodule.coe_projectionOntoL_apply, ← Submodule.coe_projectionOntoL_apply] at h
    rw [← h]
    change ((Q w : R) : F) + ((P w : C) : F) = 0
    rw [h1, h2]
    simp
  have hLk : ∀ k : K, L S k = (k : E) - (G S (S k) : E) := fun k => rfl
  refine ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero (L S)).2 fun k hk => ?_
    rw [hLk, sub_eq_zero] at hk
    have h0 : (k : E) = 0 :=
      Submodule.disjoint_def.1 hdom.isCompl.disjoint _ (hk ▸ (G S (S k)).2) k.2
    exact Subtype.ext h0
  · ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine hQP _ ?_ hk
      rw [hLk, map_sub, map_sub, hr, sub_self]
    · intro hy
      let x₁ : X₁ := X₁.projectionOntoL K hdom y
      let k : K := K.projectionOntoL X₁ hdom.symm y
      have hy' : y = (x₁ : E) + (k : E) := by
        have h := Submodule.projectionL_add_projectionL_eq_self hdom y
        rw [← Submodule.coe_projectionOntoL_apply, ← Submodule.coe_projectionOntoL_apply] at h
        exact h.symm
      have hGk : G S (S k) = -x₁ := by
        have h : G S (S y) = 0 := by rw [hy, map_zero]
        rw [hy', map_add, map_add, hl] at h
        exact eq_neg_of_add_eq_zero_right h
      have hLy : L S k = y := by
        rw [hLk, hGk, hy']
        simp
        abel
      refine ⟨k, ?_, hLy⟩
      show P (S (L S k)) = 0
      rw [hLy, hy, map_zero]

open ContinuousLinearMap in
theorem b63r_schur_core {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T₀ : E →L[ℂ] F) (hT₀ : T₀.IsFredholm) :
    ∃ 𝒰 : Set (E →L[ℂ] F), IsOpen 𝒰 ∧ T₀ ∈ 𝒰 ∧
      ∃ (M : (E →L[ℂ] F) → (Fin (finrank ℂ (T₀.ker)) → ℂ) →L[ℂ]
          (Fin (finrank ℂ (F ⧸ T₀.range)) → ℂ))
        (L : (E →L[ℂ] F) → (Fin (finrank ℂ (T₀.ker)) → ℂ) →L[ℂ] E),
        AnalyticOnNhd ℂ M 𝒰 ∧ AnalyticOnNhd ℂ L 𝒰 ∧ M T₀ = 0 ∧
        ∀ S ∈ 𝒰, Function.Injective (L S) ∧
          (M S).ker.map (L S).toLinearMap = S.ker := by
  obtain ⟨pkg⟩ := hT₀.nonempty_fredholmPackage
  obtain ⟨𝒰, h𝒰, hT₀𝒰, M, L, hM, hL, hM0, hS⟩ := b63r_schur_pkg pkg
  have := pkg.decDom.finite_X₀
  have := pkg.decCodom.finite_X₀
  have hK : finrank ℂ (Fin (finrank ℂ T₀.ker) → ℂ) = finrank ℂ pkg.decDom.X₀ := by
    rw [Module.finrank_fin_fun, pkg.ker_eq]
  have hC : finrank ℂ pkg.decCodom.X₀ = finrank ℂ (Fin (finrank ℂ (F ⧸ T₀.range)) → ℂ) := by
    rw [Module.finrank_fin_fun, pkg.range_eq]
    exact (Submodule.quotientEquivOfIsCompl _ _ pkg.decCodom.isTopCompl.isCompl).finrank_eq.symm
  let eK := ContinuousLinearEquiv.ofFinrankEq hK
  let eC := ContinuousLinearEquiv.ofFinrankEq hC
  refine ⟨𝒰, h𝒰, hT₀𝒰, fun S => (eC : _ →L[ℂ] _) ∘L M S ∘L (eK : _ →L[ℂ] _),
    fun S => L S ∘L (eK : _ →L[ℂ] _), ?_, ?_, ?_, ?_⟩
  · exact b63r_schur_analyticOnNhd_comp analyticOnNhd_const
      (b63r_schur_analyticOnNhd_comp hM analyticOnNhd_const)
  · exact b63r_schur_analyticOnNhd_comp hL analyticOnNhd_const
  · simp [hM0]
  · intro S hS'
    refine ⟨(hS S hS').1.comp eK.injective, ?_⟩
    rw [← (hS S hS').2]
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, comp_apply,
      ContinuousLinearEquiv.coe_coe]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨eK v, (map_eq_zero_iff eC eC.injective).1 hv, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨eK.symm k, by simp [hk], by simp⟩

end HodgeLean.Foundations
