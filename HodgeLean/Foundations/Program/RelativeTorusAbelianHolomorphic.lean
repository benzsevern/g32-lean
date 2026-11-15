import HodgeLean.Foundations.Program.RelativeTorusAbelianLattice
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Track B2, comparison with abelian varieties: holomorphy

Helpers for `RelativeTorusAbelianProofs.lean`. The inverse chart of `b2_torusChart` at `t` is the
quotient map in linear coordinates, so holomorphy out of the torus is holomorphy of the lift to
`ℂ^n`. The exponential of `X(ℂ)` has a holomorphic local inverse at `0` in the identity chart
(holomorphic inverse function theorem, its derivative there being the identity), and translating
it gives a holomorphic local inverse of the comparison map at every point.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Manifold
open scoped TensorProduct ContDiff CategoryTheory.MonObj Topology
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open Filter

namespace HodgeLean.Foundations.Program

section General

/-- Holomorphy at `x` follows from continuity at `x` and holomorphy of the map in the chart at `x`
(no compatibility of the source atlas is needed: this is the definition). -/
theorem b2a_contMDiffAt_of_chart_symm {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] {M N : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace E' N] {f : M → N} {x : M}
    (hc : ContinuousAt f x)
    (hg : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E') ω (f ∘ (chartAt E x).symm) (chartAt E x x)) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E') ω f x := by
  rw [contMDiffAt_iff] at hg ⊢
  refine ⟨hc, ?_⟩
  have h1 : (f ∘ (chartAt E x).symm) (chartAt E x x) = f x := by
    simp [(chartAt E x).left_inv (mem_chart_source E x)]
  have h := hg.2
  rw [h1, extChartAt_model_space_eq_id] at h
  simpa [extChartAt_coe, extChartAt_coe_symm, Function.comp_def] using h

variable (Λ : Type*) [AddCommGroup Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))

/-- The inverse of the torus chart is the quotient map in linear coordinates. -/
theorem b2a_torusChart_symm_apply [Module.Finite ℤ Λ]
    [DiscreteTopology (b2_latticeMap Λ F).range] (t : b2_torus Λ F)
    (y : Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) :
    (b2_torusChart Λ F t).symm y = QuotientAddGroup.mk ((b2_coordHomeomorph Λ F).symm y) := by
  rw [b2_torusChart, OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm]
  exact (congrFun (Classical.choose_spec (b2_isLocalHomeomorph_mk Λ F t.out)).2 _).symm

end General

section Abelian

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The induced linear map `(ℂ ⊗ Λ_X) ⧸ F_X → ℂ^g`.
Source: Birkenhake–Lange, §1.1; Mathlib `Submodule.liftQ`. -/
abbrev b2a_evalQ : ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X) →ₗ[ℂ] (Fin (dim X.left) → ℂ) :=
  (b2_abelianF X).liftQ (b2_abelianEval X) le_rfl

example (u : ℂ ⊗[ℤ] b2_abelianLattice X) :
    b2a_evalQ X (Submodule.Quotient.mk u) = b2_abelianEval X u := rfl

theorem b2a_toPoint_mk' (q : (ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X) :
    b2_abelianToPoint X (QuotientAddGroup.mk q) =
      complexExponential X (dim X.left) (b2a_evalQ X q) := rfl

theorem b2a_toPoint_continuous :
    Continuous (fun t : b2_torus (b2_abelianLattice X) (b2_abelianF X) ↦
      Additive.toMul (b2_abelianToPoint X t)) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  apply QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
  change Continuous fun q ↦ Additive.toMul (complexExponential X (dim X.left) (b2a_evalQ X q))
  exact continuous_toMul.comp ((continuous_complexExponential X (dim X.left)).comp
    (IsModuleTopology.continuous_of_linearMap _))

theorem b2a_toPoint_contMDiff
    [DiscreteTopology (b2_latticeMap (b2_abelianLattice X) (b2_abelianF X)).range] :
    ContMDiff
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X)) → ℂ)
      𝓘(ℂ, Fin (dim X.left) → ℂ) ω (fun t ↦ Additive.toMul (b2_abelianToPoint X t)) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  intro t
  apply b2a_contMDiffAt_of_chart_symm (b2a_toPoint_continuous X).continuousAt
  let Lin := (b2a_evalQ X).comp (b2_coord ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X)).symm.toLinearMap
  have h : (fun t ↦ Additive.toMul (b2_abelianToPoint X t)) ∘
      (chartAt (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X)) → ℂ) t).symm =
      fun y ↦ Additive.toMul (complexExponential X (dim X.left) (Lin y)) := by
    funext y
    change Additive.toMul (b2_abelianToPoint X ((b2_torusChart _ _ t).symm y)) = _
    rw [b2a_torusChart_symm_apply, b2a_toPoint_mk']
    rfl
  rw [h]
  exact ((spec_contMDiff_complexExponential X (dim X.left)).comp
    (LinearMap.toContinuousLinearMap Lin).contDiff.contMDiff).contMDiffAt

omit [IsProjective X.hom] in
/-- **A holomorphic local inverse of the exponential** at `0`, in the identity chart: the chart
expression `E` of `exp` is analytic at `0` with real derivative the identity, so its complex
derivative is the identity and the holomorphic inverse function theorem applies. -/
theorem b2a_exp_localInverse [IsCommMonObj X] :
    ∃ L : (Fin (dim X.left) → ℂ) → (Fin (dim X.left) → ℂ), ContDiffAt ℂ ω L 0 ∧ L 0 = 0 ∧
      ∀ᶠ z in 𝓝 0, identityChart X (dim X.left)
        (Additive.toMul (complexExponential X (dim X.left) (L z))) = z := by
  set E : (Fin (dim X.left) → ℂ) → (Fin (dim X.left) → ℂ) := fun w ↦
    identityChart X (dim X.left) (Additive.toMul (complexExponential X (dim X.left) w)) with hEdef
  have hE : AnalyticAt ℂ E 0 := spec_analyticAt_complexExponential_chart X (dim X.left)
  have hR : HasFDerivAt E (ContinuousLinearMap.id ℝ (Fin (dim X.left) → ℂ)) 0 :=
    hasFDerivAt_complexExponential_chart X (dim X.left)
  have hd : HasFDerivAt E (fderiv ℂ E 0) 0 := hE.differentiableAt.hasFDerivAt
  have hd' : HasFDerivAt E
      ((ContinuousLinearEquiv.refl ℂ (Fin (dim X.left) → ℂ)) :
        (Fin (dim X.left) → ℂ) →L[ℂ] (Fin (dim X.left) → ℂ)) 0 := by
    have heq := (hd.restrictScalars ℝ).unique hR
    convert hd using 1
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have := DFunLike.congr_fun heq v
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.coe_id',
      id_eq] at this
    simp [this]
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hc : ContDiffAt ℂ ω E 0 := hE.contDiffAt
  have hs := hc.hasStrictFDerivAt' hd' hn
  have hE0 : E 0 = 0 := by
    simp only [hEdef, complexExponential_zero, toMul_zero, identityChart_one]
  refine ⟨hs.localInverse E _ 0, ?_, ?_, ?_⟩
  · have := hc.to_localInverse hd' hn
    rwa [hE0] at this
  · have := hs.localInverse_apply_image
    rwa [hE0] at this
  · have := hs.eventually_right_inverse
    rwa [hE0] at this

/-- The linear isomorphism `(ℂ ⊗ Λ_X) ⧸ F_X ≃ ℂ^g` induced by the evaluation.
Source: Birkenhake–Lange, §1.1; Mathlib `LinearMap.quotKerEquivOfSurjective`. -/
def b2a_evalEquiv :
    ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X) ≃ₗ[ℂ] (Fin (dim X.left) → ℂ) :=
  (b2_abelianEval X).quotKerEquivOfSurjective (b2a_eval_surjective X)

example (u : ℂ ⊗[ℤ] b2_abelianLattice X) :
    b2a_evalEquiv X (Submodule.Quotient.mk u) = b2_abelianEval X u := rfl

theorem b2a_evalQ_eq (q : (ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X) :
    b2a_evalQ X q = b2a_evalEquiv X q := by
  induction q using Submodule.Quotient.induction_on with
  | H u => rfl

/-- The comparison map inverts the exponential: `ψ (exp v) = [[v]]`. -/
theorem b2a_symm_exp (hb : Function.Bijective (b2_abelianToPoint X))
    (v : Fin (dim X.left) → ℂ) :
    (Equiv.ofBijective _ hb).symm (complexExponential X (dim X.left) v) =
      QuotientAddGroup.mk ((b2a_evalEquiv X).symm v) := by
  apply (Equiv.ofBijective _ hb).injective
  rw [Equiv.apply_symm_apply, Equiv.ofBijective_apply, b2a_toPoint_mk', b2a_evalQ_eq,
    LinearEquiv.apply_symm_apply]

/-- **The inverse comparison is holomorphic.** Near `x = exp v₁`, with `v₁` the evaluation of the
chart representative of `ψ x`, `ψ y = [[v₁ + L (φ (x⁻¹ y))]]` for the holomorphic local inverse `L`
of the exponential in the identity chart `φ`; in the torus chart at `ψ x` this is
`y ↦ coord (eval⁻¹ (v₁ + L (φ (x⁻¹ y))))`. -/
theorem b2a_toPoint_symm_contMDiff
    [DiscreteTopology (b2_latticeMap (b2_abelianLattice X) (b2_abelianF X)).range]
    (hb : Function.Bijective (b2_abelianToPoint X)) :
    ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X)) → ℂ) ω
      (fun x : ComplexPoint X ↦ (Equiv.ofBijective _ hb).symm (Additive.ofMul x)) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  obtain ⟨L, hL, hL0, hLinv⟩ := b2a_exp_localInverse X
  intro x
  set ψ := fun x : ComplexPoint X ↦ (Equiv.ofBijective _ hb).symm (Additive.ofMul x) with hψdef
  set t₀ := ψ x
  set e := Classical.choose (b2_isLocalHomeomorph_mk (b2_abelianLattice X) (b2_abelianF X) t₀.out)
  have he := Classical.choose_spec
    (b2_isLocalHomeomorph_mk (b2_abelianLattice X) (b2_abelianF X) t₀.out)
  set Me := b2a_evalEquiv X
  set v₁ := Me t₀.out
  have hv₁ : Additive.toMul (complexExponential X (dim X.left) v₁) = x := by
    have h1 : (Equiv.ofBijective _ hb) t₀ = Additive.ofMul x := Equiv.apply_symm_apply _ _
    have h2 : b2_abelianToPoint X (QuotientAddGroup.mk t₀.out) = Additive.ofMul x := by
      rw [QuotientAddGroup.out_eq']
      exact h1
    rw [b2a_toPoint_mk', b2a_evalQ_eq] at h2
    exact congrArg Additive.toMul h2
  set z : ComplexPoint X → (Fin (dim X.left) → ℂ) := fun y ↦ identityChart X (dim X.left) (x⁻¹ * y)
  have hz : ContMDiffAt 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω z x := by
    have hc : ContMDiffAt 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω
        (chartAt (Fin (dim X.left) → ℂ) (1 : ComplexPoint X)) 1 :=
      contMDiffOn_chart.contMDiffAt
        ((chartAt _ (1 : ComplexPoint X)).open_source.mem_nhds (mem_chart_source _ 1))
    have h1 : ContMDiffAt 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω
        (fun y : ComplexPoint X ↦ identityChart X (dim X.left) y) (x⁻¹ * x) := by
      rw [inv_mul_cancel]
      exact hc.sub contMDiffAt_const
    exact h1.comp x ((spec_contMDiff_mul_left X (dim X.left) x⁻¹) x)
  have hz0 : z x = 0 := by
    simp only [z, inv_mul_cancel, identityChart_one]
  set W : ComplexPoint X → (Fin (dim X.left) → ℂ) := fun y ↦ v₁ + L (z y)
  have hLz : ContinuousAt (fun y ↦ L (z y)) x :=
    hL.continuousAt.comp_of_eq hz.continuousAt hz0
  have hWc : ContinuousAt W x := continuousAt_const.add hLz
  have hWx : W x = v₁ := by simp only [W, hz0, hL0, add_zero]
  have hcont_exp : Continuous fun v ↦ Additive.toMul (complexExponential X (dim X.left) v) :=
    continuous_toMul.comp (continuous_complexExponential X (dim X.left))
  have ha : ∀ᶠ y in 𝓝 x, Additive.toMul (complexExponential X (dim X.left) (W y)) = y := by
    have hzt : Tendsto z (𝓝 x) (𝓝 0) := hz0 ▸ hz.continuousAt.tendsto
    have h1 := hzt.eventually hLinv
    have h2 : ∀ᶠ y in 𝓝 x, x⁻¹ * y ∈ (identityChart X (dim X.left)).source := by
      apply ((spec_contMDiff_mul_left X (dim X.left) x⁻¹).continuous.continuousAt
        (x := x)).preimage_mem_nhds
      rw [inv_mul_cancel]
      exact (identityChart X (dim X.left)).open_source.mem_nhds (mem_localChart_source _ _ 1)
    have h3 : ∀ᶠ y in 𝓝 x, Additive.toMul (complexExponential X (dim X.left) (L (z y))) ∈
        (identityChart X (dim X.left)).source := by
      apply (hcont_exp.continuousAt.comp hLz).preimage_mem_nhds
      simp only [Function.comp_apply, hz0, hL0, complexExponential_zero, toMul_zero]
      exact (identityChart X (dim X.left)).open_source.mem_nhds (mem_localChart_source _ _ 1)
    filter_upwards [h1, h2, h3] with y h1 h2 h3
    have h4 : Additive.toMul (complexExponential X (dim X.left) (L (z y))) = x⁻¹ * y :=
      (identityChart X (dim X.left)).injOn h3 h2 h1
    have hadd := (complexExponentialHom X (dim X.left)).map_add v₁ (L (z y))
    change complexExponential X (dim X.left) (v₁ + L (z y)) =
      complexExponential X (dim X.left) v₁ + complexExponential X (dim X.left) (L (z y)) at hadd
    change Additive.toMul (complexExponential X (dim X.left) (v₁ + L (z y))) = y
    rw [hadd, toMul_add, hv₁, h4, mul_inv_cancel_left]
  have hMc : Continuous Me.symm := IsModuleTopology.continuous_of_linearMap Me.symm.toLinearMap
  have hMW : ContinuousAt (fun y ↦ Me.symm (W y)) x := hMc.continuousAt.comp hWc
  have hsrc : ∀ᶠ y in 𝓝 x, Me.symm (W y) ∈ e.source := by
    apply hMW.preimage_mem_nhds
    rw [hWx, LinearEquiv.symm_apply_apply]
    exact e.open_source.mem_nhds he.1
  have hψ : ∀ᶠ y in 𝓝 x, ψ y = QuotientAddGroup.mk (Me.symm (W y)) := by
    filter_upwards [ha] with y hy
    conv_lhs => rw [← hy]
    change (Equiv.ofBijective _ hb).symm
      (Additive.ofMul (Additive.toMul (complexExponential X (dim X.left) (W y)))) = _
    rw [ofMul_toMul, b2a_symm_exp]
  have hchart : ∀ᶠ y in 𝓝 x,
      (extChartAt 𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X)) → ℂ)
        (ψ x)) (ψ y) =
      b2_coord ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X) (Me.symm (W y)) := by
    filter_upwards [hψ, hsrc] with y h1 h2
    rw [extChartAt_coe, Function.comp_apply, modelWithCornersSelf_coe, id, h1]
    change b2_torusChart _ _ t₀ (QuotientAddGroup.mk (Me.symm (W y))) = _
    rw [show (QuotientAddGroup.mk (Me.symm (W y)) : b2_torus (b2_abelianLattice X)
      (b2_abelianF X)) = e (Me.symm (W y)) from congrFun he.2 _]
    rw [b2_torusChart, OpenPartialHomeomorph.coe_trans, Function.comp_apply, e.left_inv h2]
    rfl
  rw [contMDiffAt_iff_target]
  refine ⟨?_, ?_⟩
  · have hq : ContinuousAt (fun y ↦ (QuotientAddGroup.mk (Me.symm (W y)) :
        b2_torus (b2_abelianLattice X) (b2_abelianF X))) x :=
      QuotientAddGroup.continuous_mk.continuousAt.comp hMW
    exact hq.congr (hψ.mono fun y h ↦ h.symm)
  · let Lc := LinearMap.toContinuousLinearMap
      ((b2_coord ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X)).toLinearMap ∘ₗ
        Me.symm.toLinearMap)
    have hA : ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ)
        𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b2_abelianLattice X) ⧸ b2_abelianF X)) → ℂ) ω
        (fun w ↦ Lc (v₁ + w)) :=
      (Lc.contDiff.comp (contDiff_const.add contDiff_id)).contMDiff
    have hΦ := (hA (L (z x))).comp x (hL.contMDiffAt.comp_of_eq hz hz0)
    exact hΦ.congr_of_eventuallyEq hchart

end Abelian

end HodgeLean.Foundations.Program
