import HodgeLean.Foundations.Program.CurveJacobianRest2Rank

/-! # Track B3, lane Rest2: the period lattice carries a weight-one Hodge structure

* `b3Rest2_isWeightOne_of_ker`: for a finite free `ℤ`-module `Λ` and a `ℂ`-linear map
  `P : ℂ ⊗ Λ → V` with `rk Λ = 2 dim (range P)`, if no nonzero `x` has `P x = P x̄ = 0`, then
  `ker P` is a weight-one filtration: `F ∩ F̄ = 0` directly, and `F + F̄` is everything by counting
  dimensions (`dim F̄ = dim F` through the conjugation, a semilinear bijection).
* For a compact connected Riemann surface, with `P` the complexified period map: writing
  `x = Σ cᵢ ⊗ λᵢ` in a basis of the lattice, `P x = P x̄ = 0` gives `Σ Re cᵢ λᵢ = Σ Im cᵢ λᵢ = 0`;
  the real parts `Re λᵢ` are `rk Λ = 2g = dim_ℝ Ω¹(C)` functionals spanning the real dual of
  `Ω¹(C)` (a form with vanishing real periods is zero), hence independent, and `c = 0`.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold
open scoped TensorProduct ContDiff

namespace HodgeLean.Foundations.Program

section Abstract

variable {Λ : Type} [AddCommGroup Λ]

theorem b3Rest2_conj_conj (x : ℂ ⊗[ℤ] Λ) : b2_conj Λ (b2_conj Λ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c l =>
    show (starRingEnd ℂ (starRingEnd ℂ c)) ⊗ₜ[ℤ] l = c ⊗ₜ[ℤ] l
    rw [Complex.conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem b3Rest2_conj_smul (c : ℂ) (x : ℂ ⊗[ℤ] Λ) :
    b2_conj Λ (c • x) = (starRingEnd ℂ c) • b2_conj Λ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d l =>
    rw [TensorProduct.smul_tmul']
    show (starRingEnd ℂ (c • d)) ⊗ₜ[ℤ] l = (starRingEnd ℂ c) • ((starRingEnd ℂ d) ⊗ₜ[ℤ] l)
    rw [TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem b3Rest2_mem_conjSubmodule {F : Submodule ℂ (ℂ ⊗[ℤ] Λ)} {x : ℂ ⊗[ℤ] Λ} :
    x ∈ b2_conjSubmodule Λ F ↔ ∃ y ∈ F, b2_conj Λ y = x := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz => exact hz
    | zero => exact ⟨0, F.zero_mem, map_zero _⟩
    | add z w _ _ hz hw =>
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨y', hy', rfl⟩ := hw
      exact ⟨y + y', F.add_mem hy hy', map_add _ _ _⟩
    | smul c z _ hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      refine ⟨(starRingEnd ℂ c) • y, F.smul_mem _ hy, ?_⟩
      rw [b3Rest2_conj_smul, Complex.conj_conj]
  · rintro ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩

variable [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- **A weight-one criterion**: if `P x = P x̄ = 0` forces `x = 0` and `rk Λ = 2 dim (range P)`,
then `ker P` is a weight-one filtration. -/
theorem b3Rest2_isWeightOne_of_ker (P : ℂ ⊗[ℤ] Λ →ₗ[ℂ] V)
    (hdisj : ∀ x, P x = 0 → P (b2_conj Λ x) = 0 → x = 0)
    (hdim : Module.finrank ℤ Λ = 2 * Module.finrank ℂ (LinearMap.range P)) :
    b2_IsWeightOne Λ (LinearMap.ker P) := by
  set F := LinearMap.ker P
  set G := b2_conjSubmodule Λ F
  have hinf : F ⊓ G = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxF, hxG⟩
    obtain ⟨y, hy, rfl⟩ := b3Rest2_mem_conjSubmodule.1 hxG
    refine (Submodule.mem_bot ℂ).2 (hdisj _ hxF ?_)
    rw [b3Rest2_conj_conj]
    exact hy
  -- `dim G = dim F`
  let j : F ≃+ G :=
    { toFun := fun y ↦ ⟨b2_conj Λ y, b3Rest2_mem_conjSubmodule.2 ⟨y, y.2, rfl⟩⟩
      invFun := fun z ↦ ⟨b2_conj Λ z, by
        obtain ⟨y, hy, hyz⟩ := b3Rest2_mem_conjSubmodule.1 z.2
        rw [← hyz, b3Rest2_conj_conj]
        exact hy⟩
      left_inv := fun y ↦ Subtype.ext (b3Rest2_conj_conj _)
      right_inv := fun z ↦ Subtype.ext (b3Rest2_conj_conj _)
      map_add' := fun y y' ↦ Subtype.ext (map_add _ _ _) }
  have hFG : Module.finrank ℂ F = Module.finrank ℂ G := by
    have := rank_eq_of_equiv_equiv (starRingEnd ℂ) j
      (Function.Involutive.bijective fun c ↦ Complex.conj_conj c) (fun c y ↦ Subtype.ext (b3Rest2_conj_smul c y.1))
    unfold Module.finrank
    rw [this]
  have hT : Module.finrank ℂ (ℂ ⊗[ℤ] Λ) = Module.finrank ℤ Λ := Module.finrank_baseChange
  have hrn := LinearMap.finrank_range_add_finrank_ker P
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq F G
  rw [hinf, finrank_bot, add_zero] at hsup
  refine ⟨disjoint_iff.2 hinf, codisjoint_iff.2 (Submodule.eq_top_of_finrank_eq ?_)⟩
  have hrn' : Module.finrank ℂ (LinearMap.range P) + Module.finrank ℂ F = Module.finrank ℤ Λ := by
    rw [← hT]; exact hrn
  rw [hsup, ← hFG, hT]
  omega

end Abstract

section Curve

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

/-- The `ℂ`-linear functionals on `Ω¹(C)` inside all functions are the dual space. -/
def b3Rest2_linearDualEquiv : b3_linearDual E C ≃ₗ[ℂ] Module.Dual ℂ (b3_HolForm E C) where
  toFun u :=
    { toFun := u.1
      map_add' := fun θ η ↦ by
        have h := u.2 1 θ η
        simpa using h
      map_smul' := fun c θ ↦ by
        have h := u.2 c θ 0
        rw [add_zero, b3Forms_linearDual_apply_zero u.2, add_zero] at h
        simpa using h }
  invFun f := ⟨⇑f, fun a θ η ↦ by simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E] [ConnectedSpace C]
variable (hE : Module.finrank ℂ E = 1)
include hE

/-- **A holomorphic form on which every lattice vector has vanishing real part is zero.** -/
theorem b3Rest2_eq_zero_of_re_lattice {φ : b3_HolForm E C}
    (h : ∀ l : b3_periodLattice E C, (l.1 φ).re = 0) : φ = 0 := by
  have hper : b3Forms_PeriodsVanish (b3Forms_reForm φ) := fun γ hp hγ ↦ by
    rw [← b3Rest2_re_period φ ⟨γ, hp, hγ⟩]
    exact h (b3_latticePeriod E C ⟨γ, hp, hγ⟩)
  obtain ⟨g, hg, hdg⟩ := b3Forms_exists_primitive (b3Forms_isSmooth_reForm φ)
    (b3Forms_d_reForm hE φ) hper
  exact b3Forms_hol_eq_zero_of_reForm_exact hE φ hg hdg

theorem b3Rest2_finrank_linearDual :
    Module.finrank ℂ (b3_linearDual E C) = Module.finrank ℂ (b3_HolForm E C) := by
  haveI : FiniteDimensional ℂ (b3_HolForm E C) := b3Forms_holForm_finiteDimensional hE
  rw [b3Rest2_linearDualEquiv.finrank_eq, Subspace.dual_finrank_eq]

/-- **The real parts of a lattice basis are independent.** -/
theorem b3Rest2_linearIndependent_ρ (hK : b3Rest2_Key (C := C) hE) :
    haveI : Module.Finite ℤ (b3_periodLattice E C) := b3Forms_periodLattice_finite hE
    haveI : Module.Free ℤ (b3_periodLattice E C) := b3A_periodLattice_free
    LinearIndependent ℝ (fun i ↦ b3Rest2_ρ (Module.Free.chooseBasis ℤ (b3_periodLattice E C) i)) := by
  haveI : Module.Finite ℤ (b3_periodLattice E C) := b3Forms_periodLattice_finite hE
  haveI : Module.Free ℤ (b3_periodLattice E C) := b3A_periodLattice_free
  haveI := b3Forms_holForm_finiteDimensional_real (C := C) hE
  set b := Module.Free.chooseBasis ℤ (b3_periodLattice E C)
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
  · by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
      (lt_top_iff_ne_top.2 (fun h ↦ hne (top_le_iff.2 h))) inferInstance
    set φ := (Module.evalEquiv ℝ (b3_HolForm E C)).symm f
    have hfφ : ∀ g, f g = g φ := fun g ↦ by
      have : Module.evalEquiv ℝ (b3_HolForm E C) φ = f := LinearEquiv.apply_symm_apply _ _
      rw [← this]
      rfl
    have hb : ∀ i, b3Rest2_ρ (b i) φ = 0 := fun i ↦ by
      have hmem := Submodule.mem_map_of_mem (f := f)
        (Submodule.subset_span (R := ℝ) ⟨i, rfl⟩ :
          b3Rest2_ρ (b i) ∈ Submodule.span ℝ (Set.range fun i ↦ b3Rest2_ρ (b i)))
      rw [hf] at hmem
      rw [← hfφ]
      exact (Submodule.mem_bot ℝ).1 hmem
    have hφ : φ = 0 := b3Rest2_eq_zero_of_re_lattice hE fun l ↦ by
      rw [← b3Rest2_ρ_apply, ← b.sum_repr l, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [map_zsmul, LinearMap.smul_apply, hb i, smul_zero]
    apply hf0
    ext g
    rw [hfφ, hφ, map_zero, LinearMap.zero_apply]
  · rw [Subspace.dual_finrank_eq, ← Module.finrank_eq_card_chooseBasisIndex, b3Rest2_finrank_eq hE hK,
      finrank_real_of_complex]

/-- **The kernel filtration of the period map is a weight-one Hodge structure**, given the local
intersection computation. -/
theorem b3Rest2_isWeightOne (hK : b3Rest2_Key (C := C) hE) :
    b2_IsWeightOne (b3_periodLattice E C) (b3_periodF E C) := by
  haveI : Module.Finite ℤ (b3_periodLattice E C) := b3Forms_periodLattice_finite hE
  haveI : Module.Free ℤ (b3_periodLattice E C) := b3A_periodLattice_free
  set b := Module.Free.chooseBasis ℤ (b3_periodLattice E C)
  set B := Algebra.TensorProduct.basis ℂ b
  have hli := b3Rest2_linearIndependent_ρ hE hK
  refine b3Rest2_isWeightOne_of_ker (b3_cplxPeriod E C) (fun x hx hcx ↦ ?_) ?_
  · set c := fun i ↦ B.repr x i
    have hx' : x = ∑ i, c i • B i := (B.sum_repr x).symm
    have hB : ∀ i, B i = (1 : ℂ) ⊗ₜ[ℤ] b i := fun i ↦ Algebra.TensorProduct.basis_apply _ _
    have hP : ∀ (d : ℂ) i, b3_cplxPeriod E C (d • B i) = d • ((b i : b3_periodLattice E C) :
        b3_HolForm E C → ℂ) := fun d i ↦ by
      rw [hB, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
    have hconj : ∀ (d : ℂ) i, b2_conj _ (d • B i) = (starRingEnd ℂ d) • B i := fun d i ↦ by
      rw [b3Rest2_conj_smul, hB]
      show _ • ((starRingEnd ℂ 1) ⊗ₜ[ℤ] b i) = _
      rw [map_one]
    have h1 : ∑ i, c i • ((b i : b3_periodLattice E C) : b3_HolForm E C → ℂ) = 0 := by
      rw [← hx]; conv_rhs => rw [hx']
      rw [map_sum]; simp only [hP]
    have h2 : ∑ i, (starRingEnd ℂ (c i)) • ((b i : b3_periodLattice E C) :
        b3_HolForm E C → ℂ) = 0 := by
      rw [← hcx]; conv_rhs => rw [hx']
      rw [map_sum, map_sum]; simp only [hconj, hP]
    -- real and imaginary parts
    have hre : ∀ φ, ∑ i, (c i).re * b3Rest2_ρ (b i) φ = 0 ∧
        ∑ i, (c i).im * b3Rest2_ρ (b i) φ = 0 := by
      intro φ
      have e1 := congrFun h1 φ
      have e2 := congrFun h2 φ
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2
      have r1 := congrArg Complex.re e1
      have r2 := congrArg Complex.re e2
      have i1 := congrArg Complex.im e1
      have i2 := congrArg Complex.im e2
      simp only [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.zero_re, Complex.zero_im] at r1 r2 i1 i2
      simp only [b3Rest2_ρ_apply]
      constructor
      · have : ∑ i, (c i).re * ((b i).1 φ).re =
            (1 / 2) * ((∑ i, ((c i).re * ((b i).1 φ).re - (c i).im * ((b i).1 φ).im)) +
              ∑ i, ((c i).re * ((b i).1 φ).re - -(c i).im * ((b i).1 φ).im)) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          ring
        rw [this, r1, r2]; ring
      · have : ∑ i, (c i).im * ((b i).1 φ).re =
            (1 / 2) * ((∑ i, ((c i).re * ((b i).1 φ).im + (c i).im * ((b i).1 φ).re)) -
              ∑ i, ((c i).re * ((b i).1 φ).im + -(c i).im * ((b i).1 φ).re)) := by
          rw [← Finset.sum_sub_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          ring
        rw [this, i1, i2]; ring
    have hzero : ∀ r : _ → ℝ, (∀ φ, ∑ i, r i * b3Rest2_ρ (b i) φ = 0) → ∀ i, r i = 0 := by
      intro r hr
      refine Fintype.linearIndependent_iff.1 hli r ?_
      ext φ
      rw [LinearMap.sum_apply, LinearMap.zero_apply]
      simpa only [LinearMap.smul_apply, smul_eq_mul] using hr φ
    have hc : ∀ i, c i = 0 := fun i ↦
      Complex.ext (hzero _ (fun φ ↦ (hre φ).1) i) (hzero _ (fun φ ↦ (hre φ).2) i)
    rw [hx']
    simp [hc]
  · rw [b3Rest2_finrank_eq hE hK, b3Forms_range_cplxPeriod hE, b3Rest2_finrank_linearDual hE]

end Curve

end HodgeLean.Foundations.Program
