import HodgeLean.Foundations.Program.CurveJacobianRest2Weight
import HodgeLean.Foundations.Program.CurveJacobianRestUnique

/-! # Track B3, lane Rest2: the Riemann bilinear relations

Let `Q` be the intersection form, so that `Q(λ, μ) = W(θ_λ, θ_μ)` with `W(θ, φ) = ∫ Re θ ∧ Re φ`.
Write `x ∈ ℂ ⊗ Λ` as `Σ cᵢ ⊗ λᵢ` in a basis of the lattice and put `u = Σ Re cᵢ θ_{λᵢ}`,
`v = Σ Im cᵢ θ_{λᵢ}`. Then
* `Q_ℂ(x, y) = W(u, u') - W(v, v') + i (W(u, v') + W(v, u'))`;
* `W(iθ, iφ) = W(θ, φ)` (two holomorphic forms wedge to zero) and `λ(φ) = W(φ, θ_λ) - i W(iφ, θ_λ)`;
  so `x ∈ F` (all periods vanish) gives `v = -i u`;
* for `x, y ∈ F` this makes `Q_ℂ(x, y) = 0` (**isotropy**), and `Q_ℂ(x, x̄) = 2i W(u, iu)` with
  `W(u, iu) = -∫ Re u ∧ Im u < 0` for `u ≠ 0` (**positivity**); `u = 0` forces `x = 0` since the
  `θ_{λᵢ}` are independent over `ℝ`.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold
open scoped TensorProduct ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

omit [IsManifold 𝓘(ℂ, E) ω C] in
theorem b3Rest2_wedgeForm_smul_left (c : ℝ) (α β : C → E [⋀^Fin 1]→L[ℝ] ℝ) :
    b3Forms_wedgeForm (c • α) β = c • b3Forms_wedgeForm α β := by
  funext z
  simp only [b3Forms_wedgeForm, Pi.smul_apply, b3Forms_wedge_smul_left]

theorem b3Rest2_I_I (φ : b3_HolForm E C) : Complex.I • (Complex.I • φ) = -φ := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

theorem b3Rest2_bilin_sum {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
    (W : LinearMap.BilinForm ℝ H) (θ : ι → H) (r s : ι → ℝ) :
    W (∑ i, r i • θ i) (∑ j, s j • θ j) = ∑ i, ∑ j, r i * s j * W (θ i) (θ j) := by
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

theorem b3Rest2_cplx_term (c d : ℂ) (w : ℝ) :
    c * d * (w : ℂ) = ((c.re * d.re * w - c.im * d.im * w : ℝ) : ℂ) +
      Complex.I * ((c.re * d.im * w + c.im * d.re * w : ℝ) : ℂ) := by
  apply Complex.ext <;> simp <;> ring

theorem b3Rest2_cplx_expand {ι : Type*} [Fintype ι] (w : ι → ι → ℝ) (c d : ι → ℂ) :
    ∑ i, ∑ j, c i * d j * (w i j : ℂ) =
      ((∑ i, ∑ j, (c i).re * (d j).re * w i j - ∑ i, ∑ j, (c i).im * (d j).im * w i j : ℝ) :
        ℂ) + Complex.I * ((∑ i, ∑ j, (c i).re * (d j).im * w i j +
          ∑ i, ∑ j, (c i).im * (d j).re * w i j : ℝ) : ℂ) := by
  simp only [b3Rest2_cplx_term, Finset.sum_add_distrib, ← Finset.mul_sum, Complex.ofReal_sum,
    Complex.ofReal_sub, Complex.ofReal_add, Finset.sum_sub_distrib]

theorem b3Rest2_im_term (c : ℂ) (a a' : ℝ) :
    (c * ((a : ℂ) - Complex.I * (a' : ℂ))).im = c.im * a - c.re * a' := by
  simp; ring

variable [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E] [ConnectedSpace C]
variable (hE : Module.finrank ℂ E = 1)
include hE

theorem b3Rest2_W_I_I (φ ψ : b3_HolForm E C) :
    b3Rest2_W hE (Complex.I • φ) (Complex.I • ψ) = b3Rest2_W hE φ ψ := by
  rw [b3Rest2_W_apply, b3Rest2_W_apply, b3Rest2_reForm_I, b3Rest2_reForm_I,
    b3Rest2_wedgeForm_smul_left, b3Rest_wedgeForm_smul, smul_smul, b3Forms_integral_smul,
    ← (b3Forms_wedge_hol_eq hE φ ψ).1]
  norm_num

theorem b3Rest2_W_I_left (φ ψ : b3_HolForm E C) :
    b3Rest2_W hE (Complex.I • φ) ψ = -b3Rest2_W hE φ (Complex.I • ψ) := by
  have := b3Rest2_W_I_I hE (Complex.I • φ) ψ
  rw [b3Rest2_I_I, map_neg, LinearMap.neg_apply] at this
  linarith

theorem b3Rest2_lattice_apply (l : b3_periodLattice E C) (φ : b3_HolForm E C) :
    l.1 φ = (b3Rest2_W hE φ (b3Rest2_θ hE l) : ℂ) -
      Complex.I * (b3Rest2_W hE (Complex.I • φ) (b3Rest2_θ hE l) : ℂ) := by
  have hl := b3Forms_periodLattice_le_linearDual l.2
  have h1 := hl Complex.I φ 0
  rw [add_zero, b3Forms_linearDual_apply_zero hl, add_zero] at h1
  rw [b3Rest2_W_θ, b3Rest2_W_θ, h1]
  apply Complex.ext <;> simp

/-- The `θ_{λᵢ}` of a lattice basis are independent over `ℝ`. -/
theorem b3Rest2_linearIndependent_θ (hK : b3Rest2_Key (C := C) hE) :
    haveI : Module.Finite ℤ (b3_periodLattice E C) := b3Forms_periodLattice_finite hE
    haveI : Module.Free ℤ (b3_periodLattice E C) := b3A_periodLattice_free
    ∀ r : Module.Free.ChooseBasisIndex ℤ (b3_periodLattice E C) → ℝ,
      ∑ i, r i • b3Rest2_θ hE (Module.Free.chooseBasis ℤ (b3_periodLattice E C) i) = 0 →
        ∀ i, r i = 0 := by
  haveI : Module.Finite ℤ (b3_periodLattice E C) := b3Forms_periodLattice_finite hE
  haveI : Module.Free ℤ (b3_periodLattice E C) := b3A_periodLattice_free
  intro r hr
  refine Fintype.linearIndependent_iff.1 (b3Rest2_linearIndependent_ρ hE hK) r ?_
  ext φ
  have := congrArg (fun θ ↦ b3Rest2_W hE φ θ) hr
  simp only [map_sum, map_smul, smul_eq_mul, map_zero, b3Rest2_W_θ] at this
  rw [LinearMap.sum_apply, LinearMap.zero_apply]
  simpa only [LinearMap.smul_apply, smul_eq_mul, b3Rest2_ρ_apply] using this

theorem b3Rest2_W_self (θ : b3_HolForm E C) : b3Rest2_W hE θ θ = 0 := by
  have := b3Rest2_W_skew hE θ θ
  linarith

section Basis

variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ (b3_periodLattice E C))

/-- `Σ Re cᵢ θ_{λᵢ}`. -/
def b3Rest2_uR (c : ι → ℂ) : b3_HolForm E C := ∑ i, (c i).re • b3Rest2_θ hE (b i)

/-- `Σ Im cᵢ θ_{λᵢ}`. -/
def b3Rest2_uI (c : ι → ℂ) : b3_HolForm E C := ∑ i, (c i).im • b3Rest2_θ hE (b i)

theorem b3Rest2_tmulBasis (i : ι) :
    Algebra.TensorProduct.basis ℂ b i = (1 : ℂ) ⊗ₜ[ℤ] b i :=
  Algebra.TensorProduct.basis_apply _ _

theorem b3Rest2_cplxPeriod_coords (x : ℂ ⊗[ℤ] b3_periodLattice E C) :
    b3_cplxPeriod E C x = ∑ i, (Algebra.TensorProduct.basis ℂ b).equivFun x i •
      ((b i : b3_periodLattice E C) : b3_HolForm E C → ℂ) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis ℂ b).sum_equivFun x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [b3Rest2_tmulBasis hE b, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

theorem b3Rest2_conj_coords (x : ℂ ⊗[ℤ] b3_periodLattice E C) :
    (Algebra.TensorProduct.basis ℂ b).equivFun (b2_conj _ x) =
      fun i ↦ starRingEnd ℂ ((Algebra.TensorProduct.basis ℂ b).equivFun x i) := by
  set B := Algebra.TensorProduct.basis ℂ b
  have : b2_conj _ x = ∑ i, starRingEnd ℂ (B.equivFun x i) • B i := by
    conv_lhs => rw [← B.sum_equivFun x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [b3Rest2_conj_smul, b3Rest2_tmulBasis hE b]
    show _ • ((starRingEnd ℂ 1) ⊗ₜ[ℤ] b i) = _
    rw [map_one]
  rw [this, ← B.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem b3Rest2_baseChange_coords (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C))
    (hQW : ∀ l m, (Q l m : ℝ) = b3Rest2_W hE (b3Rest2_θ hE l) (b3Rest2_θ hE m))
    (x y : ℂ ⊗[ℤ] b3_periodLattice E C) :
    Q.baseChange ℂ x y =
      ((b3Rest2_W hE (b3Rest2_uR hE b ((Algebra.TensorProduct.basis ℂ b).equivFun x))
          (b3Rest2_uR hE b ((Algebra.TensorProduct.basis ℂ b).equivFun y)) -
        b3Rest2_W hE (b3Rest2_uI hE b ((Algebra.TensorProduct.basis ℂ b).equivFun x))
          (b3Rest2_uI hE b ((Algebra.TensorProduct.basis ℂ b).equivFun y)) : ℝ) : ℂ) +
      Complex.I * ((b3Rest2_W hE (b3Rest2_uR hE b ((Algebra.TensorProduct.basis ℂ b).equivFun x))
          (b3Rest2_uI hE b ((Algebra.TensorProduct.basis ℂ b).equivFun y)) +
        b3Rest2_W hE (b3Rest2_uI hE b ((Algebra.TensorProduct.basis ℂ b).equivFun x))
          (b3Rest2_uR hE b ((Algebra.TensorProduct.basis ℂ b).equivFun y)) : ℝ) : ℂ) := by
  set B := Algebra.TensorProduct.basis ℂ b
  set c := B.equivFun x
  set d := B.equivFun y
  have hl : Q.baseChange ℂ x y = ∑ i, ∑ j, c i * d j *
      ((b3Rest2_W hE (b3Rest2_θ hE (b i)) (b3Rest2_θ hE (b j)) : ℝ) : ℂ) := by
    conv_lhs => rw [← B.sum_equivFun x]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    conv_lhs => rw [← B.sum_equivFun y]
    rw [map_smul, LinearMap.smul_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, smul_eq_mul, smul_eq_mul, b3Rest2_tmulBasis hE b, b3Rest2_tmulBasis hE b,
      LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul, mul_one, ← hQW]
    push_cast
    ring
  rw [hl, b3Rest2_cplx_expand]
  simp only [b3Rest2_uR, b3Rest2_uI, b3Rest2_bilin_sum]

/-- **Vectors of `F` satisfy `v = -i u`.** -/
theorem b3Rest2_uI_of_mem_F {x : ℂ ⊗[ℤ] b3_periodLattice E C} (hxF : x ∈ b3_periodF E C) :
    b3Rest2_uI hE b ((Algebra.TensorProduct.basis ℂ b).equivFun x) =
      -(Complex.I • b3Rest2_uR hE b ((Algebra.TensorProduct.basis ℂ b).equivFun x)) := by
  set c := (Algebra.TensorProduct.basis ℂ b).equivFun x
  have h0 : ∀ φ, ∑ i, c i * (b i).1 φ = 0 := fun φ ↦ by
    have := congrFun ((LinearMap.mem_ker.1 hxF).symm.trans (b3Rest2_cplxPeriod_coords hE b x)) φ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact this.symm
  have hW0 : ∀ φ, b3Rest2_W hE φ (b3Rest2_uI hE b c + Complex.I • b3Rest2_uR hE b c) = 0 := by
    intro φ
    have him := congrArg Complex.im (h0 φ)
    simp only [b3Rest2_lattice_apply hE, Complex.im_sum, b3Rest2_im_term, Complex.zero_im] at him
    have hI : b3Rest2_W hE φ (Complex.I • b3Rest2_uR hE b c) =
        -b3Rest2_W hE (Complex.I • φ) (b3Rest2_uR hE b c) := by
      rw [b3Rest2_W_I_left, neg_neg]
    rw [map_add, hI]
    simp only [b3Rest2_uR, b3Rest2_uI, map_sum, map_smul, smul_eq_mul]
    rw [← him, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  exact add_eq_zero_iff_eq_neg.1 ((b3Rest2_W_nondegenerate hE).2 _ hW0)

end Basis

set_option maxHeartbeats 400000 in
/-- **The intersection form is a Riemann form**, given the local intersection computation. -/
theorem b3Rest2_isRiemannForm (hK : b3Rest2_Key (C := C) hE)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C)) (hQ : b3_IsIntersectionForm E Q) :
    b2_IsRiemannForm (b3_periodLattice E C) (b3_periodF E C) Q := by
  haveI : Module.Finite ℤ (b3_periodLattice E C) := b3Forms_periodLattice_finite hE
  haveI : Module.Free ℤ (b3_periodLattice E C) := b3A_periodLattice_free
  classical
  have hQW : ∀ l m, (Q l m : ℝ) = b3Rest2_W hE (b3Rest2_θ hE l) (b3Rest2_θ hE m) := by
    have := b3Rest_intersectionForm_unique hE Q (b3Rest2_QZ hE hK) hQ
      (b3Rest2_isIntersectionForm hE hK)
    intro l m
    rw [this, b3Rest2_QZ_apply, b3Rest2_Q_eq_W]
  set b := Module.Free.chooseBasis ℤ (b3_periodLattice E C)
  set B := Algebra.TensorProduct.basis ℂ b
  refine ⟨b3Rest_intersectionForm_alt hE Q hQ, fun x hxF y hyF ↦ ?_, fun x hxF hx0 ↦ ?_⟩
  · rw [b3Rest2_baseChange_coords hE b Q hQW, b3Rest2_uI_of_mem_F hE b hxF,
      b3Rest2_uI_of_mem_F hE b hyF]
    simp only [map_neg, LinearMap.neg_apply, neg_neg, b3Rest2_W_I_I, b3Rest2_W_I_left hE,
      sub_self, b3Rest2_I_I]
    simp
  · rw [b3Rest2_baseChange_coords hE b Q hQW, b3Rest2_conj_coords hE b]
    set c := B.equivFun x
    have hu : b3Rest2_uR hE b (fun i ↦ starRingEnd ℂ (c i)) = b3Rest2_uR hE b c := by
      simp [b3Rest2_uR]
    have hv : b3Rest2_uI hE b (fun i ↦ starRingEnd ℂ (c i)) = -b3Rest2_uI hE b c := by
      simp only [b3Rest2_uI, Complex.conj_im, neg_smul, Finset.sum_neg_distrib]
    have hvF := b3Rest2_uI_of_mem_F hE b hxF
    rw [hu, hv, hvF]
    set w := b3Rest2_uR hE b c
    have hu0 : w ≠ 0 := by
      intro h0
      have hv0 : b3Rest2_uI hE b c = 0 := by rw [hvF, h0, smul_zero, neg_zero]
      have hre := b3Rest2_linearIndependent_θ hE hK (fun i ↦ (c i).re) h0
      have him := b3Rest2_linearIndependent_θ hE hK (fun i ↦ (c i).im) hv0
      apply hx0
      rw [← B.sum_equivFun x]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [show B.equivFun x i = 0 from Complex.ext (hre i) (him i), zero_smul]
    have hneg := b3Rest2_W_I_neg hE hu0
    have hs := b3Rest2_W_skew hE w (Complex.I • w)
    simp only [neg_neg, map_neg, LinearMap.neg_apply, b3Rest2_W_I_I, b3Rest2_W_self hE]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im]
    simp
    linarith

end HodgeLean.Foundations.Program
