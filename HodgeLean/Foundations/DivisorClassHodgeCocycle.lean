import HodgeLean.Foundations.DivisorClassHodgeAnalysis

/-! # Divisor classes on abelian varieties: cocycles and the normal form (DC1, sub-stage d)

Helpers for the bodies `dc1_additiveCocycle_aux`, `dc1_linearization_aux` and
`dc1_chernForm_typeOneOne_aux`:

* the coordinate `∂̄` calculus of `dbar_coord`: it vanishes on holomorphic functions, commutes
  with translations, preserves smoothness, and two of them commute on smooth functions
  (symmetry of second derivatives);
* `dca_additiveCocycle`: an additive cocycle of entire functions is `δh + A`, from a smooth
  coboundary `φ`, the `∂̄`-decomposition of the periodic form `∂̄φ` on the torus, and
  `dbar_holomorphic`; the smooth-coboundary and torus inputs are binders, filled in the proofs
  file by `dc1_smooth_coboundary_aux` and `dc1_torus_dbar_aux`;
* `dca_linearization`: the normal form `F_l + δh = lin_l + b_l` of a holomorphic logarithm
  (constant integer defect, derivative cocycles, periodic curl constant by Liouville, linear
  symmetrization, holomorphic Poincaré lemma);
* `dca_log_differentiable` and `dca_chernForm_typeOneOne`: a continuous logarithm of a
  holomorphic factor is holomorphic, and `logForm` of the normal form is `lin_m(l) - lin_l(m)`.

HC no distance; AV milestone no distance.
-/

noncomputable section

open HodgeLean.Foundations.AppellHumbert HodgeLean.Foundations.AutomorphyChernClass
open Filter Set Topology
open scoped ContDiff

namespace HodgeLean.Foundations
variable {n : ℕ}

theorem dca_dbar_eq_zero {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (hf : DifferentiableAt ℂ f z)
    (j : Fin n) : dbar_coord n j f z = 0 := by
  simp only [dbar_coord, hf.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars']
  rw [show (Pi.single j Complex.I : Fin n → ℂ) = Complex.I • Pi.single j 1 by
    rw [← Pi.single_smul', smul_eq_mul, mul_one], map_smul, smul_eq_mul, ← mul_assoc,
    Complex.I_mul_I]
  ring

theorem dca_dbar_comp_add (f : (Fin n → ℂ) → ℂ) (l z : Fin n → ℂ) (j : Fin n) :
    dbar_coord n j (fun x ↦ f (x + l)) z = dbar_coord n j f (z + l) := by
  simp only [dbar_coord, fderiv_comp_add_right]

theorem dca_dbar_add {f g : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (j : Fin n) :
    dbar_coord n j (f + g) z = dbar_coord n j f z + dbar_coord n j g z := by
  simp only [dbar_coord, fderiv_add hf hg, add_apply]
  ring

theorem dca_dbar_sub {f g : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (j : Fin n) :
    dbar_coord n j (f - g) z = dbar_coord n j f z - dbar_coord n j g z := by
  simp only [dbar_coord, fderiv_sub hf hg, sub_apply]
  ring

theorem dca_dbar_clm (χ : (Fin n → ℂ) →L[ℝ] ℂ) (z : Fin n → ℂ) (j : Fin n) :
    dbar_coord n j χ z = (χ (Pi.single j 1) + Complex.I * χ (Pi.single j Complex.I)) / 2 := by
  simp only [dbar_coord, ContinuousLinearMap.fderiv]

theorem dca_contDiff_dbar {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ ∞ f) (j : Fin n) :
    ContDiff ℝ ∞ (dbar_coord n j f) := by
  have h : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  unfold dbar_coord
  exact ((h.clm_apply contDiff_const).add
    (contDiff_const.mul (h.clm_apply contDiff_const))).div_const _

theorem dca_fderiv_dbar {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) z) (j : Fin n) (w : Fin n → ℂ) :
    fderiv ℝ (dbar_coord n j f) z w = (fderiv ℝ (fderiv ℝ f) z w (Pi.single j 1) +
      Complex.I * fderiv ℝ (fderiv ℝ f) z w (Pi.single j Complex.I)) / 2 := by
  have h1 := (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1 : ℂ))).hasFDerivAt.comp z
    hf.hasFDerivAt
  have h2 := (ContinuousLinearMap.apply ℝ ℂ (Pi.single j Complex.I)).hasFDerivAt.comp z
    hf.hasFDerivAt
  have h3 := ((h1.add (h2.const_mul Complex.I)).mul_const (1 / 2 : ℂ))
  have e : dbar_coord n j f = fun x ↦
      ((ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1 : ℂ))) (fderiv ℝ f x) +
        Complex.I * (ContinuousLinearMap.apply ℝ ℂ (Pi.single j Complex.I)) (fderiv ℝ f x)) *
          (1 / 2 : ℂ) := by
    ext x; simp only [dbar_coord, ContinuousLinearMap.apply_apply]; ring
  have h4 : HasFDerivAt (dbar_coord n j f) ((1 / 2 : ℂ) •
      ((ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1 : ℂ))).comp (fderiv ℝ (fderiv ℝ f) z) +
        Complex.I • (ContinuousLinearMap.apply ℝ ℂ (Pi.single j Complex.I)).comp
          (fderiv ℝ (fderiv ℝ f) z))) z := by
    rw [e]; exact h3
  rw [h4.fderiv]
  simp
  ring

theorem dca_dbar_dbar_comm {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ ∞ f) (j k : Fin n)
    (z : Fin n → ℂ) :
    dbar_coord n k (dbar_coord n j f) z = dbar_coord n j (dbar_coord n k f) z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) z
  have hs := (hf.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)
  simp only [dbar_coord, dca_fderiv_dbar hd]
  rw [hs (Pi.single k 1) (Pi.single j Complex.I), hs (Pi.single k Complex.I) (Pi.single j 1),
    hs (Pi.single k Complex.I) (Pi.single j Complex.I), hs (Pi.single k 1) (Pi.single j 1)]
  ring


theorem dca_contDiff_real {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) :
    ContDiff ℝ ∞ f :=
  (dca_contDiff hf).restrict_scalars ℝ

section Lattice

variable (L : Submodule ℤ (Fin n → ℂ))

theorem dca_additiveCocycle
    (htorus : ∀ (w : Fin n → (Fin n → ℂ) → ℂ), (∀ j, ContDiff ℝ ∞ (w j)) →
      (∀ j (l : L) z, w j (z + l) = w j z) →
      (∀ j k z, dbar_coord n k (w j) z = dbar_coord n j (w k) z) →
      ∃ (c : Fin n → ℂ) (ψ : (Fin n → ℂ) → ℂ), ContDiff ℝ ∞ ψ ∧
        (∀ (l : L) z, ψ (z + l) = ψ z) ∧ ∀ j z, w j z = c j + dbar_coord n j ψ z)
    (hcob : ∀ (a : L → (Fin n → ℂ) → ℂ), (∀ l, ContDiff ℝ ∞ (a l)) →
      (∀ (l m : L) z, a (l + m) z = a l (z + m) + a m z) →
      ∃ φ : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ φ ∧ ∀ (l : L) z, φ (z + l) - φ z = a l z)
    (a : L → (Fin n → ℂ) → ℂ) (ha : ∀ l, Differentiable ℂ (a l))
    (hcoc : ∀ (l m : L) z, a (l + m) z = a l (z + m) + a m z) :
    ∃ (h : (Fin n → ℂ) → ℂ) (A : L →+ ℂ), Differentiable ℂ h ∧
      ∀ (l : L) z, a l z = h (z + l) - h z + A l := by
  obtain ⟨φ, hφ, hδφ⟩ := hcob a (fun l ↦ dca_contDiff_real (ha l)) hcoc
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφl : ∀ l : L, (fun x ↦ φ (x + l)) = φ + a l := by
    intro l; ext x; simp only [Pi.add_apply]; rw [← hδφ l x]; ring
  have hwper : ∀ j (l : L) z, dbar_coord n j φ (z + l) = dbar_coord n j φ z := by
    intro j l z
    rw [← dca_dbar_comp_add, hφl l,
      dca_dbar_add (hφd z) ((dca_contDiff_real (ha l)).differentiable (by simp) z),
      dca_dbar_eq_zero ((ha l) z), add_zero]
  obtain ⟨c, ψ, hψ, hψper, hw⟩ := htorus (fun j ↦ dbar_coord n j φ)
    (fun j ↦ dca_contDiff_dbar hφ j) hwper (fun j k z ↦ dca_dbar_dbar_comm hφ j k z)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  let χ : (Fin n → ℂ) →L[ℝ] ℂ := ∑ k, c k • (Complex.conjCLE.toContinuousLinearMap.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℂ) k))
  let h : (Fin n → ℂ) → ℂ := φ - ψ - χ
  have hhd : Differentiable ℝ h := (hφd.sub hψd).sub χ.differentiable
  have hdbar : ∀ j z, dbar_coord n j h z = 0 := by
    intro j z
    simp only [h]
    rw [dca_dbar_sub ((hφd.sub hψd) z) (χ.differentiable z),
      dca_dbar_sub (hφd z) (hψd z), dca_dbar_clm, hw j z]
    simp [χ, Pi.single_apply, apply_ite (starRingEnd ℂ), mul_ite]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hhol : Differentiable ℂ h := by
    have := dbar_holomorphic n univ isOpen_univ h (fun z _ ↦ hhd z) (fun j z _ ↦ hdbar j z)
    exact differentiableOn_univ.1 this.differentiableOn
  refine ⟨h, ⟨⟨fun l ↦ χ l, by simp⟩, fun l m ↦ by simp⟩, hhol, fun l z ↦ ?_⟩
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, h, Pi.sub_apply, map_add]
  rw [← hδφ l z, hψper l z]
  ring

end Lattice

/-- A continuous `g` with `exp(2πi g) = 1` everywhere is constant. -/
theorem dca_const_of_exp_eq_one {g : (Fin n → ℂ) → ℂ} (hg : Continuous g)
    (h : ∀ v, Complex.exp (2 * Real.pi * Complex.I * g v) = 1) (v w : Fin n → ℂ) :
    g v = g w := by
  have h2πI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hn : ∀ v, ∃ k : ℤ, g v = k := fun v ↦ by
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp (h v)
    refine ⟨k, mul_left_cancel₀ h2πI ?_⟩
    rw [hk]; ring
  choose k hk using hn
  have hc : Continuous k := by
    rw [Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff]
    have : ((Int.cast : ℤ → ℝ) ∘ k) = fun v ↦ (g v).re := by
      funext v; simp [hk v]
    rw [this]; exact Complex.continuous_re.comp hg
  rw [hk v, hk w, PreconnectedSpace.constant inferInstance hc]

theorem dca_differentiable_partial {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (v : Fin n → ℂ) : Differentiable ℂ fun z ↦ fderiv ℂ f z v :=
  (((dca_contDiff hf (m := 2)).fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num)).clm_apply (differentiable_const v)

theorem dca_fderiv_partial {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (v w z : Fin n → ℂ) :
    fderiv ℂ (fun x ↦ fderiv ℂ f x v) z w = fderiv ℂ (fderiv ℂ f) z w v := by
  have hd : DifferentiableAt ℂ (fderiv ℂ f) z :=
    ((dca_contDiff hf (m := 2)).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) z
  have h1 := (ContinuousLinearMap.apply ℂ ℂ v).hasFDerivAt.comp z hd.hasFDerivAt
  rw [show (fun x ↦ fderiv ℂ f x v) = ⇑(ContinuousLinearMap.apply ℂ ℂ v) ∘ fderiv ℂ f from rfl,
    h1.fderiv]
  rfl

theorem dca_partial_symm {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (v w z : Fin n → ℂ) : fderiv ℂ (fderiv ℂ f) z v w = fderiv ℂ (fderiv ℂ f) z w v :=
  ((dca_contDiff hf (m := 2)).contDiffAt.isSymmSndFDerivAt (by simp)) v w

section Lattice

variable (L : Submodule ℤ (Fin n → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L]

theorem dca_linearization
    (hcocy : ∀ (a : L → (Fin n → ℂ) → ℂ), (∀ l, Differentiable ℂ (a l)) →
      (∀ (l m : L) z, a (l + m) z = a l (z + m) + a m z) →
      ∃ (h : (Fin n → ℂ) → ℂ) (A : L →+ ℂ), Differentiable ℂ h ∧
        ∀ (l : L) z, a l z = h (z + l) - h z + A l)
    (a F : L → (Fin n → ℂ) → ℂ)
    (hcoc : ∀ (l m : L) v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * F l v))
    (hF : ∀ l, Differentiable ℂ (F l)) :
    ∃ (h : (Fin n → ℂ) → ℂ) (lin : L →+ ((Fin n → ℂ) →ₗ[ℂ] ℂ)) (b : L → ℂ),
      Differentiable ℂ h ∧ ∀ (l : L) z, F l z + h (z + l) - h z = lin l z + b l := by
  -- the integer defect is constant
  have hdef : ∀ l m : L, ∀ z, F (l + m) z = F l (z + m) + F m z -
      (F l ((0 : Fin n → ℂ) + m) + F m 0 - F (l + m) 0) := by
    intro l m z
    have := dca_const_of_exp_eq_one (g := fun v : Fin n → ℂ ↦ F l (v + m) + F m v - F (l + m) v)
      (by have := fun l ↦ (hF l).continuous; fun_prop) (fun v ↦ by
        have h := hcoc l m v
        rw [hlog, hlog, hlog, ← Complex.exp_add] at h
        rw [mul_sub, Complex.exp_sub, mul_add, ← h, div_self (Complex.exp_ne_zero _)]) z 0
    rw [← this]; ring
  have hsh : ∀ {g : (Fin n → ℂ) → ℂ}, Differentiable ℂ g → ∀ c : Fin n → ℂ,
      Differentiable ℂ fun x ↦ g (x + c) := fun hg c ↦ hg.comp (differentiable_id.add_const c)
  -- the partial derivatives form additive cocycles
  let u : Fin n → L → (Fin n → ℂ) → ℂ := fun k l z ↦ fderiv ℂ (F l) z (Pi.single k 1)
  have hu : ∀ k l, Differentiable ℂ (u k l) := fun k l ↦ dca_differentiable_partial (hF l) _
  have hucoc : ∀ k (l m : L) z, u k (l + m) z = u k l (z + m) + u k m z := by
    intro k l m z
    simp only [u]
    rw [show F (l + m) = fun z ↦ F l (z + m) + F m z -
      (F l ((0 : Fin n → ℂ) + m) + F m 0 - F (l + m) 0) from funext (hdef l m)]
    rw [fderiv_sub_const, fderiv_fun_add (hsh (hF l) _ _) (hF m _),
      fderiv_comp_add_right]
    rfl
  choose hk A hkd hkA using fun k ↦ hcocy (u k) (hu k) (hucoc k)
  -- the curl of `hk` is periodic, hence constant
  let D : Fin n → Fin n → (Fin n → ℂ) → ℂ := fun j k z ↦
    fderiv ℂ (hk k) z (Pi.single j 1) - fderiv ℂ (hk j) z (Pi.single k 1)
  have hδk : ∀ k j (l : L) z, fderiv ℂ (hk k) (z + l) (Pi.single j 1) -
      fderiv ℂ (hk k) z (Pi.single j 1) =
        fderiv ℂ (fderiv ℂ (F l)) z (Pi.single j 1) (Pi.single k 1) := by
    intro k j l z
    have e : (fun x ↦ hk k (x + l) - hk k x) = fun x ↦ u k l x - A k l := by
      ext x; rw [hkA k l x]; ring
    have : fderiv ℂ (fun x ↦ hk k (x + l) - hk k x) z (Pi.single j 1) =
        fderiv ℂ (fun x ↦ u k l x - A k l) z (Pi.single j 1) := by rw [e]
    rw [fderiv_fun_sub (hsh (hkd k) _ _) (hkd k _), fderiv_sub_const,
      fderiv_comp_add_right] at this
    rw [← dca_fderiv_partial (hF l)]
    exact this
  have hDc : ∀ j k z, D j k z = D j k 0 := by
    intro j k z
    refine dca_periodic_entire_const L (D j k) ?_ (fun l z ↦ ?_) z 0
    · exact (dca_differentiable_partial (hkd k) _).sub (dca_differentiable_partial (hkd j) _)
    · have h1 := hδk k j l z
      have h2 := hδk j k l z
      rw [dca_partial_symm (hF l)] at h1
      simp only [D]
      linear_combination h1 - h2
  let C : Fin n → Fin n → ℂ := fun j k ↦ D j k 0
  -- symmetrize
  let h' : Fin n → (Fin n → ℂ) → ℂ := fun k z ↦ hk k z - (1 / 2) * ∑ j, C j k * z j
  have hlinpart : ∀ k : Fin n, Differentiable ℂ fun z : Fin n → ℂ ↦ ∑ j, C j k * z j :=
    fun k ↦ by fun_prop
  have hlinD : ∀ k z j, fderiv ℂ (fun z : Fin n → ℂ ↦ ∑ j, C j k * z j) z (Pi.single j 1) =
      C j k := by
    intro k z j
    have : (fun z : Fin n → ℂ ↦ ∑ j, C j k * z j) =
        ⇑(∑ j, C j k • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) j) := by
      ext z; simp
    rw [this, ContinuousLinearMap.fderiv]
    simp [Pi.single_apply]
  have hh'd : ∀ k, Differentiable ℂ (h' k) := fun k ↦
    (hkd k).sub ((hlinpart k).const_mul _)
  have hh'D : ∀ k z j, fderiv ℂ (h' k) z (Pi.single j 1) =
      fderiv ℂ (hk k) z (Pi.single j 1) - (1 / 2) * C j k := by
    intro k z j
    simp only [h']
    rw [fderiv_fun_sub (hkd k _) (((hlinpart k).const_mul _) _), fderiv_const_mul (hlinpart k _)]
    simp only [sub_apply, smul_apply, smul_eq_mul, hlinD]
  have hclosed : ∀ j k z, fderiv ℂ (h' j) z (Pi.single k 1) =
      fderiv ℂ (h' k) z (Pi.single j 1) := by
    intro j k z
    rw [hh'D, hh'D]
    have := hDc j k z
    simp only [C, D] at this ⊢
    have hC : D k j 0 = - D j k 0 := by simp only [D]; ring
    simp only [D] at hC
    linear_combination -this + (1 / 2 : ℂ) * hC
  obtain ⟨H, hHd, hHD⟩ := dca_holomorphic_poincare h' hh'd hclosed
  -- the normalized logarithm is affine
  let A' : Fin n → L → ℂ := fun k l ↦ A k l + (1 / 2) * ∑ j, C j k * (l : Fin n → ℂ) j
  have hA'0 : ∀ k, A' k 0 = 0 := fun k ↦ by simp [A']
  have hA'add : ∀ k (l m : L), A' k (l + m) = A' k l + A' k m := by
    intro k l m
    simp only [A', map_add, Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  have hu' : ∀ k (l : L) z, u k l z = h' k (z + l) - h' k z + A' k l := by
    intro k l z
    rw [hkA k l z]
    simp only [h', A', Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  let Φ : L → (Fin n → ℂ) → ℂ := fun l z ↦ F l z - H (z + l) + H z
  have hΦd : ∀ l, Differentiable ℂ (Φ l) := fun l ↦ ((hF l).sub (hsh hHd _)).add hHd
  have hΦD : ∀ l z k, fderiv ℂ (Φ l) z (Pi.single k 1) = A' k l := by
    intro l z k
    simp only [Φ]
    rw [fderiv_fun_add (f := fun y ↦ F l y - H (y + l)) (g := H)
      ((hF l z).sub (hsh hHd _ z)) (hHd z),
      fderiv_fun_sub (hF l z) (hsh hHd _ z), fderiv_comp_add_right]
    simp only [add_apply, sub_apply, hHD]
    have := hu' k l z
    simp only [u] at this
    linear_combination this
  let Λ : L → (Fin n → ℂ) →L[ℂ] ℂ := fun l ↦
    ∑ k, A' k l • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) k
  have hΛ : ∀ l z, fderiv ℂ (Φ l) z = Λ l := by
    intro l z
    ext1 w
    rw [← dca_sum_single_apply]
    simp only [hΦD, Λ]
    simp [mul_comm]
  have hΦaff : ∀ l z, Φ l z = Λ l z + Φ l 0 := by
    intro l z
    have := is_const_of_fderiv_eq_zero (f := fun x ↦ Φ l x - Λ l x)
      ((hΦd l).sub (Λ l).differentiable) (fun x ↦ by
        rw [fderiv_fun_sub (hΦd l x) ((Λ l).differentiableAt), hΛ, ContinuousLinearMap.fderiv,
          sub_self]) z 0
    simp only [map_zero, sub_zero] at this
    linear_combination this
  let lin : L →+ ((Fin n → ℂ) →ₗ[ℂ] ℂ) :=
    { toFun := fun l ↦ (Λ l : (Fin n → ℂ) →ₗ[ℂ] ℂ)
      map_zero' := by ext; simp [Λ, hA'0]
      map_add' := fun l m ↦ by ext; simp [Λ, hA'add, add_mul, Finset.sum_add_distrib] }
  refine ⟨fun z ↦ -H z, lin, fun l ↦ Φ l 0, hHd.neg, fun l z ↦ ?_⟩
  have := hΦaff l z
  simp only [Φ] at this
  simp only [lin, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ContinuousLinearMap.coe_coe]
  linear_combination this

end Lattice

/-- A continuous logarithm of a holomorphic function is holomorphic: near each point it differs
from a branch of `log (a / a z₀) / 2πi` by the constant `F z₀`. -/
theorem dca_log_differentiable {a F : (Fin n → ℂ) → ℂ} (ha : Differentiable ℂ a)
    (hlog : ∀ v, a v = Complex.exp (2 * Real.pi * Complex.I * F v)) (hF : Continuous F) :
    Differentiable ℂ F := by
  intro z₀
  have h2πI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have ha₀ : a z₀ ≠ 0 := by rw [hlog]; exact Complex.exp_ne_zero _
  have hnear : ∀ᶠ w in 𝓝 z₀, ‖F w - F z₀‖ < 1 / 2 := by
    filter_upwards [Metric.tendsto_nhds.1 (hF.tendsto z₀) (1 / 2) (by norm_num)] with w hw
    rwa [← dist_eq_norm]
  have heq : (fun w ↦ F z₀ + Complex.log (a w * (a z₀)⁻¹) * (2 * Real.pi * Complex.I)⁻¹)
      =ᶠ[𝓝 z₀] F := by
    filter_upwards [hnear] with w hw
    have hre : |(F w - F z₀).re| < 1 / 2 := (Complex.abs_re_le_norm _).trans_lt hw
    have him : (2 * Real.pi * Complex.I * (F w - F z₀)).im = 2 * Real.pi * (F w - F z₀).re := by
      simp
    have hq : a w * (a z₀)⁻¹ = Complex.exp (2 * Real.pi * Complex.I * (F w - F z₀)) := by
      rw [hlog w, hlog z₀, ← div_eq_mul_inv, ← Complex.exp_sub]; ring_nf
    rw [hq, Complex.log_exp]
    · field_simp; ring
    · rw [him]; have := abs_lt.1 hre; nlinarith [Real.pi_pos]
    · rw [him]; have := abs_lt.1 hre; nlinarith [Real.pi_pos]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
  refine (differentiableAt_const _).add (DifferentiableAt.mul_const ?_ _)
  refine ((ha z₀).mul_const _).clog ?_
  rw [mul_inv_cancel₀ ha₀]
  exact Complex.one_mem_slitPlane

section Lattice

variable (L : Submodule ℤ (Fin n → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L]

theorem dca_chernForm_typeOneOne (a F : L → (Fin n → ℂ) → ℂ)
    (hlin : ∃ (h : (Fin n → ℂ) → ℂ) (lin : L →+ ((Fin n → ℂ) →ₗ[ℂ] ℂ)) (b : L → ℂ),
      Differentiable ℂ h ∧ ∀ (l : L) z, F l z + h (z + l) - h z = lin l z + b l)
    (hcoc : ∀ (l m : L) v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * F l v))
    (hF : ∀ l, Continuous (F l))
    (B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ) (hB : ∀ l m : L, B l m = chernForm F l m) :
    IsTypeOneOne (fun v w ↦ B v w) := by
  obtain ⟨h, lin, b, -, hrel⟩ := hlin
  have hF' : ∀ l z, F l z = lin l z + b l - h (z + l) + h z := fun l z ↦ by
    linear_combination hrel l z
  have hlf : ∀ l m : L, logForm F 0 l m = lin m l - lin l m := by
    intro l m
    simp only [logForm, hF', zero_add, map_zero]
    rw [add_comm (m : Fin n → ℂ) l]
    ring
  refine dca_typeOneOne_of_affine L lin B fun l m ↦ ?_
  rw [hB, ← hlf, spec_logForm_eq_chernForm a F hcoc hlog hF 0 l m]
  push_cast
  rfl

end Lattice

end HodgeLean.Foundations
