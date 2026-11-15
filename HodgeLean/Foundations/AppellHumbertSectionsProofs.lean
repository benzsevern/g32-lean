import HodgeLean.Foundations.AppellHumbertSectionsDefs

/-! # Proofs for the Appell--Humbert sections spec

* The cocycle of `holFactor` is an exponent identity: `iπE(l,m) + (π/2)(H(l,m) + conj H(l,m))`
  equals `πH(l,m)`, so no integrality is needed. `χ(0) = 1` follows from `semicharacter_add` at
  `(0,0)`.
* Reduction to generators is `AddSubgroup.closure_induction`, using the cocycle and the fact that
  the factor never vanishes. Translation by `w` rests on `H(l,w) - conj H(l,w) = 2i E(l,w)`, and
  products of sections on `holFactor` being multiplicative in the datum.
* Sections of the trivial datum are periodic, so bounded by their maximum on the closure of the
  fundamental domain of a real basis of the lattice; Liouville makes them constant.
* For the frozen `factor`, along `t ↦ v₀ + t w` a nonzero solution would make
  `t ↦ exp(π conj(t) H(w,l))` complex-differentiable at `0`; its derivatives along the real and
  imaginary axes are incompatible unless `H(w,l) = 0`.
* `latticeDualBasisQ` is the rational dual basis as a `ℚ`-basis of `Λ →+ ℚ`. On basis vectors,
  contraction with `latticeClass E` is the Gram matrix of `E`
  (`contract_latticeClass_apply_of_alt`). This gives injectivity, and for positive-definite data a
  trivial kernel (`gram_nondegenerate`, through `spec_positive_imaginary_nondegenerate` on the real
  span); `Symplectic.wedgePow_ne_zero_of_isNondegenerate` then gives the top power.
* Genus one: the datum has `χ(a + bτ) = exp(πi ab)`. The functional equation is checked on the
  generators `1` and `τ` with `jacobiTheta₂_add_left` and `jacobiTheta₂_add_left'`, using
  `conj τ = τ - 2i Im τ`. Nonvanishing follows from `∫₀¹ ϑ(x, τ) dx = 1`, integrating the series
  term by term.
-/

noncomputable section

namespace HodgeLean.Foundations.AppellHumbert

section LatticeClassHelpers

open Module

variable {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]

omit [Module.Finite ℤ Λ] in
theorem latticeDualBasis_apply_basis (i j : Free.ChooseBasisIndex ℤ Λ) :
    latticeDualBasis i (Free.chooseBasis ℤ Λ j) = if j = i then 1 else 0 := by
  simp [latticeDualBasis, Finsupp.single_apply]

/-- A rational character of the lattice is determined by its values on the chosen basis. -/
def latticeDualEquiv : (Λ →+ ℚ) ≃ₗ[ℚ] (Free.ChooseBasisIndex ℤ Λ → ℚ) where
  toFun φ i := φ (Free.chooseBasis ℤ Λ i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun c := ∑ i, c i • latticeDualBasis i
  left_inv φ := by
    ext x
    simp only [latticeDualBasis, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply,
      AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      Basis.coord_apply, Int.coe_castAddHom, smul_eq_mul]
    conv_rhs => rw [← (Free.chooseBasis ℤ Λ).sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  right_inv c := by
    funext j
    simp [latticeDualBasis_apply_basis]

/-- The rational dual basis, as a `ℚ`-basis of `Λ →+ ℚ`. -/
def latticeDualBasisQ : Basis (Free.ChooseBasisIndex ℤ Λ) ℚ (Λ →+ ℚ) :=
  Basis.ofEquivFun latticeDualEquiv

theorem latticeDualBasisQ_apply (i : Free.ChooseBasisIndex ℤ Λ) :
    latticeDualBasisQ i = latticeDualBasis (Λ := Λ) i := by
  classical
  rw [latticeDualBasisQ, Basis.coe_ofEquivFun]
  simp [latticeDualEquiv, Pi.single_apply]

theorem contract_latticeClass_apply (E : Λ →+ Λ →+ ℤ) (ψ : Dual ℚ (Λ →+ ℚ))
    (k : Free.ChooseBasisIndex ℤ Λ) :
    Symplectic.contract (latticeClass E) ψ (Free.chooseBasis ℤ Λ k) =
      ∑ i, ψ (latticeDualBasis i) * (((E (Free.chooseBasis ℤ Λ i) (Free.chooseBasis ℤ Λ k) -
        E (Free.chooseBasis ℤ Λ k) (Free.chooseBasis ℤ Λ i) : ℤ) : ℚ) / 2) := by
  simp [latticeClass, latticeDualBasis_apply_basis, Finset.sum_sub_distrib, mul_sub, sub_div]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

omit [Module.Free ℤ Λ] [Module.Finite ℤ Λ] in
theorem antisymm_of_alt (E : Λ →+ Λ →+ ℤ) (hE : ∀ x, E x x = 0) (x y : Λ) :
    E y x = -E x y := by
  have := hE (x + y)
  simp only [map_add, AddMonoidHom.add_apply, hE] at this
  omega

theorem contract_latticeClass_apply_of_alt (E : Λ →+ Λ →+ ℤ) (hE : ∀ x, E x x = 0)
    (ψ : Dual ℚ (Λ →+ ℚ)) (k : Free.ChooseBasisIndex ℤ Λ) :
    Symplectic.contract (latticeClass E) ψ (Free.chooseBasis ℤ Λ k) =
      ∑ i, ψ (latticeDualBasis i) *
        (E (Free.chooseBasis ℤ Λ i) (Free.chooseBasis ℤ Λ k) : ℚ) := by
  rw [contract_latticeClass_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [antisymm_of_alt E hE]
  push_cast
  ring

omit [Module.Finite ℤ Λ] in
theorem biadditive_ext {E₁ E₂ : Λ →+ Λ →+ ℤ}
    (h : ∀ i j, E₁ (Free.chooseBasis ℤ Λ i) (Free.chooseBasis ℤ Λ j) =
      E₂ (Free.chooseBasis ℤ Λ i) (Free.chooseBasis ℤ Λ j)) : E₁ = E₂ := by
  have h1 : ∀ j x, E₁ x (Free.chooseBasis ℤ Λ j) = E₂ x (Free.chooseBasis ℤ Λ j) := fun j x ↦ by
    have : (E₁.flip (Free.chooseBasis ℤ Λ j)).toIntLinearMap =
        (E₂.flip (Free.chooseBasis ℤ Λ j)).toIntLinearMap :=
      (Free.chooseBasis ℤ Λ).ext fun i ↦ by simpa using h i j
    simpa using LinearMap.congr_fun this x
  ext x y
  have : (E₁ x).toIntLinearMap = (E₂ x).toIntLinearMap :=
    (Free.chooseBasis ℤ Λ).ext fun j ↦ by simpa using h1 j x
  simpa using LinearMap.congr_fun this y

end LatticeClassHelpers

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem hermitian_zero_left (H : HermitianForm (V := V)) (y : V) : H.toFun 0 y = 0 := by
  simpa using H.smul_left 0 0 y

omit [FiniteDimensional ℂ V] in
theorem hermitian_zero_right (H : HermitianForm (V := V)) (x : V) : H.toFun x 0 = 0 := by
  simpa using H.smul_right 0 x 0

omit [FiniteDimensional ℂ V] in
theorem semicharacter_zero (D : Datum (V := V)) : D.semicharacter 0 = 1 := by
  have h := D.semicharacter_add 0 0
  simp only [add_zero, ZeroMemClass.coe_zero, HermitianForm.imaginary, hermitian_zero_left,
    Complex.zero_im, mul_zero, Circle.exp_zero, mul_one] at h
  exact (mul_eq_left.mp h.symm)

theorem exp_shuffle (χ T a b c h : ℂ) :
    Complex.exp (-(Real.pi * (a + star h))) *
        (χ * Complex.exp (Real.pi * (b + h) + Real.pi / 2 * c) * T) =
      χ * Complex.exp (↑(2 * Real.pi * h.im) * Complex.I) *
        Complex.exp (Real.pi * b + Real.pi / 2 * c) * (Complex.exp (-(Real.pi * a)) * T) := by
  have e : -(Real.pi * (a + star h)) + (Real.pi * (b + h) + Real.pi / 2 * c) =
      ↑(2 * Real.pi * h.im) * Complex.I + (Real.pi * b + Real.pi / 2 * c) +
        -(Real.pi * a) := by
    apply Complex.ext <;> simp <;> ring
  calc _ = χ * Complex.exp (-(Real.pi * (a + star h)) +
        (Real.pi * (b + h) + Real.pi / 2 * c)) * T := by
          rw [Complex.exp_add (-(Real.pi * (a + star h)))]; ring
    _ = _ := by
          rw [e, Complex.exp_add (↑(2 * Real.pi * h.im) * Complex.I +
            (Real.pi * b + Real.pi / 2 * c)), Complex.exp_add (↑(2 * Real.pi * h.im) * Complex.I)]
          ring

omit [FiniteDimensional ℂ V] in
theorem holFactor_ne_zero (D : Datum (V := V)) (l : D.lattice) (v : V) : holFactor D l v ≠ 0 :=
  mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _)

set_option linter.unusedSectionVars false in
theorem spec_holFactor_cocycle_aux (D : Datum (V := V)) (l m : D.lattice) (v : V) :
    holFactor D (l + m) v = holFactor D l (v + m) * holFactor D m v := by
  have hsymm : D.hermitian.toFun (m : V) l = star (D.hermitian.toFun l m) :=
    (D.hermitian.conj_symm m l).symm
  unfold holFactor
  rw [D.semicharacter_add, Submodule.coe_add, Circle.coe_mul, Circle.coe_mul, Circle.coe_exp]
  simp only [D.hermitian.add_left, D.hermitian.add_right, hsymm, HermitianForm.imaginary]
  generalize (D.semicharacter l : ℂ) = cl
  generalize (D.semicharacter m : ℂ) = cm
  generalize D.hermitian.toFun l m = h
  rw [mul_assoc (cl * cm), ← Complex.exp_add, mul_mul_mul_comm, ← Complex.exp_add]
  congr 2
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.div_ofNat_re, Complex.div_ofNat_im] <;>
    ring

set_option linter.unusedSectionVars false in
theorem spec_holFactor_zero_aux (D : Datum (V := V)) (v : V) : holFactor D 0 v = 1 := by
  simp [holFactor, semicharacter_zero, hermitian_zero_left]

set_option linter.unusedSectionVars false in
theorem spec_sections_of_generators_aux (D : Datum (V := V)) (S : Set D.lattice)
    (hS : AddSubgroup.closure S = ⊤) (θ : V → ℂ) (hθ : Differentiable ℂ θ)
    (hgen : ∀ l ∈ S, ∀ v : V, θ (v + l) = holFactor D l v * θ v) :
    θ ∈ sections D := by
  refine ⟨hθ, fun l ↦ ?_⟩
  have hl : l ∈ AddSubgroup.closure S := hS ▸ AddSubgroup.mem_top l
  induction hl using AddSubgroup.closure_induction with
  | mem l hl => exact hgen l hl
  | zero => intro v; simp [spec_holFactor_zero_aux]
  | add l m _ _ hl hm =>
    intro v
    rw [spec_holFactor_cocycle_aux, Submodule.coe_add,
      show v + (↑l + ↑m) = (v + ↑m) + ↑l by abel, hl, hm]
    ring
  | neg l _ hl =>
    intro v
    have h1 := hl (v + ↑(-l))
    have h2 := spec_holFactor_cocycle_aux D l (-l) v
    rw [add_neg_cancel, spec_holFactor_zero_aux] at h2
    have e : v + ↑(-l) + ↑l = v := by simp
    rw [e] at h1
    linear_combination (-(holFactor D (-l) v)) * h1 + θ (v + ↑(-l)) * h2

theorem spec_sections_translate_aux (D : Datum (V := V)) (w : V) (θ : V → ℂ)
    (hθ : θ ∈ sections D) :
    (fun v ↦ Complex.exp (-(Real.pi * D.hermitian.toFun w v)) * θ (v + w)) ∈
      sections (D.twist w) := by
  obtain ⟨hd, hfe⟩ := hθ
  let f : V →ₗ[ℂ] ℂ :=
    { toFun := D.hermitian.toFun w
      map_add' := D.hermitian.add_right w
      map_smul' := fun c x ↦ D.hermitian.smul_right c w x }
  have hf : Differentiable ℂ (fun v ↦ D.hermitian.toFun w v) :=
    (LinearMap.toContinuousLinearMap f).differentiable
  refine ⟨((hf.const_mul _).neg.cexp).mul (hd.comp (differentiable_id.add_const w)),
    fun l v ↦ ?_⟩
  beta_reduce
  rw [show v + ↑l + w = (v + w) + ↑l by abel, hfe l (v + w)]
  simp only [holFactor, Datum.twist, Circle.coe_mul, Circle.coe_exp, D.hermitian.add_right,
    HermitianForm.imaginary]
  rw [← D.hermitian.conj_symm w ↑l]
  exact exp_shuffle _ _ _ _ _ _

set_option linter.unusedSectionVars false in
theorem spec_twist_lattice_aux (D : Datum (V := V)) (m : D.lattice) :
    (D.twist m).semicharacter = D.semicharacter := by
  funext l
  obtain ⟨n, hn⟩ := D.integral l m
  show D.semicharacter l * Circle.exp (2 * Real.pi * D.hermitian.imaginary l m) = _
  rw [hn, Circle.exp_two_pi_mul_int, mul_one]

set_option linter.unusedSectionVars false in
theorem spec_sections_mul_aux (D₁ D₂ : Datum (V := V)) (h : D₁.lattice ≤ D₂.lattice)
    (θ₁ θ₂ : V → ℂ) (h₁ : θ₁ ∈ sections D₁) (h₂ : θ₂ ∈ sections D₂) :
    θ₁ * θ₂ ∈ sections (D₁.tensor D₂ h) := by
  refine ⟨h₁.1.mul h₂.1, fun l v ↦ ?_⟩
  have e1 := h₁.2 l v
  have e2 : θ₂ (v + l) = holFactor D₂ ⟨l, h l.2⟩ v * θ₂ v := h₂.2 ⟨l, h l.2⟩ v
  simp only [Pi.mul_apply]
  rw [e1, e2]
  simp only [holFactor, Datum.tensor, HermitianForm.add, Circle.coe_mul]
  rw [show ∀ a b c d : ℂ, (Real.pi : ℂ) * (a + b) + Real.pi / 2 * (c + d) =
    (Real.pi * a + Real.pi / 2 * c) + (Real.pi * b + Real.pi / 2 * d) from
    fun a b c d ↦ by ring, Complex.exp_add (_ + _) (_ + _)]
  ring

theorem spec_trivial_sections_aux (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (θ : V → ℂ) : θ ∈ sections (Datum.trivial L) ↔ ∃ c : ℂ, θ = fun _ ↦ c := by
  have hfac : ∀ (l : (Datum.trivial L).lattice) v, holFactor (Datum.trivial L) l v = 1 :=
    fun l v ↦ by simp [holFactor, Datum.trivial, HermitianForm.zero]
  constructor
  · rintro ⟨hd, hfe⟩
    have hper : ∀ (l : (Datum.trivial L).lattice) v, θ (v + l) = θ v := fun l v ↦ by
      rw [hfe l v, hfac l v, one_mul]
    have : Module.Free ℤ L := ZLattice.module_free ℝ L
    have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
    let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
    have hspan : Submodule.span ℤ (Set.range b) = L := Module.Basis.ofZLatticeBasis_span ℝ L _
    have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
      (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hd.continuous.continuousOn
    have hall : ∀ v, θ v = θ (ZSpan.fract b v) := by
      intro v
      have hm : (ZSpan.floor b v : V) ∈ L := hspan.le (ZSpan.floor b v).2
      rw [ZSpan.fract_apply]
      conv_lhs => rw [← sub_add_cancel v (ZSpan.floor b v : V)]
      exact hper ⟨_, hm⟩ _
    have hb : Bornology.IsBounded (Set.range θ) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨C, ?_⟩
      rintro _ ⟨v, rfl⟩
      rw [hall]
      exact hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain b v))
    exact ⟨θ 0, funext fun v ↦ hd.apply_eq_apply_of_bounded hb v 0⟩
  · rintro ⟨c, rfl⟩
    exact ⟨differentiable_const c, fun l v ↦ by rw [hfac, one_mul]⟩

theorem real_hasDerivAt_exp_mul (c : ℂ) :
    HasDerivAt (fun r : ℝ ↦ Complex.exp (↑r * c)) c 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const c).cexp

set_option linter.unusedSectionVars false in
theorem spec_factor_no_holomorphic_solutions_aux (D : Datum (V := V))
    (hH : ∃ (l : D.lattice) (w : V), D.hermitian.toFun l w ≠ 0) (θ : V → ℂ)
    (hθ : Differentiable ℂ θ) (hfe : ∀ (l : D.lattice) (v : V), θ (v + l) = factor D l v * θ v) :
    θ = 0 := by
  obtain ⟨l, w, hlw⟩ := hH
  set α := D.hermitian.toFun w l with hα
  have hα0 : α ≠ 0 := by
    rw [hα, ← D.hermitian.conj_symm w l]
    exact star_ne_zero.mpr hlw
  funext v₀
  by_contra hne
  set c := (D.semicharacter l : ℂ) *
    Complex.exp (Real.pi * D.hermitian.toFun v₀ l + Real.pi / 2 * D.hermitian.toFun l l)
  have hc : c ≠ 0 := mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _)
  set g : ℂ → ℂ := fun t ↦ θ (v₀ + t • w)
  set h : ℂ → ℂ := fun t ↦ θ (v₀ + t • w + l)
  set e : ℂ → ℂ := fun t ↦ Complex.exp (Real.pi * (star t * α))
  have hrel : ∀ t, h t = c * e t * g t := by
    intro t
    simp only [h, g, e, c]
    rw [hfe l, factor, D.hermitian.add_left, D.hermitian.smul_left, mul_add, ← hα,
      add_right_comm, Complex.exp_add _ (Real.pi * (star t * α))]
    ring
  have hg : Differentiable ℂ g :=
    hθ.comp ((differentiable_const _).add (differentiable_id.smul_const w))
  have hh : Differentiable ℂ h :=
    hθ.comp (((differentiable_const _).add (differentiable_id.smul_const w)).add_const _)
  have hg0 : g 0 ≠ 0 := by simpa [g] using hne
  have hev : e =ᶠ[nhds 0] fun t ↦ h t / c / g t := by
    filter_upwards [(hg.continuous.continuousAt (x := 0)).eventually_ne hg0] with t ht
    rw [hrel]
    field_simp
  have hd := ((((hh 0).hasDerivAt.div_const c).div (hg 0).hasDerivAt hg0).differentiableAt
    ).hasDerivAt
  set d := deriv (fun t ↦ h t / c / g t) 0
  have he : HasDerivAt e d 0 := hd.congr_of_eventuallyEq hev
  have h1 : HasDerivAt (fun r : ℝ ↦ e r) d 0 := by
    have he' : HasDerivAt e d ((0 : ℝ) : ℂ) := by rw [Complex.ofReal_zero]; exact he
    exact he'.comp_ofReal
  have h1' : HasDerivAt (fun r : ℝ ↦ e r) (Real.pi * α) 0 := by
    have : (fun r : ℝ ↦ e r) = fun r : ℝ ↦ Complex.exp (↑r * (Real.pi * α)) := by
      funext r
      simp only [e, Complex.star_def, Complex.conj_ofReal]
      ring_nf
    rw [this]
    exact real_hasDerivAt_exp_mul _
  have h2 : HasDerivAt (fun r : ℝ ↦ e (r * Complex.I)) (d * Complex.I) 0 := by
    have he' : HasDerivAt e d (((0 : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.ofReal_zero, zero_mul]; exact he
    have hI : HasDerivAt (fun r : ℝ ↦ (r : ℂ) * Complex.I) Complex.I 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I
    have := he'.comp (0 : ℝ) hI
    exact this
  have h2' : HasDerivAt (fun r : ℝ ↦ e (r * Complex.I)) (-(Real.pi * α * Complex.I)) 0 := by
    have : (fun r : ℝ ↦ e (r * Complex.I)) =
        fun r : ℝ ↦ Complex.exp (↑r * (-(Real.pi * α * Complex.I))) := by
      funext r
      simp only [e, Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring_nf
    rw [this]
    exact real_hasDerivAt_exp_mul _
  have e1 := h1.unique h1'
  have e2 := h2.unique h2'
  have : (Real.pi : ℂ) * α * Complex.I * 2 = 0 := by
    linear_combination e2 - Complex.I * e1
  simp [Real.pi_ne_zero, hα0, Complex.I_ne_zero] at this

omit [FiniteDimensional ℂ V] in
theorem hermitian_real_smul_left (H : HermitianForm (V := V)) (r : ℝ) (x y : V) :
    H.toFun (r • x) y = r * H.toFun x y := by
  rw [← algebraMap_smul ℂ r x, H.smul_left]
  simp

omit [FiniteDimensional ℂ V] in
theorem hermitian_real_smul_right (H : HermitianForm (V := V)) (r : ℝ) (x y : V) :
    H.toFun x (r • y) = r * H.toFun x y := by
  rw [← algebraMap_smul ℂ r y, H.smul_right]
  rfl

omit [FiniteDimensional ℂ V] in
theorem imForm_cast (D : Datum (V := V)) (l m : D.lattice) :
    (D.imForm l m : ℝ) = D.hermitian.imaginary l m := by
  obtain ⟨n, hn⟩ := D.integral l m
  show ((⌊D.hermitian.imaginary l m⌋ : ℤ) : ℝ) = _
  rw [hn, Int.floor_intCast]

omit [FiniteDimensional ℂ V] in
theorem imForm_self (D : Datum (V := V)) (x : D.lattice) : D.imForm x x = 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [imForm_cast, Int.cast_zero, HermitianForm.imaginary]
  exact Complex.conj_eq_iff_im.mp (D.hermitian.conj_symm x x)

/-- For a positive-definite datum, the Gram matrix of `E = Im H` on a `ℤ`-basis of the lattice
has trivial left kernel over `ℚ`. -/
theorem gram_nondegenerate (D : Datum (V := V)) [Module.Free ℤ D.lattice]
    [Module.Finite ℤ D.lattice] (hH : D.hermitian.IsPositiveDefinite)
    (q : Module.Free.ChooseBasisIndex ℤ D.lattice → ℚ)
    (hq : ∀ k, ∑ i, q i * (D.imForm (Module.Free.chooseBasis ℤ D.lattice i)
      (Module.Free.chooseBasis ℤ D.lattice k) : ℚ) = 0) :
    q = 0 := by
  set b := Module.Free.chooseBasis ℤ D.lattice
  let bR := b.ofZLatticeBasis ℝ D.lattice
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ D.hermitian.imaginary
    (fun x y z ↦ by simp [HermitianForm.imaginary, D.hermitian.add_left])
    (fun r x y ↦ by simp [HermitianForm.imaginary, hermitian_real_smul_left])
    (fun x y z ↦ by simp [HermitianForm.imaginary, D.hermitian.add_right])
    (fun r x y ↦ by simp [HermitianForm.imaginary, hermitian_real_smul_right])
  have hBapp : ∀ a c, B a c = D.hermitian.imaginary a c := fun _ _ ↦ rfl
  set x : V := ∑ i, (q i : ℝ) • (b i : V)
  have hxk : ∀ k, B x (bR k) = 0 := by
    intro k
    simp only [x, bR, Module.Basis.ofZLatticeBasis_apply, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hBapp, ← imForm_cast]
    exact_mod_cast hq k
  have hB : B x = 0 := bR.ext fun k ↦ by rw [hxk k, LinearMap.zero_apply]
  have hx0 : x = 0 := spec_positive_imaginary_nondegenerate D.hermitian hH x fun y ↦ by
    simpa [hBapp] using LinearMap.congr_fun hB y
  have hli := Fintype.linearIndependent_iff.mp bR.linearIndependent (fun i ↦ (q i : ℝ))
    (by simpa [bR] using hx0)
  funext i
  exact_mod_cast hli i

theorem spec_latticeClass_positive_nondegenerate_aux (D : Datum (V := V))
    [Module.Free ℤ D.lattice] [Module.Finite ℤ D.lattice]
    (hH : D.hermitian.IsPositiveDefinite) :
    Symplectic.IsNondegenerate (latticeClass D.imForm) := by
  have : FiniteDimensional ℚ (D.lattice →+ ℚ) := Module.Finite.of_basis latticeDualBasisQ
  have hinj : Function.Injective (Symplectic.contract (latticeClass D.imForm)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ψ hψ
    have hq := gram_nondegenerate D hH (fun i ↦ ψ (latticeDualBasis i)) fun k ↦ by
      rw [← contract_latticeClass_apply_of_alt _ (imForm_self D), hψ]
      rfl
    exact latticeDualBasisQ.ext fun i ↦ by
      rw [latticeDualBasisQ_apply, LinearMap.zero_apply]
      exact congrFun hq i
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    Subspace.dual_finrank_eq).mp hinj⟩

theorem spec_latticeClass_wedgePow_ne_zero_aux (D : Datum (V := V))
    [Module.Free ℤ D.lattice] [Module.Finite ℤ D.lattice]
    (hH : D.hermitian.IsPositiveDefinite) :
    Symplectic.wedgePow (latticeClass D.imForm) (Module.finrank ℂ V) ≠ 0 := by
  apply Symplectic.wedgePow_ne_zero_of_isNondegenerate
    (spec_latticeClass_positive_nondegenerate_aux D hH)
  rw [Module.finrank_eq_card_basis latticeDualBasisQ, ← Module.finrank_eq_card_chooseBasisIndex,
    ZLattice.rank ℝ D.lattice, finrank_real_of_complex]

theorem spec_trivial_datum_falsification_aux (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] [Module.Free ℤ (Datum.trivial L).lattice]
    [Module.Finite ℤ (Datum.trivial L).lattice] :
    (∀ c : ℂ, (fun _ : V ↦ c) ∈ sections (Datum.trivial L)) ∧
      latticeClass (Datum.trivial L).imForm = 0 ∧
      ∀ g : ℕ, 0 < g → Symplectic.wedgePow (latticeClass (Datum.trivial L).imForm) g = 0 := by
  have h0 : (Datum.trivial L).imForm = 0 := by
    ext l m
    show ⌊(Datum.trivial L).hermitian.imaginary l m⌋ = 0
    simp [Datum.trivial, HermitianForm.zero, HermitianForm.imaginary]
  refine ⟨fun c ↦ (spec_trivial_sections_aux L _).2 ⟨c, rfl⟩, ?_, fun g hg ↦ ?_⟩
  · rw [h0]; simp [latticeClass]
  · rw [h0]
    apply Subtype.ext
    rw [Symplectic.coe_wedgePow]
    simp [latticeClass, zero_pow hg.ne']

end Lattice

theorem integral_jacobiTheta₂_term (n : ℤ) (τ : ℂ) :
    ∫ x in (0 : ℝ)..1, jacobiTheta₂_term n x τ = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn
    simp [jacobiTheta₂_term]
  · have hc : 2 * (Real.pi : ℂ) * Complex.I * n ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hn]
    have e : ∀ x : ℝ, jacobiTheta₂_term n x τ = Complex.exp (Real.pi * Complex.I * n ^ 2 * τ) *
        Complex.exp ((2 * Real.pi * Complex.I * n) * x) := by
      intro x
      rw [jacobiTheta₂_term, ← Complex.exp_add]
      ring_nf
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_one, mul_one,
        show 2 * (Real.pi : ℂ) * Complex.I * n = n * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h1]
    simp

/-- The zeroth Fourier coefficient of `x ↦ ϑ(x, τ)` is `1`; in particular `ϑ(·, τ) ≠ 0`. -/
theorem integral_jacobiTheta₂ {τ : ℂ} (hτ : 0 < τ.im) :
    ∫ x in (0 : ℝ)..1, jacobiTheta₂ x τ = 1 := by
  let F : ℤ → C(ℝ, ℂ) := fun n ↦
    ⟨fun x ↦ jacobiTheta₂_term n x τ, by unfold jacobiTheta₂_term; fun_prop⟩
  have hsum : Summable fun n : ℤ ↦
      ‖(F n).restrict (⟨Set.uIcc 0 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
    refine (summable_pow_mul_jacobiTheta₂_term_bound 0 hτ 0).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun n ↦ ?_
    refine (ContinuousMap.norm_le _ (by positivity :
      (0 : ℝ) ≤ (|n| ^ 0 : ℝ) * Real.exp (-Real.pi * (τ.im * n ^ 2 - 2 * 0 * |n|)))).mpr
      fun x ↦ ?_
    simpa [F] using norm_jacobiTheta₂_term_le hτ (S := 0) (z := ((x : ℝ) : ℂ)) (by simp) le_rfl n
  have h := intervalIntegral.hasSum_intervalIntegral_of_summable_norm hsum
  simp only [F, ContinuousMap.coe_mk, integral_jacobiTheta₂_term] at h
  show ∫ x in (0 : ℝ)..1, ∑' i : ℤ, jacobiTheta₂_term i x τ = 1
  exact h.unique (hasSum_ite_eq 0 1)

theorem spec_jacobiTheta₂_section_aux (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ D : Datum (V := ℂ), D.lattice = Submodule.span ℤ {1, τ} ∧
      (∀ z w : ℂ, D.hermitian.toFun z w = star z * w / τ.im) ∧
      D.hermitian.IsPositiveDefinite ∧
      (fun z ↦ Complex.exp (Real.pi * z ^ 2 / (2 * τ.im)) * jacobiTheta₂ z τ) ∈ sections D ∧
      (fun z ↦ Complex.exp (Real.pi * z ^ 2 / (2 * τ.im)) * jacobiTheta₂ z τ) ≠ 0 := by
  have hy : (τ.im : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hli : LinearIndependent ℝ ![(1 : ℂ), τ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have him := congrArg Complex.im hst
    have hre := congrArg Complex.re hst
    simp at him hre
    have ht : t = 0 := by
      rcases him with h | h
      · exact h
      · exact absurd h hτ.ne'
    subst ht
    simpa using hre
  let bR : Module.Basis (Fin 2) ℝ ℂ :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [Complex.finrank_real_complex])
  have hbR : Set.range bR = {1, τ} := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.range_cons, Matrix.range_cons,
      Matrix.range_empty]
    simp [Set.pair_comm]
  set L := Submodule.span ℤ (Set.range bR) with hLdef
  have hL : L = Submodule.span ℤ {1, τ} := by rw [hLdef, hbR]
  have hcoord : ∀ z ∈ L, ∃ a b : ℤ, z = a + b * τ := by
    intro z hz
    rw [hL, Submodule.mem_span_pair] at hz
    obtain ⟨a, b, rfl⟩ := hz
    exact ⟨a, b, by simp [zsmul_eq_mul]⟩
  let H : HermitianForm (V := ℂ) :=
    { toFun := fun z w ↦ star z * w / τ.im
      add_left := fun x y z ↦ by simp [add_mul, add_div]
      smul_left := fun c x y ↦ by simp [mul_assoc, mul_div_assoc]
      add_right := fun x y z ↦ by simp [mul_add, add_div]
      smul_right := fun c x y ↦ by simp only [smul_eq_mul]; ring
      conj_symm := fun x y ↦ by simp [mul_comm] }
  have hEim : ∀ a b c d : ℤ, (H.toFun (a + b * τ) (c + d * τ)).im = a * d - b * c := by
    intro a b c d
    simp only [H, Complex.div_ofReal_im, Complex.mul_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im,
      Complex.mul_re]
    field_simp
    ring
  let f : ℂ → ℝ := fun z ↦ (z.re - z.im / τ.im * τ.re) * (z.im / τ.im)
  have hf : ∀ a b : ℤ, f (a + b * τ) = a * b := by
    intro a b
    simp only [f, Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im,
      Complex.mul_re, Complex.mul_im]
    field_simp
    ring
  let D : Datum (V := ℂ) :=
    { lattice := L
      hermitian := H
      integral := fun l m ↦ by
        obtain ⟨a, b, hl⟩ := hcoord l l.2
        obtain ⟨c, d, hm⟩ := hcoord m m.2
        exact ⟨a * d - b * c, by rw [HermitianForm.imaginary, hl, hm, hEim]; push_cast; ring⟩
      semicharacter := fun l ↦ Circle.exp (Real.pi * f l)
      semicharacter_add := fun l m ↦ by
        obtain ⟨a, b, hl⟩ := hcoord l l.2
        obtain ⟨c, d, hm⟩ := hcoord m m.2
        have hlm : ((l + m : L) : ℂ) = ((a + c : ℤ) : ℂ) + ((b + d : ℤ) : ℂ) * τ := by
          rw [Submodule.coe_add, hl, hm]; push_cast; ring
        rw [hlm, hl, hm, hf, hf, hf, HermitianForm.imaginary, hEim, ← Circle.exp_add,
          ← Circle.exp_add,
          show Real.pi * (((a + c : ℤ) : ℝ) * ((b + d : ℤ) : ℝ)) = Real.pi * (a * b) +
            Real.pi * (c * d) + Real.pi * (a * d - b * c) + 2 * Real.pi * ((b * c : ℤ) : ℝ) by
            push_cast; ring,
          Circle.exp_add _ (2 * Real.pi * _), Circle.exp_two_pi_mul_int, mul_one] }
  have h1L : (1 : ℂ) ∈ L := by rw [hL]; exact Submodule.subset_span (by simp)
  have hτL : τ ∈ L := by rw [hL]; exact Submodule.subset_span (by simp)
  refine ⟨D, hL, fun z w ↦ rfl, ?_, ?_, ?_⟩
  · intro v hv
    show 0 < (star v * v / τ.im).re
    rw [Complex.div_ofReal_re]
    have hn := Complex.normSq_pos.mpr hv
    rw [Complex.normSq_apply] at hn
    have : (star v * v).re = v.re * v.re + v.im * v.im := by
      simp [Complex.mul_re]
    rw [this]
    exact div_pos hn hτ
  · apply spec_sections_of_generators_aux D {⟨1, h1L⟩, ⟨τ, hτL⟩}
    · refine eq_top_iff.mpr fun x _ ↦ ?_
      obtain ⟨a, b, hx⟩ := hcoord x x.2
      have : x = a • (⟨1, h1L⟩ : D.lattice) + b • (⟨τ, hτL⟩ : D.lattice) :=
        Subtype.ext (by simp [hx, zsmul_eq_mul])
      rw [this]
      exact add_mem (zsmul_mem (AddSubgroup.subset_closure (by simp)) _)
        (zsmul_mem (AddSubgroup.subset_closure (by simp)) _)
    · intro z
      exact ((by fun_prop : Differentiable ℂ fun z : ℂ ↦
        Complex.exp (Real.pi * z ^ 2 / (2 * τ.im))) z).mul
        (differentiableAt_jacobiTheta₂_fst z hτ)
    · rintro l (rfl | rfl) v
      · have hf1 : f 1 = 0 := by simp [f]
        show Complex.exp (Real.pi * (v + 1) ^ 2 / (2 * τ.im)) * jacobiTheta₂ (v + 1) τ =
          (Circle.exp (Real.pi * f 1) : ℂ) * Complex.exp (Real.pi * (star (1 : ℂ) * v / τ.im) +
            Real.pi / 2 * (star (1 : ℂ) * 1 / τ.im)) *
            (Complex.exp (Real.pi * v ^ 2 / (2 * τ.im)) * jacobiTheta₂ v τ)
        rw [hf1, mul_zero, Circle.exp_zero, Circle.coe_one, one_mul, jacobiTheta₂_add_left,
          ← mul_assoc, ← Complex.exp_add]
        congr 2
        simp only [star_one, one_mul]
        field_simp
        ring
      · have hfτ : f τ = 0 := by simp [f, div_self hτ.ne']
        have hst : star τ = τ - 2 * Complex.I * τ.im := by
          apply Complex.ext <;> simp
          ring
        show Complex.exp (Real.pi * (v + τ) ^ 2 / (2 * τ.im)) * jacobiTheta₂ (v + τ) τ =
          (Circle.exp (Real.pi * f τ) : ℂ) * Complex.exp (Real.pi * (star τ * v / τ.im) +
            Real.pi / 2 * (star τ * τ / τ.im)) *
            (Complex.exp (Real.pi * v ^ 2 / (2 * τ.im)) * jacobiTheta₂ v τ)
        rw [hfτ, mul_zero, Circle.exp_zero, Circle.coe_one, one_mul, jacobiTheta₂_add_left',
          ← mul_assoc, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add, hst]
        congr 2
        field_simp
        ring
  · intro h0
    have hint := integral_jacobiTheta₂ hτ
    have hz : ∀ x : ℝ, jacobiTheta₂ (x : ℂ) τ = 0 := fun x ↦ by
      simpa [Complex.exp_ne_zero] using congrFun h0 x
    simp [hz] at hint

section LatticeClass

variable {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]

theorem spec_latticeClass_add_aux (E₁ E₂ : Λ →+ Λ →+ ℤ) :
    latticeClass (E₁ + E₂) = latticeClass E₁ + latticeClass E₂ := by
  simp only [latticeClass, AddMonoidHom.add_apply, Int.cast_add, add_div, add_smul,
    Finset.sum_add_distrib]

theorem spec_latticeClass_injective_aux (E₁ E₂ : Λ →+ Λ →+ ℤ)
    (h₁ : ∀ x, E₁ x x = 0) (h₂ : ∀ x, E₂ x x = 0)
    (h : latticeClass E₁ = latticeClass E₂) : E₁ = E₂ := by
  refine biadditive_ext fun i k ↦ ?_
  have := congrArg (fun ω ↦ Symplectic.contract ω (latticeDualBasisQ.coord i)
    (Module.Free.chooseBasis ℤ Λ k)) h
  simp only [contract_latticeClass_apply_of_alt _ h₁, contract_latticeClass_apply_of_alt _ h₂,
    ← latticeDualBasisQ_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply] at this
  simpa using this

end LatticeClass

end HodgeLean.Foundations.AppellHumbert
