import HodgeLean.Foundations.Program.PeriodMarkingDefs

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (M : Type*) [AddCommGroup M]

def b64b_realPart : (ℂ ⊗[ℤ] M) →ₗ[ℝ] (ℝ ⊗[ℤ] M) where
  toFun := LinearMap.rTensor M (Complex.reLm.restrictScalars ℤ)
  map_add' := map_add _
  map_smul' r x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul c x =>
      simp only [TensorProduct.smul_tmul', LinearMap.rTensor_tmul]
      congr 1
      exact Complex.reLm.map_smul r c

def b64b_realIncl : (ℝ ⊗[ℤ] M) →ₗ[ℝ] (ℂ ⊗[ℤ] M) where
  toFun := LinearMap.rTensor M (Complex.ofRealLI.toLinearMap.restrictScalars ℤ)
  map_add' := map_add _
  map_smul' r x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul c x =>
      simp only [TensorProduct.smul_tmul', LinearMap.rTensor_tmul]
      congr 1
      exact Complex.ofRealLI.toLinearMap.map_smul r c

theorem b64b_realPart_tmul (c : ℂ) (x : M) :
    b64b_realPart M (c ⊗ₜ[ℤ] x) = c.re ⊗ₜ[ℤ] x := rfl

theorem b64b_realIncl_tmul (c : ℝ) (x : M) :
    b64b_realIncl M (c ⊗ₜ[ℤ] x) = (c : ℂ) ⊗ₜ[ℤ] x := rfl

theorem b64b_realPart_realIncl (x : ℝ ⊗[ℤ] M) :
    b64b_realPart M (b64b_realIncl M x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x => rfl

theorem b64b_realIncl_realPart (x : ℂ ⊗[ℤ] M) :
    (2 : ℂ) • b64b_realIncl M (b64b_realPart M x) = x + b2_conj M x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]; abel
  | tmul c x =>
    rw [b64b_realPart_tmul, b64b_realIncl_tmul, b2a_conj_tmul,
      TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
    congr 1
    simpa only [Complex.real_smul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
      using (Complex.add_conj c).symm

theorem b64b_realPart_injective_on (F : Submodule ℂ (ℂ ⊗[ℤ] M))
    (hW : b2_IsWeightOne M F) :
    Function.Injective ((b64b_realPart M).comp (F.subtype.restrictScalars ℝ)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hs := b64b_realIncl_realPart M x.val
  rw [show b64b_realPart M x.val = 0 from hx, map_zero, smul_zero] at hs
  have hc : b2_conj M x.val = -x.val := by
    apply eq_neg_of_add_eq_zero_right
    exact hs.symm
  apply Subtype.ext
  apply (Submodule.mem_bot ℂ).1
  apply hW.disjoint.le_bot
  refine ⟨x.property, ?_⟩
  rw [← neg_neg x.val, ← hc]
  exact (b2_conjSubmodule M F).neg_mem (b2a_conj_mem_conjSubmodule x.property)

theorem b64b_realPart_equiv [Module.Free ℤ M] [Module.Finite ℤ M]
    (F : Submodule ℂ (ℂ ⊗[ℤ] M)) (hW : b2_IsWeightOne M F) :
    ∃ e : F ≃ₗ[ℝ] (ℝ ⊗[ℤ] M), ∀ x, e x = b64b_realPart M x.val := by
  let : Module.Finite ℝ F := Module.Finite.trans ℂ F
  let f := (b64b_realPart M).comp (F.subtype.restrictScalars ℝ)
  have hi : Function.Injective f := b64b_realPart_injective_on M F hW
  have hd : Module.finrank ℝ F = Module.finrank ℝ (ℝ ⊗[ℤ] M) := by
    have h := Submodule.finrank_add_eq_of_isCompl hW
    rw [b2a_finrank_conjSubmodule F, Module.finrank_baseChange] at h
    rw [← Module.finrank_mul_finrank ℝ ℂ F, Complex.finrank_real_complex,
      Module.finrank_baseChange]
    omega
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi
  exact ⟨LinearEquiv.ofBijective f ⟨hi, hs⟩, fun _ => rfl⟩

theorem b64b_realIncl_pairing (Q : LinearMap.BilinForm ℤ M) (x y : ℝ ⊗[ℤ] M) :
    Q.baseChange ℂ (b64b_realIncl M x) (b64b_realIncl M y) =
      (Q.baseChange ℝ x y : ℂ) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, Complex.ofReal_add, hx, hz]
  | tmul c x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, Complex.ofReal_add, hy, hz]
    | tmul d y =>
      simp only [b64b_realIncl_tmul, LinearMap.BilinForm.baseChange_tmul,
        zsmul_eq_mul, Complex.ofReal_mul, Complex.ofReal_intCast]

theorem b64b_realIncl_action (A : M →ₗ[ℤ] M) (x : ℝ ⊗[ℤ] M) :
    b64b_realIncl M (A.baseChange ℝ x) = A.baseChange ℂ (b64b_realIncl M x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x => rfl

theorem b64b_action_conj (A : M →ₗ[ℤ] M) (x : ℂ ⊗[ℤ] M) :
    A.baseChange ℂ (b2_conj M x) = b2_conj M (A.baseChange ℂ x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x => rfl

theorem b64b_realPart_eigen_pairing (Q : LinearMap.BilinForm ℤ M)
    (hQ : ∀ x, Q x x = 0) (A : M →ₗ[ℤ] M) (s : ℝ) (x : ℂ ⊗[ℤ] M)
    (hx : A.baseChange ℂ x = (-Complex.I * (s : ℂ)) • x) :
    2 * Q.baseChange ℝ (b64b_realPart M x) (A.baseChange ℝ (b64b_realPart M x)) =
      s * (Complex.I * Q.baseChange ℂ x (b2_conj M x)).re := by
  let u := b64b_realPart M x
  have hb : (4 : ℂ) * (Q.baseChange ℝ u (A.baseChange ℝ u) : ℂ) =
      Q.baseChange ℂ (x + b2_conj M x) (A.baseChange ℂ (x + b2_conj M x)) := by
    rw [← b64b_realIncl_realPart M x]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← b64b_realIncl_action]
    rw [b64b_realIncl_pairing]
    ring
  simp only [map_add, b64b_action_conj, hx, b2a_conj_smul,
    LinearMap.add_apply, map_smul,
    b2a_baseChange_alt Q hQ, b2a_baseChange_skew Q hQ (b2_conj M x) x,
    map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, neg_neg,
    smul_eq_mul, zero_add, add_zero] at hb
  have hr := congrArg Complex.re hb
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    mul_zero, zero_mul, sub_zero, zero_sub, one_mul] at hr ⊢
  dsimp only [u] at hr
  rw [show (4 : ℂ).re = (4 : ℝ) from rfl] at hr
  nlinarith

set_option maxHeartbeats 400000 in
theorem b64b_real_signature [Module.Free ℤ M] [Module.Finite ℤ M]
    (Q : LinearMap.BilinForm ℤ M) (A : M →ₗ[ℤ] M)
    (F : Submodule ℂ (ℂ ⊗[ℤ] M)) (hW : b2_IsWeightOne M F)
    (hR : b2_IsRiemannForm M F Q) (hdim : Module.finrank ℂ F = 6)
    (hneg : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hpos : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3) :
    let q := LinearMap.BilinMap.toQuadraticMap ((Q.baseChange ℝ).compl₂ (A.baseChange ℝ))
    sigPos q = 6 ∧ sigNeg q = 6 := by
  let n := (F ⊓ Module.End.eigenspace (A.baseChange ℂ)
    (-Complex.I * (Real.sqrt 3 : ℂ))).comap F.subtype
  let p := (F ⊓ Module.End.eigenspace (A.baseChange ℂ)
    (Complex.I * (Real.sqrt 3 : ℂ))).comap F.subtype
  have hn : Module.finrank ℂ n = 3 :=
    (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq.trans hneg
  have hp : Module.finrank ℂ p = 3 :=
    (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq.trans hpos
  let : Module.Finite ℝ n := Module.Finite.trans ℂ n
  let : Module.Finite ℝ p := Module.Finite.trans ℂ p
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hz : (-Complex.I * (Real.sqrt 3 : ℂ)) ≠ (Complex.I * (Real.sqrt 3 : ℂ)) := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.mul_im, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_add, neg_mul, one_mul] at hh
    linarith
  have hd : Disjoint n p := by
    rw [Submodule.disjoint_def]
    intro x hx hy
    change x.val ∈ F ⊓ _ at hx hy
    have hx' := Module.End.mem_eigenspace_iff.mp hx.2
    have hy' := Module.End.mem_eigenspace_iff.mp hy.2
    have hh : ((-Complex.I * (Real.sqrt 3 : ℂ)) -
        (Complex.I * (Real.sqrt 3 : ℂ))) • x.val = 0 := by
      rw [sub_smul, ← hx', ← hy', sub_self]
    exact Subtype.ext ((smul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hz))
  have hc : IsCompl n p := by
    refine ⟨hd, ?_⟩
    rw [codisjoint_iff]
    apply Submodule.eq_top_of_finrank_eq
    have hh := Submodule.finrank_sup_add_finrank_inf_eq n p
    rw [hd.eq_bot, finrank_bot, hn, hp, add_zero] at hh
    exact hh.trans hdim.symm
  obtain ⟨e, he⟩ := b64b_realPart_equiv M F hW
  have hc' := Submodule.isCompl_map e ((Submodule.isCompl_restrictScalars_iff ℝ).mpr
    (show IsCompl n p from hc) : IsCompl (n.restrictScalars ℝ) (p.restrictScalars ℝ))
  have hsign := HodgeLean.Foundations.WeilHermitian.sigPos_sigNeg_of_isCompl hc'
    (Q := LinearMap.BilinMap.toQuadraticMap ((Q.baseChange ℝ).compl₂ (A.baseChange ℝ)))
  have hpositive : ∀ v ∈ (n.restrictScalars ℝ).map e.toLinearMap, v ≠ 0 →
      0 < Q.baseChange ℝ v (A.baseChange ℝ v) := by
    rintro _ ⟨x, hx, rfl⟩ hv
    have hx0 : x.val ≠ 0 := by
      intro hh
      apply hv
      simp only [LinearEquiv.coe_coe]
      rw [he x]
      simp only [hh, map_zero]
    have hx' : x.val ∈ F ⊓ Module.End.eigenspace (A.baseChange ℂ)
        (-Complex.I * (Real.sqrt 3 : ℂ)) := hx
    have heq := b64b_realPart_eigen_pairing M Q hR.alt A (Real.sqrt 3) x.val
      (Module.End.mem_eigenspace_iff.mp hx'.2)
    simp only [LinearEquiv.coe_coe]
    rw [he x]
    have hpos' := hR.positive x.val x.property hx0
    nlinarith [mul_pos hs hpos']
  have hnegative : ∀ v ∈ (p.restrictScalars ℝ).map e.toLinearMap, v ≠ 0 →
      Q.baseChange ℝ v (A.baseChange ℝ v) < 0 := by
    rintro _ ⟨x, hx, rfl⟩ hv
    have hx0 : x.val ≠ 0 := by
      intro hh
      apply hv
      simp only [LinearEquiv.coe_coe]
      rw [he x]
      simp only [hh, map_zero]
    have hx' : x.val ∈ F ⊓ Module.End.eigenspace (A.baseChange ℂ)
        (Complex.I * (Real.sqrt 3 : ℂ)) := hx
    have heig : A.baseChange ℂ x.val = (-Complex.I * ((-Real.sqrt 3 : ℝ) : ℂ)) • x.val := by
      simpa only [Complex.ofReal_neg, neg_mul_neg] using
        (Module.End.mem_eigenspace_iff.mp hx'.2)
    have heq := b64b_realPart_eigen_pairing M Q hR.alt A (-Real.sqrt 3) x.val heig
    simp only [LinearEquiv.coe_coe]
    rw [he x]
    have hpos' := hR.positive x.val x.property hx0
    nlinarith [mul_pos hs hpos']
  obtain ⟨h1, h2⟩ := hsign hpositive hnegative
  simp only [e.finrank_map_eq] at h1 h2
  have hnR : Module.finrank ℝ (n.restrictScalars ℝ) = 6 := by
    rw [((Submodule.restrictScalarsEquiv ℝ ℂ F n).restrictScalars ℝ).finrank_eq,
      ← Module.finrank_mul_finrank ℝ ℂ n, Complex.finrank_real_complex, hn]
  have hpR : Module.finrank ℝ (p.restrictScalars ℝ) = 6 := by
    rw [((Submodule.restrictScalarsEquiv ℝ ℂ F p).restrictScalars ℝ).finrank_eq,
      ← Module.finrank_mul_finrank ℝ ℂ p, Complex.finrank_real_complex, hp]
  exact ⟨h1.trans hnR, h2.trans hpR⟩

theorem b64b_cancel_pairing_real (Q : LinearMap.BilinForm ℤ M)
    (c d : ℝ) (x y : ℚ ⊗[ℤ] M) :
    Q.baseChange ℝ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℝ ℝ M (c ⊗ₜ[ℚ] x))
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℝ ℝ M (d ⊗ₜ[ℚ] y)) =
      c * d * ((Q.baseChange ℚ x y : ℚ) : ℝ) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz =>
    simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, Rat.cast_add,
      mul_add, hx, hz]
  | tmul q n =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz =>
      simp only [TensorProduct.tmul_add, map_add, Rat.cast_add, mul_add, hy, hz]
    | tmul r k =>
      simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul, Rat.smul_def,
        Rat.cast_mul, Rat.cast_intCast]
      ring

theorem b64b_cancel_pairing_real_all (Q : LinearMap.BilinForm ℤ M)
    (x y : ℝ ⊗[ℚ] (ℚ ⊗[ℤ] M)) :
    Q.baseChange ℝ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℝ ℝ M x)
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℝ ℝ M y) =
      (Q.baseChange ℚ).baseChange ℝ x y := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul c u =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul d v =>
      rw [b64b_cancel_pairing_real, LinearMap.BilinForm.baseChange_tmul]
      simp only [Rat.smul_def, mul_comm]

theorem b64b_cancel_action_real (A : M →ₗ[ℤ] M)
    (x : ℝ ⊗[ℚ] (ℚ ⊗[ℤ] M)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℝ ℝ M
      ((A.baseChange ℚ).baseChange ℝ x) =
      A.baseChange ℝ (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℝ ℝ M x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c y =>
    rw [LinearMap.baseChange_tmul]
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz]
    | tmul q n =>
      simp only [LinearMap.baseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

theorem b64b_hermitian_real_isometry (Q : LinearMap.BilinForm ℤ M)
    (J : {J : Module.End ℚ (ℚ ⊗[ℤ] M) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id})
    (hskew : ∀ x y, Q.baseChange ℚ (J.1 x) y = -Q.baseChange ℚ x (J.1 y))
    (A : M →ₗ[ℤ] M) (hA : A.baseChange ℚ = J.1) :
    Nonempty (((HodgeLean.Foundations.HermitianForm.hermQuadForm
      (b64b_latticeH M Q J hskew)).baseChange ℝ).IsometryEquiv
        (LinearMap.BilinMap.toQuadraticMap ((Q.baseChange ℝ).compl₂ (A.baseChange ℝ)))) := by
  let e0 := (HodgeLean.Foundations.WeilHermitian.WithJ.equiv J).baseChange ℚ ℝ _ _
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℝ ℝ M
  refine ⟨{ e0.trans c with map_app' := ?_ }⟩
  intro x
  rw [show b64b_latticeH M Q J hskew =
    HodgeLean.Foundations.WeilHermitian.weilHermitian (Q.baseChange ℚ) J hskew from rfl,
    HodgeLean.Foundations.WeilHermitian.baseChange_hermQuadForm_weilHermitian]
  change Q.baseChange ℝ (c (e0 x)) (A.baseChange ℝ (c (e0 x))) =
    (Q.baseChange ℚ).baseChange ℝ (e0 x) (J.1.baseChange ℝ (e0 x))
  rw [← hA, ← b64b_cancel_action_real M A (e0 x)]
  exact b64b_cancel_pairing_real_all M Q _ _

end HodgeLean.Foundations.Program
