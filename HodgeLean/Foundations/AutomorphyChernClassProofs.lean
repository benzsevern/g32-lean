import HodgeLean.Foundations.AutomorphyChernClassDefs
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

/-! Proofs of the frozen spec of the alternating form of a factor of automorphy. All twelve `_aux`
theorems are proved, by two parallel provers (statements 1-5 and 6-12). -/

noncomputable section

namespace HodgeLean.Foundations.AutomorphyChernClass

open AppellHumbert

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}

theorem spec_exists_continuous_log_aux (a : L → V → ℂ) (ha : ∀ l, Continuous (a l))
    (ha₀ : ∀ l v, a l v ≠ 0) :
    ∃ f : L → V → ℂ, (∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v)) ∧
      ∀ l, Continuous (f l) := by
  have hF : ∀ l, ∃ F : C(V, ℂ), Complex.exp ∘ F = a l := fun l ↦
    let ⟨F, ⟨_, hF⟩, _⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
      ⟨a l, ha l⟩ (a₀ := 0) (Complex.exp_log (ha₀ l 0)) (fun v ↦ ha₀ l v)
    ⟨F, hF⟩
  choose F hF using hF
  have h2πI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨fun l v ↦ F l v / (2 * Real.pi * Complex.I), fun l v ↦ ?_, fun l ↦ ?_⟩
  · rw [mul_div_cancel₀ _ h2πI, ← hF l, Function.comp_apply]
  · exact (F l).continuous.div_const _

/-- A continuous `g : V → ℂ` with `exp(2πi g) = 1` everywhere is constant. -/
private theorem const_of_exp_eq_one {g : V → ℂ} (hg : Continuous g)
    (h : ∀ v, Complex.exp (2 * Real.pi * Complex.I * g v) = 1) (v w : V) : g v = g w := by
  have hn : ∀ v, ∃ n : ℤ, g v = n := fun v ↦ by
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (h v)
    refine ⟨n, ?_⟩
    have h2πI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ h2πI
    rw [hn]; ring
  choose n hn using hn
  have hc : Continuous n := by
    rw [Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff]
    have : ((Int.cast : ℤ → ℝ) ∘ n) = fun v ↦ (g v).re := by
      funext v; simp [hn v]
    rw [this]; exact Complex.continuous_re.comp hg
  rw [hn v, hn w, PreconnectedSpace.constant inferInstance hc]

omit [NormedSpace ℂ V] in
/-- The cocycle defect `f(l, v + m) + f(m, v) - f(l + m, v)` of a logarithm of a cocycle is an
integer. -/
private theorem defect_int (a f : L → V → ℂ)
    (hcoc : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v)) (l m : L) (v : V) :
    Complex.exp (2 * Real.pi * Complex.I * (f l (v + m) + f m v - f (l + m) v)) = 1 := by
  have h := hcoc l m v
  rw [hlog, hlog, hlog, ← Complex.exp_add] at h
  rw [mul_sub, Complex.exp_sub, mul_add, ← h, div_self (Complex.exp_ne_zero _)]

private theorem defect_const (a f : L → V → ℂ)
    (hcoc : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) (l m : L) (v w : V) :
    f l (v + m) + f m v - f (l + m) v = f l (w + m) + f m w - f (l + m) w :=
  const_of_exp_eq_one (g := fun v ↦ f l (v + m) + f m v - f (l + m) v)
    (by fun_prop) (defect_int a f hcoc hlog l m) v w

omit [NormedSpace ℂ V] in
private theorem defect_exists_int (a f : L → V → ℂ)
    (hcoc : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v)) (l m : L) (v : V) :
    ∃ n : ℤ, f l (v + m) + f m v - f (l + m) v = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (defect_int a f hcoc hlog l m v)
  refine ⟨n, ?_⟩
  have h2πI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  apply mul_left_cancel₀ h2πI
  rw [hn]; ring

theorem spec_logForm_eq_chernForm_aux (a f : L → V → ℂ)
    (hcoc : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) (v : V) (l m : L) :
    logForm f v l m = chernForm f l m := by
  have key : ∀ w, logForm f w l m = (f m (w + l) + f l w - f (m + l) w) -
      (f l (w + m) + f m w - f (l + m) w) := fun w ↦ by
    rw [add_comm m l]; unfold logForm; ring
  obtain ⟨n₁, hn₁⟩ := defect_exists_int a f hcoc hlog m l 0
  obtain ⟨n₂, hn₂⟩ := defect_exists_int a f hcoc hlog l m 0
  have h0 : logForm f 0 l m = ((n₁ - n₂ : ℤ) : ℂ) := by
    rw [key, hn₁, hn₂]; push_cast; ring
  have hv : logForm f v l m = logForm f 0 l m := by
    rw [key, key, defect_const a f hcoc hlog hf m l v 0, defect_const a f hcoc hlog hf l m v 0]
  rw [hv, chernForm, h0]
  simp

theorem spec_chernForm_antisymm_aux (a f : L → V → ℂ)
    (hcoc : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) (l m : L) :
    chernForm f m l = -chernForm f l m := by
  have h1 := spec_logForm_eq_chernForm_aux a f hcoc hlog hf 0 m l
  have h2 := spec_logForm_eq_chernForm_aux a f hcoc hlog hf 0 l m
  have : ((chernForm f m l : ℤ) : ℂ) = ((-chernForm f l m : ℤ) : ℂ) := by
    rw [← h1, Int.cast_neg, ← h2]; unfold logForm; ring
  exact_mod_cast this

private theorem chernForm_add_left (a f : L → V → ℂ)
    (hcoc : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) (l l' m : L) :
    chernForm f (l + l') m = chernForm f l m + chernForm f l' m := by
  have h1 := spec_logForm_eq_chernForm_aux a f hcoc hlog hf 0 (l + l') m
  have h2 := spec_logForm_eq_chernForm_aux a f hcoc hlog hf (l' : V) l m
  have h3 := spec_logForm_eq_chernForm_aux a f hcoc hlog hf 0 l' m
  have hd := defect_const a f hcoc hlog hf l l' 0 m
  have : ((chernForm f (l + l') m : ℤ) : ℂ) = ((chernForm f l m + chernForm f l' m : ℤ) : ℂ) := by
    rw [← h1, Int.cast_add, ← h2, ← h3]
    unfold logForm
    simp only [zero_add, Submodule.coe_add] at hd ⊢
    rw [add_comm (l : V) (l' : V)]
    rw [add_comm (m : V) (l' : V)] at hd
    linear_combination -hd
  exact_mod_cast this

theorem spec_chernForm_biadditive_aux (a f : L → V → ℂ)
    (hcoc : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) :
    ∃ E : L →+ L →+ ℤ, ∀ l m, E l m = chernForm f l m := by
  have hr : ∀ l m m', chernForm f l (m + m') = chernForm f l m + chernForm f l m' := by
    intro l m m'
    rw [spec_chernForm_antisymm_aux a f hcoc hlog hf (m + m') l,
      chernForm_add_left a f hcoc hlog hf, spec_chernForm_antisymm_aux a f hcoc hlog hf m l,
      spec_chernForm_antisymm_aux a f hcoc hlog hf m' l]
    ring
  refine ⟨AddMonoidHom.mk' (fun l ↦ AddMonoidHom.mk' (fun m ↦ chernForm f l m) (hr l))
    (fun l l' ↦ ?_), fun l m ↦ rfl⟩
  ext m
  exact chernForm_add_left a f hcoc hlog hf l l' m

theorem spec_chernForm_log_indep_aux (a f f' : L → V → ℂ)
    (hlog : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hlog' : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f' l v))
    (hf : ∀ l, Continuous (f l)) (hf' : ∀ l, Continuous (f' l)) :
    chernForm f = chernForm f' := by
  have hc : ∀ l v, f l v - f' l v = f l 0 - f' l 0 := fun l v ↦
    const_of_exp_eq_one (g := fun v ↦ f l v - f' l v) (by fun_prop)
      (fun v ↦ by
        rw [mul_sub, Complex.exp_sub, ← hlog, ← hlog', div_self]
        rw [hlog]; exact Complex.exp_ne_zero _) v 0
  funext l m
  unfold chernForm logForm
  congr 2
  linear_combination hc m (0 + l) + hc l 0 - hc l (0 + m) - hc m 0

theorem spec_chernForm_mul_aux (a b f g h : L → V → ℂ)
    (hcoca : ∀ l m v, a (l + m) v = a l (v + m) * a m v)
    (hcocb : ∀ l m v, b (l + m) v = b l (v + m) * b m v)
    (hloga : ∀ l v, a l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hlogb : ∀ l v, b l v = Complex.exp (2 * Real.pi * Complex.I * g l v))
    (hlogab : ∀ l v, a l v * b l v = Complex.exp (2 * Real.pi * Complex.I * h l v))
    (hf : ∀ l, Continuous (f l)) (hg : ∀ l, Continuous (g l)) (hh : ∀ l, Continuous (h l)) :
    chernForm h = chernForm f + chernForm g := by
  have hfg : ∀ l v, a l v * b l v =
      Complex.exp (2 * Real.pi * Complex.I * (f + g) l v) := fun l v ↦ by
    rw [hloga, hlogb, ← Complex.exp_add, Pi.add_apply, Pi.add_apply, mul_add]
  rw [spec_chernForm_log_indep_aux (fun l v ↦ a l v * b l v) h (f + g) hlogab hfg hh
    fun l ↦ (hf l).add (hg l)]
  funext l m
  have hF := spec_logForm_eq_chernForm_aux a f hcoca hloga hf 0 l m
  have hG := spec_logForm_eq_chernForm_aux b g hcocb hlogb hg 0 l m
  have hsum : logForm (f + g) 0 l m = logForm f 0 l m + logForm g 0 l m := by
    simp only [logForm, Pi.add_apply]; ring
  simp only [Pi.add_apply]
  rw [chernForm, hsum, hF, hG, Complex.add_re, Complex.intCast_re, Complex.intCast_re,
    ← Int.cast_add, round_intCast]

theorem spec_chernForm_coboundary_aux (k : V → ℂ) (hk : Continuous k) (hk₀ : ∀ v, k v ≠ 0)
    (f : L → V → ℂ)
    (hlog : ∀ (l : L) v, k (v + l) / k v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) :
    chernForm f = 0 := by
  obtain ⟨g₀, hg₀, hg₀c⟩ := spec_exists_continuous_log_aux (L := L) (fun _ v ↦ k v)
    (fun _ ↦ hk) (fun _ v ↦ hk₀ v)
  set g := g₀ 0
  have hlog' : ∀ (l : L) v, k (v + l) / k v =
      Complex.exp (2 * Real.pi * Complex.I * (fun (l : L) v ↦ g (v + l) - g v) l v) :=
    fun l v ↦ by
      rw [hg₀ 0 (v + l), hg₀ 0 v, ← Complex.exp_sub, mul_sub]
  rw [spec_chernForm_log_indep_aux (fun (l : L) v ↦ k (v + l) / k v) f _ hlog hlog' hf
    fun l ↦ ((hg₀c 0).comp (continuous_id.add continuous_const)).sub (hg₀c 0)]
  funext l m
  have h0 : logForm (fun (l : L) v ↦ g (v + l) - g v) 0 l m = 0 := by
    simp only [logForm, zero_add]
    rw [add_comm (m : V) l]; ring
  simp [chernForm, h0]

theorem spec_chernForm_trivial_aux (f : L → V → ℂ)
    (hlog : ∀ l v, Complex.exp (2 * Real.pi * Complex.I * f l v) = 1)
    (hf : ∀ l, Continuous (f l)) :
    chernForm f = 0 := by
  have h0 : ∀ (l : L) (v : V), (fun _ _ ↦ 1 : L → V → ℂ) l v =
      Complex.exp (2 * Real.pi * Complex.I * (0 : L → V → ℂ) l v) := fun _ _ ↦ by simp
  rw [spec_chernForm_log_indep_aux (fun _ _ ↦ 1) f 0 (fun l v ↦ (hlog l v).symm) h0 hf
    fun _ ↦ continuous_const]
  funext l m
  simp [chernForm, logForm]

end General

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem spec_holLog_isLog_aux (D : Datum (V := V)) :
    (∀ l v, holFactor D l v = Complex.exp (2 * Real.pi * Complex.I * holLog D l v)) ∧
      ∀ l, Continuous (holLog D l) := by
  refine ⟨fun l v ↦ ?_, fun l ↦ ?_⟩
  · unfold holFactor holLog
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hc : ‖(D.semicharacter l : ℂ)‖ = 1 := Circle.norm_coe _
    generalize (D.semicharacter l : ℂ) = c at hc ⊢
    generalize Real.pi * D.hermitian.toFun l v + Real.pi / 2 * D.hermitian.toFun l l = B
    have h : 2 * Real.pi * Complex.I * ((c.arg : ℂ) / (2 * Real.pi) + B / (2 * Real.pi * Complex.I))
        = c.arg * Complex.I + B := by
      field_simp
    rw [h, Complex.exp_add]
    congr 1
    have := Complex.norm_mul_exp_arg_mul_I c
    rw [hc, Complex.ofReal_one, one_mul] at this
    exact this.symm
  · let φ : V →ₗ[ℂ] ℂ :=
      { toFun := D.hermitian.toFun l
        map_add' := D.hermitian.add_right l
        map_smul' := fun c x ↦ D.hermitian.smul_right c l x }
    have hφ : Continuous (D.hermitian.toFun l) := φ.continuous_of_finiteDimensional
    unfold holLog
    fun_prop

theorem spec_chernForm_holFactor_aux (D : Datum (V := V)) (f : D.lattice → V → ℂ)
    (hlog : ∀ l v, holFactor D l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) (l m : D.lattice) :
    chernForm f l m = -D.imForm l m := by
  rw [spec_chernForm_log_indep_aux (holFactor D) f (holLog D) hlog (spec_holLog_isLog_aux D).1 hf
    (spec_holLog_isLog_aux D).2]
  obtain ⟨n, hn⟩ := D.integral l m
  have h0 : ∀ x : V, D.hermitian.toFun x 0 = 0 := fun x ↦ by
    have := D.hermitian.add_right x 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have key : logForm (holLog D) 0 l m = ((-n : ℤ) : ℂ) := by
    unfold logForm holLog
    simp only [zero_add, h0]
    rw [← D.hermitian.conj_symm (m : V) l]
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hz : star (D.hermitian.toFun l m) = D.hermitian.toFun l m - 2 * Complex.I * n := by
      rw [HermitianForm.imaginary] at hn
      apply Complex.ext <;> simp [hn] <;> ring
    rw [hz]
    push_cast
    field_simp
    ring
  rw [chernForm, key, Complex.intCast_re, round_intCast]
  show -n = -⌊D.hermitian.imaginary l m⌋
  rw [hn, Int.floor_intCast]

theorem spec_chernForm_holFactor_latticeClass_aux (D : Datum (V := V))
    [Module.Free ℤ D.lattice] [Module.Finite ℤ D.lattice] (f : D.lattice → V → ℂ)
    (hlog : ∀ l v, holFactor D l v = Complex.exp (2 * Real.pi * Complex.I * f l v))
    (hf : ∀ l, Continuous (f l)) :
    ∃ E : D.lattice →+ D.lattice →+ ℤ, (∀ l m, E l m = chernForm f l m) ∧
      latticeClass E = -latticeClass D.imForm := by
  refine ⟨-D.imForm, fun l m ↦ ?_, ?_⟩
  · rw [spec_chernForm_holFactor_aux D f hlog hf l m]
    rfl
  · have hadd : ∀ E₁ E₂ : D.lattice →+ D.lattice →+ ℤ,
        latticeClass (E₁ + E₂) = latticeClass E₁ + latticeClass E₂ := fun E₁ E₂ ↦ by
      simp only [latticeClass, AddMonoidHom.add_apply, Int.cast_add, add_div, add_smul,
        Finset.sum_add_distrib]
    refine eq_neg_of_add_eq_zero_left ?_
    rw [← hadd, neg_add_cancel]
    simp [latticeClass]

end Lattice

theorem spec_logForm_cocycle_failure_aux :
    let L : Submodule ℤ ℂ := ⊤
    let one : L := ⟨1, Submodule.mem_top⟩
    let f : L → ℂ → ℂ := fun _ v ↦ v ^ 2
    let a : L → ℂ → ℂ := fun l v ↦ Complex.exp (2 * Real.pi * Complex.I * f l v)
    (∃ (l m : L) (v : ℂ), a (l + m) v ≠ a l (v + m) * a m v) ∧
      (¬ ∃ n : ℤ, logForm f (1 / 4) one 0 = n) ∧ logForm f 0 one 0 ≠ logForm f 1 one 0 := by
  intro L one f a
  refine ⟨⟨0, ⟨1 / 2, Submodule.mem_top⟩, 0, ?_⟩, ?_, ?_⟩
  · simp only [a, f, zero_add, ne_eq]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 / 2) ^ 2 = Real.pi / 2 * Complex.I by ring]
    simp only [Complex.exp_pi_div_two_mul_I]
    intro h
    simpa using congrArg Complex.im h
  · rintro ⟨n, hn⟩
    have h : logForm f (1 / 4) one 0 = 3 / 2 := by
      simp only [logForm, f, one]
      push_cast
      ring
    rw [h] at hn
    have hre := congrArg Complex.re hn
    simp only [Complex.div_ofNat_re, Complex.intCast_re] at hre
    norm_num at hre
    have : (3 : ℝ) = 2 * n := by linarith
    have : (3 : ℤ) = 2 * n := by exact_mod_cast this
    omega
  · simp only [logForm, f, one]
    push_cast
    norm_num

end HodgeLean.Foundations.AutomorphyChernClass
