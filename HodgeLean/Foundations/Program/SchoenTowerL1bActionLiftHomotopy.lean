import HodgeLean.Foundations.Program.SchoenTowerL1bActionHalfPlaneLift
import Mathlib.Topology.Homotopy.Path

noncomputable section
set_option maxHeartbeats 200000
open scoped unitInterval
namespace HodgeLean.Foundations.Program

/-- Paths in the punctured plane with logarithmic lifts sharing both endpoints
are homotopic with their endpoints fixed. -/
theorem s2v_l1b_action_log_paths_homotopic
    {a b : {z : ℂ // z ≠ 0}} (p q : Path a b)
    (L K : C(unitInterval, ℂ))
    (hL : ∀ t, Complex.exp (L t) = (p t).val)
    (hK : ∀ t, Complex.exp (K t) = (q t).val)
    (hzero : L 0 = K 0) (hone : L 1 = K 1) :
    p.Homotopic q := by
  refine ⟨{
    toFun := fun x => ⟨Complex.exp
      ((1 - (x.1.val : ℂ)) * L x.2 + (x.1.val : ℂ) * K x.2),
        Complex.exp_ne_zero _⟩
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · apply Continuous.subtype_mk
    apply Complex.continuous_exp.comp
    exact ((continuous_const.sub (Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_fst))).mul
      (L.continuous.comp continuous_snd)).add
      ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
        (K.continuous.comp continuous_snd))
  · intro t
    apply Subtype.ext
    change Complex.exp ((1 - (((0 : unitInterval).val) : ℂ)) * L t +
      (((0 : unitInterval).val) : ℂ) * K t) = (p t).val
    simpa only [Set.Icc.coe_zero, Complex.ofReal_zero, sub_zero, one_mul,
      zero_mul, add_zero] using hL t
  · intro t
    apply Subtype.ext
    change Complex.exp ((1 - (((1 : unitInterval).val) : ℂ)) * L t +
      (((1 : unitInterval).val) : ℂ) * K t) = (q t).val
    simpa only [Set.Icc.coe_one, Complex.ofReal_one, sub_self, zero_mul,
      one_mul, zero_add] using hK t
  · intro t s hs
    apply Subtype.ext
    rcases hs with hs | hs
    · subst s
      change Complex.exp ((1 - (t.val : ℂ)) * L 0 + (t.val : ℂ) * K 0) = (p 0).val
      rw [← hL, ← hzero]
      congr 1
      ring
    · have hs' : s = 1 := Set.mem_singleton_iff.mp hs
      subst s
      change Complex.exp ((1 - (t.val : ℂ)) * L 1 + (t.val : ℂ) * K 1) = (p 1).val
      rw [← hL, ← hone]
      congr 1
      ring

/-- Equality of logarithmic increments suffices for homotopy of paths in the
punctured plane, independently of the selected logarithms at the initial point. -/
theorem s2v_l1b_action_log_increment_homotopic
    {a b : {z : ℂ // z ≠ 0}} (p q : Path a b)
    (L K : C(unitInterval, ℂ))
    (hL : ∀ t, Complex.exp (L t) = (p t).val)
    (hK : ∀ t, Complex.exp (K t) = (q t).val)
    (hinc : L 1 - L 0 = K 1 - K 0) :
    p.Homotopic q := by
  have he : Complex.exp (L 0) = Complex.exp (K 0) := by
    rw [hL, hK, p.source, q.source]
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  let K' : C(unitInterval, ℂ) := ⟨fun t => K t +
    (k : ℂ) * (2 * Real.pi * Complex.I), K.continuous.add continuous_const⟩
  apply s2v_l1b_action_log_paths_homotopic p q L K' hL
  · intro t
    change Complex.exp (K t + (k : ℂ) * (2 * Real.pi * Complex.I)) = (q t).val
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, hK]
  · exact hk
  · change L 1 = K 1 + (k : ℂ) * (2 * Real.pi * Complex.I)
    linear_combination hinc + hk

/-- A loop with integral logarithmic increment is homotopic, fixing its
basepoint, to the exponential loop with that many turns. -/
theorem s2v_l1b_action_log_loop_normal_form
    {a : {z : ℂ // z ≠ 0}} (p : Path a a) (L : C(unitInterval, ℂ))
    (hL : ∀ t, Complex.exp (L t) = (p t).val)
    (k : ℤ) (hk : L 1 = L 0 + (k : ℂ) * (2 * Real.pi * Complex.I)) :
    ∃ q : Path a a,
      (∀ t, (q t).val = Complex.exp
        (L 0 + (t.val : ℂ) * ((k : ℂ) * (2 * Real.pi * Complex.I)))) ∧
      p.Homotopic q := by
  let K : C(unitInterval, ℂ) := ⟨fun t => L 0 + (t.val : ℂ) *
    ((k : ℂ) * (2 * Real.pi * Complex.I)), continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const)⟩
  let q : Path a a :=
    { toFun := fun t => ⟨Complex.exp (K t), Complex.exp_ne_zero _⟩
      continuous_toFun := (Complex.continuous_exp.comp K.continuous).subtype_mk _
      source' := by
        apply Subtype.ext
        change Complex.exp (L 0 + ((0 : ℝ) : ℂ) * _) = a.val
        simpa only [Complex.ofReal_zero, zero_mul, add_zero, p.source] using hL 0
      target' := by
        apply Subtype.ext
        change Complex.exp (L 0 + ((1 : ℝ) : ℂ) * _) = a.val
        rw [Complex.ofReal_one, one_mul, Complex.exp_add,
          Complex.exp_int_mul_two_pi_mul_I, mul_one, hL, p.source] }
  refine ⟨q, fun _ => rfl, ?_⟩
  apply s2v_l1b_action_log_paths_homotopic p q L K hL (fun _ => rfl)
  · change L 0 = L 0 + ((0 : ℝ) : ℂ) * _
    rw [Complex.ofReal_zero, zero_mul, add_zero]
  · change L 1 = L 0 + ((1 : ℝ) : ℂ) * _
    simpa only [Complex.ofReal_one, one_mul] using hk

/-- On a circular orbit in a covering half-plane, the deck coefficient of a
logarithmic lift gives the homotopy class of the image loop. -/
theorem s2v_l1b_action_halfplane_loop_normal_form
    (h L : ℂ → ℂ) (b : ℝ)
    (hL : ContinuousOn L {z : ℂ | z.re < b})
    (he : ∀ z, z.re < b → Complex.exp (L z) = h (Complex.exp z))
    (k : ℤ) (hk : ∀ z, z.re < b →
      L (z + 2 * Real.pi * Complex.I) = L z + (k : ℂ) * (2 * Real.pi * Complex.I))
    (z : ℂ) (hz : z.re < b)
    {a : {w : ℂ // w ≠ 0}} (p : Path a a)
    (hp : ∀ t, (p t).val = h (Complex.exp
      (z + (t.val : ℂ) * (2 * Real.pi * Complex.I)))) :
    ∃ q : Path a a,
      (∀ t, (q t).val = Complex.exp
        (L z + (t.val : ℂ) * ((k : ℂ) * (2 * Real.pi * Complex.I)))) ∧
      p.Homotopic q := by
  let T : unitInterval → ℂ := fun t => z + (t.val : ℂ) * (2 * Real.pi * Complex.I)
  have hc : Continuous T := continuous_const.add
    ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const)
  have hdeck : (2 * Real.pi * Complex.I).re = 0 := by simp
  have hmem (t : unitInterval) : (T t).re < b := by
    simpa only [T, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hdeck, mul_zero, zero_mul, sub_zero, add_zero] using hz
  let F : C(unitInterval, ℂ) := ⟨fun t => L (T t), hL.comp_continuous hc hmem⟩
  have hF (t : unitInterval) : Complex.exp (F t) = (p t).val :=
    (he (T t) (hmem t)).trans (hp t).symm
  have hzero : F 0 = L z := by
    change L (z + ((0 : ℝ) : ℂ) * _) = L z
    rw [Complex.ofReal_zero, zero_mul, add_zero]
  have hone : F 1 = F 0 + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hzero]
    change L (z + ((1 : ℝ) : ℂ) * _) = _
    rw [Complex.ofReal_one, one_mul]
    exact hk z hz
  obtain ⟨q, hq, hhom⟩ := s2v_l1b_action_log_loop_normal_form p F hF k hone
  exact ⟨q, fun t => (hq t).trans (by rw [hzero]), hhom⟩

end HodgeLean.Foundations.Program
