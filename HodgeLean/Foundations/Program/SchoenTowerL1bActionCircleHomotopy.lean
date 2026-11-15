import HodgeLean.Foundations.Program.SchoenTowerL1bActionLiftHomotopy
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.CompactOpen
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology

noncomputable section
set_option maxHeartbeats 200000
open scoped unitInterval
namespace HodgeLean.Foundations.Program

/-- Circle maps into the punctured plane with the same logarithmic deck
coefficient are freely homotopic. -/
theorem s2v_l1b_action_circle_log_homotopic
    (p q : C(UnitAddCircle, {z : ℂ // z ≠ 0}))
    (L K : ℝ → ℂ) (hL : Continuous L) (hK : Continuous K)
    (hp : ∀ s : ℝ, Complex.exp (L s) = (p (s : UnitAddCircle)).val)
    (hq : ∀ s : ℝ, Complex.exp (K s) = (q (s : UnitAddCircle)).val)
    (k : ℤ)
    (hdL : ∀ s, L (s + 1) = L s + (k : ℂ) * (2 * Real.pi * Complex.I))
    (hdK : ∀ s, K (s + 1) = K s + (k : ℂ) * (2 * Real.pi * Complex.I)) :
    ContinuousMap.Homotopic p q := by
  let A : C(ℝ × unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun x => ⟨Complex.exp ((1 - (x.2.val : ℂ)) * L x.1 +
      (x.2.val : ℂ) * K x.1), Complex.exp_ne_zero _⟩,
      (Complex.continuous_exp.comp
        (((continuous_const.sub (Complex.continuous_ofReal.comp
          (continuous_subtype_val.comp continuous_snd))).mul
            (hL.comp continuous_fst)).add
          ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd)).mul
            (hK.comp continuous_fst)))).subtype_mk _⟩
  have hperiod : Function.Periodic A.curry 1 := by
    intro s
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    change Complex.exp ((1 - (t.val : ℂ)) * L (s + 1) + (t.val : ℂ) * K (s + 1)) =
      Complex.exp ((1 - (t.val : ℂ)) * L s + (t.val : ℂ) * K s)
    rw [hdL, hdK]
    have he : (1 - (t.val : ℂ)) * (L s + (k : ℂ) * (2 * Real.pi * Complex.I)) +
        (t.val : ℂ) * (K s + (k : ℂ) * (2 * Real.pi * Complex.I)) =
        ((1 - (t.val : ℂ)) * L s + (t.val : ℂ) * K s) +
          (k : ℂ) * (2 * Real.pi * Complex.I) := by ring
    rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  let F : C(UnitAddCircle, C(unitInterval, {z : ℂ // z ≠ 0})) :=
    ⟨hperiod.lift, A.curry.continuous.quotient_lift _⟩
  refine ⟨{
    toFun := fun x => F x.2 x.1
    continuous_toFun := F.uncurry.continuous.comp continuous_swap
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro x
    induction x using Quotient.inductionOn with
    | h s =>
      apply Subtype.ext
      change Complex.exp ((1 - (((0 : unitInterval).val) : ℂ)) * L s +
        (((0 : unitInterval).val) : ℂ) * K s) = (p (s : UnitAddCircle)).val
      simpa only [Set.Icc.coe_zero, Complex.ofReal_zero, sub_zero, one_mul,
        zero_mul, add_zero] using hp s
  · intro x
    induction x using Quotient.inductionOn with
    | h s =>
      apply Subtype.ext
      change Complex.exp ((1 - (((1 : unitInterval).val) : ℂ)) * L s +
        (((1 : unitInterval).val) : ℂ) * K s) = (q (s : UnitAddCircle)).val
      simpa only [Set.Icc.coe_one, Complex.ofReal_one, sub_self, zero_mul,
        one_mul, zero_add] using hq s

/-- Equal logarithmic deck coefficients give the same map on integral
singular homology of the circle. -/
theorem s2v_l1b_action_circle_log_homology
    (p q : C(UnitAddCircle, {z : ℂ // z ≠ 0}))
    (L K : ℝ → ℂ) (hL : Continuous L) (hK : Continuous K)
    (hp : ∀ s : ℝ, Complex.exp (L s) = (p (s : UnitAddCircle)).val)
    (hq : ∀ s : ℝ, Complex.exp (K s) = (q (s : UnitAddCircle)).val)
    (k : ℤ)
    (hdL : ∀ s, L (s + 1) = L s + (k : ℂ) * (2 * Real.pi * Complex.I))
    (hdK : ∀ s, K (s + 1) = K s + (k : ℂ) * (2 * Real.pi * Complex.I))
    (n : ℕ) :
    AlgebraicTopology.Singular.homologyMap ℤ n (TopCat.ofHom p) =
      AlgebraicTopology.Singular.homologyMap ℤ n (TopCat.ofHom q) := by
  obtain ⟨H⟩ := s2v_l1b_action_circle_log_homotopic p q L K hL hK hp hq k hdL hdK
  exact congrArg (fun f => f.hom)
    (TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (f := TopCat.ofHom p) (g := TopCat.ofHom q) H
      (ModuleCat.of ℤ ℤ) n)

end HodgeLean.Foundations.Program
