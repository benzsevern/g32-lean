import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian6DegreeDefs
import HodgeLean.Adapters.DegreeOneLatticeLoops
import Mathlib.Algebra.Homology.HomologySequenceLemmas

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
  TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs Set Topology
namespace HodgeLean.Adapters

private lemma bh6_boundaryCircuit_continuous
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (l m : abelianPeriodLattice X)
    (z : Fin (dim X.left) → ℂ) :
    Continuous (bh6_boundaryCircuit X l m z) := by
  unfold bh6_boundaryCircuit
  have h3 : Continuous (fun t : ℝ ↦ if t ≤ 3 then
      bh4_squareEdge X l m z 2 (t - 2) else bh4_squareEdge X l m z 3 (t - 3)) := by
    refine continuous_if_le continuous_id continuous_const
      (by unfold bh4_squareEdge; fun_prop) (by unfold bh4_squareEdge; fun_prop) ?_
    intro t ht
    subst t
    norm_num [bh4_squareEdge]
  have h2 : Continuous (fun t : ℝ ↦ if t ≤ 2 then
      bh4_squareEdge X l m z 1 (t - 1) else if t ≤ 3 then
        bh4_squareEdge X l m z 2 (t - 2) else bh4_squareEdge X l m z 3 (t - 3)) := by
    refine continuous_if_le continuous_id continuous_const
      (by unfold bh4_squareEdge; fun_prop) h3.continuousOn ?_
    intro t ht
    subst t
    norm_num [bh4_squareEdge]
  refine continuous_if_le continuous_id continuous_const
    (by unfold bh4_squareEdge; fun_prop) h2.continuousOn ?_
  intro t ht
  subst t
  norm_num [bh4_squareEdge]

private lemma bh6_boundaryCircuit_ne_zero
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : (Fin (dim X.left) → ℂ) → ℂ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0) :
    ∀ t ∈ Icc (0 : ℝ) 4, f (bh6_boundaryCircuit X l m z t) ≠ 0 := by
  intro t ht
  rw [bh6_boundaryCircuit]
  split_ifs with h1 h2 h3
  · exact hnz 0 t ⟨ht.1, h1⟩
  · exact hnz 1 (t - 1)
      ⟨sub_nonneg.mpr (le_of_not_ge h1), sub_le_iff_le_add.mpr (by linarith)⟩
  · exact hnz 2 (t - 2)
      ⟨sub_nonneg.mpr (le_of_not_ge h2), sub_le_iff_le_add.mpr (by linarith)⟩
  · exact hnz 3 (t - 3) ⟨sub_nonneg.mpr (le_of_not_ge h3), by linarith [ht.2]⟩

/-- Lift the nonvanishing ordered boundary circuit to a continuous real phase.
No derivative or degree comparison is assumed.
Source: Hatcher, Proposition 1.30, covering-space path lifting for the exponential circle cover. -/
theorem bh6_boundary_phase_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : (Fin (dim X.left) → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 4) ∧
      ∀ t ∈ Icc (0 : ℝ) 4, f (bh6_boundaryCircuit X l m z t) =
        (‖f (bh6_boundaryCircuit X l m z t)‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I) := by
  let p : ℝ → ℝ := fun t ↦ (projIcc (0 : ℝ) 4 (by norm_num) t : ℝ)
  let F : ℝ → ℂ := fun t ↦ f (bh6_boundaryCircuit X l m z (p t))
  have hp : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hp_mem (t : ℝ) : p t ∈ Icc (0 : ℝ) 4 := (projIcc 0 4 (by norm_num) t).property
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr fun x ↦
    (hf x (mem_univ x)).continuousAt
  have hF : Continuous F := hfcont.comp ((bh6_boundaryCircuit_continuous X l m z).comp hp)
  have hFne (t : ℝ) : F t ≠ 0 :=
    bh6_boundaryCircuit_ne_zero X f l m z hnz (p t) (hp_mem t)
  let g : ℝ → ℂ := fun t ↦ F t / ‖F t‖
  have hg : Continuous g := hF.div (Complex.continuous_ofReal.comp hF.norm) fun t ↦ by
    exact_mod_cast (norm_ne_zero_iff.mpr (hFne t))
  have hgnorm (t : ℝ) : ‖g t‖ = 1 := by
    simp [g, norm_ne_zero_iff.mpr (hFne t)]
  let G : ℝ → Circle := fun t ↦ ⟨g t, by simp [Submonoid.unitSphere, hgnorm]⟩
  have hG : Continuous G := continuous_induced_rng.mpr hg
  obtain ⟨T, hT, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    ⟨G, hG⟩ 0 (Complex.arg (G 0)) (Circle.exp_arg (G 0))
  refine ⟨T, T.continuous.continuousOn, ?_⟩
  intro t ht
  have hp_eq : p t = t := by
    simp only [p, projIcc_of_mem (by norm_num) ht]
  have hFeq : F t = f (bh6_boundaryCircuit X l m z t) := by simp [F, hp_eq]
  have hExpCircle : Circle.exp (T t) = G t := congr_fun hT.2 t
  have hExp : Complex.exp ((T t : ℂ) * Complex.I) = g t := by
    simpa [G, Circle.coe_exp] using congrArg Subtype.val hExpCircle
  rw [← hFeq, hExp]
  change F t = (‖F t‖ : ℂ) * (F t / (‖F t‖ : ℂ))
  field_simp [norm_ne_zero_iff.mpr (hFne t)]

/-- The integer extracted from the endpoint change of a real boundary lift.
For a closed nonvanishing loop, exponential periodicity makes the quotient integral.
Source: Hatcher, section 1.3, winding computed from a lift to the real line. -/
def bh6_phaseDegree (θ : ℝ → ℝ) : ℤ :=
  ⌊(θ 4 - θ 0) / (2 * Real.pi)⌋

/-- A closed boundary lift changes by an integral multiple of a full positive turn.
Source: Hatcher, section 1.3, exponential covering and winding of loops. -/
theorem bh6_phase_integer_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : (Fin (dim X.left) → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0)
    (θ : ℝ → ℝ) (hθ : ContinuousOn θ (Icc 0 4))
    (he : ∀ t ∈ Icc (0 : ℝ) 4, f (bh6_boundaryCircuit X l m z t) =
      (‖f (bh6_boundaryCircuit X l m z t)‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)) :
    (θ 4 - θ 0) / (2 * Real.pi) = (bh6_phaseDegree θ : ℝ) := by
  have hc : bh6_boundaryCircuit X l m z 4 = bh6_boundaryCircuit X l m z 0 := by
    norm_num [bh6_boundaryCircuit, bh4_squareEdge]
  have he0 := he 0 (by norm_num)
  have he4 := he 4 (by norm_num)
  rw [hc] at he4
  have hn : (‖f (bh6_boundaryCircuit X l m z 0)‖ : ℂ) ≠ 0 := by
    rw [show bh6_boundaryCircuit X l m z 0 = bh4_squareEdge X l m z 0 0 by
      norm_num [bh6_boundaryCircuit]]
    exact_mod_cast norm_ne_zero_iff.mpr (hnz 0 0 (by norm_num))
  have hexp : Complex.exp ((θ 4 : ℂ) * Complex.I) =
      Complex.exp ((θ 0 : ℂ) * Complex.I) :=
    mul_left_cancel₀ hn (he4.symm.trans he0)
  have hexpc : Circle.exp (θ 4) = Circle.exp (θ 0) := Subtype.ext hexp
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hexpc
  have hq : (θ 4 - θ 0) / (2 * Real.pi) = (k : ℝ) := by
    rw [hk]
    field_simp [Real.pi_ne_zero]
    ring
  unfold bh6_phaseDegree
  rw [hq]
  simp

/-- The positive complex boundary generator normalizes the point coclass evaluation.
Source: Hatcher, section 3.3, local orientation and its dual normalized coclass. -/
theorem bh6_boundary_normalization_aux
    (c : RelativeHomology ℚ (puncturedPair ℂ 1) 2) (k : ℤ)
    (hc : relativeSingularBoundary (puncturedPair ℂ 1) 1 c =
      (k : ℚ) • relativeSingularBoundary (puncturedPair ℂ 1) 1
        (standardComplexLocalClass ℚ 1)) :
    relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ 1) 2
      (normalizedPointCoclass 1) c = (k : ℚ) := by
  have hzero : IsZero (Homology ℚ (puncturedPair ℂ 1).fst 2) := by
    let e := (ContractibleSpace.hequiv_unit (Fin 1 → ℂ)).some
    exact (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat (R := ℚ)) 2 (ModuleCat.of ℚ ℚ) (TopCat.of Unit) (by omega)).of_iso
        (rationalSingularHomologyIsoOfHomotopyEquiv 2 e)
  letI : Mono (relativeSingularBoundary (puncturedPair ℂ 1) 1) :=
    (relativeSingular_homology_exact_relative (puncturedPair ℂ 1) 1).mono_g
      (hzero.eq_of_src _ 0)
  have hc' : c = (k : ℚ) • standardComplexLocalClass ℚ 1 := by
    apply (ModuleCat.mono_iff_injective
      (relativeSingularBoundary (puncturedPair ℂ 1) 1)).mp (by infer_instance)
    simpa only [map_smul] using hc
  rw [hc', map_smul, normalizedRelativeCoclass_pairing_self]
  simp

private lemma bh6_differentiableAt_of_cexp_lift {L q : ℝ → ℂ} {t : ℝ}
    (hL : ContinuousAt L t) (hq : DifferentiableAt ℝ q t)
    (he : ∀ᶠ s in nhds t, Complex.exp (L s) = q s) : DifferentiableAt ℝ L t := by
  let A : ℂ →L[ℝ] ℂ := Complex.exp (L t) • (1 : ℂ →L[ℝ] ℂ)
  let B : ℂ →L[ℝ] ℂ := (Complex.exp (L t))⁻¹ • (1 : ℂ →L[ℝ] ℂ)
  have hfd := HasFDerivAt.of_comp_of_leftInverse (f'symm := B) hL
    (Complex.hasStrictFDerivAt_exp_real (L t)).hasFDerivAt hq.hasFDerivAt
    he (fun v ↦ by simp [B])
  exact hfd.differentiableAt

private lemma bh6_boundaryCircuit_edge
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (i : Fin 4) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    bh6_boundaryCircuit X l m z (i.val + s) = bh4_squareEdge X l m z i s := by
  rcases hs with ⟨hs0, hs1⟩
  fin_cases i
  · simp [bh6_boundaryCircuit, hs1.le]
  · simp [bh6_boundaryCircuit, show ¬(1 + s ≤ 1) by linarith,
      show 1 + s ≤ 2 by linarith]
  · simp [bh6_boundaryCircuit, show ¬(2 + s ≤ 1) by linarith,
      show ¬(2 + s ≤ 2) by linarith, show 2 + s ≤ 3 by linarith]
  · simp [bh6_boundaryCircuit, show ¬(3 + s ≤ 1) by linarith,
      show ¬(3 + s ≤ 2) by linarith, show ¬(3 + s ≤ 3) by linarith]

/-- On one edge, the logarithmic integral is the modulus-log change plus the phase change.
Source: Ahlfors, *Complex Analysis*, Chapter 4, section 5, local logarithms and the fundamental theorem. -/
theorem bh6_edge_integral_phase_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : (Fin (dim X.left) → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0)
    (θ : ℝ → ℝ) (hθ : ContinuousOn θ (Icc 0 4))
    (he : ∀ t ∈ Icc (0 : ℝ) 4, f (bh6_boundaryCircuit X l m z t) =
      (‖f (bh6_boundaryCircuit X l m z t)‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)) (i : Fin 4) :
    (∫ t in (0 : ℝ)..1,
      deriv (fun s : ℝ ↦ f (bh4_squareEdge X l m z i s)) t /
        (2 * Real.pi * Complex.I * f (bh4_squareEdge X l m z i t))) =
      (((Real.log ‖f (bh6_boundaryCircuit X l m z (i.val + 1))‖ -
          Real.log ‖f (bh6_boundaryCircuit X l m z i.val)‖ : ℝ) : ℂ) +
        Complex.I * ((θ (i.val + 1) - θ i.val : ℝ) : ℂ)) /
        (2 * Real.pi * Complex.I) := by
  let q : ℝ → ℂ := fun s ↦ f (bh4_squareEdge X l m z i s)
  let L : ℝ → ℂ := fun s ↦ (Real.log ‖q s‖ : ℂ) + (θ (i.val + s) : ℂ) * Complex.I
  have hfR : ContDiff ℝ ⊤ f := hf.contDiff.restrict_scalars ℝ
  have hedge : ContDiff ℝ ⊤ (bh4_squareEdge X l m z i) := by
    fin_cases i
    · change ContDiff ℝ ⊤ (fun t ↦ z + t • (l : Fin (dim X.left) → ℂ))
      fun_prop
    · change ContDiff ℝ ⊤ (fun t ↦ z + l + t • (m : Fin (dim X.left) → ℂ))
      fun_prop
    · change ContDiff ℝ ⊤ (fun t ↦ z + (1 - t) • (l : Fin (dim X.left) → ℂ) + m)
      fun_prop
    · change ContDiff ℝ ⊤ (fun t ↦ z + (1 - t) • (m : Fin (dim X.left) → ℂ))
      fun_prop
  have hq : ContDiff ℝ ⊤ q := hfR.comp (by simpa [q] using hedge)
  have hqne (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : q s ≠ 0 := hnz i s hs
  have hmap (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (i.val : ℝ) + s ∈ Icc (0 : ℝ) 4 := by
    have hi0 : (0 : ℝ) ≤ i.val := by positivity
    have hi3 : (i.val : ℝ) ≤ 3 := by exact_mod_cast Nat.le_pred_of_lt i.isLt
    constructor <;> linarith [hi0, hi3, hs.1, hs.2]
  have hLcont : ContinuousOn L (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.add
    · exact Complex.continuous_ofReal.comp_continuousOn
        (hq.continuous.norm.continuousOn.log fun s hs ↦ norm_ne_zero_iff.mpr (hqne s hs))
    · exact (Complex.continuous_ofReal.comp_continuousOn
        (hθ.comp (continuous_const.add continuous_id).continuousOn hmap)).mul continuousOn_const
  have hExp (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : Complex.exp (L s) = q s := by
    change Complex.exp ((Real.log ‖q s‖ : ℂ) + (θ (i.val + s) : ℂ) * Complex.I) = q s
    rw [Complex.exp_add, ← Complex.ofReal_exp]
    rw [Real.exp_log (norm_pos_iff.mpr (hqne s ⟨hs.1.le, hs.2.le⟩))]
    have hh := he _ (hmap s ⟨hs.1.le, hs.2.le⟩)
    rw [bh6_boundaryCircuit_edge X l m z i hs] at hh
    simpa [q] using hh.symm
  have hLdiff (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : DifferentiableAt ℝ L s := by
    apply bh6_differentiableAt_of_cexp_lift
    · exact hLcont.continuousAt (Icc_mem_nhds hs.1 hs.2)
    · exact hq.differentiable (by norm_num) s
    · filter_upwards [Ioo_mem_nhds hs.1 hs.2] with u hu using hExp u hu
  have hderiv (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : deriv q s / q s = deriv L s := by
    have hd := deriv_cexp (hLdiff s hs)
    have heq : (fun u ↦ Complex.exp (L u)) =ᶠ[nhds s] q := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with u hu using hExp u hu
    rw [heq.deriv_eq] at hd
    apply (div_eq_iff (hqne s ⟨hs.1.le, hs.2.le⟩)).2
    rw [hd, hExp s hs]
    ring
  have hint : IntervalIntegrable (fun s ↦ deriv q s / q s) MeasureTheory.volume 0 1 := by
    change IntervalIntegrable (deriv q / q) MeasureTheory.volume 0 1
    have hdq : Continuous (deriv q) := hq.continuous_deriv (by simp)
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hdq.continuousOn.div hq.continuous.continuousOn hqne
  have hFTC : (∫ s in (0 : ℝ)..1, deriv q s / q s) = L 1 - L 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (by norm_num) hLcont
    · intro s hs
      exact (hLdiff s hs).hasDerivAt.congr_deriv (hderiv s hs).symm |>.hasDerivWithinAt
    · exact hint
  rw [show (fun s : ℝ ↦ f (bh4_squareEdge X l m z i s)) = q from rfl]
  have hfun : (fun t ↦ deriv q t / (2 * Real.pi * Complex.I * q t)) =
      fun t ↦ (deriv q t / q t) / (2 * Real.pi * Complex.I) := by
    funext t
    ring
  rw [hfun, intervalIntegral.integral_div, hFTC]
  have hc0 : bh6_boundaryCircuit X l m z i.val = bh4_squareEdge X l m z i 0 := by
    fin_cases i <;> norm_num [bh6_boundaryCircuit, bh4_squareEdge]
  have hc1 : bh6_boundaryCircuit X l m z (i.val + 1) = bh4_squareEdge X l m z i 1 := by
    fin_cases i <;> norm_num [bh6_boundaryCircuit, bh4_squareEdge]
  rw [hc0, hc1]
  simp only [L, q]
  field_simp [Complex.I_ne_zero, Real.pi_ne_zero]
  push_cast
  ring

/-- Four consecutive endpoint differences telescope, and the closed modulus term cancels.
Source: finite telescoping sums and the normalization of winding by a positive full turn. -/
theorem bh6_four_edge_telescope (r θ : ℝ → ℝ) (hr : r 4 = r 0) :
    (∑ i : Fin 4,
      (((r (i.val + 1) - r i.val : ℝ) : ℂ) +
        Complex.I * ((θ (i.val + 1) - θ i.val : ℝ) : ℂ)) /
        (2 * Real.pi * Complex.I)) = (((θ 4 - θ 0) / (2 * Real.pi) : ℝ) : ℂ) := by
  norm_num [Fin.sum_univ_four]
  rw [hr]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- Integrate the logarithmic derivative along the four edges using a lifted boundary phase.
The positive modulus contributes zero around the closed circuit.
Source: Ahlfors, *Complex Analysis*, Chapter 4, section 5, change of argument along a contour. -/
theorem bh6_boundary_integral_phase_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : (Fin (dim X.left) → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0)
    (θ : ℝ → ℝ) (hθ : ContinuousOn θ (Icc 0 4))
    (he : ∀ t ∈ Icc (0 : ℝ) 4, f (bh6_boundaryCircuit X l m z t) =
      (‖f (bh6_boundaryCircuit X l m z t)‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)) :
    bh4_boundaryWinding X l m z f = (((θ 4 - θ 0) / (2 * Real.pi) : ℝ) : ℂ) := by
  unfold bh4_boundaryWinding
  simp_rw [bh6_edge_integral_phase_aux X f hf l m z hnz θ hθ he]
  apply bh6_four_edge_telescope (fun t ↦ Real.log ‖f (bh6_boundaryCircuit X l m z t)‖) θ
  congr 2
  norm_num [bh6_boundaryCircuit, bh4_squareEdge]

/- Connecting maps and the action of an integral phase on circle homology. -/
private theorem bh6_boundary_naturality {P Q : TopPair} (f : P ⟶ Q) (n : ℕ)
    (c : RelativeHomology ℚ P (n + 1)) :
    relativeSingularBoundary Q n (relativeHomologyMap ℚ (n + 1) f c) =
      homologyMap ℚ n (TopPair.Hom.snd f) (relativeSingularBoundary P n c) := by
  let φ : relativeChainShortComplex ℚ P ⟶ relativeChainShortComplex ℚ Q :=
    { τ₁ := ((chainPairFunctor ℚ).map f).left
      τ₂ := ((chainPairFunctor ℚ).map f).right
      τ₃ := (relativeChainFunctor ℚ).map f
      comm₁₂ := ((chainPairFunctor ℚ).map f).w
      comm₂₃ := by simp [relativeChainShortComplex, relativeChainProjection,
        relativeChainFunctor] }
  exact (ConcreteCategory.congr_hom
    (HomologicalComplex.HomologySequence.δ_naturality φ
      (relativeChainShortComplex_shortExact ℚ P)
      (relativeChainShortComplex_shortExact ℚ Q) (n + 1) n (by simp)) c).symm

private theorem bh6_circle_cohomology_zsmul (k : ℤ)
    (a : Cohomology ℚ (TopCat.of UnitAddCircle) 1) :
    cohomologyMap ℚ 1 (TopCat.ofHom (circleZsmul k)) a = (k : ℚ) • a := by
  have hdegree : Function.Injective circleDegree := by
    intro a b h
    apply circleClassBasis.repr.injective
    apply Finsupp.ext
    intro i
    fin_cases i
    exact h
  apply hdegree
  have hspan : a ∈ Submodule.span ℚ
      ({HodgeLean.Foundations.Singular.circleClass} : Set _) := by
    rw [HodgeLean.Foundations.Singular.span_circleClass_eq_top]
    exact Submodule.mem_top
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hspan
  have hk := loopPeriod_circleZsmul k
  change circleDegree (cohomologyMap ℚ 1 (TopCat.ofHom (circleZsmul k))
    HodgeLean.Foundations.Singular.circleClass) = (k : ℚ) at hk
  have h1 := loopPeriod_id_circleClass
  change circleDegree (cohomologyMap ℚ 1 (𝟙 (TopCat.of UnitAddCircle))
    HodgeLean.Foundations.Singular.circleClass) = 1 at h1
  rw [cohomologyMap_id, LinearMap.id_apply] at h1
  simp only [map_smul, hk, h1, smul_eq_mul, mul_one]
  exact mul_comm _ _

private theorem bh6_circle_homology_zsmul (k : ℤ)
    (c : Homology ℚ (TopCat.of UnitAddCircle) 1) :
    homologyMap ℚ 1 (TopCat.ofHom (circleZsmul k)) c = (k : ℚ) • c := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro φ
  obtain ⟨a, rfl⟩ := (cohomologyEquivDualHomology ℚ (TopCat.of UnitAddCircle) 1).surjective φ
  rw [map_sub, ← cohomologyEquivDualHomology_cohomologyMap,
    bh6_circle_cohomology_zsmul, map_smul, map_smul]
  simp only [LinearMap.smul_apply, sub_self]

private theorem bh6_homology_add_real_lift (k : ℤ) (a : C(UnitAddCircle, ℝ))
    (c : Homology ℚ (TopCat.of UnitAddCircle) 1) :
    homologyMap ℚ 1 (TopCat.ofHom
      ⟨fun x : UnitAddCircle ↦ k • x + (a x : UnitAddCircle),
        (continuous_zsmul k).add ((AddCircle.continuous_mk' 1).comp a.continuous)⟩) c =
      (k : ℚ) • c := by
  let H : ContinuousMap.Homotopy
      (⟨fun x : UnitAddCircle ↦ k • x + (a x : UnitAddCircle),
        (continuous_zsmul k).add ((AddCircle.continuous_mk' 1).comp a.continuous)⟩ :
        C(UnitAddCircle, UnitAddCircle)) (circleZsmul k) :=
    { toFun := fun p ↦ k • p.2 + (((1 - (p.1 : ℝ)) * a p.2 : ℝ) : UnitAddCircle)
      continuous_toFun := by fun_prop
      map_zero_left := by intro x; simp
      map_one_left := by intro x; simp [circleZsmul] }
  have h := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (f := TopCat.ofHom _) (g := TopCat.ofHom (circleZsmul k))
    H (ModuleCat.of ℚ ℚ) 1
  exact (ConcreteCategory.congr_hom h c).trans (bh6_circle_homology_zsmul k c)

private theorem bh6_phase_circle_homology (θ : ℝ → ℝ)
    (hθ : ContinuousOn θ (Icc 0 4)) (k : ℤ)
    (hk : (θ 4 - θ 0) / (2 * Real.pi) = (k : ℝ)) :
    ∃ p : C(UnitAddCircle, UnitAddCircle),
      (∀ t ∈ Ico (0 : ℝ) 1,
        p (t : UnitAddCircle) = ((θ (4 * t) / (2 * Real.pi) : ℝ) : UnitAddCircle)) ∧
      ∀ c : Homology ℚ (TopCat.of UnitAddCircle) 1,
        homologyMap ℚ 1 (TopCat.ofHom p) c = (k : ℚ) • c := by
  let r : ℝ → ℝ := fun t ↦ θ (4 * t) / (2 * Real.pi) - (k : ℝ) * t
  have hr : r 0 = r 1 := by
    dsimp only [r]
    simp only [mul_zero, mul_one, sub_zero]
    rw [sub_div] at hk
    linarith
  have hrc : ContinuousOn r (Icc 0 1) := by
    apply ContinuousOn.sub
    · exact (hθ.comp (continuous_const.mul continuous_id).continuousOn
        (fun t ht ↦ ⟨by change 0 ≤ 4 * t; linarith [ht.1],
          by change 4 * t ≤ 4; linarith [ht.2]⟩)).div_const _
    · exact (continuous_const.mul continuous_id).continuousOn
  let a : C(UnitAddCircle, ℝ) :=
    ⟨AddCircle.liftIco 1 0 r, AddCircle.liftIco_zero_continuous hr hrc⟩
  let p : C(UnitAddCircle, UnitAddCircle) :=
    ⟨fun x ↦ k • x + (a x : UnitAddCircle),
      (continuous_zsmul k).add ((AddCircle.continuous_mk' 1).comp a.continuous)⟩
  refine ⟨p, ?_, fun c ↦ bh6_homology_add_real_lift k a c⟩
  intro t ht
  change k • (t : UnitAddCircle) +
    ((AddCircle.liftIco 1 0 r (t : UnitAddCircle) : ℝ) : UnitAddCircle) = _
  rw [AddCircle.liftIco_zero_coe_apply ht, ← AddCircle.coe_zsmul, ← AddCircle.coe_add]
  congr 1
  simp only [r, zsmul_eq_mul]
  ring

private theorem bh6_homology_modulus {Y : TopCat} (f g : Y ⟶ (puncturedPair ℂ 1).snd)
    (h : ∀ y, (f y).val = ‖(f y).val‖ • (g y).val) (n : ℕ) :
    homologyMap ℚ n f = homologyMap ℚ n g := by
  have hpos (t : unitInterval) (y : Y) :
      0 < (1 - (t : ℝ)) * ‖(f y).val‖ + (t : ℝ) := by
    have hn : 0 < ‖(f y).val‖ := norm_pos_iff.mpr (f y).property
    by_cases ht : (t : ℝ) = 0
    · simpa only [ht, sub_zero, one_mul, add_zero] using hn
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr t.property.2) hn.le)
        (lt_of_le_of_ne t.property.1 (Ne.symm ht))
  let H : TopCat.Homotopy f g :=
    { toFun := fun p ↦
        ⟨((1 - (p.1 : ℝ)) * ‖(f p.2).val‖ + (p.1 : ℝ)) • (g p.2).val,
          smul_ne_zero (ne_of_gt (hpos p.1 p.2)) (g p.2).property⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (((continuous_const.sub continuous_fst.subtype_val).mul
          ((continuous_subtype_val.comp (f.hom.continuous.comp continuous_snd)).norm)).add
          continuous_fst.subtype_val).smul
          (continuous_subtype_val.comp (g.hom.continuous.comp continuous_snd))
      map_zero_left := by
        intro y
        apply Subtype.ext
        simpa using (h y).symm
      map_one_left := by intro y; apply Subtype.ext; simp }
  exact congrArg ModuleCat.Hom.hom
    (TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H (ModuleCat.of ℚ ℚ) n)

private theorem bh6_circuit_continuous
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ) :
    Continuous (bh6_boundaryCircuit X l m z) := by
  have hc (i : Fin 4) : Continuous (bh4_squareEdge X l m z i) := by
    change Continuous (fun t ↦ bh4_squareEdge X l m z i t)
    fin_cases i <;> dsimp [bh4_squareEdge] <;> fun_prop
  unfold bh6_boundaryCircuit
  refine Continuous.if_le (hc 0) ?_ continuous_id continuous_const ?_
  · refine Continuous.if_le ((hc 1).comp (continuous_id.sub continuous_const))
      ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le ((hc 2).comp (continuous_id.sub continuous_const))
        ((hc 3).comp (continuous_id.sub continuous_const)) continuous_id continuous_const ?_
      intro t ht
      subst t
      norm_num [bh4_squareEdge]
    · intro t ht
      subst t
      norm_num [bh4_squareEdge]
  · intro t ht
    subst t
    norm_num [bh4_squareEdge]

private theorem bh6_circuit_ne_zero
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : (Fin (dim X.left) → ℂ) → ℂ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) : f (bh6_boundaryCircuit X l m z t) ≠ 0 := by
  unfold bh6_boundaryCircuit
  split_ifs with h1 h2 h3
  · exact hnz 0 t ⟨ht.1, h1⟩
  · exact hnz 1 (t - 1) ⟨by linarith, by linarith⟩
  · exact hnz 2 (t - 2) ⟨by linarith, by linarith⟩
  · exact hnz 3 (t - 3) ⟨by linarith, by linarith [ht.2]⟩


private def bh6_circlePuncture : C(UnitAddCircle, (puncturedPair ℂ 1).snd) :=
  ⟨fun s ↦ ⟨fun _ ↦ (AddCircle.toCircle s : ℂ), by
      intro h
      exact (AddCircle.toCircle s).coe_ne_zero (congrFun h 0)⟩,
    by
      apply Continuous.subtype_mk
      exact continuous_pi fun _ ↦ continuous_subtype_val.comp AddCircle.continuous_toCircle⟩

private def bh6_boundaryLoop
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : Continuous f)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0) :
    C(UnitAddCircle, (puncturedPair ℂ 1).snd) := by
  let b : ℝ → Fin 1 → ℂ := fun t _ ↦ f (bh6_boundaryCircuit X l m z (4 * t))
  have hb : b 0 = b 1 := by
    ext i
    norm_num [b, bh6_boundaryCircuit, bh4_squareEdge]
  have hc : Continuous b := continuous_pi fun _ ↦
    hf.comp ((bh6_circuit_continuous X l m z).comp (continuous_const.mul continuous_id))
  have hne (s : UnitAddCircle) : AddCircle.liftIco 1 0 b s ≠ 0 := by
    intro he
    have ht := (AddCircle.equivIco 1 0 s).property
    have hn := bh6_circuit_ne_zero X f l m z hnz (4 * (AddCircle.equivIco 1 0 s : ℝ))
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact hn (congrFun he 0)
  exact ⟨fun s ↦ ⟨AddCircle.liftIco 1 0 b s, hne s⟩,
    (AddCircle.liftIco_zero_continuous hb hc.continuousOn).subtype_mk _⟩

private theorem bh6_boundaryLoop_apply
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : Continuous f)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
    (bh6_boundaryLoop X f hf l m z hnz (t : UnitAddCircle)).val =
      fun _ ↦ f (bh6_boundaryCircuit X l m z (4 * t)) := by
  change AddCircle.liftIco 1 0 (fun u _ ↦ f (bh6_boundaryCircuit X l m z (4 * u)))
    (t : UnitAddCircle) = _
  exact AddCircle.liftIco_zero_coe_apply ht


set_option backward.isDefEq.respectTransparency false in
private theorem bh6_boundaryLoop_homology
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : Continuous f)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0)
    (θ : ℝ → ℝ) (hθ : ContinuousOn θ (Icc 0 4))
    (he : ∀ t ∈ Icc (0 : ℝ) 4, f (bh6_boundaryCircuit X l m z t) =
      (‖f (bh6_boundaryCircuit X l m z t)‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I))
    (k : ℤ) (hk : (θ 4 - θ 0) / (2 * Real.pi) = (k : ℝ))
    (c : Homology ℚ (TopCat.of UnitAddCircle) 1) :
    homologyMap ℚ 1 (TopCat.ofHom (bh6_boundaryLoop X f hf l m z hnz)) c =
      (k : ℚ) • homologyMap ℚ 1 (TopCat.ofHom bh6_circlePuncture) c := by
  obtain ⟨p, hp, hpdeg⟩ := bh6_phase_circle_homology θ hθ k hk
  have hm : ∀ s : UnitAddCircle,
      (bh6_boundaryLoop X f hf l m z hnz s).val =
        ‖(bh6_boundaryLoop X f hf l m z hnz s).val‖ • (bh6_circlePuncture (p s)).val := by
    intro s
    let t := (AddCircle.equivIco 1 0 s : ℝ)
    have ht : t ∈ Ico (0 : ℝ) 1 := by
      simpa only [zero_add] using (AddCircle.equivIco 1 0 s).property
    have hs : (t : UnitAddCircle) = s := AddCircle.coe_equivIco
    rw [← hs, bh6_boundaryLoop_apply X f hf l m z hnz t ht, hp t ht]
    ext i
    change f (bh6_boundaryCircuit X l m z (4 * t)) =
      ‖(fun _ : Fin 1 ↦ f (bh6_boundaryCircuit X l m z (4 * t)))‖ •
        (AddCircle.toCircle ((θ (4 * t) / (2 * Real.pi) : ℝ) : UnitAddCircle) : ℂ)
    rw [pi_norm_const, AddCircle.toCircle_apply_mk, div_one,
      mul_div_cancel₀ _ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero),
      Circle.coe_exp, Complex.real_smul]
    exact he (4 * t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmap := bh6_homology_modulus
    (TopCat.ofHom (bh6_boundaryLoop X f hf l m z hnz))
    (TopCat.ofHom p ≫ TopCat.ofHom bh6_circlePuncture) hm 1
  rw [hmap, homologyMap_comp, LinearMap.comp_apply, hpdeg, map_smul]

set_option backward.isDefEq.respectTransparency false in
private theorem bh6_disk_boundary_restrict :
    homologyMap ℚ 1 (TopPair.Hom.snd
      (supportInclusionPairMap (TopCat.of (Fin 1 → ℂ))
        (Set.singleton_subset_iff.mpr
          (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2)))))
      (relativeSingularBoundary bh5_diskPair 1 bh5_diskClass) =
    relativeSingularBoundary (puncturedPair ℂ 1) 1 (standardComplexLocalClass ℚ 1) := by
  have h := bh6_boundary_naturality (P := bh5_diskPair) (Q := puncturedPair ℂ 1)
    (supportInclusionPairMap (TopCat.of (Fin 1 → ℂ))
      (Set.singleton_subset_iff.mpr
        (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2)))) 1 bh5_diskClass
  apply h.symm.trans
  apply congrArg (relativeSingularBoundary (puncturedPair ℂ 1) 1)
  exact (Equiv.ofBijective _ (j5c_convex_restrict_bijective
    (convex_closedBall (0 : Fin 1 → ℂ) (2 : ℝ)) (isCompact_closedBall 0 2)
    (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2)) 2)).apply_symm_apply _


/- The clamped disk complement and the positively oriented square boundary. -/
private def bh6_squarePerimeter (t : ℝ) : ℂ :=
  if t ≤ 1 then (2 * t - 1) - Complex.I
  else if t ≤ 2 then 1 + (2 * t - 3) * Complex.I
  else if t ≤ 3 then (5 - 2 * t) + Complex.I
  else -1 + (7 - 2 * t) * Complex.I

private theorem bh6_squarePerimeter_continuous : Continuous bh6_squarePerimeter := by
  unfold bh6_squarePerimeter
  refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
  · refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const ?_
      intro t ht
      subst t
      norm_num [sub_eq_add_neg]
    · intro t ht
      subst t
      norm_num [sub_eq_add_neg]
  · intro t ht
    subst t
    norm_num [sub_eq_add_neg]

private theorem bh6_squarePerimeter_ne_zero (t : ℝ) : bh6_squarePerimeter t ≠ 0 := by
  unfold bh6_squarePerimeter
  split_ifs
  · intro h
    have := congrArg Complex.im h
    norm_num at this
  · intro h
    have := congrArg Complex.re h
    norm_num at this
  · intro h
    have := congrArg Complex.im h
    norm_num at this
  · intro h
    have := congrArg Complex.re h
    norm_num at this

private def bh6_squareLoop : C(UnitAddCircle, (puncturedPair ℂ 1).snd) := by
  let b : ℝ → Fin 1 → ℂ := fun t _ ↦ bh6_squarePerimeter (4 * t)
  have hb : b 0 = b 1 := by
    ext i
    norm_num [b, bh6_squarePerimeter, sub_eq_add_neg]
  have hc : Continuous b := continuous_pi fun _ ↦
    bh6_squarePerimeter_continuous.comp (continuous_const.mul continuous_id)
  have hne (s : UnitAddCircle) : AddCircle.liftIco 1 0 b s ≠ 0 := by
    intro he
    exact bh6_squarePerimeter_ne_zero _ (congrFun he 0)
  exact ⟨fun s ↦ ⟨AddCircle.liftIco 1 0 b s, hne s⟩,
    (AddCircle.liftIco_zero_continuous hb hc.continuousOn).subtype_mk _⟩

private theorem bh6_squareLoop_apply (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
    (bh6_squareLoop (t : UnitAddCircle)).val = fun _ ↦ bh6_squarePerimeter (4 * t) := by
  change AddCircle.liftIco 1 0 (fun u _ ↦ bh6_squarePerimeter (4 * u))
    (t : UnitAddCircle) = _
  exact AddCircle.liftIco_zero_coe_apply ht


private theorem bh6_squarePerimeter_interpolate_ne_zero
    (t u : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) (hu : u ∈ Icc (0 : ℝ) 1) :
    (1 - u) • bh6_squarePerimeter t + u •
      Complex.exp (((Real.pi / 2 * t - 3 * Real.pi / 4 : ℝ) : ℂ) * Complex.I) ≠ 0 := by
  have hneg (a : ℝ) (ha : a < 0) : (1 - u) * (-1) + u * a < 0 := by
    by_cases h : u = 0
    · simp [h]
    · have := mul_neg_of_pos_of_neg (lt_of_le_of_ne hu.1 (Ne.symm h)) ha
      nlinarith [hu.2]
  have hpos (a : ℝ) (ha : 0 < a) : (1 - u) * 1 + u * a > 0 := by
    by_cases h : u = 0
    · simp [h]
    · have := mul_pos (lt_of_le_of_ne hu.1 (Ne.symm h)) ha
      nlinarith [hu.2]
  unfold bh6_squarePerimeter
  split_ifs with h1 h2 h3
  · have hs : Real.sin (Real.pi / 2 * t - 3 * Real.pi / 4) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt (by nlinarith [Real.pi_pos])
        (by nlinarith [ht.1, Real.pi_pos])
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im, Complex.smul_im, Complex.exp_ofReal_mul_I_im] at hi
    norm_num at hi
    linarith [hneg _ hs]
  · have hc : 0 < Real.cos (Real.pi / 2 * t - 3 * Real.pi / 4) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.smul_re, Complex.exp_ofReal_mul_I_re] at hr
    norm_num at hr
    linarith [hpos _ hc]
  · have hs : 0 < Real.sin (Real.pi / 2 * t - 3 * Real.pi / 4) :=
      Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im, Complex.smul_im, Complex.exp_ofReal_mul_I_im] at hi
    norm_num at hi
    linarith [hpos _ hs]
  · have hc : Real.cos (Real.pi / 2 * t - 3 * Real.pi / 4) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt (by nlinarith [Real.pi_pos])
        (by nlinarith [ht.2, Real.pi_pos])
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.smul_re, Complex.exp_ofReal_mul_I_re] at hr
    norm_num at hr
    linarith [hneg _ hc]


private def bh6_perimeterPhase (s t : ℝ) : UnitAddCircle :=
  if t = 0 then (s / 4 : ℝ)
  else if s = 1 then ((1 + t) / 4 : ℝ)
  else if t = 1 then ((3 - s) / 4 : ℝ)
  else ((4 - t) / 4 : ℝ)

private theorem bh6_perimeterPhase_bottom (s : ℝ) :
    bh6_perimeterPhase s 0 = ((s / 4 : ℝ) : UnitAddCircle) := by
  simp [bh6_perimeterPhase]

private theorem bh6_perimeterPhase_right (t : ℝ) :
    bh6_perimeterPhase 1 t = (((1 + t) / 4 : ℝ) : UnitAddCircle) := by
  by_cases h : t = 0 <;> simp [bh6_perimeterPhase, h]

private theorem bh6_perimeterPhase_top (s : ℝ) :
    bh6_perimeterPhase s 1 = (((3 - s) / 4 : ℝ) : UnitAddCircle) := by
  by_cases h : s = 1 <;> norm_num [bh6_perimeterPhase, h]

private theorem bh6_perimeterPhase_left (t : ℝ) :
    bh6_perimeterPhase 0 t = (((4 - t) / 4 : ℝ) : UnitAddCircle) := by
  by_cases h0 : t = 0
  · subst t
    norm_num [bh6_perimeterPhase]
    exact (AddCircle.coe_period (1 : ℝ)).symm
  · by_cases h1 : t = 1 <;> norm_num [bh6_perimeterPhase, h0, h1]

private theorem bh6_perimeterPhase_continuous {Y : Type} [TopologicalSpace Y]
    (s t : C(Y, ℝ)) (hb : ∀ y, s y = 0 ∨ s y = 1 ∨ t y = 0 ∨ t y = 1) :
    Continuous (fun y ↦ bh6_perimeterPhase (s y) (t y)) := by
  have h0 : ContinuousOn (fun y ↦ bh6_perimeterPhase (s y) (t y)) {y | s y = 0} := by
    refine (((AddCircle.continuous_mk' 1).comp
      (((continuous_const : Continuous (fun _ : Y ↦ (4 : ℝ))).sub t.continuous).div_const 4)).continuousOn).congr ?_
    intro y hy
    change bh6_perimeterPhase (s y) (t y) = _
    rw [hy, bh6_perimeterPhase_left]
    rfl
  have h1 : ContinuousOn (fun y ↦ bh6_perimeterPhase (s y) (t y)) {y | s y = 1} := by
    refine (((AddCircle.continuous_mk' 1).comp
      (((continuous_const : Continuous (fun _ : Y ↦ (1 : ℝ))).add t.continuous).div_const 4)).continuousOn).congr ?_
    intro y hy
    change bh6_perimeterPhase (s y) (t y) = _
    rw [hy, bh6_perimeterPhase_right]
    rfl
  have h2 : ContinuousOn (fun y ↦ bh6_perimeterPhase (s y) (t y)) {y | t y = 0} := by
    refine (((AddCircle.continuous_mk' 1).comp
      (s.continuous.div_const 4)).continuousOn).congr ?_
    intro y hy
    change bh6_perimeterPhase (s y) (t y) = _
    rw [hy, bh6_perimeterPhase_bottom]
    rfl
  have h3 : ContinuousOn (fun y ↦ bh6_perimeterPhase (s y) (t y)) {y | t y = 1} := by
    refine (((AddCircle.continuous_mk' 1).comp
      (((continuous_const : Continuous (fun _ : Y ↦ (3 : ℝ))).sub s.continuous).div_const 4)).continuousOn).congr ?_
    intro y hy
    change bh6_perimeterPhase (s y) (t y) = _
    rw [hy, bh6_perimeterPhase_top]
    rfl
  have hc := h0.union_of_isClosed
    (h1.union_of_isClosed (h2.union_of_isClosed h3
      (isClosed_eq t.continuous continuous_const) (isClosed_eq t.continuous continuous_const))
      (isClosed_eq s.continuous continuous_const)
      ((isClosed_eq t.continuous continuous_const).union (isClosed_eq t.continuous continuous_const)))
    (isClosed_eq s.continuous continuous_const)
    ((isClosed_eq s.continuous continuous_const).union
      ((isClosed_eq t.continuous continuous_const).union (isClosed_eq t.continuous continuous_const)))
  have hu : {y | s y = 0} ∪ ({y | s y = 1} ∪ ({y | t y = 0} ∪ {y | t y = 1})) = univ :=
    Set.eq_univ_of_forall hb
  rw [hu] at hc
  exact continuousOn_univ.mp hc

set_option backward.isDefEq.respectTransparency false in
private theorem bh6_squareLoop_homology (c : Homology ℚ (TopCat.of UnitAddCircle) 1) :
    homologyMap ℚ 1 (TopCat.ofHom bh6_squareLoop) c =
      homologyMap ℚ 1 (TopCat.ofHom bh6_circlePuncture) c := by
  let a : C(UnitAddCircle, ℝ) := ContinuousMap.const _ (-3 / 8)
  let p : C(UnitAddCircle, UnitAddCircle) :=
    ⟨fun s ↦ (1 : ℤ) • s + (a s : UnitAddCircle), by fun_prop⟩
  let g := bh6_circlePuncture.comp p
  have hg (t : ℝ) : (g (t : UnitAddCircle)).val = fun _ ↦
      Complex.exp (((Real.pi / 2 * (4 * t) - 3 * Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
    ext i
    change (AddCircle.toCircle ((1 : ℤ) • (t : UnitAddCircle) +
      ((-3 / 8 : ℝ) : UnitAddCircle)) : ℂ) = _
    rw [one_zsmul, ← AddCircle.coe_add, AddCircle.toCircle_apply_mk, Circle.coe_exp]
    congr 3
    ring
  have hne (u : unitInterval) (s : UnitAddCircle) :
      (1 - (u : ℝ)) • (bh6_squareLoop s).val + (u : ℝ) • (g s).val ≠ 0 := by
    let t := (AddCircle.equivIco 1 0 s : ℝ)
    have ht : t ∈ Ico (0 : ℝ) 1 := by
      simpa only [zero_add] using (AddCircle.equivIco 1 0 s).property
    have hs : (t : UnitAddCircle) = s := AddCircle.coe_equivIco
    rw [← hs, bh6_squareLoop_apply t ht, hg]
    intro hzero
    exact bh6_squarePerimeter_interpolate_ne_zero (4 * t) u
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ u.property (congrFun hzero 0)
  let H : TopCat.Homotopy (TopCat.ofHom bh6_squareLoop) (TopCat.ofHom g) :=
    { toFun := fun x ↦ ⟨(1 - (x.1 : ℝ)) • (bh6_squareLoop x.2).val +
        (x.1 : ℝ) • (g x.2).val, hne x.1 x.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact ((continuous_const.sub continuous_fst.subtype_val).smul
          (continuous_subtype_val.comp (bh6_squareLoop.continuous.comp continuous_snd))).add
          (continuous_fst.subtype_val.smul
            (continuous_subtype_val.comp (g.continuous.comp continuous_snd)))
      map_zero_left := by intro s; apply Subtype.ext; simp
      map_one_left := by intro s; apply Subtype.ext; simp }
  have h := ConcreteCategory.congr_hom
    (TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H (ModuleCat.of ℚ ℚ) 1) c
  change homologyMap ℚ 1 (TopCat.ofHom bh6_squareLoop) c =
    homologyMap ℚ 1 (TopCat.ofHom p ≫ TopCat.ofHom bh6_circlePuncture) c at h
  rw [homologyMap_comp, LinearMap.comp_apply, bh6_homology_add_real_lift] at h
  simpa only [Int.cast_one, one_smul] using h

private theorem bh6_clamped_on_boundary (q : bh5_diskPair.snd) :
    bh5_clamp (((q.val 0).re + 1) / 2) = 0 ∨
    bh5_clamp (((q.val 0).re + 1) / 2) = 1 ∨
    bh5_clamp (((q.val 0).im + 1) / 2) = 0 ∨
    bh5_clamp (((q.val 0).im + 1) / 2) = 1 := by
  by_contra! h
  have hr : -1 < (q.val 0).re ∧ (q.val 0).re < 1 := by
    constructor
    · by_contra! hh
      apply h.1
      simp [bh5_clamp, min_eq_right (by linarith : ((q.val 0).re + 1) / 2 ≤ 1),
        max_eq_left (by linarith : ((q.val 0).re + 1) / 2 ≤ 0)]
    · by_contra! hh
      apply h.2.1
      simp [bh5_clamp, min_eq_left (by linarith : 1 ≤ ((q.val 0).re + 1) / 2)]
  have hi : -1 < (q.val 0).im ∧ (q.val 0).im < 1 := by
    constructor
    · by_contra! hh
      apply h.2.2.1
      simp [bh5_clamp, min_eq_right (by linarith : ((q.val 0).im + 1) / 2 ≤ 1),
        max_eq_left (by linarith : ((q.val 0).im + 1) / 2 ≤ 0)]
    · by_contra! hh
      apply h.2.2.2
      simp [bh5_clamp, min_eq_left (by linarith : 1 ≤ ((q.val 0).im + 1) / 2)]
  apply q.property
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
  intro i
  fin_cases i
  calc
    ‖q.val 0‖ ≤ |(q.val 0).re| + |(q.val 0).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 := by
      have := abs_le.mpr ⟨hr.1.le, hr.2.le⟩
      have := abs_le.mpr ⟨hi.1.le, hi.2.le⟩
      linarith


private def bh6_diskPhase : C(bh5_diskPair.snd, UnitAddCircle) :=
  ⟨fun q ↦ bh6_perimeterPhase (bh5_clamp (((q.val 0).re + 1) / 2))
    (bh5_clamp (((q.val 0).im + 1) / 2)),
    bh6_perimeterPhase_continuous
      ⟨fun q : bh5_diskPair.snd ↦ bh5_clamp (((q.val 0).re + 1) / 2), by
        unfold bh5_clamp
        exact continuous_const.max (continuous_const.min
          (((Complex.continuous_re.comp ((continuous_apply 0).comp continuous_subtype_val)).add
            continuous_const).div_const 2))⟩
      ⟨fun q : bh5_diskPair.snd ↦ bh5_clamp (((q.val 0).im + 1) / 2), by
        unfold bh5_clamp
        exact continuous_const.max (continuous_const.min
          (((Complex.continuous_im.comp ((continuous_apply 0).comp continuous_subtype_val)).add
            continuous_const).div_const 2))⟩
      bh6_clamped_on_boundary⟩

private def bh6_perimeterTime (s t : ℝ) : ℝ :=
  if t = 0 then s else if s = 1 then 1 + t else if t = 1 then 3 - s else 4 - t

private theorem bh6_perimeterPhase_time (s t : ℝ) :
    bh6_perimeterPhase s t = ((bh6_perimeterTime s t / 4 : ℝ) : UnitAddCircle) := by
  unfold bh6_perimeterPhase bh6_perimeterTime
  split_ifs <;> rfl

private theorem bh6_perimeterTime_bounds (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : bh6_perimeterTime s t ∈ Ico (0 : ℝ) 4 := by
  unfold bh6_perimeterTime
  split_ifs with h0 h1 h2
  · constructor <;> linarith [hs.1, hs.2]
  · constructor <;> linarith [ht.1, ht.2]
  · constructor <;> linarith [hs.1, hs.2]
  · have hp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h0)
    constructor <;> linarith [ht.2]

private theorem bh6_squarePerimeter_time (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hb : s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) :
    bh6_squarePerimeter (bh6_perimeterTime s t) =
      (2 * s - 1 : ℝ) + (2 * t - 1 : ℝ) * Complex.I := by
  unfold bh6_perimeterTime
  split_ifs with ht0 hs1 ht1
  · subst t
    simp [bh6_squarePerimeter, hs.2]
    ring
  · subst s
    have h1 : ¬1 + t ≤ 1 := by
      have := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      linarith
    have h2 : 1 + t ≤ 2 := by linarith [ht.2]
    simp [bh6_squarePerimeter, h1, h2]
    ring
  · subst t
    have h1 : ¬3 - s ≤ 1 := by linarith [hs.2]
    have h2 : ¬3 - s ≤ 2 := by
      have := lt_of_le_of_ne hs.2 hs1
      linarith
    have h3 : 3 - s ≤ 3 := by linarith [hs.1]
    simp [bh6_squarePerimeter, h1, h2, h3]
    ring
  · have hs0 : s = 0 := hb.resolve_right (not_or.mpr ⟨hs1, not_or.mpr ⟨ht0, ht1⟩⟩)
    subst s
    have h1 : ¬4 - t ≤ 1 := by linarith [ht.2]
    have h2 : ¬4 - t ≤ 2 := by linarith [ht.2]
    have h3 : ¬4 - t ≤ 3 := by
      have := lt_of_le_of_ne ht.2 ht1
      linarith
    simp [bh6_squarePerimeter, h1, h2, h3]
    ring

private theorem bh6_boundaryCircuit_time
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hb : s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) :
    bh6_boundaryCircuit X l m z (bh6_perimeterTime s t) = z + s • l.val + t • m.val := by
  unfold bh6_perimeterTime
  split_ifs with ht0 hs1 ht1
  · subst t
    simp [bh6_boundaryCircuit, bh4_squareEdge, hs.2]
  · subst s
    have h1 : ¬1 + t ≤ 1 := by
      have := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      linarith
    have h2 : 1 + t ≤ 2 := by linarith [ht.2]
    simp [bh6_boundaryCircuit, bh4_squareEdge, h1, h2]
  · subst t
    have h1 : ¬3 - s ≤ 1 := by linarith [hs.2]
    have h2 : ¬3 - s ≤ 2 := by
      have := lt_of_le_of_ne hs.2 hs1
      linarith
    have h3 : 3 - s ≤ 3 := by linarith [hs.1]
    have he : 1 - (3 - s - 2) = s := by ring
    simp [bh6_boundaryCircuit, bh4_squareEdge, h1, h2, h3, he]
  · have hs0 : s = 0 := hb.resolve_right (not_or.mpr ⟨hs1, not_or.mpr ⟨ht0, ht1⟩⟩)
    subst s
    have h1 : ¬4 - t ≤ 1 := by linarith [ht.2]
    have h2 : ¬4 - t ≤ 2 := by linarith [ht.2]
    have h3 : ¬4 - t ≤ 3 := by
      have := lt_of_le_of_ne ht.2 ht1
      linarith
    have he : 1 - (4 - t - 3) = t := by ring
    simp [bh6_boundaryCircuit, bh4_squareEdge, h1, h2, h3, he]


set_option backward.isDefEq.respectTransparency false in
private theorem bh6_squareLoop_diskPhase (q : bh5_diskPair.snd) :
    (bh6_squareLoop (bh6_diskPhase q)).val = fun _ ↦
      (2 * bh5_clamp (((q.val 0).re + 1) / 2) - 1 : ℝ) +
      (2 * bh5_clamp (((q.val 0).im + 1) / 2) - 1 : ℝ) * Complex.I := by
  let s := bh5_clamp (((q.val 0).re + 1) / 2)
  let t := bh5_clamp (((q.val 0).im + 1) / 2)
  have hs := bh5_clamp_bounds (((q.val 0).re + 1) / 2)
  have ht := bh5_clamp_bounds (((q.val 0).im + 1) / 2)
  have hb := bh6_clamped_on_boundary q
  change (bh6_squareLoop (bh6_perimeterPhase s t)).val = _
  rw [bh6_perimeterPhase_time]
  have hu := bh6_perimeterTime_bounds s t hs ht
  rw [bh6_squareLoop_apply _ ⟨by linarith [hu.1], by linarith [hu.2]⟩,
    show 4 * (bh6_perimeterTime s t / 4) = bh6_perimeterTime s t by ring,
    bh6_squarePerimeter_time s t hs ht hb]


set_option backward.isDefEq.respectTransparency false in
private theorem bh6_equation_boundary_factor
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : (Fin (dim X.left) → ℂ) → ℂ) (hf : Continuous f)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0) :
    TopPair.Hom.snd (bh5_equationPairMap X l m z f hf hnz) =
      TopCat.ofHom bh6_diskPhase ≫ TopCat.ofHom (bh6_boundaryLoop X f hf l m z hnz) := by
  ext q
  apply Subtype.ext
  funext i
  let s := bh5_clamp (((q.val 0).re + 1) / 2)
  let t := bh5_clamp (((q.val 0).im + 1) / 2)
  have hs := bh5_clamp_bounds (((q.val 0).re + 1) / 2)
  have ht := bh5_clamp_bounds (((q.val 0).im + 1) / 2)
  have hb := bh6_clamped_on_boundary q
  change f (bh5_squareMap (dim X.left) l.val m.val z q.val) =
    (bh6_boundaryLoop X f hf l m z hnz (bh6_perimeterPhase s t)).val i
  rw [bh6_perimeterPhase_time]
  have hu := bh6_perimeterTime_bounds s t hs ht
  rw [bh6_boundaryLoop_apply X f hf l m z hnz _
    ⟨by linarith [hu.1], by linarith [hu.2]⟩,
    show 4 * (bh6_perimeterTime s t / 4) = bh6_perimeterTime s t by ring,
    bh6_boundaryCircuit_time X l m z s t hs ht hb]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem bh6_clamp_interpolate_ne_zero (q : bh5_diskPair.snd) (u : unitInterval) :
    (1 - (u : ℝ)) • q.val + (u : ℝ) •
      (fun _ : Fin 1 ↦ (2 * bh5_clamp (((q.val 0).re + 1) / 2) - 1 : ℝ) +
        (2 * bh5_clamp (((q.val 0).im + 1) / 2) - 1 : ℝ) * Complex.I) ≠ 0 := by
  have hout : (q.val 0).re ≤ -1 ∨ 1 ≤ (q.val 0).re ∨
      (q.val 0).im ≤ -1 ∨ 1 ≤ (q.val 0).im := by
    by_contra! h
    apply q.property
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
    intro i
    fin_cases i
    calc
      ‖q.val 0‖ ≤ |(q.val 0).re| + |(q.val 0).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 2 := by
        have := abs_le.mpr ⟨h.1.le, h.2.1.le⟩
        have := abs_le.mpr ⟨h.2.2.1.le, h.2.2.2.le⟩
        linarith
  intro he
  have he0 := congrFun he 0
  change (1 - (u : ℝ)) • q.val 0 + (u : ℝ) •
    ((2 * bh5_clamp (((q.val 0).re + 1) / 2) - 1 : ℝ) +
      (2 * bh5_clamp (((q.val 0).im + 1) / 2) - 1 : ℝ) * Complex.I) = 0 at he0
  rcases hout with h | h | h | h
  · have hc : bh5_clamp (((q.val 0).re + 1) / 2) = 0 := by
      simp [bh5_clamp, min_eq_right (by linarith : ((q.val 0).re + 1) / 2 ≤ 1),
        max_eq_left (by linarith : ((q.val 0).re + 1) / 2 ≤ 0)]
    have hh := congrArg Complex.re he0
    norm_num [Pi.add_apply, Pi.smul_apply, Complex.smul_re, hc] at hh
    have hp := mul_nonneg (sub_nonneg.mpr u.property.2)
      (show 0 ≤ -1 - (q.val 0).re by linarith)
    nlinarith
  · have hc : bh5_clamp (((q.val 0).re + 1) / 2) = 1 := by
      simp [bh5_clamp, min_eq_left (by linarith : 1 ≤ ((q.val 0).re + 1) / 2)]
    have hh := congrArg Complex.re he0
    norm_num [Pi.add_apply, Pi.smul_apply, Complex.smul_re, hc] at hh
    have hp := mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr h)
    nlinarith
  · have hc : bh5_clamp (((q.val 0).im + 1) / 2) = 0 := by
      simp [bh5_clamp, min_eq_right (by linarith : ((q.val 0).im + 1) / 2 ≤ 1),
        max_eq_left (by linarith : ((q.val 0).im + 1) / 2 ≤ 0)]
    have hh := congrArg Complex.im he0
    norm_num [Pi.add_apply, Pi.smul_apply, Complex.smul_im, hc] at hh
    have hp := mul_nonneg (sub_nonneg.mpr u.property.2)
      (show 0 ≤ -1 - (q.val 0).im by linarith)
    nlinarith
  · have hc : bh5_clamp (((q.val 0).im + 1) / 2) = 1 := by
      simp [bh5_clamp, min_eq_left (by linarith : 1 ≤ ((q.val 0).im + 1) / 2)]
    have hh := congrArg Complex.im he0
    norm_num [Pi.add_apply, Pi.smul_apply, Complex.smul_im, hc] at hh
    have hp := mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr h)
    nlinarith


set_option backward.isDefEq.respectTransparency false in
private theorem bh6_square_boundary_factor_homology (c : Homology ℚ bh5_diskPair.snd 1) :
    homologyMap ℚ 1 (TopPair.Hom.snd
      (supportInclusionPairMap (TopCat.of (Fin 1 → ℂ))
        (Set.singleton_subset_iff.mpr
          (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2))))) c =
      homologyMap ℚ 1 (TopCat.ofHom bh6_squareLoop)
        (homologyMap ℚ 1 (TopCat.ofHom bh6_diskPhase) c) := by
  let f : bh5_diskPair.snd ⟶ (puncturedPair ℂ 1).snd := TopPair.Hom.snd
    (supportInclusionPairMap (TopCat.of (Fin 1 → ℂ))
      (Set.singleton_subset_iff.mpr
        (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2))))
  let g := bh6_squareLoop.comp bh6_diskPhase
  have hne (u : unitInterval) (q : bh5_diskPair.snd) :
      (1 - (u : ℝ)) • q.val + (u : ℝ) • (g q).val ≠ 0 := by
    change (1 - (u : ℝ)) • q.val + (u : ℝ) •
      (bh6_squareLoop (bh6_diskPhase q)).val ≠ 0
    rw [bh6_squareLoop_diskPhase]
    exact bh6_clamp_interpolate_ne_zero q u
  let H : TopCat.Homotopy f (TopCat.ofHom g) :=
    { toFun := fun x ↦ ⟨(1 - (x.1 : ℝ)) • x.2.val + (x.1 : ℝ) • (g x.2).val,
        hne x.1 x.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact ((continuous_const.sub continuous_fst.subtype_val).smul
          (continuous_subtype_val.comp continuous_snd)).add
          (continuous_fst.subtype_val.smul
            (continuous_subtype_val.comp (g.continuous.comp continuous_snd)))
      map_zero_left := by intro q; apply Subtype.ext; simp; rfl
      map_one_left := by intro q; apply Subtype.ext; simp }
  have h := ConcreteCategory.congr_hom
    (TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H (ModuleCat.of ℚ ℚ) 1) c
  change homologyMap ℚ 1 f c =
    homologyMap ℚ 1 (TopCat.ofHom bh6_diskPhase ≫ TopCat.ofHom bh6_squareLoop) c at h
  rw [homologyMap_comp, LinearMap.comp_apply] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The relative boundary of the pushed disk class is the winding multiple of the complex generator.
Source: Hatcher, section 2.2, naturality of the connecting map and degree of a circle map. -/
theorem bh6_relative_boundary_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : (Fin (dim X.left) → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0)
    (θ : ℝ → ℝ) (hθ : ContinuousOn θ (Icc 0 4))
    (he : ∀ t ∈ Icc (0 : ℝ) 4, f (bh6_boundaryCircuit X l m z t) =
      (‖f (bh6_boundaryCircuit X l m z t)‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I))
    (k : ℤ) (hk : (θ 4 - θ 0) / (2 * Real.pi) = (k : ℝ)) :
    relativeSingularBoundary (puncturedPair ℂ 1) 1
      (relativeHomologyMap ℚ 2
        (bh5_equationPairMap X l m z f
          (continuous_iff_continuousAt.mpr fun p ↦ (hf p (mem_univ p)).continuousAt) hnz)
        bh5_diskClass) =
      (k : ℚ) • relativeSingularBoundary (puncturedPair ℂ 1) 1
        (standardComplexLocalClass ℚ 1) := by
  let hf' : Continuous f := continuous_iff_continuousAt.mpr fun p ↦
    (hf p (mem_univ p)).continuousAt
  let c := relativeSingularBoundary bh5_diskPair 1 bh5_diskClass
  let d := homologyMap ℚ 1 (TopCat.ofHom bh6_diskPhase) c
  have hn := bh6_boundary_naturality (bh5_equationPairMap X l m z f hf' hnz) 1 bh5_diskClass
  change relativeSingularBoundary (puncturedPair ℂ 1) 1
    (relativeHomologyMap ℚ 2 (bh5_equationPairMap X l m z f hf' hnz) bh5_diskClass) = _
  calc
    _ = homologyMap ℚ 1 (TopPair.Hom.snd (bh5_equationPairMap X l m z f hf' hnz)) c := hn
    _ = homologyMap ℚ 1 (TopCat.ofHom (bh6_boundaryLoop X f hf' l m z hnz)) d := by
      rw [bh6_equation_boundary_factor, homologyMap_comp]
      rfl
    _ = (k : ℚ) • homologyMap ℚ 1 (TopCat.ofHom bh6_circlePuncture) d :=
      bh6_boundaryLoop_homology X f hf' l m z hnz θ hθ he k hk d
    _ = (k : ℚ) • homologyMap ℚ 1 (TopCat.ofHom bh6_squareLoop) d :=
      congrArg ((k : ℚ) • ·) (bh6_squareLoop_homology d).symm
    _ = (k : ℚ) • relativeSingularBoundary (puncturedPair ℂ 1) 1
        (standardComplexLocalClass ℚ 1) :=
      congrArg ((k : ℚ) • ·)
        ((bh6_square_boundary_factor_homology c).symm.trans bh6_disk_boundary_restrict)


/-- Relative degree is the change of a lifted boundary phase, with the complex orientation.
This is a topological statement and contains no boundary integral.
Source: Hatcher, section 2.2, degree and boundary homomorphism; section 3.3, orientation. -/
theorem bh6_relative_degree_phase_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : (Fin (dim X.left) → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0)
    (θ : ℝ → ℝ) (hθ : ContinuousOn θ (Icc 0 4))
    (he : ∀ t ∈ Icc (0 : ℝ) 4, f (bh6_boundaryCircuit X l m z t) =
      (‖f (bh6_boundaryCircuit X l m z t)‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)) :
    (relativeCohomologyEquivDualHomology ℚ bh5_diskPair 2
      (relativeCohomologyMap ℚ 2
        (bh5_equationPairMap X l m z f
          (continuous_iff_continuousAt.mpr fun p ↦ (hf p (mem_univ p)).continuousAt) hnz)
        (normalizedPointCoclass 1)) bh5_diskClass : ℂ) = (((θ 4 - θ 0) / (2 * Real.pi) : ℝ) : ℂ) := by
  let k := bh6_phaseDegree θ
  have hk := bh6_phase_integer_aux X f hf l m z hnz θ hθ he
  have hb := bh6_relative_boundary_aux X f hf l m z hnz θ hθ he k hk
  have hn := bh6_boundary_normalization_aux _ k hb
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap]
  rw [hn, hk]
  norm_cast

/-- Compose phase lifting, relative degree and logarithmic integration at the stage-five type.
Source: the boundary-phase, relative-degree and integration statements above. -/
theorem bh6_argument_principle
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : (Fin (dim X.left) → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0) :
    (relativeCohomologyEquivDualHomology ℚ bh5_diskPair 2
      (relativeCohomologyMap ℚ 2
        (bh5_equationPairMap X l m z f
          (continuous_iff_continuousAt.mpr fun p ↦ (hf p (mem_univ p)).continuousAt) hnz)
        (normalizedPointCoclass 1)) bh5_diskClass : ℂ) = bh4_boundaryWinding X l m z f := by
  obtain ⟨θ, hθ, he⟩ := bh6_boundary_phase_aux X f hf l m z hnz
  exact (bh6_relative_degree_phase_aux X f hf l m z hnz θ hθ he).trans
    (bh6_boundary_integral_phase_aux X f hf l m z hnz θ hθ he).symm

end HodgeLean.Adapters
