import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeTranslation
import HodgeLean.Adapters.NormalConeB4aGysinRegularParameters
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartPointClassNormalization

/-! # Isolated degree from conserved local fibre lengths

A small regular value is selected by the complex critical-value theorem.
Every fibre point then has length one, so conservation gives the count
that the open-domain homology calculation detects.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Adapters
open scoped BigOperators
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem isolated_degree_of_length_conservation
    (d : ℕ) (O : Set (Fin d → ℂ)) (f : (Fin d → ℂ) → (Fin d → ℂ))
    (hf : AnalyticOnNhd ℂ f O) (r : ℝ) (hr : 0 < r)
    (hO : Metric.closedBall (0 : Fin d → ℂ) r ⊆ O)
    (hiso : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, f x = 0 → x = 0)
    (length : (Fin d → ℂ) → (Fin d → ℂ) → ℕ∞) (m : ℕ)
    (hcons : ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin d → ℂ, ‖a‖ < δ →
      ∃ S : Finset (Fin d → ℂ), (S : Set (Fin d → ℂ)) ⊆ Metric.ball 0 r ∧
        (∀ x ∈ Metric.ball (0 : Fin d → ℂ) r, f x = a ↔ x ∈ S) ∧
        ∑ x ∈ S, length a x = (m : ℕ∞))
    (hone : ∀ a x, x ∈ Metric.ball (0 : Fin d → ℂ) r → f x = a →
      IsUnit (fderiv ℂ f x) → length a x = 1)
    (z : RelativeHomology ℚ (neighborhoodPointComplementPair
      (Metric.ball (0 : Fin d → ℂ) r) 0) (2 * d))
    (hz : relativeHomologyMap ℚ (2 * d)
      (neighborhoodPointComplementPairMap (Metric.ball (0 : Fin d → ℂ) r) 0) z =
      standardComplexLocalClass ℚ d) :
    relativeHomologyMap ℚ (2 * d)
      (a3b4_supportPairMap
        (TopCat.ofHom ⟨fun u : Metric.ball (0 : Fin d → ℂ) r => f u.1,
          (hf.continuousOn.mono (Metric.ball_subset_closedBall.trans hO)).domRestrict⟩)
        {u : Metric.ball (0 : Fin d → ℂ) r | u.1 = 0} ({0} : Set (Fin d → ℂ))
        (fun u hu => hiso u.1 (Metric.ball_subset_closedBall u.2) hu)) z =
      (m : ℚ) • standardComplexLocalClass ℚ d := by
  classical
  let E := Fin d → ℂ
  let U := Metric.ball (0 : E) r
  have hUO : U ⊆ O := Metric.ball_subset_closedBall.trans hO
  obtain ⟨ε, hε, hdegree⟩ := isolated_degree_on_ball_of_regular_translation d O f
    hf.continuousOn r hr hO hiso
  obtain ⟨δ, hδ, hsum⟩ := hcons
  have hdiff : DifferentiableOn ℂ f U :=
    fun x hx => (hf x (hUO hx)).differentiableAt.differentiableWithinAt
  obtain ⟨a, ha, _, hreg⟩ := a3b4a_gysin_small_common_regular_parameter
    (ι := Unit) (fun _ => U) (fun _ => Metric.isOpen_ball) (fun _ => f)
    (fun _ => hdiff) ∅ (by simp) (min ε δ) (lt_min hε hδ)
  have haε : ‖a‖ < ε := lt_of_lt_of_le ha (min_le_left _ _)
  have haδ : ‖a‖ < δ := lt_of_lt_of_le ha (min_le_right _ _)
  obtain ⟨S, hSU, hS, hlen⟩ := hsum a haδ
  have hunit (x : S) : IsUnit (fderiv ℂ f x.1) :=
    hreg () x.1 (hSU x.2) ((hS x.1 (hSU x.2)).mpr x.2)
  let A : S → Matrix (Fin d) (Fin d) ℂ :=
    fun x => complexMatrixOfContinuousLinearMap d (fderiv ℂ f x.1)
  have hA (x : S) : (A x).det ≠ 0 :=
    complexMatrixOfContinuousLinearMap_det_ne_zero d (fderiv ℂ f x.1)
      (ContinuousLinearMap.isUnit_iff_bijective.mp (hunit x)).1
  have hd (x : S) : HasFDerivAt (fun v => f (v + x.1) - a)
      ((A x).mulVecLin.toContinuousLinearMap : E →L[ℂ] E) 0 := by
    have hdf : HasFDerivAt f (fderiv ℂ f x.1) x.1 :=
      (hf x.1 (hUO (hSU x.2))).differentiableAt.hasFDerivAt
    have hdf₀ : HasFDerivAt f (fderiv ℂ f x.1) ((0 : E) + x.1) := by
      simpa only [zero_add] using hdf
    have h := (hdf₀.comp 0 ((hasFDerivAt_id (0 : E)).add_const x.1)).sub_const a
    have hAL : ((A x).mulVecLin.toContinuousLinearMap : E →L[ℂ] E) = fderiv ℂ f x.1 :=
      ContinuousLinearMap.ext (complexMatrixOfContinuousLinearMap_mulVec d (fderiv ℂ f x.1))
    rw [hAL]
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using h
  have hones : ∑ x ∈ S, length a x = (S.card : ℕ∞) := by
    calc
      _ = ∑ _x ∈ S, (1 : ℕ∞) := Finset.sum_congr rfl (fun x hx =>
        hone a x (hSU hx) ((hS x (hSU hx)).mpr hx) (hunit ⟨x, hx⟩))
      _ = _ := by simp
  have hcard : S.card = m := by exact_mod_cast (hones.symm.trans hlen)
  have hdeg := hdegree a haε S hSU hS A hA hd z hz
  simpa only [hcard] using hdeg

end AlgebraicGeometry.SingularCycles
