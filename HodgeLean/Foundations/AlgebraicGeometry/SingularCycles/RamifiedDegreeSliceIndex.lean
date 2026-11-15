import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeConservation
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeChartConservation
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeSliceRegular
import HodgeLean.Adapters.NormalConeB4aGysinBridgeProofs

/-! # Local degree for an isolated regular-sequence slice

The exact source-slice conservation theorem and the algebraic Jacobian
comparison supply the two inputs of the local homological index formula.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular HodgeLean.Adapters Point
open scoped BigOperators
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem regular_sequence_slice_local_index
    {Z K : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [IsNoetherian Z]
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (i : K ⟶ Z) (hi : IsClosedImmersion i) (d : ℕ)
    [SmoothOfRelativeDimension d (Over.mk (i ≫ q)).hom]
    [LocallyOfFiniteType (Over.mk (i ≫ q)).hom]
    (U : Z.Opens) (hU : IsAffineOpen U) (g : Fin d → Γ(Z, U))
    (w j : ComplexPoint (Over.mk (i ≫ q))) (hwU : i w.underlying ∈ U)
    (hg0 : ∀ k, evaluate (X := Over.mk q) U (g k) (Point.map (Over.homMk i rfl) w) = 0)
    (hreg : RingTheory.Sequence.IsRegular (K.presheaf.stalk w.underlying)
      (a3b4a_gysin_sliceSequence q i U g 0 w.underlying hwU))
    (m : ℕ) (hm : a3b4a_gysin_sliceLength q i U g 0 w = m)
    (e : OpenPartialHomeomorph (ComplexPoint (Over.mk (i ≫ q))) (Fin d → ℂ))
    (hw : w ∈ e.source) (he0 : e w = 0) (c : Fin d → ℂ)
    (hinv : ∀ v, e.symm v = (chartAt (Fin d → ℂ) j).symm (v + c))
    (htarget : ∀ v ∈ e.target, v + c ∈ (chartAt (Fin d → ℂ) j).target)
    (hsource : ∀ v ∈ e.target, i (e.symm v).underlying ∈ U)
    (hiso : ∀ z ∈ e.source,
      (fun k => evaluate (X := Over.mk q) U (g k) (Point.map (Over.homMk i rfl) z)) = 0 → z = w) :
    let parameter := fun z : ComplexPoint (Over.mk (i ≫ q)) => fun k =>
      evaluate (X := Over.mk q) U (g k) (Point.map (Over.homMk i rfl) z)
    let F := fun v => parameter (e.symm v)
    ∃ (r : ℝ) (_hr : 0 < r) (_hball : Metric.closedBall (0 : Fin d → ℂ) r ⊆ e.target)
      (hc : ContinuousOn F (Metric.ball 0 r))
      (hzero : ∀ v ∈ Metric.ball (0 : Fin d → ℂ) r, F v = 0 → v = 0),
      ∀ z : RelativeHomology ℚ (neighborhoodPointComplementPair (Metric.ball (0 : Fin d → ℂ) r) 0) (2 * d),
        relativeHomologyMap ℚ (2 * d) (neighborhoodPointComplementPairMap (Metric.ball 0 r) 0) z =
          standardComplexLocalClass ℚ d →
        relativeHomologyMap ℚ (2 * d)
          (a3b4_supportPairMap (TopCat.ofHom ⟨fun v : Metric.ball (0 : Fin d → ℂ) r => F v.1,
            hc.domRestrict⟩) {v : Metric.ball (0 : Fin d → ℂ) r | v.1 = 0} {0}
            (fun v hv => hzero v.1 v.2 hv)) z = (m : ℚ) • standardComplexLocalClass ℚ d := by
  classical
  dsimp only
  let X := Over.mk (i ≫ q)
  let f : X ⟶ Over.mk q := Over.homMk i rfl
  let P := fun z : ComplexPoint X => fun k => evaluate (X := Over.mk q) U (g k) (Point.map f z)
  let F := fun v => P (e.symm v)
  let L := fun a z => a3b4a_gysin_sliceLength q i U g a z
  obtain ⟨N₀, hN₀, hwN₀, _, hcons⟩ :=
    a3b4a_gysin_slice_exact_model_aux i hi U hU g w hwU hg0 hreg m hm
  have hfamily : ∃ N₀ : Set (ComplexPoint X), IsOpen N₀ ∧ w ∈ N₀ ∧
      ∀ N : Set (ComplexPoint X), IsOpen N → w ∈ N → N ⊆ N₀ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin d → ℂ, ‖a‖ < δ →
          ∃ T : Finset (ComplexPoint X), (∀ z, z ∈ T ↔ z ∈ N ∧ P z = a) ∧
            ∑ z ∈ T, L a z = (m : ℕ∞) := by
    refine ⟨N₀, hN₀, hwN₀, ?_⟩
    intro N hN hwN hNN₀
    obtain ⟨δ, hδ, hδc⟩ := hcons N hN hwN hNN₀
    refine ⟨δ, hδ, ?_⟩
    intro a ha
    obtain ⟨T, hT, hsum⟩ := hδc a ha
    refine ⟨T, ?_, hsum⟩
    intro z
    rw [hT z]
    exact and_congr_right (fun _ => ⟨fun h => funext h, fun h k => congrFun h k⟩)
  obtain ⟨r, hr, hball, δ, hδ, hδc⟩ :=
    chart_fibre_length_conservation d P L w m e hw he0 hfamily
  have hF : AnalyticOnNhd ℂ F e.target := by
    intro v hv
    apply AnalyticAt.pi
    intro k
    have ha := ComplexPoint.analyticAt_localChart_symm_evaluate X d j (htarget v hv)
      (i ⁻¹ᵁ U) (i.app U (g k)) (by
        change i ((chartAt (Fin d → ℂ) j).symm (v + c)).underlying ∈ U
        rw [← hinv v]
        exact hsource v hv)
    have ht : AnalyticAt ℂ (fun t : Fin d → ℂ => t + c) v := analyticAt_id.add analyticAt_const
    have hh := ha.comp (f := fun t : Fin d → ℂ => t + c) (x := v) ht
    apply hh.congr
    filter_upwards [] with t
    change evaluate (i ⁻¹ᵁ U) (i.app U (g k))
      ((chartAt (Fin d → ℂ) j).symm (t + c)) =
        evaluate (X := Over.mk q) U (g k) (Point.map f (e.symm t))
    rw [← hinv t]
    exact (Point.evaluate_map f U (g k) _).symm
  have hzero : ∀ v ∈ e.target, F v = 0 → v = 0 := by
    intro v hv hz
    have hs := hiso (e.symm v) (e.map_target hv) hz
    calc
      v = e (e.symm v) := (e.right_inv hv).symm
      _ = e w := congrArg e hs
      _ = 0 := he0
  have hone : ∀ a v, v ∈ Metric.ball (0 : Fin d → ℂ) r → F v = a →
      IsUnit (fderiv ℂ F v) → L a (e.symm v) = 1 := by
    intro a v hv hvalue hunit
    have hvt : v ∈ e.target := hball (Metric.ball_subset_closedBall hv)
    let χ := chartAt (Fin d → ℂ) j
    have hwχ : e.symm v ∈ χ.source := by rw [hinv v]; exact χ.map_target (htarget v hvt)
    apply sliceLength_one_of_regular_parameter_value q i d (e.symm v) j hwχ U g a (hsource v hvt)
    · intro k
      exact congrFun hvalue k
    · have hχ : χ (e.symm v) = v + c := by rw [hinv v, χ.right_inv (htarget v hvt)]
      change IsUnit (fderiv ℂ (fun t => P (χ.symm t)) (χ (e.symm v)))
      rw [hχ]
      have hform : F = fun t => P (χ.symm (t + c)) := funext fun t => congrArg P (hinv t)
      rw [hform] at hunit
      have hder := fderiv_comp_add_right (𝕜 := ℂ) (f := fun t => P (χ.symm t)) (x := v) c
      rw [hder] at hunit
      exact hunit
  refine ⟨r, hr, hball, hF.continuousOn.mono (Metric.ball_subset_closedBall.trans hball), ?_, ?_⟩
  · intro v hv
    exact hzero v (hball (Metric.ball_subset_closedBall hv))
  · intro z hz
    exact isolated_degree_of_length_conservation d e.target F hF r hr hball
      (fun v hv => hzero v (hball hv)) (fun a v => L a (e.symm v)) m
      ⟨δ, hδ, hδc⟩ hone z hz

end AlgebraicGeometry.SingularCycles
