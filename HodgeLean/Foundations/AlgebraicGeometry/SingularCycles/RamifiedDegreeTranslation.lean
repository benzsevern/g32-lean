import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeCount

/-! # Computing isolated degree with a small regular translation

Compact annuli trap the straight translation homotopy inside the chart
domain. A finite regular translated fibre determines its homological degree.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Adapters
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem isolated_degree_on_ball_of_regular_translation
    (d : ℕ) (O : Set (Fin d → ℂ)) (f : (Fin d → ℂ) → (Fin d → ℂ))
    (hf : ContinuousOn f O) (r : ℝ) (hr : 0 < r)
    (hO : Metric.closedBall (0 : Fin d → ℂ) r ⊆ O)
    (hiso : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, f x = 0 → x = 0) :
    let U := Metric.ball (0 : Fin d → ℂ) r
    let F : C(U, Fin d → ℂ) := ⟨fun u => f u.1,
      (hf.mono (Metric.ball_subset_closedBall.trans hO)).domRestrict⟩
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : Fin d → ℂ, ‖a‖ < ε →
      ∀ (S : Finset (Fin d → ℂ)) (hSU : (S : Set (Fin d → ℂ)) ⊆ U)
        (hS : ∀ x ∈ U, f x = a ↔ x ∈ S)
        (A : S → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ x, (A x).det ≠ 0)
        (hd : ∀ x : S, HasFDerivAt (fun z => f (z + x.1) - a)
          ((A x).mulVecLin.toContinuousLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0)
        (z : RelativeHomology ℚ (neighborhoodPointComplementPair U 0) (2 * d)),
        relativeHomologyMap ℚ (2 * d) (neighborhoodPointComplementPairMap U 0) z =
          standardComplexLocalClass ℚ d →
        relativeHomologyMap ℚ (2 * d)
          (a3b4_supportPairMap (TopCat.ofHom F) {u : U | u.1 = 0}
            ({0} : Set (Fin d → ℂ))
            (fun u hu => hiso u.1 (Metric.ball_subset_closedBall u.2) hu)) z =
          (S.card : ℚ) • standardComplexLocalClass ℚ d := by
  classical
  dsimp only
  let E := Fin d → ℂ
  let U := Metric.ball (0 : E) r
  have hfU : ContinuousOn f U := hf.mono (Metric.ball_subset_closedBall.trans hO)
  let F : C(U, E) := ⟨fun u => f u.1, hfU.domRestrict⟩
  let K := Metric.closedBall (0 : E) (r / 2)
  have hKU : K ⊆ U := Metric.closedBall_subset_ball (half_lt_self hr)
  obtain ⟨ε, hε, htrap⟩ := isolated_zero_translation_trapping_on_open O f hf r (r / 2)
    (half_pos hr) hO hiso
  refine ⟨ε, hε, ?_⟩
  intro a ha S hSU hS A hA hd z hz
  let g : E → E := fun v => f v - a
  have hg : ContinuousOn g U := hfU.sub continuousOn_const
  let H : ContinuousMap.Homotopy F ⟨fun u : U => g u.1, hg.domRestrict⟩ :=
    { toFun := fun tu => f tu.2.1 - (tu.1 : ℝ) • a
      continuous_toFun := F.continuous.comp continuous_snd |>.sub
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const)
      map_zero_left := fun u => by
        change f u.1 - (0 : ℝ) • a = f u.1
        rw [zero_smul, sub_zero]
      map_one_left := fun u => by
        change f u.1 - (1 : ℝ) • a = f u.1 - a
        rw [one_smul] }
  apply isolated_degree_on_open_of_regular_deformation d U Metric.isOpen_ball
    (Metric.mem_ball_self hr) F g hg H K (isCompact_closedBall _ _) hKU
    (Metric.mem_closedBall_self (le_of_lt (half_pos hr)))
    (fun u hu => hiso u.1 (Metric.ball_subset_closedBall u.2) hu)
    (fun t u hu => Metric.ball_subset_closedBall
      (htrap a ha t u.1 (Metric.ball_subset_closedBall u.2) hu))
    S hSU (fun x hx => (sub_eq_zero.trans (hS x hx))) A hA hd z hz

end AlgebraicGeometry.SingularCycles
