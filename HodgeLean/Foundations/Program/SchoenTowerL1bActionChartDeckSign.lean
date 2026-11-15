import HodgeLean.Foundations.Program.SchoenTowerL1bActionChartConjugacyDiagram
import HodgeLean.Foundations.Program.SchoenTowerL1bActionChartDiskClass
import HodgeLean.Foundations.Program.SchoenTowerL1bActionDiskAction

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The logarithmic deck coefficient of the actual centered coordinate
homeomorphism equals its coefficient on the exact integral chart classes. -/
theorem s2v_l1b_action_chart_deck_sign
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N] [T1Space N]
    (e : OpenPartialHomeomorph M (Fin 1 → ℂ))
    (d : OpenPartialHomeomorph N (Fin 1 → ℂ)) (E : M ≃ₜ N) (x : M)
    (hx : x ∈ e.source) (hy : E x ∈ d.source)
    (ε : ℤ) (horient : relativeHomologyMap ℤ 2
      (imagePointPairMap (TopCat.ofHom ⟨E, E.continuous⟩) E.injective x)
      (b6m_localClassOfChart ℤ 1 e x hx) = ε • b6m_localClassOfChart ℤ 1 d (E x) hy)
    (r : ℝ) (hr : 0 < r)
    (hb : Metric.ball (0 : ℂ) r ⊆ (s2v_l1b_action_vectorConjugacy e d E x).source)
    (hc : ContinuousOn (s2v_l1b_action_vectorConjugacy e d E x) (Metric.ball 0 r))
    (hn : ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 →
      s2v_l1b_action_vectorConjugacy e d E x z ≠ 0)
    (L : ℂ → ℂ) (hL : ContinuousOn L {z : ℂ | z.re < Real.log r})
    (he : ∀ z, z.re < Real.log r → Complex.exp (L z) =
      s2v_l1b_action_vectorConjugacy e d E x (Complex.exp z))
    (k : ℤ) (hk : ∀ z, z.re < Real.log r →
      L (z + 2 * Real.pi * Complex.I) = L z + (k : ℂ) * (2 * Real.pi * Complex.I)) :
    k = ε := by
  let H := s2v_l1b_action_vectorConjugacy e d E x
  have hs : ∀ z ∈ Metric.ball (0 : ℂ) r, b6m_surfaceCoordinateEquiv z + e x ∈ e.target :=
    fun z hz => (s2v_l1b_action_vectorConjugacy_domains e d E x z (hb hz)).1
  have ht : ∀ z ∈ Metric.ball (0 : ℂ) r, b6m_surfaceCoordinateEquiv (H z) + d (E x) ∈ d.target :=
    fun z hz => (s2v_l1b_action_vectorConjugacy_domains e d E x z (hb hz)).2
  obtain ⟨a, ha⟩ := (b6m_point_excision_bijective ℤ (Metric.ball (0 : ℂ) r) 0
    Metric.isOpen_ball (Metric.mem_ball_self hr) 2).2 (s2v_l1b_action_scalarLocalClass ℤ)
  have hid : s2v_l1b_action_disk_pair_map (fun z => z) r continuous_id.continuousOn
      (fun _ _ h => h) = neighborhoodPointComplementPairMap (Metric.ball (0 : ℂ) r) 0 := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext z <;> rfl
  have haid : relativeHomologyMap ℤ 2
      (s2v_l1b_action_disk_pair_map (fun z => z) r continuous_id.continuousOn
        (fun _ _ h => h)) a = (1 : ℤ) • s2v_l1b_action_scalarLocalClass ℤ := by
    simpa only [hid, one_smul] using ha
  have hsrc := s2v_l1b_action_chart_disk_class ℤ e x hx (fun z => z) r
    continuous_id.continuousOn (fun _ _ h => h) hs a 1 haid
  rw [one_smul] at hsrc
  have hact := s2v_l1b_action_disk_relative_action H L r hr hc hn hL he k hk a
  rw [ha] at hact
  have htar := s2v_l1b_action_chart_disk_class ℤ d (E x) hy H r hc hn ht a k hact
  have hdiag := congrArg (fun F => relativeHomologyMap ℤ 2 F a)
    (s2v_l1b_action_chart_conjugacy_pair_diagram e d E x r hb hc hn hs ht)
  rw [htar, relativeHomologyMap_comp, LinearMap.comp_apply, hsrc] at hdiag
  have hcoeff : k • b6m_localClassOfChart ℤ 1 d (E x) hy =
      ε • b6m_localClassOfChart ℤ 1 d (E x) hy := hdiag.trans horient
  have hinj : Function.Injective (fun n : ℤ => n • b6m_localClassOfChart ℤ 1 d (E x) hy) := by
    convert (b6m_localClassOfChart_one_smul_bijective ℤ d (E x) hy).1 using 1
    funext n
    exact (Int.cast_smul_eq_zsmul ℤ n _).symm
  exact hinj hcoeff

end HodgeLean.Foundations.Program
