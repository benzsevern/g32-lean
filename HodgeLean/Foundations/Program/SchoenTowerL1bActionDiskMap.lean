import HodgeLean.Foundations.Program.SchoenTowerL1bActionBallDegree

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A continuous disk map avoiding zero off the puncture gives a map of
point-complement pairs. -/
def s2v_l1b_action_disk_pair_map (h : ℂ → ℂ) (r : ℝ)
    (hc : ContinuousOn h (Metric.ball 0 r))
    (hn : ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → h z ≠ 0) :
    neighborhoodPointComplementPair (Metric.ball (0 : ℂ) r) 0 ⟶
      pointComplementPair (0 : ℂ) :=
  TopPair.ofSubsetHom (TopCat.ofHom
    ⟨fun z : Metric.ball (0 : ℂ) r => h z, continuousOn_iff_continuous_domRestrict.mp hc⟩)
      (fun z hz => hn z z.property hz)

/-- The deck coefficient of a logarithmic lift on a punctured disk equals
the integral relative local degree computed through disk excision. -/
theorem s2v_l1b_action_disk_deck_degree
    (h L : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hc : ContinuousOn h (Metric.ball 0 r))
    (hn : ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → h z ≠ 0)
    (hL : ContinuousOn L {z : ℂ | z.re < Real.log r})
    (he : ∀ z, z.re < Real.log r → Complex.exp (L z) = h (Complex.exp z))
    (k : ℤ) (hk : ∀ z, z.re < Real.log r →
      L (z + 2 * Real.pi * Complex.I) = L z + (k : ℂ) * (2 * Real.pi * Complex.I))
    (a : RelativeHomology ℤ (neighborhoodPointComplementPair (Metric.ball (0 : ℂ) r) 0) 2)
    (ha : relativeHomologyMap ℤ 2 (neighborhoodPointComplementPairMap (Metric.ball (0 : ℂ) r) 0) a =
      b6m_surfaceLocalClass ℤ (0 : ℂ))
    (ε : ℤ) (hf : relativeHomologyMap ℤ 2 (s2v_l1b_action_disk_pair_map h r hc hn) a =
      ε • b6m_surfaceLocalClass ℤ (0 : ℂ)) :
    k = ε := by
  let ρ := r / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ < r := by dsimp [ρ]; linarith
  let c : ℂ := (Real.log ρ : ℂ)
  let K : ℝ → ℂ := fun s => L (c + (s : ℂ) * (2 * Real.pi * Complex.I))
  have hmem (s : ℝ) : (c + (s : ℂ) * (2 * Real.pi * Complex.I)).re < Real.log r := by
    have hb : Real.log ρ < Real.log r := Real.log_lt_log hρ hρr
    simpa [c] using hb
  have hK : Continuous K := hL.comp_continuous
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) hmem
  have hp (s : ℝ) : Complex.exp (K s) =
      ((s2v_l1b_action_disk_pair_map h r hc hn).left
        (s2v_l1b_action_ball_loop r ρ hρ hρr (s : UnitAddCircle))).val := by
    change Complex.exp (L (c + (s : ℂ) * (2 * Real.pi * Complex.I))) =
      h ((s2v_l1b_action_windingCircleMap c 1 (s : UnitAddCircle)).val)
    rw [he _ (hmem s), s2v_l1b_action_windingCircleMap_coe]
    simp only [Int.cast_one, one_mul]
  have hd (s : ℝ) : K (s + 1) = K s + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    change L (c + ((s + 1 : ℝ) : ℂ) * _) = _
    rw [Complex.ofReal_add, Complex.ofReal_one, add_mul, one_mul, ← add_assoc]
    exact hk _ (hmem s)
  exact s2v_l1b_action_neighbourhood_deck_degree
    (neighborhoodPointComplementPairMap (Metric.ball (0 : ℂ) r) 0)
    (s2v_l1b_action_disk_pair_map h r hc hn)
    (s2v_l1b_action_ball_homology_bijective r hr).1
    (s2v_l1b_action_ball_loop r ρ hρ hρr)
    (s2v_l1b_action_ball_loop_homology r ρ hρ hρr)
    K hK hp k hd a ha ε hf

end HodgeLean.Foundations.Program
