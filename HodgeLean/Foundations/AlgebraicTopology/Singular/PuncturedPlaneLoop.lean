import HodgeLean.Foundations.AlgebraicTopology.Singular.PuncturedPlaneChains
import HodgeLean.Foundations.Program.SchoenTowerL1bActionCircleHomotopy

/-! Logarithmic lifts and integral loop coefficients.
Source: Hatcher, Algebraic Topology (2002), §§2.1–2.2.
HC no distance; AV milestone no distance. -/
noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
open HodgeLean.Foundations.Program
namespace AlgebraicTopology.Singular.PuncturedPlane
set_option maxHeartbeats 200000

private theorem windingCircle_coe (c : ℂ) (k : ℤ) (s : ℝ) :
    (windingCircle c k (s : UnitAddCircle)).val =
      Complex.exp (c + (s : ℂ) * ((k : ℂ) * (2 * Real.pi * Complex.I))) := rfl

theorem circle_homology_normal_form
    (p : C(UnitAddCircle, {z : ℂ // z ≠ 0}))
    (L : ℝ → ℂ) (hL : Continuous L)
    (hp : ∀ s : ℝ, Complex.exp (L s) = (p (s : UnitAddCircle)).val)
    (k : ℤ)
    (hdL : ∀ s, L (s + 1) = L s + (k : ℂ) * (2 * Real.pi * Complex.I))
    (n : ℕ) :
    AlgebraicTopology.Singular.homologyMap ℤ n (TopCat.ofHom p) =
      AlgebraicTopology.Singular.homologyMap ℤ n
        (TopCat.ofHom (windingCircle 0 k)) := by
  apply s2v_l1b_action_circle_log_homology p (windingCircle 0 k)
    L (fun s : ℝ => (s : ℂ) * ((k : ℂ) * (2 * Real.pi * Complex.I))) hL
    (Complex.continuous_ofReal.mul continuous_const) hp _ k hdL _ n
  · intro s
    rw [windingCircle_coe, zero_add]
  · intro s
    rw [Complex.ofReal_add, Complex.ofReal_one, add_mul, one_mul]

theorem loopClass_of_lift
    (p : C(UnitAddCircle, {z : ℂ // z ≠ 0}))
    (L : ℝ → ℂ) (hL : Continuous L)
    (hp : ∀ s : ℝ, Complex.exp (L s) = (p (s : UnitAddCircle)).val)
    (k : ℤ) (hk : ∀ s, L (s + 1) = L s + (k : ℂ) * (2 * Real.pi * Complex.I)) :
    ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
      (loopCycle ℤ p) =
    k • ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
      (loopCycle ℤ (windingCircle 0 1)) := by
  have hm := circle_homology_normal_form p L hL hp k hk 1
  have hmap := b6m_homologyMap_loopCycle p (ContinuousMap.id UnitAddCircle)
  have hnorm := b6m_homologyMap_loopCycle (windingCircle 0 k)
    (ContinuousMap.id UnitAddCircle)
  rw [hm] at hmap
  have he := hmap.symm.trans hnorm
  simp only [ContinuousMap.comp_id] at he
  exact he.trans (winding_loop_class k)

end AlgebraicTopology.Singular.PuncturedPlane
