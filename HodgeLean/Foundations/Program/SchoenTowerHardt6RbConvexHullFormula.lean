import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBarycentricFormula
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismCoordinates

/-! Actual Boolean descriptions of convex hulls of arbitrary finite vertex families. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_convexHull_range_formula {n m : ℕ}
    (v : Fin m → EuclideanSpace ℝ (Fin n)) :
    ∃ f : s2v_t11b_Formula n, f.realize = convexHull ℝ (Set.range v) := by
  have hsum (w : Fin m → ℝ) (i : Fin n) :
      (∑ j, w j • v j) i = ∑ j, w j * v j i := by
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i) (∑ j, w j • v j) = _
    rw [map_sum]
    simp only [map_smul, PiLp.projₗ_apply, smul_eq_mul]
  obtain ⟨F, hF⟩ := s2v_hardt6rb_barycentric_relation_formula v
  obtain ⟨f, hf⟩ := s2v_hardt2_repeated_projection F
  refine ⟨f, ?_⟩
  ext x
  rw [hf, s2v_hardt6rb_convexHull_range_weights]
  simp only [hF, s2v_hardt2_insert_bound, s2v_hardt2_insert_free]
  constructor
  · rintro ⟨w, hpos, hw, hx⟩
    refine ⟨⟨w, hpos, hw⟩, ?_⟩
    ext i
    exact (hsum w i).trans (hx i).symm
  · rintro ⟨w, hw⟩
    refine ⟨w.val, w.property.1, w.property.2, ?_⟩
    intro i
    exact ((hsum w.val i).symm.trans (congrArg (fun z => z i) hw)).symm

end HodgeLean.Foundations.Program
