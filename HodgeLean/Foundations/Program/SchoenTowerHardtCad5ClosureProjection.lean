import HodgeLean.Foundations.Program.SchoenTowerHardtCad5GraphImages
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Interior
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5PolynomialLimits

/-! Polynomial constraints on coordinate projections of ambient limit sets. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_projection_polynomial_limit {n d : ℕ}
    (S : s2v_t11b_Formula n) (P : s2v_hardt_cad5_Partition S.realize)
    (hd : P.dimension < (d : ℤ)) (r : Fin d → Fin n) :
    ∃ p : MvPolynomial (Fin d) ℝ, p ≠ 0 ∧
      ∀ x ∈ closure S.realize, MvPolynomial.eval (fun i => x (r i)) p = 0 := by
  obtain ⟨F, Q, hImage, hQ⟩ := s2v_hardt_cad5_coordinate_image_partition S P r
  have hi : interior F.realize = ∅ :=
    s2v_hardt_cad5_interior_empty_of_dimension_lt Q (hQ.trans_lt hd)
  obtain ⟨p, hp, hpoly⟩ := s2v_hardt_cad5_thin_boolean_polynomial_limit F hi
  have hs : S.realize ⊆ {x | MvPolynomial.eval (fun i => x (r i)) p = 0} := by
    intro x hx
    exact hpoly (subset_closure ((hImage _).mpr ⟨⟨x, hx⟩, rfl⟩))
  have hc : IsClosed {x : EuclideanSpace ℝ (Fin n) |
      MvPolynomial.eval (fun i => x (r i)) p = 0} :=
    isClosed_eq (p.continuous_eval.comp (continuous_pi (fun i =>
      (continuous_apply (r i)).comp (PiLp.continuous_ofLp 2 _)))) continuous_const
  exact ⟨p, hp, fun x hx => closure_minimal hs hc hx⟩

end HodgeLean.Foundations.Program
