import HodgeLean.Foundations.Program.RoucheRootCountBoxes

/-! # Proof obligations for the Rouché and Pellet root counts and the twelve boxes -/

noncomputable section
namespace HodgeLean.Foundations.Program

open Polynomial Complex

theorem rou_rouche_aux (p q : ℂ[X]) (c : ℂ) (r : ℝ)
    (h : ∀ z ∈ Metric.sphere c r, ‖(p - q).eval z‖ < ‖q.eval z‖) :
    rou_discCount p c r = rou_discCount q c r :=
  rou_rouche_poly p q c r h

theorem rou_pellet_one_aux (p : ℂ[X]) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (h : rou_pelletTail p c r 1 < ‖(taylor c p).coeff 1‖ * r) :
    rou_discCount p c r = 1 :=
  rou_pellet_one_poly p c r hr h

theorem rou_pellet_zero_aux (p : ℂ[X]) (c : ℂ) (r : ℝ)
    (h : rou_pelletTail p c r 0 < ‖(taylor c p).coeff 0‖) :
    rou_discCount p c r = 0 :=
  rou_pellet_zero_poly p c r h

theorem rou_b65b_pellet_rational_aux :
    ∀ i : Fin 12,
      rou_ratTail (rou_sextic (b65b_boxFibre i)) (b65b_boxCentre i).1 (b65b_boxCentre i).2
          (1/10000) 1 ^ 2 <
        rou_normSq (rou_shift (rou_sextic (b65b_boxFibre i))
          (b65b_boxCentre i).1 (b65b_boxCentre i).2 1) * (1/10000) ^ 2 ∧
      rou_ratTail (rou_sextic (b65b_boxFibre i)) (b65b_boxCentre i).1 (b65b_boxCentre i).2
          (3/20000) 1 ^ 2 <
        rou_normSq (rou_shift (rou_sextic (b65b_boxFibre i))
          (b65b_boxCentre i).1 (b65b_boxCentre i).2 1) * (3/20000) ^ 2 ∧
      rou_ratTail (rou_sextic (-2 - b65b_boxFibre i)) (b65b_boxCentre i).1
          (b65b_boxCentre i).2 (3/20000) 0 ^ 2 <
        rou_normSq (rou_shift (rou_sextic (-2 - b65b_boxFibre i))
          (b65b_boxCentre i).1 (b65b_boxCentre i).2 0) := by
  decide +kernel

theorem rou_b65b_isolating_boxes_aux :
    ∀ i : Fin 12, ∃! z : ℂ,
      |z.re - ((b65b_boxCentre i).1 : ℝ)| < (1/10000 : ℝ) ∧
      |z.im - ((b65b_boxCentre i).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre i) z = 0 := by
  intro i
  obtain ⟨h1, h2, -⟩ := rou_b65b_pellet_rational_aux i
  have hc1 := rou_sextic_pellet_one _ _ _ (1/10000) (by norm_num) h1
  have hc2 := rou_sextic_pellet_one _ _ _ (3/20000) (by norm_num) h2
  have hu := rou_square_unique _ _ (1/10000)
    (by norm_num) (by simpa using hc1) (by convert hc2 using 2; norm_num)
  have hε : (((b65b_boxFibre i : ℚ)) : ℂ) = (b65b_boxFibre i : ℂ) := Rat.cast_intCast _
  simpa [rou_sexticPoly_eval, hε] using hu

end HodgeLean.Foundations.Program
