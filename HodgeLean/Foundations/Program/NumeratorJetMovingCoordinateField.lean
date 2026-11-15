import HodgeLean.Foundations.Program.NumeratorJetTensorMoments
import HodgeLean.Foundations.Program.NumeratorJetFixedWeights

/-! # Finite rational moving-field contractions in sextic coordinates -/

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Rational fixed-source terms of the moving field in reduced target coordinates. -/
def b65e_movingFixedContractionCoordsQ (n : Fin 7) (e : Fin 2)
    (c : Fin 6) (i j : Fin 4) : ℚ :=
  ∑ k : Fin 4, ∑ a ∈ Finset.range (n.val + 1),
    ∑ t : Fin 4, ∑ b ∈ Finset.range (n.val - a + 1),
      (b65e_fixedJet (Fin.ofNat 8 b) k i t *
        b65e_coordinateMulQ e (b65e_fixedWeightCoeffQ (Fin.ofNat 7 a) e k)
          (fun s ↦ b65e_movingJet (Fin.ofNat 8 (n.val - a - b)) e s t j) c -
      b65e_coordinateMulQ e (b65e_fixedWeightCoeffQ (Fin.ofNat 7 a) e k)
          (fun s ↦ b65e_movingJet (Fin.ofNat 8 b) e s i t) c *
        b65e_fixedJet (Fin.ofNat 8 (n.val - a - b)) k t j)

/-- Rational moving-source terms of the moving field in reduced target coordinates. -/
def b65e_movingMovingContractionCoordsQ (n : Fin 7) (e : Fin 2)
    (c : Fin 6) (i j : Fin 4) : ℚ :=
  ∑ d : Fin 2, ∑ a ∈ Finset.range (n.val + 1),
    ∑ t : Fin 4, ∑ b ∈ Finset.range (n.val - a + 1),
      (b65e_coordinateMulQ e
        (b65e_tensorWeightedMovingQ (Fin.ofNat 7 a) (Fin.ofNat 8 b) e d i t)
        (fun s ↦ b65e_movingJet (Fin.ofNat 8 (n.val - a - b)) e s t j) c -
      b65e_coordinateMulQ e
        (fun s ↦ b65e_movingJet (Fin.ofNat 8 b) e s i t)
        (b65e_tensorWeightedMovingQ (Fin.ofNat 7 a)
          (Fin.ofNat 8 (n.val - a - b)) e d t j) c)

/-- Rational moving-field coefficient assembled from the two source types. -/
def b65e_movingContractionCoordsQ (n : Fin 7) (e : Fin 2)
    (c : Fin 6) (i j : Fin 4) : ℚ :=
  b65e_movingFixedContractionCoordsQ n e c i j +
    b65e_movingMovingContractionCoordsQ n e c i j

set_option maxHeartbeats 400000 in
/-- A second-order moving-residue coordinate satisfies the finite field contraction. -/
theorem b65e_movingContractionCoordsQ_table_1_0_0_0_0 :
    b65e_movingContractionCoordsQ 1 0 0 0 0 = 2 * b65e_movingJet 2 0 0 0 0 := by
  decide +kernel

end HodgeLean.Foundations.Program
