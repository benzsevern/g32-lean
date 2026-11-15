import HodgeLean.Foundations.Program.G32PropFourSixPacked0201
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound049_points : Finset (Fin 240) :=
  {3, 6, 15, 36, 58, 69, 75, 78, 99, 110, 116, 119, 128, 139, 159, 165, 168, 176, 187, 204, 209, 213, 221, 233}

def g32p_centralizerBound049_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

def g32p_centralizerBound049_coefficients : List HurwitzPrymRex_Zw := [⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -2⟩]

theorem g32p_centralizerBound049_base_polynomial :
    g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58)
      g32p_centralizerBound049_coefficients = g32p_integralPointScale ⟨3, 0⟩ (g32p_rootMatrix 189) := by
  decide +kernel

theorem g32p_centralizerBound049_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) := by
  decide +kernel

theorem g32p_centralizerBound049_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) := by
  decide +kernel

theorem g32p_centralizerBound049_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) := by
  decide +kernel

theorem g32p_centralizerBound049_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) := by
  decide +kernel

theorem g32p_centralizerBound049_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) := by
  decide +kernel

theorem g32p_centralizerBound049_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) := by
  decide +kernel

theorem g32p_centralizerBound049_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) := by
  decide +kernel

theorem g32p_centralizerBound049_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) := by
  decide +kernel

theorem g32p_centralizerBound049_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) := by
  decide +kernel

theorem g32p_centralizerBound049_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) := by
  decide +kernel

theorem g32p_centralizerBound049_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) := by
  decide +kernel

theorem g32p_centralizerBound049_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) := by
  decide +kernel

theorem g32p_centralizerBound049_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) := by
  decide +kernel

theorem g32p_centralizerBound049_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) := by
  decide +kernel

theorem g32p_centralizerBound049_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) := by
  decide +kernel

theorem g32p_centralizerBound049_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 49) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 49)
        (g32p_rootMatrix i) g32p_centralizerBound049_coefficients r 0).om) →
    i ∈ g32p_centralizerBound049_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound049_point_block00 t
  · exact g32p_centralizerBound049_point_block01 t
  · exact g32p_centralizerBound049_point_block02 t
  · exact g32p_centralizerBound049_point_block03 t
  · exact g32p_centralizerBound049_point_block04 t
  · exact g32p_centralizerBound049_point_block05 t
  · exact g32p_centralizerBound049_point_block06 t
  · exact g32p_centralizerBound049_point_block07 t
  · exact g32p_centralizerBound049_point_block08 t
  · exact g32p_centralizerBound049_point_block09 t
  · exact g32p_centralizerBound049_point_block10 t
  · exact g32p_centralizerBound049_point_block11 t
  · exact g32p_centralizerBound049_point_block12 t
  · exact g32p_centralizerBound049_point_block13 t
  · exact g32p_centralizerBound049_point_block14 t

theorem g32p_centralizerBound049_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 49) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 49)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound049_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound049_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 49) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 49)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound049_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound049_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 49) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 49)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound049_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound049_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 49) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 49)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound049_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound049_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 49) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 49)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound049_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound049_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 49) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 49) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound049_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 49) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 49)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound049_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound049_stabilizer_block00 t r
  · exact g32p_centralizerBound049_stabilizer_block01 t r
  · exact g32p_centralizerBound049_stabilizer_block02 t r
  · exact g32p_centralizerBound049_stabilizer_block03 t r
  · exact g32p_centralizerBound049_stabilizer_block04 t r

theorem g32p_centralizerBound049_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 49}) ≤ g32p_literalCentralizer 49 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 49 g32p_centralizerBound049_points
    g32p_centralizerBound049_stabilizers ?_ g32p_centralizerBound049_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound049_point_mem i (g32p_centralizer_point_moments 49 x i hi.symm)
    obtain ⟨j, hj⟩ := g32p_centralizer_point_polynomial 49 x i 189
      g32p_centralizerBound049_coefficients ⟨3, 0⟩ hi.symm g32p_centralizerBound049_base_polynomial
    intro r
    rw [hj]
    simp only [g32p_integralPointScale, HurwitzPrymRex_Zw.mul, zero_mul, sub_zero,
      mul_zero, add_zero]
    exact ⟨dvd_mul_right 3 _, dvd_mul_right 3 _⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound050_points : Finset (Fin 240) :=
  {0, 1, 3, 4, 6, 13, 15, 22, 32, 33, 36, 44, 54, 55, 58, 60, 63, 79, 80, 95, 96, 99, 101, 104, 120, 121, 144, 145, 150, 153, 169, 170, 191, 192, 225, 226}

def g32p_centralizerBound050_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 6), (0, 7)}

theorem g32p_centralizerBound050_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) := by
  decide +kernel

theorem g32p_centralizerBound050_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) := by
  decide +kernel

theorem g32p_centralizerBound050_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) := by
  decide +kernel

theorem g32p_centralizerBound050_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) := by
  decide +kernel

theorem g32p_centralizerBound050_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) := by
  decide +kernel

theorem g32p_centralizerBound050_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) := by
  decide +kernel

theorem g32p_centralizerBound050_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) := by
  decide +kernel

theorem g32p_centralizerBound050_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) := by
  decide +kernel

theorem g32p_centralizerBound050_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) := by
  decide +kernel

theorem g32p_centralizerBound050_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) := by
  decide +kernel

theorem g32p_centralizerBound050_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) := by
  decide +kernel

theorem g32p_centralizerBound050_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) := by
  decide +kernel

theorem g32p_centralizerBound050_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) := by
  decide +kernel

theorem g32p_centralizerBound050_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) := by
  decide +kernel

theorem g32p_centralizerBound050_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) := by
  decide +kernel

theorem g32p_centralizerBound050_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 50) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound050_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound050_point_block00 t
  · exact g32p_centralizerBound050_point_block01 t
  · exact g32p_centralizerBound050_point_block02 t
  · exact g32p_centralizerBound050_point_block03 t
  · exact g32p_centralizerBound050_point_block04 t
  · exact g32p_centralizerBound050_point_block05 t
  · exact g32p_centralizerBound050_point_block06 t
  · exact g32p_centralizerBound050_point_block07 t
  · exact g32p_centralizerBound050_point_block08 t
  · exact g32p_centralizerBound050_point_block09 t
  · exact g32p_centralizerBound050_point_block10 t
  · exact g32p_centralizerBound050_point_block11 t
  · exact g32p_centralizerBound050_point_block12 t
  · exact g32p_centralizerBound050_point_block13 t
  · exact g32p_centralizerBound050_point_block14 t

theorem g32p_centralizerBound050_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 50) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 50)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound050_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound050_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 50) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 50)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound050_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound050_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 50) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 50)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound050_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound050_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 50) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 50)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound050_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound050_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 50) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 50)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound050_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound050_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 50) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 50) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound050_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 50) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 50)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound050_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound050_stabilizer_block00 t r
  · exact g32p_centralizerBound050_stabilizer_block01 t r
  · exact g32p_centralizerBound050_stabilizer_block02 t r
  · exact g32p_centralizerBound050_stabilizer_block03 t r
  · exact g32p_centralizerBound050_stabilizer_block04 t r

theorem g32p_centralizerBound050_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 50}) ≤ g32p_literalCentralizer 50 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 50 g32p_centralizerBound050_points
    g32p_centralizerBound050_stabilizers ?_ g32p_centralizerBound050_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound050_point_mem i (g32p_centralizer_point_moments 50 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound051_points : Finset (Fin 240) :=
  {3, 6, 15, 26, 30, 33, 36, 48, 52, 55, 58, 61, 64, 65, 71, 81, 85, 89, 93, 96, 99, 102, 105, 106, 112, 122, 126, 130, 140, 144, 151, 154, 155, 161, 171, 175, 178, 188, 191, 200, 210, 212, 215, 222, 225, 228, 234, 236}

def g32p_centralizerBound051_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (18, 2), (22, 7), (24, 2), (30, 4), (36, 5), (53, 8), (63, 3), (68, 7)}

theorem g32p_centralizerBound051_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) := by
  decide +kernel

theorem g32p_centralizerBound051_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) := by
  decide +kernel

theorem g32p_centralizerBound051_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) := by
  decide +kernel

theorem g32p_centralizerBound051_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) := by
  decide +kernel

theorem g32p_centralizerBound051_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) := by
  decide +kernel

theorem g32p_centralizerBound051_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) := by
  decide +kernel

theorem g32p_centralizerBound051_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) := by
  decide +kernel

theorem g32p_centralizerBound051_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) := by
  decide +kernel

theorem g32p_centralizerBound051_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) := by
  decide +kernel

theorem g32p_centralizerBound051_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) := by
  decide +kernel

theorem g32p_centralizerBound051_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) := by
  decide +kernel

theorem g32p_centralizerBound051_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) := by
  decide +kernel

theorem g32p_centralizerBound051_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) := by
  decide +kernel

theorem g32p_centralizerBound051_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) := by
  decide +kernel

theorem g32p_centralizerBound051_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) := by
  decide +kernel

theorem g32p_centralizerBound051_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 51) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound051_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound051_point_block00 t
  · exact g32p_centralizerBound051_point_block01 t
  · exact g32p_centralizerBound051_point_block02 t
  · exact g32p_centralizerBound051_point_block03 t
  · exact g32p_centralizerBound051_point_block04 t
  · exact g32p_centralizerBound051_point_block05 t
  · exact g32p_centralizerBound051_point_block06 t
  · exact g32p_centralizerBound051_point_block07 t
  · exact g32p_centralizerBound051_point_block08 t
  · exact g32p_centralizerBound051_point_block09 t
  · exact g32p_centralizerBound051_point_block10 t
  · exact g32p_centralizerBound051_point_block11 t
  · exact g32p_centralizerBound051_point_block12 t
  · exact g32p_centralizerBound051_point_block13 t
  · exact g32p_centralizerBound051_point_block14 t

theorem g32p_centralizerBound051_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 51) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 51)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound051_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound051_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 51) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 51)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound051_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound051_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 51) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 51)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound051_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound051_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 51) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 51)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound051_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound051_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 51) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 51)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound051_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound051_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 51) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 51) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound051_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 51) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 51)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound051_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound051_stabilizer_block00 t r
  · exact g32p_centralizerBound051_stabilizer_block01 t r
  · exact g32p_centralizerBound051_stabilizer_block02 t r
  · exact g32p_centralizerBound051_stabilizer_block03 t r
  · exact g32p_centralizerBound051_stabilizer_block04 t r

theorem g32p_centralizerBound051_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 51}) ≤ g32p_literalCentralizer 51 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 51 g32p_centralizerBound051_points
    g32p_centralizerBound051_stabilizers ?_ g32p_centralizerBound051_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound051_point_mem i (g32p_centralizer_point_moments 51 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound052_points : Finset (Fin 240) :=
  {3, 6, 15, 36, 58, 64, 99, 105, 130, 154, 178, 215}

def g32p_centralizerBound052_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (2, 7), (4, 5), (7, 8), (11, 8), (13, 5), (16, 2), (21, 4), (23, 6), (24, 2), (27, 4), (29, 6), (33, 2), (35, 7), (46, 3), (49, 4), (51, 6), (53, 8), (54, 0), (56, 7), (57, 1), (59, 1), (66, 1), (67, 3)}

theorem g32p_centralizerBound052_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) := by
  decide +kernel

theorem g32p_centralizerBound052_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) := by
  decide +kernel

theorem g32p_centralizerBound052_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) := by
  decide +kernel

theorem g32p_centralizerBound052_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) := by
  decide +kernel

theorem g32p_centralizerBound052_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) := by
  decide +kernel

theorem g32p_centralizerBound052_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) := by
  decide +kernel

theorem g32p_centralizerBound052_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) := by
  decide +kernel

theorem g32p_centralizerBound052_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) := by
  decide +kernel

theorem g32p_centralizerBound052_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) := by
  decide +kernel

theorem g32p_centralizerBound052_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) := by
  decide +kernel

theorem g32p_centralizerBound052_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) := by
  decide +kernel

theorem g32p_centralizerBound052_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) := by
  decide +kernel

theorem g32p_centralizerBound052_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) := by
  decide +kernel

theorem g32p_centralizerBound052_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) := by
  decide +kernel

theorem g32p_centralizerBound052_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) := by
  decide +kernel

theorem g32p_centralizerBound052_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 52) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound052_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound052_point_block00 t
  · exact g32p_centralizerBound052_point_block01 t
  · exact g32p_centralizerBound052_point_block02 t
  · exact g32p_centralizerBound052_point_block03 t
  · exact g32p_centralizerBound052_point_block04 t
  · exact g32p_centralizerBound052_point_block05 t
  · exact g32p_centralizerBound052_point_block06 t
  · exact g32p_centralizerBound052_point_block07 t
  · exact g32p_centralizerBound052_point_block08 t
  · exact g32p_centralizerBound052_point_block09 t
  · exact g32p_centralizerBound052_point_block10 t
  · exact g32p_centralizerBound052_point_block11 t
  · exact g32p_centralizerBound052_point_block12 t
  · exact g32p_centralizerBound052_point_block13 t
  · exact g32p_centralizerBound052_point_block14 t

theorem g32p_centralizerBound052_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 52) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 52)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound052_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound052_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 52) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 52)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound052_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound052_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 52) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 52)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound052_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound052_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 52) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 52)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound052_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound052_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 52) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 52)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound052_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound052_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 52) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 52) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound052_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 52) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 52)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound052_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound052_stabilizer_block00 t r
  · exact g32p_centralizerBound052_stabilizer_block01 t r
  · exact g32p_centralizerBound052_stabilizer_block02 t r
  · exact g32p_centralizerBound052_stabilizer_block03 t r
  · exact g32p_centralizerBound052_stabilizer_block04 t r

theorem g32p_centralizerBound052_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 52}) ≤ g32p_literalCentralizer 52 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 52 g32p_centralizerBound052_points
    g32p_centralizerBound052_stabilizers ?_ g32p_centralizerBound052_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound052_point_mem i (g32p_centralizer_point_moments 52 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound053_points : Finset (Fin 240) :=
  {3, 6, 11, 12, 13, 15, 20, 21, 22, 28, 32, 33, 36, 37, 42, 43, 44, 50, 54, 55, 58, 59, 64, 69, 77, 83, 84, 91, 95, 96, 99, 100, 105, 110, 118, 124, 125, 127, 128, 130, 134, 144, 154, 159, 167, 173, 174, 176, 178, 182, 191, 213, 215, 225}

def g32p_centralizerBound053_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound053_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) := by
  decide +kernel

theorem g32p_centralizerBound053_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) := by
  decide +kernel

theorem g32p_centralizerBound053_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) := by
  decide +kernel

theorem g32p_centralizerBound053_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) := by
  decide +kernel

theorem g32p_centralizerBound053_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) := by
  decide +kernel

theorem g32p_centralizerBound053_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) := by
  decide +kernel

theorem g32p_centralizerBound053_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) := by
  decide +kernel

theorem g32p_centralizerBound053_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) := by
  decide +kernel

theorem g32p_centralizerBound053_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) := by
  decide +kernel

theorem g32p_centralizerBound053_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) := by
  decide +kernel

theorem g32p_centralizerBound053_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) := by
  decide +kernel

theorem g32p_centralizerBound053_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) := by
  decide +kernel

theorem g32p_centralizerBound053_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) := by
  decide +kernel

theorem g32p_centralizerBound053_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) := by
  decide +kernel

theorem g32p_centralizerBound053_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) := by
  decide +kernel

theorem g32p_centralizerBound053_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 53) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound053_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound053_point_block00 t
  · exact g32p_centralizerBound053_point_block01 t
  · exact g32p_centralizerBound053_point_block02 t
  · exact g32p_centralizerBound053_point_block03 t
  · exact g32p_centralizerBound053_point_block04 t
  · exact g32p_centralizerBound053_point_block05 t
  · exact g32p_centralizerBound053_point_block06 t
  · exact g32p_centralizerBound053_point_block07 t
  · exact g32p_centralizerBound053_point_block08 t
  · exact g32p_centralizerBound053_point_block09 t
  · exact g32p_centralizerBound053_point_block10 t
  · exact g32p_centralizerBound053_point_block11 t
  · exact g32p_centralizerBound053_point_block12 t
  · exact g32p_centralizerBound053_point_block13 t
  · exact g32p_centralizerBound053_point_block14 t

theorem g32p_centralizerBound053_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 53) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 53)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound053_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound053_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 53) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 53)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound053_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound053_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 53) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 53)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound053_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound053_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 53) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 53)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound053_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound053_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 53) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 53)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound053_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound053_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 53) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 53) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound053_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 53) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 53)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound053_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound053_stabilizer_block00 t r
  · exact g32p_centralizerBound053_stabilizer_block01 t r
  · exact g32p_centralizerBound053_stabilizer_block02 t r
  · exact g32p_centralizerBound053_stabilizer_block03 t r
  · exact g32p_centralizerBound053_stabilizer_block04 t r

theorem g32p_centralizerBound053_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 53}) ≤ g32p_literalCentralizer 53 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 53 g32p_centralizerBound053_points
    g32p_centralizerBound053_stabilizers ?_ g32p_centralizerBound053_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound053_point_mem i (g32p_centralizer_point_moments 53 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound054_points : Finset (Fin 240) :=
  {3, 6, 7, 12, 15, 16, 21, 24, 29, 31, 35, 36, 38, 43, 46, 51, 53, 57, 58, 64, 66, 75, 76, 84, 87, 92, 94, 98, 99, 105, 107, 116, 117, 125, 130, 131, 135, 139, 141, 148, 154, 156, 165, 166, 174, 178, 179, 183, 187, 195, 205, 215, 216, 221}

def g32p_centralizerBound054_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound054_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) := by
  decide +kernel

theorem g32p_centralizerBound054_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) := by
  decide +kernel

theorem g32p_centralizerBound054_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) := by
  decide +kernel

theorem g32p_centralizerBound054_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) := by
  decide +kernel

theorem g32p_centralizerBound054_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) := by
  decide +kernel

theorem g32p_centralizerBound054_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) := by
  decide +kernel

theorem g32p_centralizerBound054_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) := by
  decide +kernel

theorem g32p_centralizerBound054_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) := by
  decide +kernel

theorem g32p_centralizerBound054_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) := by
  decide +kernel

theorem g32p_centralizerBound054_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) := by
  decide +kernel

theorem g32p_centralizerBound054_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) := by
  decide +kernel

theorem g32p_centralizerBound054_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) := by
  decide +kernel

theorem g32p_centralizerBound054_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) := by
  decide +kernel

theorem g32p_centralizerBound054_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) := by
  decide +kernel

theorem g32p_centralizerBound054_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) := by
  decide +kernel

theorem g32p_centralizerBound054_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 54) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound054_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound054_point_block00 t
  · exact g32p_centralizerBound054_point_block01 t
  · exact g32p_centralizerBound054_point_block02 t
  · exact g32p_centralizerBound054_point_block03 t
  · exact g32p_centralizerBound054_point_block04 t
  · exact g32p_centralizerBound054_point_block05 t
  · exact g32p_centralizerBound054_point_block06 t
  · exact g32p_centralizerBound054_point_block07 t
  · exact g32p_centralizerBound054_point_block08 t
  · exact g32p_centralizerBound054_point_block09 t
  · exact g32p_centralizerBound054_point_block10 t
  · exact g32p_centralizerBound054_point_block11 t
  · exact g32p_centralizerBound054_point_block12 t
  · exact g32p_centralizerBound054_point_block13 t
  · exact g32p_centralizerBound054_point_block14 t

theorem g32p_centralizerBound054_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 54) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 54)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound054_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound054_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 54) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 54)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound054_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound054_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 54) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 54)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound054_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound054_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 54) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 54)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound054_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound054_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 54) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 54)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound054_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound054_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 54) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 54) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound054_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 54) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 54)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound054_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound054_stabilizer_block00 t r
  · exact g32p_centralizerBound054_stabilizer_block01 t r
  · exact g32p_centralizerBound054_stabilizer_block02 t r
  · exact g32p_centralizerBound054_stabilizer_block03 t r
  · exact g32p_centralizerBound054_stabilizer_block04 t r

theorem g32p_centralizerBound054_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 54}) ≤ g32p_literalCentralizer 54 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 54 g32p_centralizerBound054_points
    g32p_centralizerBound054_stabilizers ?_ g32p_centralizerBound054_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound054_point_mem i (g32p_centralizer_point_moments 54 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound055_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 9, 11, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 31, 33, 36, 38, 40, 42, 43, 46, 47, 49, 53, 55, 58, 62, 66, 67, 70, 75, 76, 83, 84, 87, 88, 90, 94, 96, 99, 103, 107, 108, 111, 116, 117, 124, 125, 129, 131, 139, 144, 152, 156, 157, 160, 165, 166, 173, 174, 177, 179, 187, 191, 214, 216, 221, 225}

def g32p_centralizerBound055_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound055_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) := by
  decide +kernel

theorem g32p_centralizerBound055_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) := by
  decide +kernel

theorem g32p_centralizerBound055_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) := by
  decide +kernel

theorem g32p_centralizerBound055_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) := by
  decide +kernel

theorem g32p_centralizerBound055_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) := by
  decide +kernel

theorem g32p_centralizerBound055_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) := by
  decide +kernel

theorem g32p_centralizerBound055_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) := by
  decide +kernel

theorem g32p_centralizerBound055_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) := by
  decide +kernel

theorem g32p_centralizerBound055_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) := by
  decide +kernel

theorem g32p_centralizerBound055_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) := by
  decide +kernel

theorem g32p_centralizerBound055_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) := by
  decide +kernel

theorem g32p_centralizerBound055_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) := by
  decide +kernel

theorem g32p_centralizerBound055_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) := by
  decide +kernel

theorem g32p_centralizerBound055_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) := by
  decide +kernel

theorem g32p_centralizerBound055_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) := by
  decide +kernel

theorem g32p_centralizerBound055_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 55) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound055_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound055_point_block00 t
  · exact g32p_centralizerBound055_point_block01 t
  · exact g32p_centralizerBound055_point_block02 t
  · exact g32p_centralizerBound055_point_block03 t
  · exact g32p_centralizerBound055_point_block04 t
  · exact g32p_centralizerBound055_point_block05 t
  · exact g32p_centralizerBound055_point_block06 t
  · exact g32p_centralizerBound055_point_block07 t
  · exact g32p_centralizerBound055_point_block08 t
  · exact g32p_centralizerBound055_point_block09 t
  · exact g32p_centralizerBound055_point_block10 t
  · exact g32p_centralizerBound055_point_block11 t
  · exact g32p_centralizerBound055_point_block12 t
  · exact g32p_centralizerBound055_point_block13 t
  · exact g32p_centralizerBound055_point_block14 t

theorem g32p_centralizerBound055_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 55) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 55)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound055_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound055_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 55) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 55)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound055_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound055_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 55) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 55)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound055_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound055_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 55) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 55)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound055_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound055_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 55) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 55)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound055_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound055_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 55) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 55) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound055_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 55) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 55)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound055_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound055_stabilizer_block00 t r
  · exact g32p_centralizerBound055_stabilizer_block01 t r
  · exact g32p_centralizerBound055_stabilizer_block02 t r
  · exact g32p_centralizerBound055_stabilizer_block03 t r
  · exact g32p_centralizerBound055_stabilizer_block04 t r

theorem g32p_centralizerBound055_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 55}) ≤ g32p_literalCentralizer 55 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 55 g32p_centralizerBound055_points
    g32p_centralizerBound055_stabilizers ?_ g32p_centralizerBound055_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound055_point_mem i (g32p_centralizer_point_moments 55 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound056_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 28, 32, 33, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 47, 48, 50, 54, 55, 57, 58, 59, 61, 64, 66, 67, 69, 77, 79, 83, 84, 85, 86, 87, 88, 89, 91, 95, 96, 98, 99, 100, 102, 105, 107, 108, 110, 118, 120, 124, 125, 126, 127, 128, 130, 131, 134, 140, 141, 144, 145, 148, 151, 154, 156, 157, 159, 167, 169, 173, 174, 175, 176, 178, 179, 182, 188, 191, 192, 195, 213, 215, 216, 222, 225, 226}

def g32p_centralizerBound056_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 6), (0, 7), (26, 1), (26, 2), (26, 8)}

theorem g32p_centralizerBound056_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) := by
  decide +kernel

theorem g32p_centralizerBound056_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) := by
  decide +kernel

theorem g32p_centralizerBound056_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) := by
  decide +kernel

theorem g32p_centralizerBound056_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) := by
  decide +kernel

theorem g32p_centralizerBound056_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) := by
  decide +kernel

theorem g32p_centralizerBound056_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) := by
  decide +kernel

theorem g32p_centralizerBound056_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) := by
  decide +kernel

theorem g32p_centralizerBound056_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) := by
  decide +kernel

theorem g32p_centralizerBound056_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) := by
  decide +kernel

theorem g32p_centralizerBound056_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) := by
  decide +kernel

theorem g32p_centralizerBound056_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) := by
  decide +kernel

theorem g32p_centralizerBound056_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) := by
  decide +kernel

theorem g32p_centralizerBound056_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) := by
  decide +kernel

theorem g32p_centralizerBound056_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) := by
  decide +kernel

theorem g32p_centralizerBound056_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) := by
  decide +kernel

theorem g32p_centralizerBound056_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 56) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound056_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound056_point_block00 t
  · exact g32p_centralizerBound056_point_block01 t
  · exact g32p_centralizerBound056_point_block02 t
  · exact g32p_centralizerBound056_point_block03 t
  · exact g32p_centralizerBound056_point_block04 t
  · exact g32p_centralizerBound056_point_block05 t
  · exact g32p_centralizerBound056_point_block06 t
  · exact g32p_centralizerBound056_point_block07 t
  · exact g32p_centralizerBound056_point_block08 t
  · exact g32p_centralizerBound056_point_block09 t
  · exact g32p_centralizerBound056_point_block10 t
  · exact g32p_centralizerBound056_point_block11 t
  · exact g32p_centralizerBound056_point_block12 t
  · exact g32p_centralizerBound056_point_block13 t
  · exact g32p_centralizerBound056_point_block14 t

theorem g32p_centralizerBound056_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 56) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 56)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound056_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound056_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 56) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 56)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound056_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound056_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 56) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 56)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound056_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound056_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 56) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 56)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound056_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound056_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 56) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 56)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound056_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound056_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 56) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 56) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound056_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 56) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 56)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound056_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound056_stabilizer_block00 t r
  · exact g32p_centralizerBound056_stabilizer_block01 t r
  · exact g32p_centralizerBound056_stabilizer_block02 t r
  · exact g32p_centralizerBound056_stabilizer_block03 t r
  · exact g32p_centralizerBound056_stabilizer_block04 t r

theorem g32p_centralizerBound056_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 56}) ≤ g32p_literalCentralizer 56 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 56 g32p_centralizerBound056_points
    g32p_centralizerBound056_stabilizers ?_ g32p_centralizerBound056_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound056_point_mem i (g32p_centralizer_point_moments 56 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound057_points : Finset (Fin 240) :=
  {3, 6, 15, 36, 58, 69, 75, 78, 99, 110, 116, 119, 128, 139, 159, 165, 168, 176, 187, 204, 209, 213, 221, 233}

def g32p_centralizerBound057_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

def g32p_centralizerBound057_coefficients : List HurwitzPrymRex_Zw := [⟨1, -1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩]

theorem g32p_centralizerBound057_base_polynomial :
    g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58)
      g32p_centralizerBound057_coefficients = g32p_integralPointScale ⟨3, 0⟩ (g32p_rootMatrix 189) := by
  decide +kernel

theorem g32p_centralizerBound057_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) := by
  decide +kernel

theorem g32p_centralizerBound057_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) := by
  decide +kernel

theorem g32p_centralizerBound057_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) := by
  decide +kernel

theorem g32p_centralizerBound057_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) := by
  decide +kernel

theorem g32p_centralizerBound057_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) := by
  decide +kernel

theorem g32p_centralizerBound057_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) := by
  decide +kernel

theorem g32p_centralizerBound057_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) := by
  decide +kernel

theorem g32p_centralizerBound057_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) := by
  decide +kernel

theorem g32p_centralizerBound057_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) := by
  decide +kernel

theorem g32p_centralizerBound057_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) := by
  decide +kernel

theorem g32p_centralizerBound057_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) := by
  decide +kernel

theorem g32p_centralizerBound057_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) := by
  decide +kernel

theorem g32p_centralizerBound057_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) := by
  decide +kernel

theorem g32p_centralizerBound057_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) := by
  decide +kernel

theorem g32p_centralizerBound057_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) := by
  decide +kernel

theorem g32p_centralizerBound057_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 57) (g32p_rootMatrix 58) →
    (∀ r : Fin 4,
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).re ∧
      3 ∣ (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix 57)
        (g32p_rootMatrix i) g32p_centralizerBound057_coefficients r 0).om) →
    i ∈ g32p_centralizerBound057_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound057_point_block00 t
  · exact g32p_centralizerBound057_point_block01 t
  · exact g32p_centralizerBound057_point_block02 t
  · exact g32p_centralizerBound057_point_block03 t
  · exact g32p_centralizerBound057_point_block04 t
  · exact g32p_centralizerBound057_point_block05 t
  · exact g32p_centralizerBound057_point_block06 t
  · exact g32p_centralizerBound057_point_block07 t
  · exact g32p_centralizerBound057_point_block08 t
  · exact g32p_centralizerBound057_point_block09 t
  · exact g32p_centralizerBound057_point_block10 t
  · exact g32p_centralizerBound057_point_block11 t
  · exact g32p_centralizerBound057_point_block12 t
  · exact g32p_centralizerBound057_point_block13 t
  · exact g32p_centralizerBound057_point_block14 t

theorem g32p_centralizerBound057_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 57) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 57)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound057_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound057_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 57) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 57)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound057_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound057_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 57) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 57)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound057_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound057_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 57) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 57)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound057_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound057_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 57) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 57)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound057_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound057_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 57) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 57) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound057_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 57) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 57)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound057_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound057_stabilizer_block00 t r
  · exact g32p_centralizerBound057_stabilizer_block01 t r
  · exact g32p_centralizerBound057_stabilizer_block02 t r
  · exact g32p_centralizerBound057_stabilizer_block03 t r
  · exact g32p_centralizerBound057_stabilizer_block04 t r

theorem g32p_centralizerBound057_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 57}) ≤ g32p_literalCentralizer 57 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 57 g32p_centralizerBound057_points
    g32p_centralizerBound057_stabilizers ?_ g32p_centralizerBound057_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound057_point_mem i (g32p_centralizer_point_moments 57 x i hi.symm)
    obtain ⟨j, hj⟩ := g32p_centralizer_point_polynomial 57 x i 189
      g32p_centralizerBound057_coefficients ⟨3, 0⟩ hi.symm g32p_centralizerBound057_base_polynomial
    intro r
    rw [hj]
    simp only [g32p_integralPointScale, HurwitzPrymRex_Zw.mul, zero_mul, sub_zero,
      mul_zero, add_zero]
    exact ⟨dvd_mul_right 3 _, dvd_mul_right 3 _⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound058_points : Finset (Fin 240) :=
  {3, 6, 15, 31, 36, 37, 53, 58, 59, 76, 77, 81, 94, 99, 100, 117, 118, 122, 166, 167, 171, 210, 234, 236}

def g32p_centralizerBound058_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (7, 8), (27, 4)}

theorem g32p_centralizerBound058_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) := by
  decide +kernel

theorem g32p_centralizerBound058_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) := by
  decide +kernel

theorem g32p_centralizerBound058_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) := by
  decide +kernel

theorem g32p_centralizerBound058_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) := by
  decide +kernel

theorem g32p_centralizerBound058_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) := by
  decide +kernel

theorem g32p_centralizerBound058_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) := by
  decide +kernel

theorem g32p_centralizerBound058_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) := by
  decide +kernel

theorem g32p_centralizerBound058_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) := by
  decide +kernel

theorem g32p_centralizerBound058_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) := by
  decide +kernel

theorem g32p_centralizerBound058_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) := by
  decide +kernel

theorem g32p_centralizerBound058_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) := by
  decide +kernel

theorem g32p_centralizerBound058_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) := by
  decide +kernel

theorem g32p_centralizerBound058_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) := by
  decide +kernel

theorem g32p_centralizerBound058_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) := by
  decide +kernel

theorem g32p_centralizerBound058_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) := by
  decide +kernel

theorem g32p_centralizerBound058_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 58) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound058_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound058_point_block00 t
  · exact g32p_centralizerBound058_point_block01 t
  · exact g32p_centralizerBound058_point_block02 t
  · exact g32p_centralizerBound058_point_block03 t
  · exact g32p_centralizerBound058_point_block04 t
  · exact g32p_centralizerBound058_point_block05 t
  · exact g32p_centralizerBound058_point_block06 t
  · exact g32p_centralizerBound058_point_block07 t
  · exact g32p_centralizerBound058_point_block08 t
  · exact g32p_centralizerBound058_point_block09 t
  · exact g32p_centralizerBound058_point_block10 t
  · exact g32p_centralizerBound058_point_block11 t
  · exact g32p_centralizerBound058_point_block12 t
  · exact g32p_centralizerBound058_point_block13 t
  · exact g32p_centralizerBound058_point_block14 t

theorem g32p_centralizerBound058_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 58) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 58)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound058_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound058_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 58) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 58)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound058_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound058_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 58) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 58)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound058_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound058_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 58) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 58)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound058_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound058_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 58) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 58)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound058_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound058_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 58) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 58) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound058_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 58) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 58)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound058_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound058_stabilizer_block00 t r
  · exact g32p_centralizerBound058_stabilizer_block01 t r
  · exact g32p_centralizerBound058_stabilizer_block02 t r
  · exact g32p_centralizerBound058_stabilizer_block03 t r
  · exact g32p_centralizerBound058_stabilizer_block04 t r

theorem g32p_centralizerBound058_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 58}) ≤ g32p_literalCentralizer 58 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 58 g32p_centralizerBound058_points
    g32p_centralizerBound058_stabilizers ?_ g32p_centralizerBound058_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound058_point_mem i (g32p_centralizer_point_moments 58 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound059_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 9, 14, 15, 18, 25, 36, 40, 47, 58, 63, 67, 80, 88, 99, 104, 108, 121, 132, 136, 143, 146, 153, 157, 170, 180, 184, 190, 193, 198, 217, 219, 224}

def g32p_centralizerBound059_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (14, 5), (32, 4)}

theorem g32p_centralizerBound059_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) := by
  decide +kernel

theorem g32p_centralizerBound059_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) := by
  decide +kernel

theorem g32p_centralizerBound059_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) := by
  decide +kernel

theorem g32p_centralizerBound059_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) := by
  decide +kernel

theorem g32p_centralizerBound059_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) := by
  decide +kernel

theorem g32p_centralizerBound059_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) := by
  decide +kernel

theorem g32p_centralizerBound059_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) := by
  decide +kernel

theorem g32p_centralizerBound059_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) := by
  decide +kernel

theorem g32p_centralizerBound059_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) := by
  decide +kernel

theorem g32p_centralizerBound059_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) := by
  decide +kernel

theorem g32p_centralizerBound059_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) := by
  decide +kernel

theorem g32p_centralizerBound059_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) := by
  decide +kernel

theorem g32p_centralizerBound059_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) := by
  decide +kernel

theorem g32p_centralizerBound059_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) := by
  decide +kernel

theorem g32p_centralizerBound059_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) := by
  decide +kernel

theorem g32p_centralizerBound059_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 59) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound059_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound059_point_block00 t
  · exact g32p_centralizerBound059_point_block01 t
  · exact g32p_centralizerBound059_point_block02 t
  · exact g32p_centralizerBound059_point_block03 t
  · exact g32p_centralizerBound059_point_block04 t
  · exact g32p_centralizerBound059_point_block05 t
  · exact g32p_centralizerBound059_point_block06 t
  · exact g32p_centralizerBound059_point_block07 t
  · exact g32p_centralizerBound059_point_block08 t
  · exact g32p_centralizerBound059_point_block09 t
  · exact g32p_centralizerBound059_point_block10 t
  · exact g32p_centralizerBound059_point_block11 t
  · exact g32p_centralizerBound059_point_block12 t
  · exact g32p_centralizerBound059_point_block13 t
  · exact g32p_centralizerBound059_point_block14 t

theorem g32p_centralizerBound059_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 59) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 59)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound059_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound059_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 59) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 59)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound059_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound059_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 59) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 59)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound059_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound059_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 59) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 59)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound059_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound059_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 59) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 59)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound059_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound059_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 59) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 59) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound059_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 59) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 59)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound059_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound059_stabilizer_block00 t r
  · exact g32p_centralizerBound059_stabilizer_block01 t r
  · exact g32p_centralizerBound059_stabilizer_block02 t r
  · exact g32p_centralizerBound059_stabilizer_block03 t r
  · exact g32p_centralizerBound059_stabilizer_block04 t r

theorem g32p_centralizerBound059_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 59}) ≤ g32p_literalCentralizer 59 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 59 g32p_centralizerBound059_points
    g32p_centralizerBound059_stabilizers ?_ g32p_centralizerBound059_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound059_point_mem i (g32p_centralizer_point_moments 59 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound060_points : Finset (Fin 240) :=
  {3, 6, 15, 31, 36, 53, 58, 63, 64, 76, 80, 94, 99, 104, 105, 117, 121, 130, 132, 143, 153, 154, 166, 170, 178, 180, 190, 215, 217, 224}

def g32p_centralizerBound060_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound060_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) := by
  decide +kernel

theorem g32p_centralizerBound060_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) := by
  decide +kernel

theorem g32p_centralizerBound060_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) := by
  decide +kernel

theorem g32p_centralizerBound060_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) := by
  decide +kernel

theorem g32p_centralizerBound060_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) := by
  decide +kernel

theorem g32p_centralizerBound060_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) := by
  decide +kernel

theorem g32p_centralizerBound060_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) := by
  decide +kernel

theorem g32p_centralizerBound060_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) := by
  decide +kernel

theorem g32p_centralizerBound060_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) := by
  decide +kernel

theorem g32p_centralizerBound060_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) := by
  decide +kernel

theorem g32p_centralizerBound060_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) := by
  decide +kernel

theorem g32p_centralizerBound060_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) := by
  decide +kernel

theorem g32p_centralizerBound060_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) := by
  decide +kernel

theorem g32p_centralizerBound060_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) := by
  decide +kernel

theorem g32p_centralizerBound060_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) := by
  decide +kernel

theorem g32p_centralizerBound060_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 60) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound060_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound060_point_block00 t
  · exact g32p_centralizerBound060_point_block01 t
  · exact g32p_centralizerBound060_point_block02 t
  · exact g32p_centralizerBound060_point_block03 t
  · exact g32p_centralizerBound060_point_block04 t
  · exact g32p_centralizerBound060_point_block05 t
  · exact g32p_centralizerBound060_point_block06 t
  · exact g32p_centralizerBound060_point_block07 t
  · exact g32p_centralizerBound060_point_block08 t
  · exact g32p_centralizerBound060_point_block09 t
  · exact g32p_centralizerBound060_point_block10 t
  · exact g32p_centralizerBound060_point_block11 t
  · exact g32p_centralizerBound060_point_block12 t
  · exact g32p_centralizerBound060_point_block13 t
  · exact g32p_centralizerBound060_point_block14 t

theorem g32p_centralizerBound060_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 60) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 60)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound060_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound060_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 60) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 60)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound060_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound060_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 60) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 60)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound060_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound060_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 60) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 60)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound060_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound060_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 60) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 60)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound060_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound060_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 60) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 60) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound060_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 60) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 60)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound060_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound060_stabilizer_block00 t r
  · exact g32p_centralizerBound060_stabilizer_block01 t r
  · exact g32p_centralizerBound060_stabilizer_block02 t r
  · exact g32p_centralizerBound060_stabilizer_block03 t r
  · exact g32p_centralizerBound060_stabilizer_block04 t r

theorem g32p_centralizerBound060_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 60}) ≤ g32p_literalCentralizer 60 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 60 g32p_centralizerBound060_points
    g32p_centralizerBound060_stabilizers ?_ g32p_centralizerBound060_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound060_point_mem i (g32p_centralizer_point_moments 60 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound061_points : Finset (Fin 240) :=
  {3, 6, 15, 36, 58, 82, 99, 123, 172, 207, 211, 235}

def g32p_centralizerBound061_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (1, 3), (12, 7), (20, 4), (24, 1), (26, 2)}

theorem g32p_centralizerBound061_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) := by
  decide +kernel

theorem g32p_centralizerBound061_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) := by
  decide +kernel

theorem g32p_centralizerBound061_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) := by
  decide +kernel

theorem g32p_centralizerBound061_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) := by
  decide +kernel

theorem g32p_centralizerBound061_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) := by
  decide +kernel

theorem g32p_centralizerBound061_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) := by
  decide +kernel

theorem g32p_centralizerBound061_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) := by
  decide +kernel

theorem g32p_centralizerBound061_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) := by
  decide +kernel

theorem g32p_centralizerBound061_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) := by
  decide +kernel

theorem g32p_centralizerBound061_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) := by
  decide +kernel

theorem g32p_centralizerBound061_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) := by
  decide +kernel

theorem g32p_centralizerBound061_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) := by
  decide +kernel

theorem g32p_centralizerBound061_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) := by
  decide +kernel

theorem g32p_centralizerBound061_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) := by
  decide +kernel

theorem g32p_centralizerBound061_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) := by
  decide +kernel

theorem g32p_centralizerBound061_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 61) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound061_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound061_point_block00 t
  · exact g32p_centralizerBound061_point_block01 t
  · exact g32p_centralizerBound061_point_block02 t
  · exact g32p_centralizerBound061_point_block03 t
  · exact g32p_centralizerBound061_point_block04 t
  · exact g32p_centralizerBound061_point_block05 t
  · exact g32p_centralizerBound061_point_block06 t
  · exact g32p_centralizerBound061_point_block07 t
  · exact g32p_centralizerBound061_point_block08 t
  · exact g32p_centralizerBound061_point_block09 t
  · exact g32p_centralizerBound061_point_block10 t
  · exact g32p_centralizerBound061_point_block11 t
  · exact g32p_centralizerBound061_point_block12 t
  · exact g32p_centralizerBound061_point_block13 t
  · exact g32p_centralizerBound061_point_block14 t

theorem g32p_centralizerBound061_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 61) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 61)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound061_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound061_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 61) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 61)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound061_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound061_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 61) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 61)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound061_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound061_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 61) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 61)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound061_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound061_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 61) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 61)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound061_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound061_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 61) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 61) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound061_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 61) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 61)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound061_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound061_stabilizer_block00 t r
  · exact g32p_centralizerBound061_stabilizer_block01 t r
  · exact g32p_centralizerBound061_stabilizer_block02 t r
  · exact g32p_centralizerBound061_stabilizer_block03 t r
  · exact g32p_centralizerBound061_stabilizer_block04 t r

theorem g32p_centralizerBound061_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 61}) ≤ g32p_literalCentralizer 61 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 61 g32p_centralizerBound061_points
    g32p_centralizerBound061_stabilizers ?_ g32p_centralizerBound061_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound061_point_mem i (g32p_centralizer_point_moments 61 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound062_points : Finset (Fin 240) :=
  {3, 6, 15, 29, 36, 51, 58, 85, 92, 99, 126, 135, 140, 175, 183, 188, 205, 222}

def g32p_centralizerBound062_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (24, 2), (53, 8)}

theorem g32p_centralizerBound062_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) := by
  decide +kernel

theorem g32p_centralizerBound062_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) := by
  decide +kernel

theorem g32p_centralizerBound062_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) := by
  decide +kernel

theorem g32p_centralizerBound062_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) := by
  decide +kernel

theorem g32p_centralizerBound062_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) := by
  decide +kernel

theorem g32p_centralizerBound062_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) := by
  decide +kernel

theorem g32p_centralizerBound062_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) := by
  decide +kernel

theorem g32p_centralizerBound062_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) := by
  decide +kernel

theorem g32p_centralizerBound062_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) := by
  decide +kernel

theorem g32p_centralizerBound062_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) := by
  decide +kernel

theorem g32p_centralizerBound062_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) := by
  decide +kernel

theorem g32p_centralizerBound062_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) := by
  decide +kernel

theorem g32p_centralizerBound062_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) := by
  decide +kernel

theorem g32p_centralizerBound062_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) := by
  decide +kernel

theorem g32p_centralizerBound062_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) := by
  decide +kernel

theorem g32p_centralizerBound062_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 62) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound062_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound062_point_block00 t
  · exact g32p_centralizerBound062_point_block01 t
  · exact g32p_centralizerBound062_point_block02 t
  · exact g32p_centralizerBound062_point_block03 t
  · exact g32p_centralizerBound062_point_block04 t
  · exact g32p_centralizerBound062_point_block05 t
  · exact g32p_centralizerBound062_point_block06 t
  · exact g32p_centralizerBound062_point_block07 t
  · exact g32p_centralizerBound062_point_block08 t
  · exact g32p_centralizerBound062_point_block09 t
  · exact g32p_centralizerBound062_point_block10 t
  · exact g32p_centralizerBound062_point_block11 t
  · exact g32p_centralizerBound062_point_block12 t
  · exact g32p_centralizerBound062_point_block13 t
  · exact g32p_centralizerBound062_point_block14 t

theorem g32p_centralizerBound062_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 62) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 62)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound062_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound062_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 62) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 62)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound062_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound062_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 62) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 62)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound062_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound062_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 62) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 62)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound062_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound062_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 62) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 62)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound062_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound062_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 62) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 62) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound062_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 62) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 62)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound062_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound062_stabilizer_block00 t r
  · exact g32p_centralizerBound062_stabilizer_block01 t r
  · exact g32p_centralizerBound062_stabilizer_block02 t r
  · exact g32p_centralizerBound062_stabilizer_block03 t r
  · exact g32p_centralizerBound062_stabilizer_block04 t r

theorem g32p_centralizerBound062_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 62}) ≤ g32p_literalCentralizer 62 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 62 g32p_centralizerBound062_points
    g32p_centralizerBound062_stabilizers ?_ g32p_centralizerBound062_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound062_point_mem i (g32p_centralizer_point_moments 62 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound063_points : Finset (Fin 240) :=
  {3, 6, 12, 13, 15, 21, 22, 30, 32, 33, 36, 43, 44, 52, 54, 55, 58, 65, 71, 73, 74, 79, 81, 84, 85, 93, 95, 96, 99, 106, 112, 114, 115, 120, 122, 125, 126, 136, 137, 140, 144, 145, 146, 155, 161, 163, 164, 169, 171, 174, 175, 184, 185, 188, 191, 192, 193, 198, 200, 203, 210, 212, 219, 220, 222, 225, 226, 228, 231, 234, 236, 237}

def g32p_centralizerBound063_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound063_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) := by
  decide +kernel

theorem g32p_centralizerBound063_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) := by
  decide +kernel

theorem g32p_centralizerBound063_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) := by
  decide +kernel

theorem g32p_centralizerBound063_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) := by
  decide +kernel

theorem g32p_centralizerBound063_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) := by
  decide +kernel

theorem g32p_centralizerBound063_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) := by
  decide +kernel

theorem g32p_centralizerBound063_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) := by
  decide +kernel

theorem g32p_centralizerBound063_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) := by
  decide +kernel

theorem g32p_centralizerBound063_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) := by
  decide +kernel

theorem g32p_centralizerBound063_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) := by
  decide +kernel

theorem g32p_centralizerBound063_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) := by
  decide +kernel

theorem g32p_centralizerBound063_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) := by
  decide +kernel

theorem g32p_centralizerBound063_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) := by
  decide +kernel

theorem g32p_centralizerBound063_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) := by
  decide +kernel

theorem g32p_centralizerBound063_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) := by
  decide +kernel

theorem g32p_centralizerBound063_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 63) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound063_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound063_point_block00 t
  · exact g32p_centralizerBound063_point_block01 t
  · exact g32p_centralizerBound063_point_block02 t
  · exact g32p_centralizerBound063_point_block03 t
  · exact g32p_centralizerBound063_point_block04 t
  · exact g32p_centralizerBound063_point_block05 t
  · exact g32p_centralizerBound063_point_block06 t
  · exact g32p_centralizerBound063_point_block07 t
  · exact g32p_centralizerBound063_point_block08 t
  · exact g32p_centralizerBound063_point_block09 t
  · exact g32p_centralizerBound063_point_block10 t
  · exact g32p_centralizerBound063_point_block11 t
  · exact g32p_centralizerBound063_point_block12 t
  · exact g32p_centralizerBound063_point_block13 t
  · exact g32p_centralizerBound063_point_block14 t

theorem g32p_centralizerBound063_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 63) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 63)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound063_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound063_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 63) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 63)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound063_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound063_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 63) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 63)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound063_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound063_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 63) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 63)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound063_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound063_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 63) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 63)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound063_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound063_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 63) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 63) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound063_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 63) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 63)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound063_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound063_stabilizer_block00 t r
  · exact g32p_centralizerBound063_stabilizer_block01 t r
  · exact g32p_centralizerBound063_stabilizer_block02 t r
  · exact g32p_centralizerBound063_stabilizer_block03 t r
  · exact g32p_centralizerBound063_stabilizer_block04 t r

theorem g32p_centralizerBound063_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 63}) ≤ g32p_literalCentralizer 63 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 63 g32p_centralizerBound063_points
    g32p_centralizerBound063_stabilizers ?_ g32p_centralizerBound063_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound063_point_mem i (g32p_centralizer_point_moments 63 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound064_points : Finset (Fin 240) :=
  {0, 1, 3, 4, 6, 7, 8, 13, 15, 16, 17, 22, 23, 27, 30, 32, 36, 38, 39, 44, 45, 49, 52, 54, 58, 60, 62, 66, 71, 74, 86, 90, 93, 95, 99, 101, 103, 107, 112, 115, 137, 150, 152, 156, 161, 164, 185, 220}

def g32p_centralizerBound064_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (18, 2), (22, 7), (24, 2), (30, 4), (36, 5), (53, 8), (63, 3), (68, 7)}

theorem g32p_centralizerBound064_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) := by
  decide +kernel

theorem g32p_centralizerBound064_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) := by
  decide +kernel

theorem g32p_centralizerBound064_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) := by
  decide +kernel

theorem g32p_centralizerBound064_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) := by
  decide +kernel

theorem g32p_centralizerBound064_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) := by
  decide +kernel

theorem g32p_centralizerBound064_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) := by
  decide +kernel

theorem g32p_centralizerBound064_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) := by
  decide +kernel

theorem g32p_centralizerBound064_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) := by
  decide +kernel

theorem g32p_centralizerBound064_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) := by
  decide +kernel

theorem g32p_centralizerBound064_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) := by
  decide +kernel

theorem g32p_centralizerBound064_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) := by
  decide +kernel

theorem g32p_centralizerBound064_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) := by
  decide +kernel

theorem g32p_centralizerBound064_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) := by
  decide +kernel

theorem g32p_centralizerBound064_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) := by
  decide +kernel

theorem g32p_centralizerBound064_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) := by
  decide +kernel

theorem g32p_centralizerBound064_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 64) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound064_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound064_point_block00 t
  · exact g32p_centralizerBound064_point_block01 t
  · exact g32p_centralizerBound064_point_block02 t
  · exact g32p_centralizerBound064_point_block03 t
  · exact g32p_centralizerBound064_point_block04 t
  · exact g32p_centralizerBound064_point_block05 t
  · exact g32p_centralizerBound064_point_block06 t
  · exact g32p_centralizerBound064_point_block07 t
  · exact g32p_centralizerBound064_point_block08 t
  · exact g32p_centralizerBound064_point_block09 t
  · exact g32p_centralizerBound064_point_block10 t
  · exact g32p_centralizerBound064_point_block11 t
  · exact g32p_centralizerBound064_point_block12 t
  · exact g32p_centralizerBound064_point_block13 t
  · exact g32p_centralizerBound064_point_block14 t

theorem g32p_centralizerBound064_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 64) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 64)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound064_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound064_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 64) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 64)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound064_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound064_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 64) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 64)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound064_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound064_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 64) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 64)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound064_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound064_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 64) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 64)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound064_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound064_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 64) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 64) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound064_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 64) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 64)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound064_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound064_stabilizer_block00 t r
  · exact g32p_centralizerBound064_stabilizer_block01 t r
  · exact g32p_centralizerBound064_stabilizer_block02 t r
  · exact g32p_centralizerBound064_stabilizer_block03 t r
  · exact g32p_centralizerBound064_stabilizer_block04 t r

theorem g32p_centralizerBound064_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 64}) ≤ g32p_literalCentralizer 64 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 64 g32p_centralizerBound064_points
    g32p_centralizerBound064_stabilizers ?_ g32p_centralizerBound064_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound064_point_mem i (g32p_centralizer_point_moments 64 x i hi.symm)

end HodgeLean.Foundations.Program

end
end
