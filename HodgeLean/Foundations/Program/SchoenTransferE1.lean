import HodgeLean.Foundations.Program.SchoenTransferE1Proofs

/-! Implication from the explicit curve, coordinate action and primitive-kernel data
to the ordered Künneth and equal-character interfaces.
Determinant transport, rational comparison and algebraic cycles belong to later units.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct DirectSum BigOperators CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program
/-- Primitive characters are absent in degrees zero and two.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemmas 1.1–1.2, pp. 5–6; Hatcher, Algebraic Topology, §3.2. -/
theorem s4_e1_curve_extremes (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (δ : Y ⟶ Y) [IsIso δ] (m : ℕ) (hm : 3 ≤ m) :
    LinearMap.ker (Polynomial.aeval (homPullback δ 0) (Polynomial.cyclotomic m ℚ)) = ⊥ ∧
      LinearMap.ker (Polynomial.aeval (homPullback δ 2) (Polynomial.cyclotomic m ℚ)) = ⊥ :=
  s4_e1_curve_extremes_aux Y hdim δ m hm

example := @s4_e1_curve_extremes

/-- The ordered projection cup maps give the full curve-power decomposition.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemmas 1.1–1.2, pp. 5–6; Hatcher, Algebraic Topology, §3.2. -/
theorem s4_e1_power_kunneth (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] (n : ℕ) :
    Function.Bijective (s4_e1_kunneth Y h n) :=
  s4_e1_power_kunneth_aux Y hdim h n

example := @s4_e1_power_kunneth

/-- Deck equivariance uses the specified coordinate squares and actual cup maps.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemmas 1.1–1.2, pp. 5–6; Hatcher, Algebraic Topology, §3.2. -/
theorem s4_e1_coordinate_naturality (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] (u : g3_power Y h ⟶ g3_power Y h)
    (b : Fin h → (Y ⟶ Y))
    (hu : ∀ i, u ≫ g3_proj Y h i = g3_proj Y h i ≫ b i)
    (d : Fin h → ℕ) :
    (homPullback u (∑ i, d i)).comp
      (s4_e1_orderedCup Y (g3_power Y h) h d (g3_proj Y h)) =
      s4_e1_orderedCup Y (g3_power Y h) h d
        (fun i => g3_proj Y h i ≫ b i) :=
  s4_e1_coordinate_naturality_aux Y hdim h u b hu d

example := @s4_e1_coordinate_naturality

/-- The primitive invariant subspace lies in the actual all-degree-one image.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemmas 1.1–1.2, pp. 5–6; Hatcher, Algebraic Topology, §3.2. -/
theorem s4_e1_primitive_degree_one (S : g32p_Supplier) (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] (hh : 0 < h)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v) :
    s4_invariantPrimitive S Y a e h hh ≤ LinearMap.range (s4_e1_oneCup Y h) :=
  s4_e1_primitive_degree_one_aux S Y hdim h hh a e ha1 hamul

example := @s4_e1_primitive_degree_one

/-- Annihilating all sum-zero tuples forces equality of the characters.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemmas 1.1–1.2, pp. 5–6; Hatcher, Algebraic Topology, §3.2. -/
theorem s4_e1_equal_characters (m h : ℕ) (hm : 3 ≤ m) (hh : 0 < h)
    (c : Fin h → ZMod m) :
    (∀ v : Fin h → ZMod m, (∑ i, v i) = 0 → (∑ i, c i * v i) = 0) ↔
      ∃ a : ZMod m, ∀ i, c i = a :=
  s4_e1_equal_characters_aux m h hm hh c

example := @s4_e1_equal_characters

/-- Geometric permutations act with the odd-degree Koszul sign.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemmas 1.1–1.2, pp. 5–6; Hatcher, Algebraic Topology, §3.2. -/
theorem s4_e1_permutation_cup (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] (σ : Equiv.Perm (Fin h)) (v : Fin h → HQ Y 1) :
    homPullback (s2_permute Y h σ) h
      (s4_e1_oneCup Y h (PiTensorProduct.tprod ℚ v)) =
      (((σ.sign : ℤˣ) : ℤ) : ℚ) •
        s4_e1_oneCup Y h (PiTensorProduct.tprod ℚ (fun i => v (σ i))) :=
  s4_e1_permutation_cup_aux Y hdim h σ v

example := @s4_e1_permutation_cup

end HodgeLean.Foundations.Program
