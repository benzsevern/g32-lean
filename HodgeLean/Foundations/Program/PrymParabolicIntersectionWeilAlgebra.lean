import HodgeLean.Foundations.Program.PrymParabolicIntersectionDefs

noncomputable section
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

theorem hga_weil_scale_identity {K : Type*} [CommRing K] (s x y : K)
    (hs : s ^ 2 = -3) :
    s * (4 * (-6 * x - 2 * s * y)) = 24 * (y - s * x) := by
  linear_combination -8 * y * hs

theorem hga_cellWeil_swap
    (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root))
    (hB : ∀ x y : hg6_cellLattice, B x y = -B y x)
    (hJ : ∀ x y : hg6_cellLattice, B (hg6_cellOperator x) y = -B x (hg6_cellOperator y))
    (a b : hg6_cellLattice) :
    hga_cellWeil B b a = ((B a (hg6_cellOperator b) : ℤ) : hp_K) -
      QuadraticAlgebra.omega * ((B a b : ℤ) : hp_K) := by
  unfold hga_cellWeil
  rw [hB b (hg6_cellOperator a), hJ a b, hB b a]
  push_cast
  ring

theorem hga_isotypic_scale_of_coordinate_duality
    (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root))
    (hB : ∀ x y : hg6_cellLattice, B x y = -B y x)
    (hJ : ∀ x y : hg6_cellLattice, B (hg6_cellOperator x) y = -B x (hg6_cellOperator y))
    (c c' : hg_eqCocycles hg4_sigmaK b4b_root) (a b : hg6_cellLattice)
    (hcup : hg6_coordCup b4b_root 0 0 c.1 c'.1 =
      -6 * ((B a b : ℤ) : hp_K) -
        2 * QuadraticAlgebra.omega * ((B a (hg6_cellOperator b) : ℤ) : hp_K)) :
    (1 + 2 * pc_zeta) * hg4_cupForm b4b_root 1 c.1 c'.1 =
      (24 : hp_K) * hga_cellWeil B b a := by
  have hs := hg6_coordCup_schur c.1 c'.1 c.2.1 c'.2.1 0 0
  simp only [ite_true] at hs
  have hfull : hg4_cupForm b4b_root 1 c.1 c'.1 =
      4 * hg6_coordCup b4b_root 0 0 c.1 c'.1 := by
    have ht := congrArg (fun x : hp_K ↦ 4 * x) hs
    have h4 : (4 : hp_K) ≠ 0 := by norm_num
    simpa only [← mul_assoc, mul_inv_cancel₀ h4, one_mul] using ht.symm
  have hz : 1 + 2 * pc_zeta = (QuadraticAlgebra.omega : hp_K) := by
    dsimp only [pc_zeta]
    ring
  have hω : (QuadraticAlgebra.omega : hp_K) ^ 2 = -3 := by
    rw [sq]
    ext <;> simp <;> rfl
  rw [hz, hfull, hcup, hga_cellWeil_swap B hB hJ a b]
  exact hga_weil_scale_identity _ _ _ hω

theorem hga_cellIntersection_skew {C : Type} [TopologicalSpace C]
    (F : hg8_DeltaMap b4b_root C) (V : Set (Fin 10 → ℂ))
    (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (P : b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (hQ : b3_IsIntersectionForm ℂ Q) (a b : hg2_H1 ℤ b4b_root) :
    hga_cellIntersection F V hV t P Q b a = -hga_cellIntersection F V hV t P Q a b := by
  exact b3Rest_intersectionForm_skew (E := ℂ) (Module.finrank_self ℂ) Q hQ _ _

#print axioms hga_cellIntersection_skew
#print axioms hga_weil_scale_identity
#print axioms hga_cellWeil_swap
#print axioms hga_isotypic_scale_of_coordinate_duality

end HodgeLean.Foundations.Program
