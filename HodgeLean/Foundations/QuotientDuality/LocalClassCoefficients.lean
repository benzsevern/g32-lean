import HodgeLean.Foundations.QuotientDuality.IntegralCoefficients
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceLocalReduction

/-! Coefficient transport for the actual two-dimensional local image cycles. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

theorem integralCoefficient_localImageChain (P : TopPair.{0})
    (F : puncturedPair ℝ 2 ⟶ P) (R : Type) [CommRing R] :
    integralCoefficient P.fst R 2 (b6m_localImageChain ℤ P F) =
      b6m_localImageChain R P F := by
  unfold b6m_localImageChain
  rw [integralCoefficient_map]
  have h := integralCoefficient_iota (puncturedPair ℝ 2).fst R 2
    (standardSingularSimplex 2) 1
  simp only [Int.cast_one] at h
  change integralCoefficient (puncturedPair ℝ 2).fst R 2
    ((standardAmbientSimplexChain ℤ 2).hom 1) =
      (standardAmbientSimplexChain R 2).hom 1 at h
  rw [h]

theorem localImage_neg_of_integral (P : TopPair.{0})
    (F G : puncturedPair ℝ 2 ⟶ P) (R : Type) [CommRing R]
    (h : relativeHomologyMap ℤ 2 F (standardLocalClass ℤ 2) =
      -relativeHomologyMap ℤ 2 G (standardLocalClass ℤ 2)) :
    relativeHomologyMap R 2 F (standardLocalClass R 2) =
      -relativeHomologyMap R 2 G (standardLocalClass R 2) := by
  have heq := relative_integralCoefficient_preserves_eq P R 2
    (b6m_localImageCycle ℤ P F) (-b6m_localImageCycle ℤ P G)
    (b6m_localImageCycle R P F) (-b6m_localImageCycle R P G)
    (b6m_localImageChain ℤ P F) (-b6m_localImageChain ℤ P G)
    (b6m_localImageCycle_inclusion ℤ P F).symm
    (by rw [map_neg, map_neg, b6m_localImageCycle_inclusion])
    (by rw [integralCoefficient_localImageChain];
        exact (b6m_localImageCycle_inclusion R P F).symm)
    (by rw [map_neg, map_neg, map_neg, integralCoefficient_localImageChain,
          b6m_localImageCycle_inclusion])
    (by rw [map_neg, b6m_localImageCycle_class, b6m_localImageCycle_class]; exact h)
  rw [map_neg, b6m_localImageCycle_class, b6m_localImageCycle_class] at heq
  exact heq

theorem surface_local_neg_of_integral {M : Type} [TopologicalSpace M]
    [ChartedSpace ℂ M] (x y : M)
    (F : pointComplementPair x ⟶ pointComplementPair y)
    (h : relativeHomologyMap ℤ 2 F (b6m_surfaceLocalClass ℤ x) =
      -b6m_surfaceLocalClass ℤ y) :
    relativeHomologyMap ℚ 2 F (b6m_surfaceLocalClass ℚ x) =
      -b6m_surfaceLocalClass ℚ y := by
  have hi : relativeHomologyMap ℤ 2 (b6m_surfaceLocalPairMap x ≫ F)
      (standardLocalClass ℤ 2) =
      -relativeHomologyMap ℤ 2 (b6m_surfaceLocalPairMap y) (standardLocalClass ℤ 2) := by
    rw [relativeHomologyMap_comp, LinearMap.comp_apply,
      ← b6m_surfaceLocalClass_eq_image, ← b6m_surfaceLocalClass_eq_image]
    exact h
  have hq := localImage_neg_of_integral (pointComplementPair y)
    (b6m_surfaceLocalPairMap x ≫ F) (b6m_surfaceLocalPairMap y) ℚ hi
  rw [relativeHomologyMap_comp, LinearMap.comp_apply,
    ← b6m_surfaceLocalClass_eq_image, ← b6m_surfaceLocalClass_eq_image] at hq
  exact hq

#print axioms surface_local_neg_of_integral
end HodgeLean.Foundations.QuotientDuality
