import HodgeLean.Foundations.Program.SchoenSegrePowerGluing
import HodgeLean.Foundations.Program.SchoenSegrePowerChartRanges
import HodgeLean.Foundations.Program.SchoenSegrePowerChartSurjectivity
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Projective

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual finite-factor Segre morphism has exactly the expected target coordinate-open preimages. -/
theorem s2_segrePowerMap_preimage_basicOpen (d n : ℕ) (a : Fin n → Fin (d + 1)) :
    s2_segrePowerMap d n ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin n → Fin (d + 1)) (ULift.{0} ℤ)) (X a) =
        (s2_segrePowerChartι d n a).opensRange := by
  ext x
  obtain ⟨b, y, rfl⟩ := s2_segrePowerChart_covers d n x
  rw [SetLike.mem_coe, SetLike.mem_coe, ← Scheme.Hom.mem_preimage, ← Scheme.Hom.mem_preimage,
    ← Scheme.Hom.comp_preimage, s2_segrePowerChartι_map, s2_segrePowerChartMap,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ zero_lt_one (isHomogeneous_X _ a),
    s2_segrePowerChartι_preimage_opensRange]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual finite-factor integral Segre morphism is a scheme closed immersion. -/
theorem s2_segrePowerMap_isClosedImmersion (d n : ℕ) :
    IsClosedImmersion (s2_segrePowerMap d n) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _
    (Proj.iSup_basicOpen_eq_top _ _ (b54_polynomial_irrelevant_le_variables
      (Fin n → Fin (d + 1)) (ULift.{0} ℤ)))]
  intro a
  refine g3c_isClosedImmersion_morphismRestrict_of_opensRange (s2_segrePowerMap d n) _
    (s2_segrePowerChartι d n a) (s2_segrePowerMap_preimage_basicOpen d n a).symm ?_
  rw [s2_segrePowerChartι_map]
  exact s2_segrePowerChartMap_restrict_isClosedImmersion d n a

end HodgeLean.Foundations.Program
