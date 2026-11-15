import HodgeLean.Foundations.Program.SchoenTowerL1bPrimeTransform

/-! Affine calculations for the retained reduced transforms.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An affine chart identifies the actual support with the zero locus of its section ideal. -/
theorem s2v_l1b_affine_support_preimage {X : Scheme} (D : X.IdealSheafData)
    (U : X.affineOpens) :
    U.2.fromSpec ⁻¹' (D.support : Set X) =
      PrimeSpectrum.zeroLocus (D.ideal U : Set Γ(X, U)) := by
  apply U.2.fromSpec.isOpenEmbedding.injective.image_injective
  rw [Set.image_preimage_eq_inter_range, IsAffineOpen.range_fromSpec,
    IsAffineOpen.fromSpec_image_zeroLocus, Scheme.IdealSheafData.coe_support_inter]

end HodgeLean.Foundations.Program
