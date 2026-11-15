import HodgeLean.Foundations.Program.G32Native.TensorSectionRestriction
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheafPolynomialSections

/-! Coordinate transitions of normalized twisted sections. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.ProjSpace
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The normalized coefficients of a global twisted section have the powered coordinate transition. -/
theorem g32l4_twisted_coefficient_transition (R : Type) [CommRing R] (n d : ℕ)
    (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    (t : Γ(F ⊗ (twistingSheaf R n).tensorPow d, ⊤))
    (i j : Fin (n + 1)) (W : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Opens)
    (hi : W ≤ standardOpen R n i) (hj : W ≤ standardOpen R n j)
    (m : Γ(F, standardOpen R n i)) (m' : Γ(F, standardOpen R n j))
    (h : (F ⊗ (twistingSheaf R n).tensorPow d).presheaf.map (homOfLE le_top).op t =
      tensorSections m (((twistingSheaf R n).tensorPow d).presheaf.map
        (homOfLE le_top).op (tensorPowSection (twistingCoordinateSection R n i) d)))
    (h' : (F ⊗ (twistingSheaf R n).tensorPow d).presheaf.map (homOfLE le_top).op t =
      tensorSections m' (((twistingSheaf R n).tensorPow d).presheaf.map
        (homOfLE le_top).op (tensorPowSection (twistingCoordinateSection R n j) d))) :
    F.presheaf.map (homOfLE hi).op m =
      (GlueOfCocycle.rO hi (coordinateRatioSection R n i j)) ^ d •
        F.presheaf.map (homOfLE hj).op m' := by
  let L := (twistingSheaf R n).tensorPow d
  let s := tensorPowSection (twistingCoordinateSection R n i) d
  let s' := tensorPowSection (twistingCoordinateSection R n j) d
  have res_res (z : Γ(L, ⊤)) :
      L.presheaf.map (homOfLE hi).op
        (L.presheaf.map (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op z) =
      L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op z := by
    change (L.presheaf.map (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op ≫
      L.presheaf.map (homOfLE hi).op).hom z = _
    rw [← Functor.map_comp]
    rfl
  have hframe := congrArg (fun z => L.presheaf.map (homOfLE hi).op z)
    (coordinateRatioSection_pow_smul_twistingCoordinateSection R n d i j)
  change L.presheaf.map (homOfLE hi).op
      (coordinateRatioSection R n i j ^ d • L.presheaf.map (homOfLE le_top).op s) =
    L.presheaf.map (homOfLE hi).op (L.presheaf.map (homOfLE le_top).op s') at hframe
  rw [L.map_smul, map_pow, res_res, res_res] at hframe
  apply g32l4_tensor_frame_coefficients_proportional F L W s
    (((isFrameOn_twistingCoordinateSection R n i).tensorPowSection_monoidalV2 d).mono hi)
    _ _ _ _ hframe.symm
  exact (g32l4_tensor_section_restriction F L hi t s m h).symm.trans
    (g32l4_tensor_section_restriction F L hj t s' m' h')

end HodgeLean.Foundations.Program
