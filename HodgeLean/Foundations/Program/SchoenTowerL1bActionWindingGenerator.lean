import HodgeLean.Foundations.Program.SchoenTowerL1bActionCircleLift
import HodgeLean.Foundations.Program.SchoenTowerL1bActionBoundary
import HodgeLean.Foundations.Program.SchoenTowerL1bActionLocalSign

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The boundary of the plane's integral local class generates integral
homology of its punctured complement. -/
theorem s2v_l1b_action_plane_boundary_generator :
    Function.Bijective (fun k : ℤ => k •
      (b6m_relativeSingularBoundary ℤ (pointComplementPair (0 : ℂ)) 1).hom
        (b6m_surfaceLocalClass ℤ (0 : ℂ))) := by
  letI : ContractibleSpace (pointComplementPair (0 : ℂ)).fst := by
    change ContractibleSpace ℂ
    infer_instance
  let e := (s2v_l1b_action_contractible_boundary_iso ℤ
    (pointComplementPair (0 : ℂ))).toLinearEquiv
  have hs : Function.Bijective (fun k : ℤ => k • b6m_surfaceLocalClass ℤ (0 : ℂ)) := by
    convert b6m_surfaceLocalClass_smul_bijective ℤ (0 : ℂ) using 1
    funext k
    exact (Int.cast_smul_eq_zsmul ℤ k _).symm
  have h := e.bijective.comp hs
  change Function.Bijective (fun k : ℤ => k • e (b6m_surfaceLocalClass ℤ (0 : ℂ)))
  simpa only [Function.comp_def, map_zsmul] using h

end HodgeLean.Foundations.Program
