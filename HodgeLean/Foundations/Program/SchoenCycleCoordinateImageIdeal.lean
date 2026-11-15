import HodgeLean.Foundations.Program.SchoenCycleProjectiveCoordinateSubspace
import HodgeLean.Foundations.Program.SchoenCycleProjectiveReducedIdeals

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The coordinate immersion has the actual residue intersection as its image ideal.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_coordinateSubspaceInclusion_kernel (k : ℕ) (T : Finset (Fin (k + 1)))
    (hT : T.card ≤ k) :
    (s2e_coordinateSubspaceInclusion k T).ker = s2e_s2b_intersectionIdeal k T := by
  classical
  obtain ⟨e⟩ := s2e_retainedCoordinate_equiv k T hT
  obtain ⟨E⟩ := s2e_complexProjectiveSpace_iso_of_equiv e
  letI : IsReduced (ProjectiveSpace (Fin (k - T.card + 1)) (Spec ↧ℂ)) :=
    s2e_complexProjectiveSpace_reduced (k - T.card)
  letI : IsReduced (ProjectiveSpace {j : Fin (k + 1) // j ∉ T} (Spec ↧ℂ)) :=
    isReduced_of_isOpenImmersion E.hom
  let f := s2e_coordinateSubspaceInclusion k T
  letI : IsClosedImmersion f := s2e_coordinateSubspaceInclusion_isClosedImmersion k T
  have hrad := s2e_kernel_radical_of_reduced f
  have hs : f.ker.support = (s2e_s2b_intersectionIdeal k T).support := by
    apply TopologicalSpace.Closeds.ext
    rw [Scheme.Hom.support_ker]
    change closure (Set.range (s2e_coordinateSubspaceInclusion k T)) = _
    rw [s2e_coordinateSubspaceInclusion_range]
    exact (s2e_s2b_intersectionIdeal k T).support.isClosed.closure_eq
  calc
    f.ker = Scheme.IdealSheafData.vanishingIdeal f.ker.support :=
      (Scheme.IdealSheafData.vanishingIdeal_support.trans hrad).symm
    _ = Scheme.IdealSheafData.vanishingIdeal (s2e_s2b_intersectionIdeal k T).support :=
      congrArg Scheme.IdealSheafData.vanishingIdeal hs
    _ = s2e_s2b_intersectionIdeal k T :=
      Scheme.IdealSheafData.vanishingIdeal_support.trans (s2e_residue_intersection_radical k T)

end HodgeLean.Foundations.Program
