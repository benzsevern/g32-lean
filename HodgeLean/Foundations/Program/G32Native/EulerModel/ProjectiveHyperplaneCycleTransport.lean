import HodgeLean.Foundations.Program.G32Native.EulerModel.CoordinateHyperplaneModels
import HodgeLean.Foundations.Program.G32Native.EulerModel.ProjectiveCoordinateOpens
import HodgeLean.Foundations.Program.SchoenCycleC2SupportHelpers
import HodgeLean.Adapters.IntersectionProductScaf

/-! # Exact component cycles of actual permuted coordinate hyperplanes -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified actual coordinate permutation retains the integral hyperplanes and their exact coefficient-one component cycles. -/
theorem projectiveCoordinateHyperplane_componentCycle (k : ℕ) (hk : 0 < k)
    (e : Equiv.Perm (Fin (k + 1))) (j : Fin (k + 1)) :
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    let I := s2e_s2b_residueIdeal k (e.symm j)
    let J := s2e_s2b_residueIdeal k j
    ∃ (hI : IsIntegral (s2c_subscheme PP I).left),
      letI := hI
      ∃ (hJ : IsIntegral (s2c_subscheme PP J).left),
        letI := hJ
        s2e_componentCycle (s2c_subschemeι PP I ≫ (complexProjectiveCoordinateIso e).hom) ℚ =
          s2e_componentCycle (s2c_subschemeι PP J) ℚ := by
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  let I := s2e_s2b_residueIdeal k (e.symm j)
  let J := s2e_s2b_residueIdeal k j
  obtain ⟨EI⟩ := residue_hyperplane_projective_model k hk (e.symm j)
  obtain ⟨EJ⟩ := residue_hyperplane_projective_model k hk j
  let MP := Over.mk (ProjectiveSpace.toBase (Fin (k - 1 + 1)) (Spec ↧ℂ))
  letI : IsIntegral MP.left := IntersectionProductScaf_projective_integral (k - 1)
  letI hI : IsIntegral (s2c_subscheme PP I).left := IsIntegral.of_isIso EI.inv.left
  letI hJ : IsIntegral (s2c_subscheme PP J).left := IsIntegral.of_isIso EJ.inv.left
  refine ⟨hI, hJ, ?_⟩
  let f := s2c_subschemeι PP I ≫ (complexProjectiveCoordinateIso e).hom
  let g := s2c_subschemeι PP J
  letI : IsClosedImmersion f.left := by
    change IsClosedImmersion (I.subschemeι ≫ (complexProjectiveCoordinateIso e).hom.left)
    infer_instance
  letI : IsClosedImmersion g.left := inferInstanceAs (IsClosedImmersion J.subschemeι)
  have hrange : Set.range f.left = Set.range g.left := by
    change Set.range ((complexProjectiveCoordinateIso e).hom.left ∘ I.subschemeι) =
      Set.range J.subschemeι
    rw [Set.range_comp, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.range_subschemeι]
    exact complexProjectiveCoordinateIso_hyperplane_image k e j
  have hp : f.left (genericPoint (s2c_subscheme PP I).left) =
      g.left (genericPoint (s2c_subscheme PP J).left) :=
    IsGenericPoint.eq (s2e_componentCycle_closure f)
      ((s2e_componentCycle_closure g).trans hrange.symm)
  change s2e_componentCycle f ℚ = s2e_componentCycle g ℚ
  simp only [s2e_componentCycle, hp]

#print axioms projectiveCoordinateHyperplane_componentCycle
end HodgeLean.Foundations.Program.G32Native.EulerModel
