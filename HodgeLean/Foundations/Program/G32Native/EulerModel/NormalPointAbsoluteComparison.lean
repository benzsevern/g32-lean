import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalPointClassNormalization
import HodgeLean.Foundations.Program.G32Native.EulerModel.CoordinateCohomology
import HodgeLean.Foundations.Program.G32Native.EulerModel.ComponentComparison

/-! # The normalized projective point and its actual canonical coordinate class -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual normalized coordinate-point coclass has the same absolute singular comparison as the canonical coordinate cycle class. -/
theorem normalComponentPointCoclass_absolute_comparison
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left] :
    singularToFieldCohomology ℚ Q (2 * k)
      (s2e_classToAbsolute Q (s2e_componentCycle (s2c_subschemeι Q
        ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) k
          (normalComponentPointCoclass k eQ)) =
    coordinate_class_at_degree Q k eQ (Finset.univ.erase 0) (by simp) k (by simp) := by
  classical
  let T : Finset (Fin (k + 1)) := Finset.univ.erase 0
  have hcard : T.card = k := by simp [T]
  have hbound : T.card ≤ k := hcard.le
  obtain ⟨_, _, hcod, _⟩ := coordinate_intersection_class Q k eQ T hbound
  have hc : Order.coheight
      ((s2c_subschemeι Q ((s2e_s2b_intersectionIdeal k T).comap eQ.hom.left)).left
        (genericPoint (s2c_subscheme Q ((s2e_s2b_intersectionIdeal k T).comap eQ.hom.left)).left)) = k :=
    by simpa only [hcard] using hcod
  rw [coordinate_class_at_degree_eq Q k eQ T hbound k hcard hc]
  exact normalized_component_class_comparison _ k hc _
    (normalComponentPointCoclass_isCycleClass Q k eQ)

#print axioms normalComponentPointCoclass_absolute_comparison
/-- The actual local kernel-section sign transfers to the canonical coordinate-point class on the specified component. -/
theorem normalKernelSection_coordinate_class_sign
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left] :
    singularToFieldCohomology ℚ Q (2 * k)
      (s2e_classToAbsolute Q (s2e_componentCycle (s2c_subschemeι Q
        ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) k
        (relativeCohomologyMap ℚ (2 * k) (normalComponentPointPairIso k eQ).inv
          ((normalProjectivePointExcisionEquiv k (2 * k)).symm
            (relativeCohomologyMap ℚ (2 * k) (normalKernelLocalSectionPairMap k)
              (normalKernelLocalThomClass k))))) =
      (-1 : ℚ) ^ k • coordinate_class_at_degree Q k eQ
        (Finset.univ.erase 0) (by simp) k (by simp) := by
  rw [normalKernelLocalThomClass_global_sign k, map_smul, map_smul,
    spec_singularToFieldCohomology_smul]
  change (-1 : ℚ) ^ k • singularToFieldCohomology ℚ Q (2 * k)
    (s2e_classToAbsolute Q _ k (normalComponentPointCoclass k eQ)) = _
  rw [normalComponentPointCoclass_absolute_comparison Q k eQ]

#print axioms normalKernelSection_coordinate_class_sign
end HodgeLean.Foundations.Program.G32Native.EulerModel
