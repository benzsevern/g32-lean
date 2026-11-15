import HodgeLean.Foundations.Program.FiniteClosedMapSheaves
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainResolution
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveParacompact

/-! Rational quotient comparison from the original point-orbit interface. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Finite orbit fibres suffice for exact direct image and preservation of
the actual source singular-cochain resolution. -/
theorem s4_q3_orbit_pushforward_resolution
    (X W : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    (q : X ⟶ W) (hsurj : Function.Surjective (Point.map q))
    (I : Type) [Fintype I] (a : I → ComplexPoint X → ComplexPoint X)
    (horbit : ∀ x y, Point.map q x = Point.map q y → ∃ i, a i x = y) :
    QuasiIso (((TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.ofHom (Point.continuousMap q))).mapHomologicalComplex (.up ℕ)).map
      (constantsToSingularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X)))) := by
  have hfib : ∀ w, ((Point.map q) ⁻¹' {w}).Finite := by
    intro w
    obtain ⟨x, rfl⟩ := hsurj w
    apply (Set.finite_range (fun i : I => a i x)).subset
    intro y hy
    obtain ⟨i, hi⟩ := horbit x y (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hy.symm)
    exact ⟨i, hi⟩
  letI := finite_closedMap_pushforward_preservesHomology
    (TopCat.ofHom (Point.continuousMap q)) (Point.continuous_map q).isClosedMap hfib
  letI := AlgebraicGeometry.ComplexPoint.constantsToSingularCochain_quasiIso X ℚ
  letI : (TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.ofHom (Point.continuousMap q))).Additive := { map_add := by intros; rfl }
  infer_instance

end HodgeLean.Foundations.Program
