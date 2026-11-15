import HodgeLean.Foundations.AnalyticAlbanese.Basic
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.Defs
import HodgeLean.Foundations.Program.RelativeTorusAbelian

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Manifold
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.AnalyticAlbanese
open scoped Manifold ContDiff TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local irreducible] b2_abelianToPoint b2_abelianF b3_periodF b3_periodLattice

/-- A pointed algebraic curve map has an additive holomorphic factor through its actual period Jacobian. -/
theorem s4_selected_analytic_abel_factor
    (X A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [ConnectedSpace (ComplexPoint X)]
    (h : Module.finrank ℂ (Fin (TopologicalSpace.dim X.left) → ℂ) = 1)
    (p : ComplexPoint X) (f : X ⟶ A) (hp : Point.map f p = 1) :
    let E := Fin (TopologicalSpace.dim X.left) → ℂ
    letI := b3_periodLattice_finite (C := ComplexPoint X) h
    letI := b2_latticeMap_discrete (b3_periodF E (ComplexPoint X)) (b3_isWeightOne h)
    ∃ H : b3_Jacobian E (ComplexPoint X) →+ Additive (ComplexPoint A),
      ContMDiff 𝓘(ℂ, b5_V (b3_periodLattice E (ComplexPoint X))
          (b3_periodF E (ComplexPoint X)))
        𝓘(ℂ, Fin (TopologicalSpace.dim A.left) → ℂ) ω
        (fun z => Additive.toMul (H z)) ∧
      ∀ x, H (analyticAbel h p x) = Additive.ofMul (Point.map f x) := by
  let E := Fin (TopologicalSpace.dim X.left) → ℂ
  let C := ComplexPoint X
  let Λ := b3_periodLattice E C
  let F := b3_periodF E C
  let Μ := b2_abelianLattice A
  let G := b2_abelianF A
  letI := b3_periodLattice_finite (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  letI := b2_latticeMap_discrete F (b3_isWeightOne h)
  letI := b2_latticeMap_discrete G (b2_abelianF_isWeightOne A)
  let e := Equiv.ofBijective (b2_abelianToPoint A) (b2_abelianToPoint_bijective A)
  let fT : C → b2_torus Μ G := fun x => e.symm (Additive.ofMul (Point.map f x))
  have hfT : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, b5_V Μ G) ω fT :=
    (b2_abelianToPoint_symm_contMDiff A).comp
      (spec_contMDiff_pointMap X A (TopologicalSpace.dim X.left)
        (TopologicalSpace.dim A.left) f)
  have hpT : fT p = 0 := by
    change e.symm (Additive.ofMul (Point.map f p)) = 0
    rw [hp]
    apply e.injective
    rw [e.apply_symm_apply]
    exact (map_zero (b2_abelianToPoint A)).symm
  letI : Module.Finite ℤ Μ := inferInstance
  letI : Module.Free ℤ Μ := inferInstance
  let L := coordinateLift G fT hfT
  have hL := coordinateLift_lattice G fT hfT
  have hfactor := factor_evaluation_of_paths E C Μ G p fT hpT
    (analyticAbel h p) (b3_exists_abelJacobi h p).choose_spec L hL
    (coordinateLift_increment G fT hfT)
  refine ⟨(b2_abelianToPoint A).comp (descend F G L hL), ?_, ?_⟩
  · exact (b2_abelianToPoint_contMDiff A).comp
      (descent_holomorphic Λ Μ F G L hL).1
  · intro x
    change b2_abelianToPoint A (descend F G L hL (analyticAbel h p x)) = _
    rw [hfactor x]
    exact e.apply_symm_apply _

#print axioms s4_selected_analytic_abel_factor

end HodgeLean.Foundations.Program
