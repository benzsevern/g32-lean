import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Defs
import HodgeLean.Foundations.Program.SchoenCycleC11Pre

/-! # Topology of finite étale inverse images

HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Topology
namespace AlgebraicGeometry.SingularCycles

/-- Finite étale maps have local continuous inverses even over singular ambients.
Source: SGA 1, Exposé XII, Théorème 5.1;
s2e_c11_finite_etale_analytic_cover. -/
theorem finite_etale_local_homeomorph {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Z.hom]
    (f : X ⟶ Z) [IsFinite f.left] [Etale f.left] :
    IsLocalHomeomorph (Point.map f) :=
  (HodgeLean.Foundations.Program.s2e_c11_finite_etale_analytic_cover X Z f).1.isLocalHomeomorph

end AlgebraicGeometry.SingularCycles
