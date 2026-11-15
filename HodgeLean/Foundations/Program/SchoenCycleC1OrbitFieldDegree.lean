import HodgeLean.Foundations.Program.SchoenCycleC1OrbitMeasuredFibres
import HodgeLean.Foundations.Program.SchoenCycleC1ActualFieldDegreeHelpers
import HodgeLean.Foundations.Program.SchoenGenericPointMorphisms

/-! # The actual generic degree of a faithful orbit projection -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Actual faithful deck maps and their complex orbit fibres determine the
field degree over the specified generic stalk embedding. -/
theorem s2e_c1_orbit_projection_actual_field_degree
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral Y.left] [IsLocallyNoetherian Y.left]
    (G : Type) [Group G] [Finite G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a) (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (horbit : ∀ x z : ComplexPoint X, Point.map q x = Point.map q z ↔
      ∃ u, Point.map (a u) x = z) :
    let hg := s2_dominant_genericPoint q.left
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
      q.left.stalkMap (genericPoint X.left)).hom
    letI := φ.toAlgebra
    Module.finrank Y.left.functionField X.left.functionField = Nat.card G := by
  exact s2e_c1_actual_fieldDegree_of_measured_fibres X Y q
    (s2_dominant_genericPoint q.left) (Nat.card G)
    (s2e_c1_orbit_fibres_measured_in_every_open X Y G a ha1 hamul hinj q hinv horbit)

end HodgeLean.Foundations.Program
