import HodgeLean.Foundations.Program.SchoenCycleC1OrbitKummerEigenfunction
import HodgeLean.Foundations.Program.SchoenCycleC1RationalPullbackScalars
import HodgeLean.Foundations.Program.SchoenCycleC1GenericLocalFieldSquare
import HodgeLean.Foundations.Program.SchoenCycleC11SchemeHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The actual cyclic curve projection supplies a nonzero rational
eigenfunction with any prescribed primitive complex eigenvalue and retains
its original descended coefficient and generic stalk equation. -/
theorem s2e_c1_complex_orbit_kummer_eigenfunction
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral Y.left] [IsLocallyNoetherian Y.left] [LocallyOfFiniteType Y.hom]
    (G : Type) [Group G] [Finite G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a) (q : X ⟶ Y) [IsFinite q.left] (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (horbit : ∀ x z : ComplexPoint X, Point.map q x = Point.map q z ↔
      ∃ u, Point.map (a u) x = z)
    (g : G) (hg : orderOf g = Nat.card G)

    (η : ℂ) (hη : IsPrimitiveRoot η (Nat.card G)) :
    letI : Surjective q.left := s2e_c11_surjective_of_point_surjective X Y q hsurj
    let hgen := s2_dominant_genericPoint q.left
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hgen.symm) ≫
      q.left.stalkMap (genericPoint X.left)).hom
    letI := s2e_step1_action_isIso X G a ha1 hamul g
    ∃ (z : X.left.functionField) (f : Y.left.functionField),
      z ≠ 0 ∧ f ≠ 0 ∧ z ^ Nat.card G = φ f ∧
      s2e_step1_fieldPullback X.left (a g).left z =
        HodgeLean.Foundations.Curves.stalkC (genericPoint X.left) η * z := by
  letI : Surjective q.left := s2e_c11_surjective_of_point_surjective X Y q hsurj
  let hgen := s2_dominant_genericPoint q.left
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hgen.symm) ≫
    q.left.stalkMap (genericPoint X.left)).hom
  letI := s2e_step1_action_isIso X G a ha1 hamul g
  let C := HodgeLean.Foundations.Curves.stalkC (genericPoint Y.left)
  have hη' : IsPrimitiveRoot (C η) (Nat.card G) := hη.map_of_injective C.injective
  obtain ⟨z, f, hz, hf, hp, he⟩ := s2e_c1_orbit_kummer_eigenfunction
    X Y G a ha1 hamul hinj q hinv horbit g hg (C η) hη'
  refine ⟨z, f, hz, hf, hp, ?_⟩
  have hC := s2e_c1_rational_pullback_complex_scalars X Y q φ
    (s2e_c1_generic_stalk_map_local_square q.left hgen) η
  exact he.trans (congrArg (fun c => c * z) hC)

end HodgeLean.Foundations.Program
