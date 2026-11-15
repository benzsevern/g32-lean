import HodgeLean.Foundations.Program.SchoenCycleC1ComplexOrbitKummerEigenfunction
import HodgeLean.Foundations.Program.SchoenCycleC1CyclicComplexCharacter
import HodgeLean.Foundations.Program.SchoenCycleC1CyclicRationalEigencharacter

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A faithful cyclic orbit projection constructs its original rational
Kummer coordinate and descended coefficient together with every action
eigenidentity for a faithful complex character. -/
theorem s2e_c1_cyclic_orbit_kummer_character
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral Y.left] [IsLocallyNoetherian Y.left] [LocallyOfFiniteType Y.hom]
    (G : Type) [Group G] [Finite G] [IsCyclic G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a) (q : X ⟶ Y) [IsFinite q.left] (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (horbit : ∀ x z : ComplexPoint X, Point.map q x = Point.map q z ↔
      ∃ u, Point.map (a u) x = z)
 :
    letI : Surjective q.left := s2e_c11_surjective_of_point_surjective X Y q hsurj
    let hgen := s2_dominant_genericPoint q.left
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hgen.symm) ≫
      q.left.stalkMap (genericPoint X.left)).hom
    ∃ χ : G →* ℂˣ, Function.Injective χ ∧
      ∃ (z : X.left.functionField) (f : Y.left.functionField),
        z ≠ 0 ∧ f ≠ 0 ∧ z ^ Nat.card G = φ f ∧
        ∀ u : G, letI := s2e_step1_action_isIso X G a ha1 hamul u
          s2e_step1_fieldPullback X.left (a u).left z =
            HodgeLean.Foundations.Curves.stalkC (genericPoint X.left) (χ u : ℂ) * z := by
  letI : Surjective q.left := s2e_c11_surjective_of_point_surjective X Y q hsurj
  obtain ⟨χ, g, hχ, hg, hη⟩ := s2e_c1_cyclic_complex_character G
  obtain ⟨z, f, hz, hf, hp, he⟩ := s2e_c1_complex_orbit_kummer_eigenfunction
    X Y G a ha1 hamul hinj q hsurj hinv horbit g hg (χ g : ℂ) hη
  exact ⟨χ, hχ, z, f, hz, hf, hp,
    s2e_c1_cyclic_rational_eigencharacter X G a ha1 hamul g hg χ z he⟩

end HodgeLean.Foundations.Program
