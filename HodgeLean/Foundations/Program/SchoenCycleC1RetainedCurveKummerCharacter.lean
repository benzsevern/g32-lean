import HodgeLean.Foundations.Program.SchoenCycleC1CyclicOrbitKummerCharacter
import HodgeLean.Foundations.Program.SchoenCycleRetainedAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The original supplier curve action constructs a faithful character in
the specified cyclic coordinates, a nonzero rational eigenfunction, and its
actual downstairs coefficient with the original covering degree. -/
theorem s2e_c1_retained_curve_kummer_character
    (S : g32p_Supplier) (Y Z : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p : Y ⟶ Z) [IsFinite p.left]
    (hsurj : Function.Surjective (Point.map p))
    (hinv : ∀ u, a u ≫ p = p)
    (horbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y) :
    letI : Surjective p.left := s2e_c11_surjective_of_point_surjective Y Z p hsurj
    let hg := s2_dominant_genericPoint p.left
    let φ := (eqToHom (congrArg Z.left.presheaf.stalk hg.symm) ≫
      p.left.stalkMap (genericPoint Y.left)).hom
    ∃ χ : Multiplicative (ZMod S.m) →* ℂˣ, Function.Injective χ ∧
      ∃ (z : Y.left.functionField) (f : Z.left.functionField),
        z ≠ 0 ∧ f ≠ 0 ∧ z ^ S.m = φ f ∧
        ∀ t : ZMod S.m,
          letI := s2e_step1_action_isIso Y (S.H ⧸ S.χ.ker) a ha1 hamul (e.symm (.ofAdd t))
          s2e_step1_fieldPullback Y.left (a (e.symm (.ofAdd t))).left z =
            HodgeLean.Foundations.Curves.stalkC (genericPoint Y.left) (χ (.ofAdd t) : ℂ) * z := by
  letI : Surjective p.left := s2e_c11_surjective_of_point_surjective Y Z p hsurj
  letI : IsCyclic (S.H ⧸ S.χ.ker) := isCyclic_of_injective e.toMonoidHom e.injective
  have hcard : Nat.card (S.H ⧸ S.χ.ker) = S.m := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (ZMod S.m) = S.m
    exact Nat.card_zmod S.m
  obtain ⟨χ, hχ, z, f, hz, hf, hp, he⟩ := s2e_c1_cyclic_orbit_kummer_character
    Y Z (S.H ⧸ S.χ.ker) a ha1 hamul hinj p hsurj hinv horbit
  refine ⟨χ.comp e.symm.toMonoidHom, hχ.comp e.symm.injective, z, f, hz, hf, ?_, ?_⟩
  · simpa only [hcard] using hp
  · intro t
    exact he (e.symm (.ofAdd t))

end HodgeLean.Foundations.Program
