import HodgeLean.Foundations.Program.SchoenTowerL1bKummerOrbitDescent
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerFullOrbits

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual original composite is a categorical quotient by all coordinate
translations and permutations. -/
theorem s2v_l1b_full_coordinate_categorical_quotient
    (S : g32p_Supplier) (Y Z B : Over (Spec ↧ℂ))
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (p : Y ⟶ Z) (hp : ∀ u, a u ≫ p = p)
    (hpsurj : Function.Surjective (Point.map p))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (n : ℕ) [IsIntegral (g3_power Y n).left]
    [IsProjective (g3_power Y n).hom] [IsProjective (g3_power Z n).hom]
    (γ : g3_power Z n ⟶ B) (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z n τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (g : g3_power Z n ⟶ T),
      (∀ τ, s2_permute Z n τ ≫ g = g) → ∃! u : B ⟶ T, γ ≫ u = g)
    (f : g3_power Y n ⟶ B) [IsFinite f.left]
    (hfac : f = s2_powerMap p n ≫ γ) :
    ∀ (T : Over (Spec ↧ℂ)) (g : g3_power Y n ⟶ T),
      (∀ v τ, s2_action S Y a e n v τ ≫ g = g) →
      ∃! u : B ⟶ T, f ≫ u = g := by
  let G := s2v_l1b_fullCoordinateGroup S Y a e ha1 hamul n
  letI : Finite G := s2v_l1b_fullCoordinateGroup_finite S Y a e ha1 hamul n
  let ρ : G →* Aut (g3_power Y n) := G.subtype
  have hinv : ∀ g, (ρ g).asIso.hom ≫ f = f := by
    intro g
    obtain ⟨v, τ, hg⟩ := g.property
    change g.val.asIso.hom ≫ f = f
    rw [hg, hfac, ← Category.assoc,
      s2v_l1b_full_action_powerMap S Y Z a e p hp n v τ, Category.assoc, hγinv]
  have hsurj : Function.Surjective (Point.map f) := by
    intro b
    obtain ⟨z, hz⟩ := hγsurj b
    obtain ⟨y, hy⟩ := s2_powerMap_point_surjective p hpsurj n z
    refine ⟨y, ?_⟩
    change y ≫ f = b
    rw [hfac, ← Category.assoc]
    change Point.map γ (Point.map (s2_powerMap p n) y) = b
    rw [hy, hz]
  have horbit : ∀ x y : ComplexPoint (g3_power Y n),
      Point.map f x = Point.map f y ↔ ∃ g, Point.map (ρ g).asIso.hom x = y := by
    intro x y
    rw [hfac, s2v_l1b_full_coordinate_point_orbits S Y Z B a e p hp hporbit n γ hγinv hγ]
    constructor
    · rintro ⟨v, τ, hxy⟩
      exact ⟨⟨Aut.of (s2_coordinateActionIso S Y a e ha1 hamul n v τ), v, τ, rfl⟩, hxy⟩
    · rintro ⟨g, hxy⟩
      obtain ⟨v, τ, hg⟩ := g.property
      refine ⟨v, τ, ?_⟩
      change Point.map g.val.asIso.hom x = y at hxy
      rwa [hg] at hxy
  intro T g hg
  apply s2v_l1b_categorical_quotient_of_point_orbits (g3_power Y n) B G ρ f hsurj hinv horbit T g
  intro k
  obtain ⟨v, τ, hk⟩ := k.property
  change k.val.asIso.hom ≫ g = g
  rw [hk]
  exact hg v τ

end HodgeLean.Foundations.Program
