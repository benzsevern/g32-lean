import HodgeLean.Foundations.Program.SchoenTowerI1aCategoricalOrbits
import HodgeLean.Foundations.Program.SchoenSumZeroActionFinite

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The retained sum-zero categorical quotient has its specified complex point orbits. -/
theorem s2v_l1b_sum_zero_point_orbits
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ) [IsProjective (g3_power Y n).hom]
    (q : g3_power Y n ⟶ W)
    (hinv : ∀ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
      ∑ j, v j = 0 → s2_action S Y a e n v τ ≫ q = q)
    (hcat : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y n ⟶ T),
      (∀ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
        ∑ j, v j = 0 → s2_action S Y a e n v τ ≫ f = f) →
      ∃! u : W ⟶ T, q ≫ u = f) :
    ∀ x y : ComplexPoint (g3_power Y n),
      Point.map q x = Point.map q y ↔
        ∃ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
          (∑ j, v j = 0) ∧ Point.map (s2_action S Y a e n v τ) x = y := by
  let G := s2_sumZeroActionGroup S Y a e ha1 hamul n
  letI : Finite G := s2_sumZeroActionGroup_finite S Y a e ha1 hamul n
  let A : G → (g3_power Y n ⟶ g3_power Y n) := fun g => g.val.asIso.hom
  have hAinv : ∀ g, A g ≫ q = q := by
    intro g
    obtain ⟨v, τ, hv, hg⟩ := g.property
    change g.val.asIso.hom ≫ q = q
    rw [hg]
    exact hinv v τ hv
  have hAcat : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y n ⟶ T),
      (∀ g, A g ≫ f = f) → ∃! u : W ⟶ T, q ≫ u = f := by
    intro T f hf
    apply hcat T f
    intro v τ hv
    exact hf ⟨Aut.of (s2_coordinateActionIso S Y a e ha1 hamul n v τ), v, τ, hv, rfl⟩
  intro x y
  constructor
  · intro hxy
    obtain ⟨g, hgxy⟩ := (s2v_i1ahi_projective_categorical_orbits
      (g3_power Y n) W G A rfl (fun _ _ => rfl) q hAinv hAcat x y).mp hxy
    obtain ⟨v, τ, hv, hg⟩ := g.property
    refine ⟨v, τ, hv, ?_⟩
    change Point.map g.val.asIso.hom x = y at hgxy
    rwa [hg] at hgxy
  · rintro ⟨v, τ, hv, hxy⟩
    rw [← hxy]
    change x ≫ q = (x ≫ s2_action S Y a e n v τ) ≫ q
    rw [Category.assoc, hinv v τ hv]

end HodgeLean.Foundations.Program
