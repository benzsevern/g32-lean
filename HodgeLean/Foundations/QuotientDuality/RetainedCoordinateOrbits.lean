import HodgeLean.Foundations.QuotientDuality.RetainedCoordinatePointAction
import HodgeLean.Foundations.Program.SchoenSumZeroProperQuotient
import HodgeLean.Foundations.Program.SchoenCycleStep1

/-! The categorical retained power quotient has exactly the actual coordinate-group orbits. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.Adapters
open HodgeLean.Foundations.Program HodgeLean.Foundations
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

theorem retained_coordinate_quotient_orbits
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ) (q : g3_power Y n ⟶ W) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
      ∑ i, v i = 0 → s2_action S Y a e n v σ ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y n ⟶ T),
      (∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
        ∑ i, v i = 0 → s2_action S Y a e n v σ ≫ f = f) →
      ∃! u : W ⟶ T, q ≫ u = f)
    (x y : ComplexPoint (g3_power Y n)) :
    Point.map q x = Point.map q y ↔
      ∃ g : retainedCoordinateSubgroup S Y a e ha1 hamul n, g • x = y := by
  letI := spec_g3b_geometricallyIntegral Y
  let G := retainedCoordinateSubgroup S Y a e ha1 hamul n
  let A : G → (g3_power Y n ⟶ g3_power Y n) := fun g => g.val.asIso.hom
  have hAinv : ∀ g, A g ≫ q = q := by
    intro g
    obtain ⟨v, hv, σ, hg⟩ := g.property
    change g.val.asIso.hom ≫ q = q
    rw [hg]
    exact hinv v σ hv
  have hAquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y n ⟶ T),
      (∀ g, A g ≫ f = f) → ∃! u : W ⟶ T, q ≫ u = f := by
    intro T f hf
    apply hquot T f
    intro v σ hv
    exact hf (retainedCoordinateElement S Y a e ha1 hamul n v hv σ)
  letI : Surjective q.left := s2e_step1_surjective_of_complexPoint_surjective _ _ q hsurj
  constructor
  · intro hxy
    exact s2e_step1_finite_quotient_point_orbits (g3_power Y n) W G A rfl
      (fun _ _ => rfl) q hAinv hAquot x y hxy
  · rintro ⟨g, rfl⟩
    change Point.map q x = Point.map q (Point.map (A g) x)
    rw [← Point.map_comp_apply, hAinv g]

#print axioms retained_coordinate_quotient_orbits
end HodgeLean.Foundations.QuotientDuality
