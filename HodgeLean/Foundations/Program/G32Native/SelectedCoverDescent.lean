import HodgeLean.Foundations.Program.G32Native.SelectedCoverPowerFinite
import HodgeLean.Foundations.Program.SchoenSelectedGeometryFiniteMorphism
import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The retained coordinate action becomes the same permutation after the curve quotient. -/
theorem g32w_action_powerMap (S : g32p_Supplier)
    {Y Z : Over (Spec ↧ℂ)}
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (p : Y ⟶ Z) (hp : ∀ u, a u ≫ p = p)
    (n : ℕ) (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)) :
    s2_action S Y a e n v τ ≫ s2_powerMap p n =
      s2_powerMap p n ≫ s2_permute Z n τ := by
  apply s2_product_hom_ext n
  intro i
  simp only [Category.assoc, s2_powerMap, s2_permute, s2_action, s2_check_lift_proj]
  rw [← Category.assoc, s2_check_lift_proj, Category.assoc, hp]

/-- A finite composite and a surjective retained quotient give finite closed fibres downstairs. -/
theorem g32w_finite_descended_map
    {X W B : Over (Spec ↧ℂ)} [IsProjective W.hom] [IsProjective B.hom]
    (q : X ⟶ W) [IsFinite q.left]
    (hq : Function.Surjective (Point.map q))
    (β : W ⟶ B) [IsFinite (q ≫ β).left] : IsFinite β.left := by
  letI : Surjective q.left :=
    s2e_step1_surjective_of_complexPoint_surjective X W q hq
  haveI : IsProper (β.left ≫ B.hom) := by rw [Over.w]; infer_instance
  haveI : IsProper β.left := IsProper.of_comp β.left B.hom
  apply s0_finite_of_finite_closed_fibers W.hom B.hom β.left
  intro b hb
  have hf := (q ≫ β).left.finite_preimage_singleton b
  apply (hf.image q.left).subset
  rintro w ⟨hw, _⟩
  obtain ⟨x, rfl⟩ := q.left.surjective w
  exact ⟨x, hw, rfl⟩

/-- Descent on the two retained quotients supplies native row S23 with its finite map square. -/
theorem g32w_selectedCoverDescent (S : g32p_Supplier)
    (Y Z W₀ B₀ : Over (Spec ↧ℂ))
    [IsProjective W₀.hom] [IsProjective B₀.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (p₀ : Y ⟶ Z) [IsFinite p₀.left]
    (hp₀ : ∀ u, a u ≫ p₀ = p₀) (h : ℕ)
    (q₀ : g3_power Y (h + 1) ⟶ W₀) [IsFinite q₀.left]
    (hqsurj : Function.Surjective (Point.map q₀))
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ T),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W₀ ⟶ T, q₀ ≫ u = f)
    (γ : g3_power Z (h + 1) ⟶ B₀) [IsFinite γ.left]
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ) :
    ∃ (β₀ : W₀ ⟶ B₀), ∃ inst19 : IsFinite β₀.left,
      let := inst19
      q₀ ≫ β₀ = s2_powerMap p₀ (h + 1) ≫ γ := by
  obtain ⟨β₀, hβ₀, _⟩ := hq B₀ (s2_powerMap p₀ (h + 1) ≫ γ) (by
    intro v τ hv
    rw [← Category.assoc, g32w_action_powerMap S a e p₀ hp₀,
      Category.assoc, hγinv])
  letI : IsFinite (s2_powerMap p₀ (h + 1)).left := g32w_power_finite Y Z p₀ (h + 1)
  letI : IsFinite (q₀ ≫ β₀).left := by
    rw [hβ₀]
    exact inferInstanceAs (IsFinite ((s2_powerMap p₀ (h + 1)).left ≫ γ.left))
  exact ⟨β₀, g32w_finite_descended_map q₀ hqsurj β₀, hβ₀⟩

#print axioms g32w_action_powerMap
#print axioms g32w_finite_descended_map
#print axioms g32w_selectedCoverDescent
end HodgeLean.Foundations.Program
