import HodgeLean.Foundations.Program.SchoenCycleGeometryChecks

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- Coordinate equality determines morphisms into the actual retained complex scheme power. -/
theorem s2_product_hom_ext {T Y : Over (Spec ↧ℂ)} (h : ℕ)
    {f g : T ⟶ g3_power Y h}
    (heq : ∀ i, f ≫ g3_proj Y h i = g ≫ g3_proj Y h i) : f = g := by
  exact CategoryTheory.Limits.Fan.IsLimit.hom_ext
    (spec_g3_isLimit_fan Y h).some _ _ heq

/-- The retained coordinate actions have their actual identity and composition laws independently of the target geometry proofs. -/
theorem s2_coordinateAction_laws (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u) (h : ℕ) :
    s2_action S Y a e h 0 1 = 𝟙 (g3_power Y h) ∧
    ∀ (v w : Fin h → ZMod S.m) (σ τ : Equiv.Perm (Fin h)),
      s2_action S Y a e h v σ ≫ s2_action S Y a e h w τ =
        s2_action S Y a e h (fun i => w i + v (τ.symm i)) (τ * σ) := by
  constructor
  · apply s2_product_hom_ext h
    intro i
    simp only [s2_action, s2_check_lift_proj, Equiv.Perm.one_apply,
      Equiv.Perm.one_symm, Pi.zero_apply, ofAdd_zero, map_one,
      ha1, Category.comp_id, Category.id_comp]
  · intro v w σ τ
    apply s2_product_hom_ext h
    intro i
    simp only [s2_action, Category.assoc, s2_check_lift_proj]
    rw [← Category.assoc, s2_check_lift_proj, Category.assoc, ← hamul]
    congr 1
    exact congrArg a (map_mul e.symm _ _).symm

end HodgeLean.Foundations.Program
