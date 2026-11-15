import HodgeLean.Foundations.Program.G32Native.InitialNormalization

/-! Initial normalization of the retained zero-sum quotient. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The native initial identification uses the original quotient and generic source. -/
theorem g32w_selected_initial_normalization
    (S : g32p_Supplier) (Y W₀ B₀ : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] [IsIntegral W₀.left]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (h : ℕ) (q₀ : g3_power Y (h + 1) ⟶ W₀)
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q₀ = q₀)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ T),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W₀ ⟶ T, q₀ ≫ u = f)
    (β₀ : W₀ ⟶ B₀) [IsFinite β₀.left]
    (r : ℕ) (B : Fin (r + 1) → Over (Spec ↧ℂ)) (e₀ : B 0 ≅ B₀)
    (η : ∀ i, Spec W₀.left.functionField ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (hη₀ : η 0 ≫ e₀.hom.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left) :
    ∃ eW : s2b_normalizationOver (B 0) (η 0) ≅ W₀,
      eW.hom ≫ β₀ = s2b_normalizationMap (B 0) (η 0) ≫ e₀.hom ∧
      (η 0).toNormalization ≫ eW.hom.left =
        W₀.left.fromSpecStalk (genericPoint W₀.left) := by
  exact g32w_initial_normalization W₀ B₀ (B 0)
    (s2_retainedQuotient_normal S Y a e ha1 hamul (h + 1) W₀ q₀ hqinv hq)
    β₀ e₀ (η 0) hη₀

end HodgeLean.Foundations.Program
