import HodgeLean.Foundations.Program.G32Native.ZeroPairCurveEtale
import HodgeLean.Foundations.Program.SchoenCycleC1NoMarksEtale
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerResidualPowers

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The exact selected power quotient is etale when its branch indices are empty. -/
theorem g32w09_power_etale
    (S : g32p_Supplier) (Y Z W B : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p : Y ⟶ Z) (hp : ∀ u, a u ≫ p = p)
    (hpsurj : Function.Surjective (Point.map p))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ u z, Point.map (a u) (eY z) = eY (u • z))
    (y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C)
    (hbranch : ∀ z : rsq_Quot S.χ.ker C, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
      ∃ i, Point.map p (eY z) = Point.map p (eY (y i)))
    (h : ℕ) (hh : 0 < h + 1)
    (q : g3_power Y (h + 1) ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q = q)
    (hq : ∀ (A : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ A),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W ⟶ A, q ≫ u = f)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (A : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ A),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ A, γ ≫ u = f)
    (β : W ⟶ B) [IsFinite β.left] (hβ : q ≫ β = s2_powerMap p (h + 1) ≫ γ)
    (d : W ⟶ W) (hd : d ≫ β = β)
    (hgenerator : q ≫ d = s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q)
    (hempty : g32p_exponents S = []) : Etale β.left := by
  classical
  have hi : IsEmpty (Fin (g32p_exponents S).length) := by
    rw [hempty]
    change IsEmpty (Fin 0)
    infer_instance
  have hpow : q ≫ (End.of d ^ S.m).asHom = q := by
    rw [s2v_l1b_residual_generator_powers S Y W a e ha1 hamul
      (h + 1) hh q d hgenerator]
    have hz : s2_delta S (h + 1) hh (S.m : ZMod S.m) = 0 := by
      funext j
      simp only [ZMod.natCast_self, s2_delta, ite_self, Pi.zero_apply]
    rw [hz, (s2_coordinateAction_laws S Y a e ha1 hamul (h + 1)).1,
      Category.id_comp]
  have horder : End.of d ^ S.m = 1 := by
    obtain ⟨u, hu, huniq⟩ := hq W q hqinv
    have h₁ : (End.of d ^ S.m).asHom = u := huniq _ hpow
    have h₂ : 𝟙 W = u := huniq _ (Category.comp_id q)
    apply End.ext
    exact h₁.trans h₂.symm
  exact s2e_c1_initial_etale_of_no_marks S Y Z W B a e ha1 hamul hinj
    p hp hpsurj hporbit (rsq_Quot S.χ.ker C) (Fin (g32p_exponents S).length)
    eY.toEquiv hpointAction (fun i => Point.map p (eY (y i))) hbranch
    h hh q hqsurj hqinv hq γ hγsurj hγinv hγ β hβ d hd horder hgenerator

#print axioms g32w09_power_etale
end HodgeLean.Foundations.Program
