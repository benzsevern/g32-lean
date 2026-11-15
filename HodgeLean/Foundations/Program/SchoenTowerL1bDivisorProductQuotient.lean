import HodgeLean.Foundations.Program.SchoenSumZeroAction
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductAction
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorOriginalAction
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerQuotientField

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A coordinate product with a common character descends through the actual sum-zero quotient. -/
theorem s2v_l1b_divisor_product_function_quotient
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [IsIntegral W.left] [LocallyOfFiniteType Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ) [IsIntegral (g3_power Y n).left]
    (q : g3_power Y n ⟶ W) [IsFinite q.left] [IsDominant q.left]
    (hqinv : ∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
      ∑ j, v j = 0 → s2_action S Y a e n v σ ≫ q = q)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y n ⟶ T),
      (∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
        ∑ j, v j = 0 → s2_action S Y a e n v σ ≫ f = f) →
      ∃! b : W ⟶ T, q ≫ b = f)
    (χ : Multiplicative (ZMod S.m) →* ℂˣ) (u : Y.left.functionField)
    (hu : u ≠ 0)
    (heigen : ∀ g,
      letI : IsIso (a g) :=
        (s2v_l1b_divisor_original_action S Y a ha1 hamul g).asIso.isIso_hom
      s2v_l1b_functionFieldPullback (a g).left u =
        ((Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫
          Y.left.germToFunctionField ⊤).hom (χ (e g) : ℂ) * u) :
    ∃ w : W.left.functionField, w ≠ 0 ∧
      s2v_l1b_functionFieldPullback q.left w =
        s2v_l1b_divisor_product_function Y n u := by
  letI : ∀ g, IsIso (a g) := fun g =>
    (s2v_l1b_divisor_original_action S Y a ha1 hamul g).asIso.isIso_hom
  let I := {v : Fin n → ZMod S.m // ∑ j, v j = 0} × Equiv.Perm (Fin n)
  let b (i : I) := s2_action S Y a e n i.1.val i.2
  letI : ∀ i : I, IsIso (b i) := fun i =>
    (s2_coordinateActionIso S Y a e ha1 hamul n i.1.val i.2).isIso_hom
  letI := (s2v_l1b_functionFieldPullback q.left).hom.toAlgebra
  have hcover (i : I) := s2v_l1b_cover_field_algEquiv q.left (b i).left
    (congrArg Over.Hom.left (hqinv i.1.val i.2 i.1.property))
  choose τ hτ using hcover
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := genericPoint W.left) (U := ⊤) trivial
  letI : Nonempty U := ⟨⟨genericPoint W.left, hxU⟩⟩
  obtain ⟨w, hw⟩ := s2v_l1b_categorical_quotient_fixed_rational_function
    (g3_power Y n) W q b (fun i => hqinv i.1.val i.2 i.1.property)
    (fun T f hf => hq T f (fun v σ hv => hf (⟨v, hv⟩, σ))) ⟨U, hU⟩ τ hτ
    (s2v_l1b_divisor_product_function Y n u) (fun i => by
      change (τ i).toRingHom _ = _
      rw [hτ i]
      exact s2v_l1b_divisor_product_function_sum_zero S Y a e n i.1.val i.2 χ u
        heigen i.1.property)
  refine ⟨w, ?_, hw⟩
  intro hz
  rw [hz, map_zero] at hw
  exact s2v_l1b_divisor_product_function_ne_zero Y n u hu hw.symm

end HodgeLean.Foundations.Program
