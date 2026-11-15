import HodgeLean.Foundations.Program.SchoenTowerL1bKummerFinite
import Mathlib.Algebra.Group.Commute.Units

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Generic pullback respects composition of dominant scheme morphisms. -/
theorem s2v_l1b_functionFieldPullback_comp
    {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g] :
    s2v_l1b_functionFieldPullback (f ≫ g) =
      s2v_l1b_functionFieldPullback g ≫ s2v_l1b_functionFieldPullback f := by
  apply Spec.map_injective
  apply (cancel_mono (Z.fromSpecStalk (genericPoint Z))).mp
  rw [s2v_l1b_functionFieldPullback_generic_square, Spec.map_comp,
    Category.assoc, s2v_l1b_functionFieldPullback_generic_square,
    ← Category.assoc (Spec.map (s2v_l1b_functionFieldPullback f)),
    s2v_l1b_functionFieldPullback_generic_square, Category.assoc]

/-- Generic pullback takes the identity scheme map to the identity field map. -/
theorem s2v_l1b_functionFieldPullback_id
    (X : Scheme.{0}) [IsIntegral X] :
    s2v_l1b_functionFieldPullback (𝟙 X) = 𝟙 X.functionField := by
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
  rw [s2v_l1b_functionFieldPullback_generic_square, Spec.map_id,
    Category.id_comp, Category.comp_id]

/-- A dominant symmetry over the base fixes the actual embedded base function field. -/
theorem s2v_l1b_functionFieldPullback_over_base
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (β : X ⟶ Y) (d : X ⟶ X) [IsDominant β] [IsDominant d]
    (hd : d ≫ β = β) :
    s2v_l1b_functionFieldPullback β ≫ s2v_l1b_functionFieldPullback d =
      s2v_l1b_functionFieldPullback β := by
  rw [← s2v_l1b_functionFieldPullback_comp]
  congr 1

/-- Generic pullback along a scheme isomorphism is an isomorphism of its actual function fields. -/
theorem s2v_l1b_functionFieldPullback_isIso
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsIso f] : IsIso (s2v_l1b_functionFieldPullback f) := by
  refine ⟨⟨s2v_l1b_functionFieldPullback (inv f), ?_, ?_⟩⟩
  · rw [← s2v_l1b_functionFieldPullback_comp]
    simpa only [IsIso.inv_hom_id] using s2v_l1b_functionFieldPullback_id Y
  · rw [← s2v_l1b_functionFieldPullback_comp]
    simpa only [IsIso.hom_inv_id] using s2v_l1b_functionFieldPullback_id X

/-- Generic pullback detects morphisms over a separated base. -/
theorem s2v_l1b_functionFieldPullback_faithful
    {X Y T : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (s : Y ⟶ T) [IsSeparated s]
    (f g : X ⟶ Y) [IsDominant f] [IsDominant g]
    (hbase : f ≫ s = g ≫ s)
    (h : s2v_l1b_functionFieldPullback f = s2v_l1b_functionFieldPullback g) : f = g := by
  haveI := s2_genericPointMorphism_dominant X
  apply ext_of_isDominant_of_isSeparated s hbase (X.fromSpecStalk (genericPoint X))
  rw [← s2v_l1b_functionFieldPullback_generic_square,
    ← s2v_l1b_functionFieldPullback_generic_square, h]

/-- Finite order on an isomorphic model makes the transported endomorphism invertible. -/
theorem s2v_l1b_finite_order_transport_isIso
    {C : Type*} [Category C] {A B : C}
    (e : A ≅ B) (d : A ⟶ A) (d₀ : B ⟶ B)
    (hd : d ≫ e.hom = e.hom ≫ d₀)
    {m : ℕ} (hm : m ≠ 0) (horder : (End.of d) ^ m = 1) : IsIso d₀ := by
  haveI : IsIso d := (isUnit_iff_isIso (End.of d)).mp
    (IsUnit.of_pow_eq_one horder hm)
  haveI : IsIso (e.hom ≫ d₀) := by
    rw [← hd]
    infer_instance
  exact IsIso.of_isIso_comp_left e.hom d₀

/-- A symmetry of the actual cover induces a field automorphism with its generic square and fixed base image. -/
theorem s2v_l1b_cover_field_automorphism
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (β : X ⟶ Y) [IsDominant β] (d : X ⟶ X) [IsIso d]
    (hd : d ≫ β = β) :
    ∃ τ : X.functionField ≃+* X.functionField,
      τ.toRingHom = (s2v_l1b_functionFieldPullback d).hom ∧
      Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
        X.fromSpecStalk (genericPoint X) =
        X.fromSpecStalk (genericPoint X) ≫ d ∧
      ∀ z : Y.functionField, τ (s2v_l1b_functionFieldPullback β z) =
        s2v_l1b_functionFieldPullback β z := by
  haveI := s2v_l1b_functionFieldPullback_isIso d
  let τ := (asIso (s2v_l1b_functionFieldPullback d)).commRingCatIsoToRingEquiv
  refine ⟨τ, rfl, ?_, ?_⟩
  · exact s2v_l1b_functionFieldPullback_generic_square d
  · intro z
    exact congrArg (fun f : Y.functionField ⟶ X.functionField => f z)
      (s2v_l1b_functionFieldPullback_over_base β d hd)

/-- The actual cover symmetry is linear over the retained base-field embedding. -/
theorem s2v_l1b_cover_field_algEquiv
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (β : X ⟶ Y) [IsDominant β] (d : X ⟶ X) [IsIso d]
    (hd : d ≫ β = β) :
    letI := (s2v_l1b_functionFieldPullback β).hom.toAlgebra
    ∃ τ : X.functionField ≃ₐ[Y.functionField] X.functionField,
      τ.toRingHom = (s2v_l1b_functionFieldPullback d).hom := by
  letI := (s2v_l1b_functionFieldPullback β).hom.toAlgebra
  obtain ⟨τ, hτ, _, hfix⟩ := s2v_l1b_cover_field_automorphism β d hd
  refine ⟨{ τ with commutes' := ?_ }, hτ⟩
  exact hfix

/-- The retained finite-order normalization action supplies an automorphism of the original covering field over the base. -/
theorem s2v_l1b_normalization_cover_field_action
    {T : Scheme.{0}} (N W B : Over T)
    [IsIntegral W.left] [IsIntegral B.left]
    (β : W ⟶ B) [IsDominant β.left]
    (e : N ≅ W) (d : N ⟶ N) (d₀ : W ⟶ W)
    (hdinit : d ≫ e.hom = e.hom ≫ d₀) (hd₀ : d₀ ≫ β = β)
    {m : ℕ} (hm : m ≠ 0) (horder : (End.of d) ^ m = 1) :
    letI := (s2v_l1b_functionFieldPullback β.left).hom.toAlgebra
    ∃ τ : W.left.functionField ≃ₐ[B.left.functionField] W.left.functionField,
      Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
        W.left.fromSpecStalk (genericPoint W.left) =
        W.left.fromSpecStalk (genericPoint W.left) ≫ d₀.left := by
  haveI : IsIso d₀ := s2v_l1b_finite_order_transport_isIso e d d₀ hdinit hm horder
  letI := (s2v_l1b_functionFieldPullback β.left).hom.toAlgebra
  obtain ⟨τ, hτ⟩ := s2v_l1b_cover_field_algEquiv β.left d₀.left
    (by simpa only [← Over.comp_left] using congrArg Over.Hom.left hd₀)
  refine ⟨τ, ?_⟩
  rw [hτ]
  exact s2v_l1b_functionFieldPullback_generic_square d₀.left

end HodgeLean.Foundations.Program
