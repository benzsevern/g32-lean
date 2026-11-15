import HodgeLean.Foundations.Program.SchoenTowerL1bKummerStageFinite
import HodgeLean.Foundations.Program.SchoenTowerL1bGenericTower

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A map inducing an isomorphism of generic fields detects dominant field-valued maps. -/
theorem s2v_l1b_generic_cancel_birational
    {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f]
    [IsIso (s2v_l1b_functionFieldPullback f)]
    (q₁ q₂ : Spec (.of K) ⟶ X) [IsDominant q₁] [IsDominant q₂]
    (h : q₁ ≫ f = q₂ ≫ f) : q₁ = q₂ := by
  obtain ⟨κ₁, hκ₁, _⟩ := s2v_l1b_generic_field_embedding X q₁
  obtain ⟨κ₂, hκ₂, _⟩ := s2v_l1b_generic_field_embedding X q₂
  have he : s2v_l1b_functionFieldPullback f ≫ κ₁ =
      s2v_l1b_functionFieldPullback f ≫ κ₂ := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      s2v_l1b_functionFieldPullback_generic_square, ← Category.assoc,
      ← Category.assoc, hκ₁, hκ₂, h]
  have hk : κ₁ = κ₂ := (cancel_epi (s2v_l1b_functionFieldPullback f)).mp he
  rw [← hκ₁, ← hκ₂, hk]

/-- A dominant field point over the original generic point identifies both generic fields. -/
theorem s2v_l1b_generic_projection_field_isIso
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f]
    (q : Spec Y.functionField ⟶ X) [IsDominant q]
    (hq : q ≫ f = Y.fromSpecStalk (genericPoint Y)) :
    IsIso (s2v_l1b_functionFieldPullback f) := by
  obtain ⟨κ, hκ, _⟩ := s2v_l1b_generic_field_embedding X q
  have he : s2v_l1b_functionFieldPullback f ≫ κ = 𝟙 Y.functionField := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp
    rw [Spec.map_comp, Category.assoc,
      s2v_l1b_functionFieldPullback_generic_square, ← Category.assoc,
      hκ, hq, Spec.map_id]
    exact (Category.id_comp _).symm
  refine ⟨⟨κ, he, ?_⟩⟩
  ext z
  apply κ.hom.injective
  exact congrArg (fun g : Y.functionField ⟶ Y.functionField => g (κ z)) he

/-- The retained original generic deck square lifts to every compatible integral tower model. -/
theorem s2v_l1b_generic_deck_tower
    {r : ℕ} (W : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (W i).left]
    (w : ∀ i : Fin r, W i.succ ⟶ W i.castSucc)
    (W₀ : Over (Spec ↧ℂ)) [IsIntegral W₀.left]
    (q : ∀ i, Spec W₀.left.functionField ⟶ (W i).left)
    [∀ i, IsDominant (q i)]
    (hq : ∀ i : Fin r, q i.succ ≫ (w i).left = q i.castSucc)
    (d : ∀ i, W i ⟶ W i) [∀ i, IsDominant (d i).left]
    (hdw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (eW : W 0 ≅ W₀) (d₀ : W₀ ⟶ W₀)
    (hdinit : d 0 ≫ eW.hom = eW.hom ≫ d₀)
    (hinit : q 0 ≫ eW.hom.left = W₀.left.fromSpecStalk (genericPoint W₀.left))
    (φ : Spec W₀.left.functionField ⟶ Spec W₀.left.functionField) [IsDominant φ]
    (hφ : φ ≫ W₀.left.fromSpecStalk (genericPoint W₀.left) =
      W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ d₀.left)
    (i : Fin (r + 1)) : φ ≫ q i = q i ≫ (d i).left := by
  let f := (s2v_towerToInitial W w i ≫ eW.hom).left
  have hg : q i ≫ f = W₀.left.fromSpecStalk (genericPoint W₀.left) :=
    s2v_l1b_generic_to_original _ W w q hq W₀ eW _ hinit i
  haveI : IsDominant (q i ≫ f) := by
    rw [hg]
    exact s2_genericPointMorphism_dominant W₀.left
  haveI : IsDominant f := IsDominant.of_comp (q i) f
  haveI := s2v_l1b_generic_projection_field_isIso f (q i) hg
  apply s2v_l1b_generic_cancel_birational f
  exact s2v_l1b_generic_deck_projected _ W w q hq d hdw W₀ eW d₀ hdinit
    _ hinit φ hφ i

end HodgeLean.Foundations.Program
