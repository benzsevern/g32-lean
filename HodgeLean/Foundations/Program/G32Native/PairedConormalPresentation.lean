import HodgeLean.Foundations.NormalPresentation.Proofs

/-! # Recovering a presentation from an elementary sequence -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.NormalPresentation

variable {C : Type*} [Category* C] [Abelian C] {L A F M : C}

/-- A lift of the divisor generator recovers the entire middle object as a
quotient presentation, preserving both arrows of the supplied sequence. -/
theorem elementary_presentation_of_lift
    (a : L ⟶ A) [Mono a]
    (f : F ⟶ M) (g : M ⟶ cokernel a) (hfg : f ≫ g = 0)
    (hs : (ShortComplex.mk f g hfg).ShortExact)
    (l : A ⟶ M) (hl : l ≫ g = cokernel.π a) :
    ∃ (b : L ⟶ F) (e : quotient a b ≅ M),
      projection a b ≫ e.hom = biprod.desc l f ∧
      freeArrow a b ≫ e.hom = f ∧
      e.hom ≫ g = divisorArrow a b := by
  have : Mono f := hs.mono_f
  have haz : (a ≫ l) ≫ g = 0 := by
    rw [Category.assoc, hl, cokernel.condition]
  let b : L ⟶ F := -(hs.exact.lift (a ≫ l) haz)
  have hb : b ≫ f = -(a ≫ l) := by
    dsimp only [b]
    rw [Preadditive.neg_comp, hs.exact.lift_f]
  have hr : relation a b ≫ biprod.desc l f = 0 := by
    simp only [relation, biprod.lift_desc, hb, add_neg_cancel]
  let q : quotient a b ⟶ M := comparison a b (biprod.desc l f) hr
  have hq : projection a b ≫ q = biprod.desc l f := cokernel.π_desc _ _ _
  have hf : freeArrow a b ≫ q = f := by
    rw [freeArrow, Category.assoc, hq, biprod.inr_desc]
  have : Epi (projection a b) := inferInstanceAs (Epi (cokernel.π (relation a b)))
  have hg : q ≫ g = divisorArrow a b := by
    apply (cancel_epi (projection a b)).mp
    rw [← Category.assoc, hq]
    change biprod.desc l f ≫ g = projection a b ≫ divisorArrow a b
    rw [divisorArrow, projection, cokernel.π_desc]
    apply biprod.hom_ext'
    · simpa only [← Category.assoc, biprod.inl_desc, biprod.inl_fst,
        Category.id_comp] using hl
    · simp only [← Category.assoc, biprod.inr_desc, hfg, biprod.inr_fst, zero_comp]
  let φ : elementary a b ⟶ ShortComplex.mk f g hfg :=
    { τ₁ := 𝟙 F
      τ₂ := q
      τ₃ := 𝟙 (cokernel a)
      comm₁₂ := by simpa only [elementary, Category.id_comp] using hf.symm
      comm₂₃ := by simpa only [elementary, Category.comp_id] using hg }
  have : IsIso φ.τ₁ := inferInstanceAs (IsIso (𝟙 F))
  have : IsIso φ.τ₃ := inferInstanceAs (IsIso (𝟙 (cokernel a)))
  have : IsIso q := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ
    (elementary_shortExact_aux a b) hs
  exact ⟨b, asIso q, hq, hf, hg⟩

end HodgeLean.Foundations.Program.G32Native
