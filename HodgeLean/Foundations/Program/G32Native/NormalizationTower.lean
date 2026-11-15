import HodgeLean.Foundations.Program.G32Native.GenericDeck

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The specified generic tower and its initial identification supply native T08--T09. -/
theorem g32w_normalization_tower
    (S : g32p_Supplier) (W₀ B₀ : Over (Spec ↧ℂ)) [IsIntegral W₀.left] [IsProjective W₀.hom]
    (β₀ : W₀ ⟶ B₀) [IsFinite β₀.left] [IsDominant β₀.left]
    (d₀ : W₀ ⟶ W₀) [IsIso d₀] (hd₀ : d₀ ≫ β₀ = β₀)
    (horder₀ : End.of d₀ ^ S.m = 1)
    (r : ℕ) (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left] [∀ i, IsProjective (B i).hom]
    [∀ i, IsSeparated (B i).hom]
    (e₀ : B 0 ≅ B₀) (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (K : ∀ i : Fin r, (B i.castSucc).left.IdealSheafData)
    (hK : ∀ i, (K i).support ≠ ⊤)
    (huniv : ∀ i (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((K i).comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! v : T ⟶ B i.succ, v ≫ b i = f)
    (η : ∀ i, Spec W₀.left.functionField ⟶ (B i).left)
    [∀ i, IsDominant (η i)] [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (hη₀ : η 0 ≫ e₀.hom.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left)
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (eW : s2b_normalizationOver (B 0) (η 0) ≅ W₀)
    (hgeneric : (η 0).toNormalization ≫ eW.hom.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left)) :
    ∃ (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
        s2b_normalizationOver (B i.castSucc) (η i.castSucc)),
    ∃ (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
        (η i.castSucc).toNormalization),
    ∃ (d : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ s2b_normalizationOver (B i) (η i)),
    ∃ (hd : ∀ i, d i ≫ s2b_normalizationMap (B i) (η i) = s2b_normalizationMap (B i) (η i)),
    ∃ (hdinit : d 0 ≫ eW.hom = eW.hom ≫ d₀),
    ∃ (hdw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc),
      ∀ i, End.of (d i) ^ S.m = 1 := by
  classical
  obtain ⟨u, hu, hm⟩ := g32w_generic_deck W₀ d₀ S.m horder₀
  have hηinit : η 0 = W₀.left.fromSpecStalk (genericPoint W₀.left) ≫
      (β₀ ≫ e₀.inv).left := by
    apply (cancel_mono e₀.hom.left).mp
    simpa only [Over.comp_left, Category.assoc, ← Over.comp_left,
      e₀.inv_hom_id, Over.id_left, Category.comp_id] using hη₀
  have hu0 : u.hom ≫ η 0 = η 0 := by
    rw [hηinit, ← Category.assoc, hu, Category.assoc]
    have he : d₀.left ≫ (β₀ ≫ e₀.inv).left = (β₀ ≫ e₀.inv).left := by
      simpa only [Over.comp_left, Category.assoc] using
        congrArg Over.Hom.left (show d₀ ≫ (β₀ ≫ e₀.inv) = β₀ ≫ e₀.inv by
          rw [← Category.assoc, hd₀])
    rw [he]
  haveI : IsFinite (β₀ ≫ e₀.inv).left := by
    change IsFinite (β₀.left ≫ e₀.inv.left)
    infer_instance
  haveI : IsDominant (β₀ ≫ e₀.inv).left := by
    change IsDominant (β₀.left ≫ e₀.inv.left)
    infer_instance
  have huη := g32w_generic_tower_invariant W₀ r B (β₀ ≫ e₀.inv)
    b K hK huniv η hηinit hη u hu0
  choose w hw hwb using fun i =>
    g32w_normalization_transition (B i.succ) (B i.castSucc) (b i)
      (η i.succ) (η i.castSucc) (hη i)
  choose d hsource hd horder using fun i =>
    g32w_normalization_deck (B i) (η i) u (huη i) S.m hm
  refine ⟨w, hw, d, hd, ?_, ?_, horder⟩
  · haveI : IsReduced (s2b_normalizationOver (B 0) (η 0)).left :=
      inferInstanceAs (IsReduced (η 0).normalization)
    apply Over.OverMorphism.ext
    apply ext_of_isDominant_of_isSeparated W₀.hom
      ((Over.w (d 0 ≫ eW.hom)).trans (Over.w (eW.hom ≫ d₀)).symm)
      (η 0).toNormalization
    change (η 0).toNormalization ≫ ((d 0).left ≫ eW.hom.left) =
      (η 0).toNormalization ≫ (eW.hom.left ≫ d₀.left)
    rw [← Category.assoc, hsource, Category.assoc, hgeneric,
      ← Category.assoc, hgeneric, hu]
  · intro i
    exact g32w_normalization_deck_transition (B i.succ) (B i.castSucc)
      (η i.succ) (η i.castSucc) u.hom (w i) (hw i)
      (d i.succ) (d i.castSucc) (hsource i.succ) (hsource i.castSucc)

end HodgeLean.Foundations.Program
