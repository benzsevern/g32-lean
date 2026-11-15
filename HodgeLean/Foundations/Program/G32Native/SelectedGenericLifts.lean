import HodgeLean.Foundations.Program.SchoenTowerFoundC1

/-! # Generic lifts in the retained native coordinates

Rows T05 and T06 of `SchoenTransferJ2NativeInput.lean:146–152`.
The paired ideals and their universal properties are supplied on the specified
bases; dominance and non-total centre supports are explicit prerequisites.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Transport the finite cover through the initial base isomorphism and retain
all generic maps, with their native instance telescope and equations. -/
theorem selectedGenericLifts
    (W₀ B₀ : Over (Spec ↧ℂ)) [IsIntegral W₀.left]
    (r : ℕ) (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left] [∀ i, IsProjective (B i).hom]
    (β₀ : W₀ ⟶ B₀) [IsFinite β₀.left] [IsDominant β₀.left]
    (e₀ : B 0 ≅ B₀)
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (hcentre : ∀ i : Fin r,
      (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩).support ≠ ⊤)
    (hblowup : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f) :
    ∃ (η : ∀ i, Spec W₀.left.functionField ⟶ (B i).left),
    ∃ inst23 : ∀ i, QuasiCompact (η i),
      let := inst23
    ∃ inst24 : ∀ i, QuasiSeparated (η i),
      let := inst24
    ∃ (hη₀ : η 0 ≫ e₀.hom.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left),
      ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc := by
  let β : W₀ ⟶ B 0 := β₀ ≫ e₀.inv
  haveI : IsIso e₀.inv.left := by
    change IsIso ((Over.forget _).map e₀.inv)
    infer_instance
  haveI : IsFinite β.left := by dsimp [β]; infer_instance
  haveI : IsDominant β.left := by dsimp [β]; infer_instance
  obtain ⟨η, hη, _⟩ := s2t_generic_tower W₀ r B β b
    (fun i => D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      D i.castSucc ⟨2 * i.val + 1, by omega⟩) hcentre hblowup
  refine ⟨η, fun i => (hη.2.2 i).2.1, fun i => (hη.2.2 i).2.2, ?_, hη.2.1⟩
  rw [hη.1]
  change (W₀.left.fromSpecStalk (genericPoint W₀.left) ≫
    β₀.left ≫ e₀.inv.left) ≫ e₀.hom.left = _
  rw [Category.assoc, Category.assoc,
    ← Over.comp_left, e₀.inv_hom_id, Over.id_left, Category.comp_id]

end HodgeLean.Foundations.Program.G32Native
