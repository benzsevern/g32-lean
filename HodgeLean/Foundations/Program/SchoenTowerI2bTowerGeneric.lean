import HodgeLean.Foundations.Program.SchoenTowerI2bBlowupGeneric

/-! Dominance and base invariance of the retained generic source along the tower.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Dominance of the initial field source propagates through the retained blowup tower.
Source: induction using the retained blowup universal property. -/
theorem s2v_i2b_tower_genericSource_dominant
    {L : Type} [Field L] {r : ℕ}
    (B : Fin (r + 1) → Over (Spec ↧ℂ)) [∀ s, IsIntegral (B s).left]
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (I : ∀ i : Fin r, (B i.castSucc).left.IdealSheafData)
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((I i).comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U.1)]
          Γ((B i.succ).left, U.1)))
    (hblowup : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((I i).comap f.left).ideal U) ≃ₗ[Γ(T.left, U.1)] Γ(T.left, U.1))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f)
    (η : ∀ s, Spec ↧L ⟶ (B s).left)
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (h0 : IsDominant (η 0)) (s : Fin (r + 1)) : IsDominant (η s) := by
  induction s using Fin.induction with
  | zero => exact h0
  | succ i ih =>
    haveI := ih
    exact s2v_i2b_blowup_fieldSource_dominant (b i) (I i) (hcartier i)
      (hblowup i) (η i.castSucc) (η i.succ) (hη i)

/-- Invariance of the initial field source propagates through the retained blowup tower.
Source: uniqueness of field-valued lifts under the retained blowup universal property. -/
theorem s2v_i2b_tower_genericSource_invariant
    {L : Type} [Field L] {r : ℕ}
    (B : Fin (r + 1) → Over (Spec ↧ℂ)) [∀ s, IsIntegral (B s).left]
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (I : ∀ i : Fin r, (B i.castSucc).left.IdealSheafData)
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((I i).comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U.1)]
          Γ((B i.succ).left, U.1)))
    (hblowup : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((I i).comap f.left).ideal U) ≃ₗ[Γ(T.left, U.1)] Γ(T.left, U.1))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f)
    (η : ∀ s, Spec ↧L ⟶ (B s).left)
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (hdom : IsDominant (η 0)) (g : Spec ↧L ⟶ Spec ↧L)
    (h0 : g ≫ η 0 = η 0) (s : Fin (r + 1)) : g ≫ η s = η s := by
  haveI : ∀ j, IsDominant (η j) :=
    s2v_i2b_tower_genericSource_dominant B b I hcartier hblowup η hη hdom
  induction s using Fin.induction with
  | zero => exact h0
  | succ i ih =>
    apply s2v_blowup_fieldSource_lift_unique (b i) (I i)
      (s2v_i2b_center_support_ne_top (b i).left (I i) (hcartier i))
      (hblowup i) (η i.castSucc) (g ≫ η i.succ) (η i.succ)
    · rw [Category.assoc, hη i, ih]
    · exact hη i

end HodgeLean.Foundations.Program
