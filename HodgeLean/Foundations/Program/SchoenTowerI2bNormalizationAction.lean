import HodgeLean.Foundations.Program.SchoenTowerI2bGenericStalk

/-! Compatibility of the normalized tower action with its retained generic source.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The initial generic stalk identification propagates through all retained transitions.
Source: injectivity of maps between generic fields and the common field-source equations. -/
theorem s2v_i2b_tower_source_stalk_iso
    {K : Type} [Field K] {r : ℕ} (X : Fin (r + 1) → Scheme)
    [∀ s, IsIntegral (X s)] (q : ∀ s, Spec ↧K ⟶ X s) [∀ s, IsDominant (q s)]
    (w : ∀ i : Fin r, X i.succ ⟶ X i.castSucc)
    (hw : ∀ i : Fin r, q i.succ ≫ w i = q i.castSucc)
    (h0 : IsIso (Scheme.stalkClosedPointTo (q 0))) (s : Fin (r + 1)) :
    IsIso (Scheme.stalkClosedPointTo (q s)) := by
  induction s using Fin.induction with
  | zero => exact h0
  | succ i ih =>
    haveI := ih
    haveI : IsIso (Scheme.stalkClosedPointTo (q i.succ ≫ w i)) := by
      rw [hw i]
      infer_instance
    exact s2v_i2b_genericSource_stalk_iso_of_comp (X i.succ) (X i.castSucc) (q i.succ) (w i)

/-- The retained normalized action intertwines the common field source at every stage.
Source: uniqueness of dominant generic lifts and compatibility of the retained deck maps. -/
theorem s2v_i2b_tower_source_action
    {K : Type} [Field K] {r : ℕ} (X : Fin (r + 1) → Scheme)
    [∀ s, IsIntegral (X s)] (q : ∀ s, Spec ↧K ⟶ X s) [∀ s, IsDominant (q s)]
    (w : ∀ i : Fin r, X i.succ ⟶ X i.castSucc)
    (hw : ∀ i : Fin r, q i.succ ≫ w i = q i.castSucc)
    (h0 : IsIso (Scheme.stalkClosedPointTo (q 0)))
    (g : Spec ↧K ⟶ Spec ↧K) [IsIso g]
    (d : ∀ s, X s ⟶ X s) [∀ s, IsIso (d s)]
    (hdw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (haction0 : g ≫ q 0 = q 0 ≫ d 0) (s : Fin (r + 1)) :
    g ≫ q s = q s ≫ d s := by
  haveI : ∀ j, IsIso (Scheme.stalkClosedPointTo (q j)) :=
    s2v_i2b_tower_source_stalk_iso X q w hw h0
  haveI : ∀ j, Mono (q j) := fun j => s2v_i2b_genericSource_mono (X j) (q j)
  induction s using Fin.induction with
  | zero => exact haction0
  | succ i ih =>
    apply s2v_i2b_genericSource_lifts_unique (X i.succ) (X i.castSucc)
      (q i.succ) (q i.castSucc) (w i) (hw i) (g ≫ q i.succ) (q i.succ ≫ d i.succ)
    calc
      (g ≫ q i.succ) ≫ w i = g ≫ q i.castSucc := by rw [Category.assoc, hw i]
      _ = q i.castSucc ≫ d i.castSucc := ih
      _ = (q i.succ ≫ d i.succ) ≫ w i := by
        rw [Category.assoc, hdw i, ← Category.assoc, hw i]

end HodgeLean.Foundations.Program
