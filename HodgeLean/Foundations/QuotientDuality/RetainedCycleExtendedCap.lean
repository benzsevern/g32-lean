import HodgeLean.Foundations.QuotientDuality.RetainedCycleGradedCap
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

noncomputable section
open CategoryTheory Limits CochainComplex.HomComplex
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The actual graded cap action on the integer-indexed extension of the chain complex. -/
def retainedExtendedCap (K : ChainComplex C ℕ) (p : ℕ)
    (cap : ∀ q, K.X (p + q) ⟶ K.X q) :
    Cochain (K.extend ComplexShape.embeddingDownNat) (K.extend ComplexShape.embeddingDownNat) (p : ℤ) :=
  Cochain.mk (fun i j h =>
    if hj : j ≤ 0 then
      let q := (-j).toNat
      have hq : ComplexShape.embeddingDownNat.f q = j := by
        simp only [ComplexShape.embeddingDownNat_f]
        dsimp only [q]
        omega
      have hi : ComplexShape.embeddingDownNat.f (p + q) = i := by
        simp only [ComplexShape.embeddingDownNat_f]
        dsimp only [q]
        omega
      (K.extendXIso ComplexShape.embeddingDownNat hi).hom ≫ cap q ≫
        (K.extendXIso ComplexShape.embeddingDownNat hq).inv
    else 0)

/-- In nonpositive degrees the extended cochain retains the specified actual cap map. -/
theorem retained_extended_cap_negative_component (K : ChainComplex C ℕ) (p q : ℕ)
    (cap : ∀ q, K.X (p + q) ⟶ K.X q) :
    (retainedExtendedCap K p cap).v (-((p + q : ℕ) : ℤ)) (-(q : ℤ)) (by push_cast; omega) =
      (K.extendXIso ComplexShape.embeddingDownNat (i := p + q)
        (i' := -((p + q : ℕ) : ℤ)) (ComplexShape.embeddingDownNat_f (p + q))).hom ≫ cap q ≫
        (K.extendXIso ComplexShape.embeddingDownNat (i := q) (i' := -(q : ℤ)) (ComplexShape.embeddingDownNat_f q)).inv := by
  simp only [retainedExtendedCap, Cochain.mk_v, dite_eq_left (by omega : -(q : ℤ) ≤ 0)]
  cases q <;> rfl

/-- Signed differential compatibility makes the extended actual cap action a closed homogeneous cochain. -/
theorem retained_extended_cap_differential_zero (K : ChainComplex C ℕ) (p : ℕ)
    (cap : ∀ q, K.X (p + q) ⟶ K.X q)
    (hd : ∀ q, cap (q + 1) ≫ K.d (q + 1) q =
      (-1 : ℤ) ^ p • (K.d (p + q + 1) (p + q) ≫ cap q)) :
    δ (p : ℤ) ((p + 1 : ℕ) : ℤ) (retainedExtendedCap K p cap) = 0 := by
  apply Cochain.ext
  intro i j h
  by_cases hj : j ≤ 0
  · obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = -(q : ℤ) := ⟨(-j).toNat, by omega⟩
    have hi : i = -((p + q + 1 : ℕ) : ℤ) := by omega
    subst i
    rw [δ_v (p : ℤ) ((p + 1 : ℕ) : ℤ) (by omega) _ _ _ h
      (-((q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ)) (by omega) (by omega)]
    erw [retained_extended_cap_negative_component K p (q + 1) cap,
      retained_extended_cap_negative_component K p q cap]
    rw [K.extend_d_eq ComplexShape.embeddingDownNat
      (ComplexShape.embeddingDownNat_f (q + 1)) (ComplexShape.embeddingDownNat_f q),
      K.extend_d_eq ComplexShape.embeddingDownNat
        (ComplexShape.embeddingDownNat_f (p + q + 1)) (ComplexShape.embeddingDownNat_f (p + q))]
    simp only [Cochain.zero_v, Category.assoc, Iso.inv_hom_id_assoc]
    rw [Units.smul_def, Int.coe_negOnePow_natCast]
    have hc : cap (q + 1) ≫ K.d (q + 1) q +
        (-1 : ℤ) ^ (p + 1) • (K.d (p + q + 1) (p + q) ≫ cap q) = 0 := by
      rw [hd q]
      simp only [pow_succ, mul_neg_one, neg_smul, add_neg_cancel]
    have ht := congrArg (fun f =>
      (K.extendXIso ComplexShape.embeddingDownNat (ComplexShape.embeddingDownNat_f (p + q + 1))).hom ≫
        f ≫ (K.extendXIso ComplexShape.embeddingDownNat (ComplexShape.embeddingDownNat_f q)).inv) hc
    simpa only [Preadditive.comp_add, Preadditive.add_comp, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp, comp_zero, zero_comp, Category.assoc] using ht
  · exact (K.isZero_extend_X ComplexShape.embeddingDownNat j (fun q hq => by
      simp only [ComplexShape.embeddingDownNat_f] at hq
      omega)).eq_of_tgt _ _

/-- The actual extended cap cocycle determined by the signed differential identity. -/
def retainedExtendedCapCocycle (K : ChainComplex C ℕ) (p : ℕ)
    (cap : ∀ q, K.X (p + q) ⟶ K.X q)
    (hd : ∀ q, cap (q + 1) ≫ K.d (q + 1) q =
      (-1 : ℤ) ^ p • (K.d (p + q + 1) (p + q) ≫ cap q)) :
    Cocycle (K.extend ComplexShape.embeddingDownNat) (K.extend ComplexShape.embeddingDownNat) (p : ℤ) :=
  Cocycle.mk (retainedExtendedCap K p cap) ((p + 1 : ℕ) : ℤ) (by omega)
    (retained_extended_cap_differential_zero K p cap hd)

/-- The actual cap action as a morphism into the shifted integer-indexed complex. -/
def retainedExtendedCapShiftHom (K : ChainComplex C ℕ) (p : ℕ)
    (cap : ∀ q, K.X (p + q) ⟶ K.X q)
    (hd : ∀ q, cap (q + 1) ≫ K.d (q + 1) q =
      (-1 : ℤ) ^ p • (K.d (p + q + 1) (p + q) ≫ cap q)) :
    K.extend ComplexShape.embeddingDownNat ⟶ (K.extend ComplexShape.embeddingDownNat)⟦(p : ℤ)⟧ :=
  Cocycle.equivHomShift.symm (retainedExtendedCapCocycle K p cap hd)

/-- The constructed shifted morphism retains the actual cap components in the original chain degrees. -/
theorem retained_extended_cap_shift_hom_component (K : ChainComplex C ℕ) (p q : ℕ)
    (cap : ∀ q, K.X (p + q) ⟶ K.X q)
    (hd : ∀ q, cap (q + 1) ≫ K.d (q + 1) q =
      (-1 : ℤ) ^ p • (K.d (p + q + 1) (p + q) ≫ cap q)) :
    ((Cocycle.equivHomShift (retainedExtendedCapShiftHom K p cap hd)).1).v
      (-((p + q : ℕ) : ℤ)) (-(q : ℤ)) (by push_cast; omega) =
    (K.extendXIso ComplexShape.embeddingDownNat (ComplexShape.embeddingDownNat_f (p + q))).hom ≫
      cap q ≫ (K.extendXIso ComplexShape.embeddingDownNat (ComplexShape.embeddingDownNat_f q)).inv := by
  simp only [retainedExtendedCapShiftHom, AddEquiv.apply_symm_apply]
  exact retained_extended_cap_negative_component K p q cap

end HodgeLean.Foundations.QuotientDuality
