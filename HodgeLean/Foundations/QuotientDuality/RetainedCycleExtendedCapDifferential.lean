import HodgeLean.Foundations.QuotientDuality.RetainedCycleExtendedCap

noncomputable section
open CategoryTheory Limits CochainComplex.HomComplex
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The Hom-complex differential retains both actual cap terms in every original chain degree. -/
theorem retained_extended_cap_differential_component (K : ChainComplex C ℕ) (p q : ℕ)
    (cap : ∀ q, K.X (p + q) ⟶ K.X q) :
    (δ (p : ℤ) ((p + 1 : ℕ) : ℤ) (retainedExtendedCap K p cap)).v
      (-((p + q + 1 : ℕ) : ℤ)) (-(q : ℤ)) (by push_cast; omega) =
      (K.extendXIso ComplexShape.embeddingDownNat
        (ComplexShape.embeddingDownNat_f (p + q + 1))).hom ≫
      (cap (q + 1) ≫ K.d (q + 1) q +
        (-1 : ℤ) ^ (p + 1) • (K.d (p + q + 1) (p + q) ≫ cap q)) ≫
      (K.extendXIso ComplexShape.embeddingDownNat
        (ComplexShape.embeddingDownNat_f q)).inv := by
  rw [δ_v (p : ℤ) ((p + 1 : ℕ) : ℤ) (by omega) _ _ _
    (by push_cast; omega) (-((q + 1 : ℕ) : ℤ))
    (-((p + q : ℕ) : ℤ)) (by omega) (by omega)]
  erw [retained_extended_cap_negative_component K p (q + 1) cap,
    retained_extended_cap_negative_component K p q cap]
  rw [K.extend_d_eq ComplexShape.embeddingDownNat
    (ComplexShape.embeddingDownNat_f (q + 1)) (ComplexShape.embeddingDownNat_f q),
    K.extend_d_eq ComplexShape.embeddingDownNat
      (ComplexShape.embeddingDownNat_f (p + q + 1)) (ComplexShape.embeddingDownNat_f (p + q))]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Units.smul_def,
    Int.coe_negOnePow_natCast, Preadditive.comp_add, Preadditive.add_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]

/-- The extended cap component retains an arbitrary specified source-degree equality. -/
theorem retained_extended_cap_component_of_degree (K : ChainComplex C ℕ) (p q : ℕ)
    (cap : ∀ q, K.X (p + q) ⟶ K.X q) (i : ℤ)
    (hi : ComplexShape.embeddingDownNat.f (p + q) = i)
    (h : i + (p : ℤ) = -(q : ℤ)) :
    (retainedExtendedCap K p cap).v i (-(q : ℤ)) h =
      (K.extendXIso ComplexShape.embeddingDownNat hi).hom ≫ cap q ≫
        (K.extendXIso ComplexShape.embeddingDownNat (ComplexShape.embeddingDownNat_f q)).inv := by
  simp only [retainedExtendedCap, Cochain.mk_v, dite_eq_left (by omega : -(q : ℤ) ≤ 0)]
  cases q <;> rfl

/-- Extension comparison maps respect equality of the original chain degrees. -/
theorem retained_extend_xiso_transport (K : ChainComplex C ℕ) {a b : ℕ} {i : ℤ}
    (ha : ComplexShape.embeddingDownNat.f a = i)
    (hb : ComplexShape.embeddingDownNat.f b = i) (hab : a = b) :
    (K.extendXIso ComplexShape.embeddingDownNat ha).hom ≫
      eqToHom (congrArg K.X hab) = (K.extendXIso ComplexShape.embeddingDownNat hb).hom := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

/-- The full homogeneous differential is the extension of its actual signed chain terms. -/
theorem retained_extended_cap_differential (K : ChainComplex C ℕ) (p : ℕ)
    (cap : ∀ q, K.X (p + q) ⟶ K.X q) :
    δ (p : ℤ) ((p + 1 : ℕ) : ℤ) (retainedExtendedCap K p cap) =
      retainedExtendedCap K (p + 1) (fun q =>
        eqToHom (by congr 1; omega : K.X (p + 1 + q) = K.X (p + (q + 1))) ≫
          cap (q + 1) ≫ K.d (q + 1) q +
        (-1 : ℤ) ^ (p + 1) • (K.d (p + 1 + q) (p + q) ≫ cap q)) := by
  apply Cochain.ext
  intro i j h
  by_cases hj : j ≤ 0
  · obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = -(q : ℤ) := ⟨(-j).toNat, by omega⟩
    have hi : i = -((p + q + 1 : ℕ) : ℤ) := by omega
    subst i
    have hb : ComplexShape.embeddingDownNat.f (p + 1 + q) = -((p + q + 1 : ℕ) : ℤ) := by
      simp only [ComplexShape.embeddingDownNat_f]; omega
    rw [retained_extended_cap_differential_component,
      retained_extended_cap_component_of_degree K (p + 1) q _ _ hb h]
    have ht (a b d : ℕ) (hab : a = b) :
        eqToHom (congrArg K.X hab) ≫ K.d b d = K.d a d := by
      subst b
      simp only [eqToHom_refl, Category.id_comp]
    have he := retained_extend_xiso_transport K hb
      (ComplexShape.embeddingDownNat_f (p + q + 1))
      (by omega : p + 1 + q = p + q + 1)
    have hh :
        eqToHom (by congr 1; omega : K.X (p + 1 + q) = K.X (p + (q + 1))) ≫
            cap (q + 1) ≫ K.d (q + 1) q +
          (-1 : ℤ) ^ (p + 1) • (K.d (p + 1 + q) (p + q) ≫ cap q) =
        eqToHom (congrArg K.X (by omega : p + 1 + q = p + q + 1)) ≫
          (cap (q + 1) ≫ K.d (q + 1) q +
            (-1 : ℤ) ^ (p + 1) • (K.d (p + q + 1) (p + q) ≫ cap q)) := by
      simp only [Preadditive.comp_add, Preadditive.comp_zsmul, ← Category.assoc]
      rw [ht (p + 1 + q) (p + q + 1) (p + q) (by omega)]
    rw [hh]
    simp only [← Category.assoc]
    rw [he]
  · exact (K.isZero_extend_X ComplexShape.embeddingDownNat j (fun q hq => by
      simp only [ComplexShape.embeddingDownNat_f] at hq
      omega)).eq_of_tgt _ _

/-- Integer scalar multiplication commutes with extension of actual graded cap maps. -/
theorem retained_extended_cap_zsmul (K : ChainComplex C ℕ) (p : ℕ)
    (cap : ∀ q, K.X (p + q) ⟶ K.X q) (r : ℤ) :
    retainedExtendedCap K p (fun q => r • cap q) = r • retainedExtendedCap K p cap := by
  apply Cochain.ext
  intro i j h
  by_cases hj : j ≤ 0
  · simp only [retainedExtendedCap, Cochain.mk_v, Cochain.smul_v, dite_eq_left hj,
      Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  · exact (K.isZero_extend_X ComplexShape.embeddingDownNat j (fun q hq => by
      simp only [ComplexShape.embeddingDownNat_f] at hq
      omega)).eq_of_tgt _ _

end HodgeLean.Foundations.QuotientDuality
