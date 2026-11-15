import HodgeLean.Foundations.RationalHomologyManifold.CapTargetComplex

/-! The actual differential sign in the bounded fixed-cycle cap model.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Consecutive degreewise units give the specified sign on the actual shifted target differential.
Source: Hatcher, Algebraic Topology, section 3.3; normalization of the fixed-cycle cap differential.
HC no distance; AV milestone no distance.
-/
theorem capTargetComplex_d (X : TopCat.{0}) (N p : ℕ) :
    (capTargetComplex X N).d p (p + 1) =
      (-1 : ℤ) ^ (N + p + 1) • (capUnnormalizedTargetComplex X N).d p (p + 1) := by
  have hu : ((capDegreeUnit N p)⁻¹ : ℤˣ) * capDegreeUnit N (p + 1) =
      (-1 : ℤˣ) ^ (N + p + 1) := by rw [capDegreeUnit, inv_mul_cancel_left]
  have hv := congrArg (fun u : ℤˣ => (u : ℤ)) hu
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at hv
  change (capDegreeUnit N p • Iso.refl _).inv ≫
    (capUnnormalizedTargetComplex X N).d p (p + 1) ≫
      (capDegreeUnit N (p + 1) • Iso.refl _).hom = _
  simp only [Preadditive.smul_iso_inv, Preadditive.smul_iso_hom, Iso.refl_inv, Iso.refl_hom,
    Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp,
    Category.comp_id, smul_smul]
  rw [mul_comm, hv]

#print axioms capTargetComplex_d
/-- The target differential has exactly the fixed-cycle cap sign on the actual good orientation truncation.
Source: Hatcher, Algebraic Topology, section 3.3; the signed boundary formula for cap by a fixed cycle.
HC no distance; AV milestone no distance.
-/
theorem capTargetComplex_d_signed (X : TopCat.{0}) (N p : ℕ) :
    (capTargetComplex X N).d p (p + 1) =
      (-1 : ℤ) ^ (p + 1) • (subdivisionTruncatedSheafComplex X N).d
        ((p : ℤ) + -(N : ℤ)) (((p + 1 : ℕ) : ℤ) + -(N : ℤ)) := by
  rw [capTargetComplex_d]
  change (-1 : ℤ) ^ (N + p + 1) • ((-(N : ℤ)).negOnePow • _) = _
  simp only [Units.smul_def, Int.negOnePow_neg, Int.coe_negOnePow_natCast, smul_smul]
  have hs : (-1 : ℤ) ^ (N + p + 1) * (-1 : ℤ) ^ N = (-1 : ℤ) ^ (p + 1) := by
    rw [← pow_add, show N + p + 1 + N = N + N + (p + 1) by omega, pow_add,
      (Even.add_self N).neg_one_pow, one_mul]
  rw [hs]
  rfl

#print axioms capTargetComplex_d_signed
end HodgeLean.Foundations.RationalHomologyManifold
