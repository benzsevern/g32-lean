import HodgeLean.Foundations.RationalHomologyManifold.CapTargetBoundary

/-! Actual signed positive-degree window of the bounded cap target.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The original supported-chain window maps to the actual bounded cap window with exactly the adjacent fixed-cycle signs in positive preceding degree.
Source: Hatcher, Algebraic Topology, section 3.3; Bredon, Sheaf Theory, second edition, VI.12.
HC no distance; AV milestone no distance.
-/
def positiveCapTargetWindowComparison (X : TopCat.{0}) (p q : ℕ) (hp : 0 < p) :
    (subdivisionLimitSheafComplex X).sc' (q + 2) (q + 1) q ⟶
      (capTargetComplex X (p + q + 2)).sc' p (p + 1) (p + 2) := by
  let N := p + q + 2
  let C := subdivisionLimitSheafComplex X
  let A := capTargetComplex X N
  let e₀ := capTargetTermIso X N p (q + 2) hp (by omega)
  let e₁ := capTargetTermIso X N (p + 1) (q + 1) (by omega) (by omega)
  let e₂ := capTargetTermIso X N (p + 2) q (by omega) (by omega)
  have hb₁ : A.d p (p + 1) ≫ e₁.hom =
      (-1 : ℤ) ^ (p + 1) • (e₀.hom ≫ C.d (q + 2) (q + 1)) :=
    capTargetTermIso_boundary X N p (q + 1) hp (by omega)
  have hb₂ : A.d (p + 1) (p + 2) ≫ e₂.hom =
      (-1 : ℤ) ^ (p + 2) • (e₁.hom ≫ C.d (q + 1) q) :=
    capTargetTermIso_boundary X N (p + 1) q (by omega) (by omega)
  refine { τ₁ := (-1 : ℤ) ^ (p + 1) • e₀.inv
           τ₂ := e₁.inv
           τ₃ := (-1 : ℤ) ^ (p + 2) • e₂.inv
           comm₁₂ := ?_
           comm₂₃ := ?_ }
  · apply (cancel_mono e₁.hom).mp
    change (((-1 : ℤ) ^ (p + 1) • e₀.inv) ≫ A.d p (p + 1)) ≫ e₁.hom =
      (C.d (q + 2) (q + 1) ≫ e₁.inv) ≫ e₁.hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Preadditive.zsmul_comp]
    rw [hb₁]
    simp only [Preadditive.comp_zsmul, Iso.inv_hom_id_assoc, smul_smul,
      ← pow_add, (Even.add_self (p + 1)).neg_one_pow, one_smul]
  · apply (cancel_mono e₂.hom).mp
    change (e₁.inv ≫ A.d (p + 1) (p + 2)) ≫ e₂.hom =
      (C.d (q + 1) q ≫ ((-1 : ℤ) ^ (p + 2) • e₂.inv)) ≫ e₂.hom
    simp only [Category.assoc, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
      Iso.inv_hom_id, Category.comp_id]
    rw [hb₂]
    simp only [Preadditive.comp_zsmul, Iso.inv_hom_id_assoc]

#print axioms positiveCapTargetWindowComparison
end HodgeLean.Foundations.RationalHomologyManifold
