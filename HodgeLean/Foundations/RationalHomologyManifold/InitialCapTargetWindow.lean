import HodgeLean.Foundations.RationalHomologyManifold.CapTargetBoundary
import HodgeLean.Foundations.RationalHomologyManifold.CapTargetZeroBoundary

/-! Actual initial window of the bounded cap target.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The original supported-chain window maps to the first positive bounded cap window through the actual top boundary quotient and fixed-cycle adjacent signs.
Source: Hatcher, Algebraic Topology, section 3.3; Bredon, Sheaf Theory, second edition, VI.12.
HC no distance; AV milestone no distance.
-/
def initialCapTargetWindowComparison (X : TopCat.{0}) (q : ℕ) :
    (subdivisionLimitSheafComplex X).sc' (q + 2) (q + 1) q ⟶
      (capTargetComplex X (q + 2)).sc' 0 1 2 := by
  let C := subdivisionLimitSheafComplex X
  let A := capTargetComplex X (q + 2)
  let e₀ := capTargetZeroTermIso X (q + 2)
  let e₁ := capTargetTermIso X (q + 2) 1 (q + 1) (by omega) (by omega)
  let e₂ := capTargetTermIso X (q + 2) 2 q (by omega) (by omega)
  have hb₁ : A.d 0 1 ≫ e₁.hom = -(e₀.hom ≫ C.fromOpcycles (q + 2) (q + 1)) :=
    capTargetZeroTermIso_boundary X (q + 1)
  have hb₂ : A.d 1 2 ≫ e₂.hom = e₁.hom ≫ C.d (q + 1) q := by
    simpa only [(Even.add_self 1).neg_one_pow, one_smul] using
      capTargetTermIso_boundary X (q + 2) 1 q (by omega) (by omega)
  refine { τ₁ := -(C.pOpcycles (q + 2) ≫ e₀.inv)
           τ₂ := e₁.inv
           τ₃ := e₂.inv
           comm₁₂ := ?_
           comm₂₃ := ?_ }
  · apply (cancel_mono e₁.hom).mp
    change ((-(C.pOpcycles (q + 2) ≫ e₀.inv)) ≫ A.d 0 1) ≫ e₁.hom =
      (C.d (q + 2) (q + 1) ≫ e₁.inv) ≫ e₁.hom
    simp only [Preadditive.neg_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hb₁]
    simp only [Preadditive.comp_neg, Iso.inv_hom_id_assoc, neg_neg,
      HomologicalComplex.p_fromOpcycles]
  · apply (cancel_mono e₂.hom).mp
    change (e₁.inv ≫ A.d 1 2) ≫ e₂.hom = (C.d (q + 1) q ≫ e₂.inv) ≫ e₂.hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hb₂]
    simp only [Iso.inv_hom_id_assoc]

#print axioms initialCapTargetWindowComparison
end HodgeLean.Foundations.RationalHomologyManifold
