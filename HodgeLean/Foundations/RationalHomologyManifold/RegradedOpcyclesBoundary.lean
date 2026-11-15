import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! The actual boundary quotient under singular-chain regrading.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Regrading retains the original differential factored through the actual chain boundary quotient.
Source: Mathlib, Algebra.Homology.Embedding.ExtendHomology; naturality of the canonical opcycles quotient.
HC no distance; AV milestone no distance.
-/
theorem extendDownNat_fromOpcycles {A : Type*} [Category* A] [Abelian A]
    (C : ChainComplex A ℕ) (n : ℕ) :
    (C.extend ComplexShape.embeddingDownNat).fromOpcycles (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫
        (C.extendXIso ComplexShape.embeddingDownNat (i := n) rfl).hom =
      (C.extendOpcyclesIso ComplexShape.embeddingDownNat (j := n + 1) rfl).hom ≫
        C.fromOpcycles (n + 1) n := by
  rw [← cancel_epi ((C.extend ComplexShape.embeddingDownNat).pOpcycles (-((n + 1 : ℕ) : ℤ)))]
  simp only [HomologicalComplex.p_fromOpcycles_assoc,
    HomologicalComplex.pOpcycles_extendOpcyclesIso_hom_assoc]
  rw [HomologicalComplex.p_fromOpcycles]
  have hd := C.extend_d_eq ComplexShape.embeddingDownNat
    (i' := -((n + 1 : ℕ) : ℤ)) (j' := -(n : ℤ)) (i := n + 1) (j := n) rfl rfl
  have ht := congrArg (fun f => f ≫ (C.extendXIso ComplexShape.embeddingDownNat (i := n) rfl).hom) hd
  exact ht.trans (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

#print axioms extendDownNat_fromOpcycles
end HodgeLean.Foundations.RationalHomologyManifold
