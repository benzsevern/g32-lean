import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Preadditive.Basic

/-! Actual sign normalization of a cochain complex for the fixed-cycle cap convention.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Transport the actual differentials through degreewise integral-unit isomorphisms.
Source: Mathlib, Algebra.Homology.HomologicalComplex; transport through degreewise isomorphisms.
HC no distance; AV milestone no distance.
-/
def signAdjustedComplex {C : Type*} [Category* C] [Preadditive C]
    (K : CochainComplex C ℕ) (u : ℕ → ℤˣ) : CochainComplex C ℕ where
  X := K.X
  d i j := (u i • Iso.refl (K.X i)).inv ≫ K.d i j ≫ (u j • Iso.refl (K.X j)).hom
  shape i j hij := by rw [K.shape i j hij, zero_comp, comp_zero]
  d_comp_d' i j k hij hjk := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, K.d_comp_d_assoc, comp_zero, zero_comp]

#print axioms signAdjustedComplex
/-- The sign-adjusted complex retains its original actual complex by a specified isomorphism in every degree.
Source: Mathlib, Algebra.Homology.HomologicalComplex, Hom.isoOfComponents.
HC no distance; AV milestone no distance.
-/
def signAdjustedComplexIso {C : Type*} [Category* C] [Preadditive C]
    (K : CochainComplex C ℕ) (u : ℕ → ℤˣ) : K ≅ signAdjustedComplex K u :=
  HomologicalComplex.Hom.isoOfComponents (fun i => u i • Iso.refl (K.X i)) (fun i j hij => by
    change (u i • Iso.refl (K.X i)).hom ≫
        ((u i • Iso.refl (K.X i)).inv ≫ K.d i j ≫ (u j • Iso.refl (K.X j)).hom) = _
    rw [Iso.hom_inv_id_assoc]
    rfl)

#print axioms signAdjustedComplexIso
end HodgeLean.Foundations.RationalHomologyManifold
