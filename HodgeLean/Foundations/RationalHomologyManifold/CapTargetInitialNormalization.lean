import HodgeLean.Foundations.RationalHomologyManifold.CapTargetInitialHomology

/-! Normalization of the actual initial cap-target homology identification.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual initial cap homology identification retains the original homology inclusion into the top boundary quotient.
Source: Bredon, Sheaf Theory, second edition, VI.12; uniqueness of the initial kernel identification.
HC no distance; AV milestone no distance.
-/
theorem capTargetInitialHomologyIso_inclusion (X : TopCat.{0}) (n : ℕ) :
    (capTargetInitialHomologyIso X n).hom ≫
        (subdivisionLimitSheafComplex X).homologyι (n + 1) ≫ (capTargetZeroTermIso X (n + 1)).inv =
      inv ((capTargetComplex X (n + 1)).homologyπ 0) ≫ (capTargetComplex X (n + 1)).iCycles 0 := by
  let h := capTargetInitialKernel X n
  let k := (capTargetComplex X (n + 1)).cyclesIsKernel 0 1 (CochainComplex.next ℕ 0)
  have hh : (h.conePointUniqueUpToIso k).inv ≫
      ((subdivisionLimitSheafComplex X).homologyι (n + 1) ≫ (capTargetZeroTermIso X (n + 1)).inv) =
        (capTargetComplex X (n + 1)).iCycles 0 :=
    IsLimit.conePointUniqueUpToIso_inv_comp h k WalkingParallelPair.zero
  exact congrArg (fun f => inv ((capTargetComplex X (n + 1)).homologyπ 0) ≫ f) hh

#print axioms capTargetInitialHomologyIso_inclusion
/-- The actual homology projection and the specified top boundary quotient identification give the same original homology inclusion.
Source: Bredon, Sheaf Theory, second edition, VI.12; normalization on initial cycles.
HC no distance; AV milestone no distance.
-/
theorem capTargetInitialHomologyIso_cycles (X : TopCat.{0}) (n : ℕ) :
    (capTargetComplex X (n + 1)).homologyπ 0 ≫ (capTargetInitialHomologyIso X n).hom ≫
        (subdivisionLimitSheafComplex X).homologyι (n + 1) =
      (capTargetComplex X (n + 1)).iCycles 0 ≫ (capTargetZeroTermIso X (n + 1)).hom := by
  apply (cancel_mono (capTargetZeroTermIso X (n + 1)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [capTargetInitialHomologyIso_inclusion, IsIso.hom_inv_id_assoc]

#print axioms capTargetInitialHomologyIso_cycles
end HodgeLean.Foundations.RationalHomologyManifold
