import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects

/-! # Reassociation of the split projective bundles -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Reassociate the trivial and negative summands without changing either rank. -/
def pairedC3SplitBundleSum (k a b : ℕ) :
    pairedC3SplitBundle k a 0 ⊞ pairedC3SplitBundle k 0 b ≅
      pairedC3SplitBundle k a b := by
  induction b with
  | zero =>
    exact biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso (Fin a) (Fin 0) ≪≫
      SheafOfModules.freeFunctor.mapIso finSumFinEquiv.toIso ≪≫
      eqToIso (by rw [Nat.add_zero]; rfl)
  | succ b ih =>
    exact (biprod.associator _ _ _).symm ≪≫ biprod.mapIso ih (Iso.refl _)

/-- A quotient with no negative summands has its unique zero section. -/
theorem paired_c3_zero_negative_quotient_section
    (k : ℕ) (E : ShortComplex (pairedC3Proj k).Modules)
    (e₃ : E.X₃ ≅ pairedC3SplitBundle k 0 0) :
    ∃ s : E.X₃ ⟶ E.X₂, s ≫ E.g = 𝟙 _ := by
  refine ⟨0, ?_⟩
  apply (cancel_epi e₃.inv).1
  apply (SheafOfModules.freeHomEquiv _ (I := Fin 0)).injective
  funext j
  exact Fin.elim0 j

/-- A short exact sequence with zero trivial kernel has an invertible quotient arrow. -/
theorem paired_c3_zero_trivial_kernel_section
    (k : ℕ) (E : ShortComplex (pairedC3Proj k).Modules)
    (hE : E.ShortExact) (e₁ : E.X₁ ≅ pairedC3SplitBundle k 0 0) :
    ∃ s : E.X₃ ⟶ E.X₂, s ≫ E.g = 𝟙 _ := by
  have hz : IsZero E.X₁ := by
    rw [IsZero.iff_id_eq_zero]
    apply (cancel_epi e₁.inv).1
    apply (SheafOfModules.freeHomEquiv _ (I := Fin 0)).injective
    funext j
    exact Fin.elim0 j
  letI : IsIso E.g := hE.isIso_g_iff.mpr hz
  exact ⟨inv E.g, IsIso.inv_hom_id E.g⟩

#print axioms paired_c3_zero_trivial_kernel_section
#print axioms paired_c3_zero_negative_quotient_section
#print axioms pairedC3SplitBundleSum
end HodgeLean.Foundations.Program.G32Native
