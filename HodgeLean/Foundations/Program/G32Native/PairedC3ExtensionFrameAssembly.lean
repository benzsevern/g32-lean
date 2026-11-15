import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNSplittingMaps
import HodgeLean.Foundations.Program.G32Native.PairedConormalFreeStabilizedFrame

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The zero-index free module has no generators. -/
theorem paired_c3_free_zero_isZero_nat (k : ℕ) :
    IsZero (SheafOfModules.free (R := (pairedC3Proj k).ringCatSheaf) (Fin 0)) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sigma.hom_ext
  intro i
  exact Fin.elim0 i

/-- Adding a trivial generator commutes with the recursive negative summands.
The rank index increases by exactly one. -/
def pairedC3SplitBundleAddUnitIso (k a b : ℕ) :
    pairedC3SplitBundle k (a + 1) b ≅
      (SheafOfModules.free (Fin a) ⊞
        SheafOfModules.unit (pairedC3Proj k).ringCatSheaf) ⊞
          pairedC3SplitBundle k 0 b := by
  induction b with
  | zero =>
    exact paired_free_biprod_unitFinIso (pairedC3Proj k) a ≪≫
      isoBiprodZero (paired_c3_free_zero_isZero_nat k)
  | succ b ih =>
    exact biprod.mapIso ih (Iso.refl _) ≪≫ biprod.associator _ _ _

/-- A section of the original quotient arrow gives the required recursive frame. -/
def pairedC3ExtensionFrameOfSection
    (k a b : ℕ) (T : ShortComplex (pairedC3Proj k).Modules) (hT : T.ShortExact)
    (e₁ : T.X₁ ≅ (SheafOfModules.free (Fin a) ⊞
      SheafOfModules.unit (pairedC3Proj k).ringCatSheaf))
    (e₃ : T.X₃ ≅ pairedC3SplitBundle k 0 b)
    (s : T.X₃ ⟶ T.X₂) (hs : s ≫ T.g = 𝟙 _) :
    T.X₂ ≅ pairedC3SplitBundle k (a + 1) b :=
  (ShortComplex.Splitting.ofExactOfSection T hT.exact s hs hT.mono_f).isoBinaryBiproduct ≪≫
    biprod.mapIso e₁ e₃ ≪≫ (pairedC3SplitBundleAddUnitIso k a b).symm

/-- With no negative quotient summands, the original inclusion is an isomorphism. -/
theorem paired_c3_extension_frame_zero
    (k a : ℕ) (T : ShortComplex (pairedC3Proj k).Modules) (hT : T.ShortExact)
    (e₁ : T.X₁ ≅ (SheafOfModules.free (Fin a) ⊞
      SheafOfModules.unit (pairedC3Proj k).ringCatSheaf))
    (e₃ : T.X₃ ≅ pairedC3SplitBundle k 0 0) :
    Nonempty (T.X₂ ≅ pairedC3SplitBundle k (a + 1) 0) := by
  have hz : IsZero T.X₃ := (paired_c3_free_zero_isZero_nat k).of_iso e₃
  letI := hT.isIso_f_iff.mpr hz
  exact ⟨(asIso T.f).symm ≪≫ e₁ ≪≫
    (paired_free_biprod_unitFinIso (pairedC3Proj k) a).symm⟩

end HodgeLean.Foundations.Program.G32Native
