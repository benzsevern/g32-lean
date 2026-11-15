import HodgeLean.Foundations.Program.G32Native.PairedC3FreeExtension

/-! # A split extension with a specified free middle module -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A frame and a rank decomposition supply the short exact extension
used by M1. This construction concerns any scheme and any framed module. -/
theorem paired_c3_extension_of_frame {X : Scheme.{0}} (M : X.Modules)
    (a b k : ℕ) (h : a + b = k)
    (e : M ≅ (SheafOfModules.free (Fin k) : X.Modules)) :
    ∃ E : ShortComplex X.Modules,
      E.ShortExact ∧ E.X₂.IsQuasicoherent ∧ Nonempty (E.X₂ ≅ M) ∧
      Nonempty (E.X₁ ≅ SheafOfModules.free (Fin a)) ∧
      Nonempty (E.X₃ ≅ SheafOfModules.free (Fin b)) := by
  let A : X.Modules := SheafOfModules.free (Fin a)
  let B : X.Modules := SheafOfModules.free (Fin b)
  let E := ShortComplex.mk (biprod.inl : A ⟶ A ⊞ B)
    (biprod.snd : A ⊞ B ⟶ B) (biprod.inl_snd)
  let ef : E.X₂ ≅ SheafOfModules.free (Fin k) :=
    biprod.isoCoprod A B ≪≫ SheafOfModules.freeSumIso (Fin a) (Fin b) ≪≫
      (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso
        (finSumFinEquiv.trans (Equiv.cast (congrArg Fin h))).toIso
  have hqc : E.X₂.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent _).prop_of_iso ef.symm inferInstance
  exact ⟨E, (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact,
    hqc, ⟨ef ≪≫ e.symm⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩

#print axioms paired_c3_extension_of_frame
end HodgeLean.Foundations.Program.G32Native
