import HodgeLean.Foundations.Program.G32Native.ConormalOpenIso
import HodgeLean.Foundations.Program.G32Native.PullbackLocalFrame

/-! Preserve actual conormal-frame ranks under ambient open restriction. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Local conormal frames retain their rank when the ideal is restricted to an ambient open. -/
theorem g32l4_conormal_frames_comap_open {X : Scheme}
    (I : X.IdealSheafData) (U : X.Opens) (r : ℕ)
    (h : ∀ x : I.subscheme, ∃ V : I.subscheme.Opens, x ∈ V ∧ Nonempty
      (Scheme.Modules.restrict (s2c_conormal I.subschemeι) V.ι ≅
        (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (Fin r) : V.toScheme.Modules))) :
    ∀ y : (I.comap U.ι).subscheme,
      ∃ V : (I.comap U.ι).subscheme.Opens, y ∈ V ∧ Nonempty
        (Scheme.Modules.restrict (s2c_conormal (I.comap U.ι).subschemeι) V.ι ≅
          (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (Fin r) : V.toScheme.Modules)) := by
  exact g32l4_local_frames_of_pullback_iso
    ((g32l4_subscheme_comap_open_iso I U).hom ≫ (I.subschemeι ⁻¹ᵁ U).ι)
    (s2c_conormal I.subschemeι) (s2c_conormal (I.comap U.ι).subschemeι) r
    (g32l4_conormal_comap_open_iso I U) h

end HodgeLean.Foundations.Program
