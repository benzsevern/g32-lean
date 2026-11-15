import HodgeLean.Foundations.Program.G32Native.SubschemeCodimensionSmooth
import HodgeLean.Foundations.Program.SchoenCycleC2SmoothConormalFramesHelpers

/-! Recover conormal frames from smoothness and quotient-stalk codimension. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Constant quotient-stalk codimension supplies actual local conormal frames of that rank. -/
theorem g32l4_conormal_frames_of_stalk_codimension
    (B : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n B.hom]
    (I : B.left.IdealSheafData) [Smooth (s2c_subscheme B I).hom] (r : ℕ)
    (hcodim : ∀ q : I.subscheme,
      ringKrullDim (B.left.presheaf.stalk (I.subschemeι q) ⧸ I.stalkIdeal (I.subschemeι q)) + r =
        ringKrullDim (B.left.presheaf.stalk (I.subschemeι q))) :
    ∀ q : I.subscheme, ∃ U : I.subscheme.Opens, q ∈ U ∧ Nonempty
      (Scheme.Modules.restrict (s2c_conormal I.subschemeι) U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin r) : U.toScheme.Modules)) := by
  letI : Smooth (I.subschemeι ≫ B.hom) :=
    inferInstanceAs (Smooth (s2c_subscheme B I).hom)
  letI : SmoothOfRelativeDimension (n - r) (I.subschemeι ≫ B.hom) :=
    g32l4_subscheme_smoothOfRelativeDimension_of_codimension B.hom n I r hcodim
  letI : SmoothOfRelativeDimension (n - r) (s2c_subscheme B I).hom :=
    inferInstanceAs (SmoothOfRelativeDimension (n - r) (I.subschemeι ≫ B.hom))
  letI : IsClosedImmersion (s2c_subschemeι B I).left :=
    inferInstanceAs (IsClosedImmersion I.subschemeι)
  intro q
  have hcount : dimCount (I.subschemeι ≫ B.hom) q = n - r :=
    Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension
      (I.subschemeι ≫ B.hom) (n - r) q
  have htotal := g32l4_subscheme_dimCount_add_codimension B.hom n I r hcodim q
  rw [hcount] at htotal
  have hnr : (n - r) + r = n := by exact_mod_cast htotal
  letI : SmoothOfRelativeDimension ((n - r) + r) B.hom := by
    rw [hnr]
    infer_instance
  exact s2e_smooth_closedImmersion_conormal_frames
    (s2c_subscheme B I) B (n - r) r (s2c_subschemeι B I) q

end HodgeLean.Foundations.Program
