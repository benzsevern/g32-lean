import HodgeLean.Foundations.Program.G32Native.ConormalDimensionAdd
import HodgeLean.Foundations.Program.G32Native.ConormalOpenFrames
import HodgeLean.Foundations.Program.G32Native.SubschemeSmoothNeighbourhood
import HodgeLean.Foundations.Program.G32Native.OpenStalkQuotient

/-! Read local codimension from the given conormal frames without an equidimensional centre. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Constant conormal-frame rank gives the dimension drop at every quotient stalk. -/
theorem g32l4_conormal_frames_local_codimension
    (B : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n B.hom]
    (I : B.left.IdealSheafData) [Smooth (s2c_subscheme B I).hom] (r : ℕ)
    (hframe : ∀ x : I.subscheme, ∃ V : I.subscheme.Opens, x ∈ V ∧ Nonempty
      (Scheme.Modules.restrict (s2c_conormal I.subschemeι) V.ι ≅
        (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (Fin r) : V.toScheme.Modules)))
    (z : I.subscheme) :
    ringKrullDim (B.left.presheaf.stalk (I.subschemeι z) ⧸ I.stalkIdeal (I.subschemeι z)) + r =
      ringKrullDim (B.left.presheaf.stalk (I.subschemeι z)) := by
  letI : Smooth (I.subschemeι ≫ B.hom) :=
    inferInstanceAs (Smooth (s2c_subscheme B I).hom)
  obtain ⟨U, hzU, m, hdim⟩ :=
    g32l4_comap_subscheme_constant_dimension_neighbourhood B.hom I z
  let BU : Over (Spec ↧ℂ) := Over.mk (U.ι ≫ B.hom)
  let J := I.comap U.ι
  letI : SmoothOfRelativeDimension n BU.hom := by
    change SmoothOfRelativeDimension n (U.ι ≫ B.hom)
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (U.ι ≫ B.hom))
  letI : SmoothOfRelativeDimension m (s2c_subscheme BU J).hom := hdim
  obtain ⟨y, hy⟩ := g32l4_subscheme_comap_open_lift_point I U z hzU
  obtain ⟨V, hyV, ⟨e⟩⟩ := g32l4_conormal_frames_comap_open I U r hframe y
  have hlocal := g32l4_conormal_frame_stalk_dimension_add BU J m n y V hyV r e
  have horiginal := (g32l4_comap_open_stalk_dimension_drop_iff I U
    (J.subschemeι y) r).mp hlocal
  rw [hy] at horiginal
  exact horiginal

end HodgeLean.Foundations.Program
