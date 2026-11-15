import HodgeLean.Foundations.Program.G32Native.SubschemeDimensionBound
import HodgeLean.Foundations.Program.G32Native.ConormalFrameDimension

/-! Recover the ambient dimension from a smooth subscheme's conormal frame. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Source dimension plus the rank of any conormal frame equals ambient dimension. -/
theorem g32l4_conormal_frame_dimension_add
    (B : Over (Spec ↧ℂ)) (I : B.left.IdealSheafData) (m n : ℕ)
    [SmoothOfRelativeDimension n B.hom]
    [SmoothOfRelativeDimension m (s2c_subscheme B I).hom]
    (x : I.subscheme) (U : I.subscheme.Opens) (hx : x ∈ U) (r : ℕ)
    (e : Scheme.Modules.restrict (s2c_conormal I.subschemeι) U.ι ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin r) : U.toScheme.Modules)) :
    m + r = n := by
  letI : SmoothOfRelativeDimension m (I.subschemeι ≫ B.hom) :=
    inferInstanceAs (SmoothOfRelativeDimension m (s2c_subscheme B I).hom)
  letI : IsClosedImmersion (s2c_subschemeι B I).left :=
    inferInstanceAs (IsClosedImmersion I.subschemeι)
  have hmn := g32l4_smooth_subscheme_relativeDimension_le B.hom I m n x
  have hn : m + (n - m) = n := by omega
  letI : SmoothOfRelativeDimension (m + (n - m)) B.hom := by
    rw [hn]
    infer_instance
  have heq := g32l4_conormal_frame_rank_eq (s2c_subscheme B I) B m (n - m)
    (s2c_subschemeι B I) x U hx r e
  omega

/-- The conormal-frame rank is the dimension drop in the actual quotient stalk. -/
theorem g32l4_conormal_frame_stalk_dimension_add
    (B : Over (Spec ↧ℂ)) (I : B.left.IdealSheafData) (m n : ℕ)
    [SmoothOfRelativeDimension n B.hom]
    [SmoothOfRelativeDimension m (s2c_subscheme B I).hom]
    (x : I.subscheme) (U : I.subscheme.Opens) (hx : x ∈ U) (r : ℕ)
    (e : Scheme.Modules.restrict (s2c_conormal I.subschemeι) U.ι ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin r) : U.toScheme.Modules)) :
    ringKrullDim (B.left.presheaf.stalk (I.subschemeι x) ⧸
      I.stalkIdeal (I.subschemeι x)) + r =
      ringKrullDim (B.left.presheaf.stalk (I.subschemeι x)) := by
  have hdim := g32l4_conormal_frame_dimension_add B I m n x U hx r e
  have hnr : n - r = m := by omega
  letI : SmoothOfRelativeDimension (n - r) (I.subschemeι ≫ B.hom) := by
    rw [hnr]
    exact inferInstanceAs (SmoothOfRelativeDimension m (s2c_subscheme B I).hom)
  have hxI : I.subschemeι x ∈ I.support := by
    change I.subschemeι x ∈ (I.support : Set B.left)
    rw [← I.range_subschemeι]
    exact ⟨x, rfl⟩
  exact ringKrullDim_quotient_stalkIdeal_add I B.hom n r (by omega) hxI

end HodgeLean.Foundations.Program
