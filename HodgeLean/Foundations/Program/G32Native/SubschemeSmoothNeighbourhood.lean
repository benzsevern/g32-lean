import HodgeLean.Foundations.Program.G32Native.SubschemeOpenNeighbourhood
import HodgeLean.Foundations.Program.G32Native.SubschemeOpenIso
import HodgeLean.Ported.Hironaka.Scheme.Snc.TotalTransformOnCentre

/-! Ambient neighbourhoods where a smooth closed subscheme has constant relative dimension. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A smooth closed subscheme has constant relative dimension after an ambient restriction. -/
theorem g32l4_smooth_subscheme_constant_dimension_neighbourhood
    {k : Type*} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)] (z : I.subscheme) :
    ∃ U : X.Opens, I.subschemeι z ∈ U ∧ ∃ m : ℕ,
      SmoothOfRelativeDimension m ((I.subschemeι ⁻¹ᵁ U).ι ≫ I.subschemeι ≫ f) := by
  obtain ⟨V, hzV, m, hdim⟩ :=
    exists_affineOpen_smoothOfRelativeDimension (I.subschemeι ≫ f) z
  obtain ⟨U, hpre⟩ := g32l4_ambient_open_for_subscheme_open I V.1
  refine ⟨U, ?_, m, ?_⟩
  · change z ∈ I.subschemeι ⁻¹ᵁ U
    rw [hpre]
    exact hzV
  · rw [hpre]
    exact hdim

/-- The actual subscheme of the pulled ideal has constant dimension on an ambient neighbourhood. -/
theorem g32l4_comap_subscheme_constant_dimension_neighbourhood
    {k : Type*} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)] (z : I.subscheme) :
    ∃ U : X.Opens, I.subschemeι z ∈ U ∧ ∃ m : ℕ,
      SmoothOfRelativeDimension m ((I.comap U.ι).subschemeι ≫ U.ι ≫ f) := by
  obtain ⟨U, hxU, m, hdim⟩ :=
    g32l4_smooth_subscheme_constant_dimension_neighbourhood f I z
  let e := g32l4_subscheme_comap_open_iso I U
  letI : SmoothOfRelativeDimension m ((I.subschemeι ⁻¹ᵁ U).ι ≫ I.subschemeι ≫ f) := hdim
  have hcomp : SmoothOfRelativeDimension m
      (e.hom ≫ (I.subschemeι ⁻¹ᵁ U).ι ≫ I.subschemeι ≫ f) := by
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + m)
        (e.hom ≫ (I.subschemeι ⁻¹ᵁ U).ι ≫ I.subschemeι ≫ f))
  have heq : e.hom ≫ (I.subschemeι ⁻¹ᵁ U).ι ≫ I.subschemeι ≫ f =
      (I.comap U.ι).subschemeι ≫ U.ι ≫ f := by
    simpa only [Category.assoc] using
      congrArg (fun k => k ≫ f) (g32l4_subscheme_comap_open_iso_to_ambient I U)
  rw [heq] at hcomp
  exact ⟨U, hxU, m, hcomp⟩

end HodgeLean.Foundations.Program
