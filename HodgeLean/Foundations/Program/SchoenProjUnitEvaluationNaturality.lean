import HodgeLean.Foundations.Program.SchoenNormalizedProjChart
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual Proj morphisms from unit-normalized global evaluations commute with graded scheme maps. -/
theorem s2_fromGlobalSections_comp_map_of_unit {A B σ τ : Type} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (X : Scheme.{0}) (φ : B →+* Γ(X, ⊤))
    (hB : (HomogeneousIdeal.irrelevant ℬ).toIdeal.map φ = ⊤)
    (hA : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (φ.comp f.toRingHom) = ⊤)
    {r : A} {d : ℕ} (hr : r ∈ 𝒜 d) (hd : 0 < d) (hφ : φ (f r) = 1) :
    Proj.fromOfGlobalSections ℬ φ hB ≫ Proj.map f hf =
      Proj.fromOfGlobalSections 𝒜 (φ.comp f.toRingHom) hA := by
  rw [s2_fromGlobalSections_normalizedChart ℬ X φ hB (f.map_mem hr) hd hφ,
    s2_fromGlobalSections_normalizedChart 𝒜 X (φ.comp f.toRingHom) hA hr hd hφ]
  simp only [Category.assoc, GradedRingHom.coe_toRingHom]
  rw [Proj.awayι_comp_map f hf hd r hr, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    s2_normalizedChartLift_map 𝒜 ℬ f hr φ hφ]

end HodgeLean.Foundations.Program
