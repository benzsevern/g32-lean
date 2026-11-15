import HodgeLean.Foundations.Program.SchoenNormalizedChartSections
import HodgeLean.Foundations.SegreProjectiveProofs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A unit-normalized homogeneous evaluation gives its actual Proj scheme morphism through the selected affine spectrum chart. -/
theorem s2_fromGlobalSections_normalizedChart {A σ : Type} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (X : Scheme.{0}) (φ : A →+* Γ(X, ⊤))
    (hI : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map φ = ⊤)
    {r : A} {d : ℕ} (hr : r ∈ 𝒜 d) (hd : 0 < d) (hφ : φ r = 1) :
    Proj.fromOfGlobalSections 𝒜 φ hI = X.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (s2_normalizedChartLift 𝒜 r φ hφ)) ≫
        Proj.awayι 𝒜 r hr hd := by
  haveI : IsIso (X.basicOpen (φ r)).ι := by
    rw [hφ, Scheme.basicOpen_one, ← Scheme.topIso_hom]
    infer_instance
  apply (cancel_epi (X.basicOpen (φ r)).ι).mp
  rw [g3c_ι_fromOfGlobalSections 𝒜 φ hI hd hr, g3c_toBasic_eq]
  rw [← s2_normalizedChartLift_toAway 𝒜 hr φ hφ,
    CommRingCat.ofHom_comp, Spec.map_comp]
  simp only [Proj.awayι, Category.assoc, g3c_basicOpenToSpecAway_spec_assoc]

end HodgeLean.Foundations.Program
