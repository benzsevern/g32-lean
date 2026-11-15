import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace HodgeLean.Foundations.Program

/-- A graded ring map induces its specified map on the actual degree-zero coefficient spectra. -/
theorem s2_projMap_toSpecZero {A B σ τ : Type} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : (HomogeneousIdeal.irrelevant ℬ) ≤
      (HomogeneousIdeal.irrelevant 𝒜).map f)
    (c : 𝒜 0 →+* ℬ 0) (hc : ∀ a, (c a : B) = f (a : A)) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom c) := by
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change Proj.awayι ℬ (f s.2) (f.map_mem s.2.property) s.1.property ≫
      (Proj.map f hf ≫ Proj.toSpecZero 𝒜) =
    Proj.awayι ℬ (f s.2) (f.map_mem s.2.property) s.1.property ≫
      (Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom c))
  rw [← Category.assoc, Proj.awayι_comp_map f hf s.1.property s.2 s.2.property]
  simp only [Category.assoc, Proj.awayι_toSpecZero, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply HomogeneousLocalization.val_injective
  simp [Away.map, HomogeneousLocalization.map_mk, fromZeroRingHom,
    HomogeneousLocalization.val_mk, hc]

end HodgeLean.Foundations.Program
