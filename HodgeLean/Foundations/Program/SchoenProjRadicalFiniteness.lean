import HodgeLean.Foundations.Program.SchoenProjRadicalCharts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry HomogeneousLocalization CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program
namespace S2RadicalProj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite homogeneous-localization maps make the actual radical-controlled
Proj scheme morphism finite. -/
theorem map_finite_of_away_finite {A B : Type} [CommRing A] [CommRing B]
    (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f.toRingHom).radical)
    (hfinite : ∀ n : ℕ, 0 < n → ∀ a : A, a ∈ 𝒜 n → (Away.map f a).Finite) :
    IsFinite (map 𝒜 ℬ f hf) := by
  apply IsZariskiLocalAtTarget.of_openCover (Proj.affineOpenCover 𝒜).openCover
  intro c
  have H := (away_isPullback 𝒜 ℬ f hf c.1.property c.2.val c.2.property).flip
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (Away.map f c.2.val))) :=
    (IsFinite.SpecMap_iff _).mpr (hfinite c.1 c.1.property c.2.val c.2.property)
  change IsFinite (pullback.snd (map 𝒜 ℬ f hf) (Proj.awayι 𝒜 c.2.val c.2.property c.1.property))
  rw [← H.isoPullback_inv_snd]
  infer_instance

end S2RadicalProj
end HodgeLean.Foundations.Program
