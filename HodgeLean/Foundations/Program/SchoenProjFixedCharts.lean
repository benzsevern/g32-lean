import HodgeLean.Foundations.Program.SchoenProjAction
import HodgeLean.Foundations.Program.SchoenHomogeneousAwayAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
namespace HodgeLean.Foundations.Program

/-- The affine Proj chart square allows the target denominator to be named by an equal element. -/
theorem s2_proj_awayι_comp_map_eq {A B : Type} [CommRing A] [CommRing B]
    (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    {n : ℕ} (hn : 0 < n) (a : A) (ha : a ∈ 𝒜 n) (b : B) (hb : b ∈ ℬ n)
    (hab : f a = b) (hMN : Submonoid.powers a ≤ (Submonoid.powers b).comap f) :
    Proj.awayι ℬ b hb hn ≫ Proj.map f hf =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map f hMN)) ≫ Proj.awayι 𝒜 a ha hn := by
  subst b
  exact Proj.awayι_comp_map f hf hn a ha

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A fixed homogeneous chart intertwines the actual Proj action and the action on its fraction ring. -/
theorem s2_projAction_fixed_awayι {A G : Type} [CommRing A] [Group G]
    [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (g : G) {n : ℕ} (hn : 0 < n) (a : FixedPoints.subring A G) (ha : a.val ∈ 𝒜 n) :
    letI := s2_homogeneousAwayAction 𝒜 hgrade a
    Proj.awayι 𝒜 a.val ha hn ≫ (s2_projAction 𝒜 hgrade g).asIso.hom =
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G (Away 𝒜 a.val) g⁻¹)) ≫
        Proj.awayι 𝒜 a.val ha hn := by
  letI := s2_homogeneousAwayAction 𝒜 hgrade a
  exact s2_proj_awayι_comp_map_eq 𝒜 𝒜 (s2_gradedActionHom 𝒜 hgrade g⁻¹)
    (s2_gradedActionHom_irrelevant_le 𝒜 hgrade g⁻¹) hn a.val ha a.val ha
    (a.property g⁻¹) (s2_fixedElement_powers_stable a g⁻¹)

end HodgeLean.Foundations.Program
