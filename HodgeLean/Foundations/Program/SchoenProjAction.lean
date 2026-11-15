import HodgeLean.Foundations.Program.SchoenGradedActionHom
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every degree-preserving action element covers the actual irrelevant ideal. -/
theorem s2_gradedActionHom_irrelevant_le {A G : Type} [CommRing A] [Group G]
    [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n) (g : G) :
    HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant 𝒜).map
      (s2_gradedActionHom 𝒜 hgrade g) := by
  apply (HomogeneousIdeal.irrelevant_le 𝒜).mpr
  intro n hn a ha
  change a ∈ Ideal.map (s2_gradedActionHom 𝒜 hgrade g).toRingHom
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  have hm : g⁻¹ • a ∈ HomogeneousIdeal.irrelevant 𝒜 :=
    HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn (hgrade g⁻¹ n a ha)
  have he := Ideal.mem_map_of_mem (s2_gradedActionHom 𝒜 hgrade g).toRingHom hm
  simpa [s2_gradedActionHom] using he

/-- The actual Proj scheme endomorphism induced by a degree-preserving action element. -/
def s2_projActionMap {A G : Type} [CommRing A] [Group G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n) (g : G) :
    Proj 𝒜 ⟶ Proj 𝒜 :=
  Proj.map (s2_gradedActionHom 𝒜 hgrade g) (s2_gradedActionHom_irrelevant_le 𝒜 hgrade g)

/-- The identity group element induces the actual Proj identity morphism. -/
theorem s2_projActionMap_one {A G : Type} [CommRing A] [Group G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n) :
    s2_projActionMap 𝒜 hgrade (1 : G) = 𝟙 (Proj 𝒜) := by
  unfold s2_projActionMap
  simp only [s2_gradedActionHom_one, Proj.map_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Multiplication of graded action elements gives contravariant Proj composition. -/
theorem s2_projActionMap_mul {A G : Type} [CommRing A] [Group G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n) (g h : G) :
    s2_projActionMap 𝒜 hgrade (g * h) =
      s2_projActionMap 𝒜 hgrade g ≫ s2_projActionMap 𝒜 hgrade h := by
  unfold s2_projActionMap
  simp only [s2_gradedActionHom_mul]
  exact Proj.map_comp _ _ _ _

/-- A degree-preserving group element defines an automorphism of the actual Proj scheme. -/
def s2_projActionIso {A G : Type} [CommRing A] [Group G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n) (g : G) : Proj 𝒜 ≅ Proj 𝒜 where
  hom := s2_projActionMap 𝒜 hgrade g⁻¹
  inv := s2_projActionMap 𝒜 hgrade g
  hom_inv_id := by rw [← s2_projActionMap_mul, inv_mul_cancel, s2_projActionMap_one]
  inv_hom_id := by rw [← s2_projActionMap_mul, mul_inv_cancel, s2_projActionMap_one]

/-- A degree-preserving ring action induces a group action on the actual Proj scheme. -/
def s2_projAction {A G : Type} [CommRing A] [Group G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n) : G →* Aut (Proj 𝒜) where
  toFun g := Aut.of (s2_projActionIso 𝒜 hgrade g)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    simp [s2_projActionIso, s2_projActionMap_one]
  map_mul' g h := by
    apply Aut.ext
    apply Iso.ext
    change s2_projActionMap 𝒜 hgrade (g * h)⁻¹ =
      s2_projActionMap 𝒜 hgrade h⁻¹ ≫ s2_projActionMap 𝒜 hgrade g⁻¹
    rw [mul_inv_rev, s2_projActionMap_mul]

/-- The actual Proj action preserves the basic open of every fixed ring element. -/
theorem s2_projAction_fixedBasicOpen {A G : Type} [CommRing A] [Group G]
    [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) (g : G) :
    (s2_projAction 𝒜 hgrade g).asIso.hom ⁻¹ᵁ Proj.basicOpen 𝒜 a.val =
      Proj.basicOpen 𝒜 a.val := by
  change Proj.basicOpen 𝒜 (g⁻¹ • a.val) = Proj.basicOpen 𝒜 a.val
  rw [a.property g⁻¹]

/-- The actual Proj action has the expected homogeneous affine chart square. -/
theorem s2_projAction_awayι {A G : Type} [CommRing A] [Group G]
    [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (g : G) {n : ℕ} (hn : 0 < n) (a : A) (ha : a ∈ 𝒜 n) :
    Proj.awayι 𝒜 (g⁻¹ • a) (hgrade g⁻¹ n a ha) hn ≫
      (s2_projAction 𝒜 hgrade g).asIso.hom =
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
      (s2_gradedActionHom 𝒜 hgrade g⁻¹) a)) ≫ Proj.awayι 𝒜 a ha hn :=
  Proj.awayι_comp_map (s2_gradedActionHom 𝒜 hgrade g⁻¹)
    (s2_gradedActionHom_irrelevant_le 𝒜 hgrade g⁻¹) hn a ha

end HodgeLean.Foundations.Program
