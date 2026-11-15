import HodgeLean.Foundations.QuotientDuality.OrientationLocalReduction
import HodgeLean.Foundations.QuotientDuality.OrientationScaling

/-! Transport of local classes along a finite orbit. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

variable (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X]

def orbitPointRestriction (y : orbitSpace G X) (x : X) (hx : orbitMap G X x = y) :
    orbitComplementPair G X y ⟶ pointComplementPair x :=
  TopPair.ofSubsetHom (𝟙 X) fun t ht => by
    change t ≠ x
    intro h
    apply ht
    change orbitMap G X t = y
    simpa only [h] using hx

def pointDeckMap [ContinuousConstSMul G X] (g : G) (x : X) :
    pointComplementPair x ⟶ pointComplementPair (g⁻¹ • x) :=
  TopPair.ofSubsetHom (deckMap G X g) fun t ht => by
    change g⁻¹ • t ≠ g⁻¹ • x
    exact (Homeomorph.smul g⁻¹).injective.ne ht

lemma orbitPointRestriction_global (y : orbitSpace G X) (x : X)
    (hx : orbitMap G X x = y) (n : ℕ) (c : Homology ℚ X n) :
    relativeHomologyMap ℚ n (orbitPointRestriction G X y x hx)
      ((relativeHomologyProjection ℚ (orbitComplementPair G X y) n).hom c) =
        localOrientation X n c x := by
  rw [relative_projection_naturality]
  change (relativeHomologyProjection ℚ (pointComplementPair x) n).hom
    (homologyMap ℚ n (𝟙 X) c) = _
  rw [homologyMap_id]
  rfl

lemma pointDeck_localOrientation [ContinuousConstSMul G X] (g : G) (x : X)
    (n : ℕ) (c : Homology ℚ X n)
    (hc : homologyMap ℚ n (deckMap G X g) c = c) :
    relativeHomologyMap ℚ n (pointDeckMap G X g x) (localOrientation X n c x) =
      localOrientation X n c (g⁻¹ • x) := by
  unfold localOrientation
  rw [relative_projection_naturality]
  change (relativeHomologyProjection ℚ (pointComplementPair (g⁻¹ • x)) n).hom
    (homologyMap ℚ n (deckMap G X g) c) = _
  rw [hc]

lemma orbitPointRestriction_deck [ContinuousConstSMul G X] (y : orbitSpace G X)
    (g : G) (x : X) (hx : orbitMap G X x = y)
    (hgx : orbitMap G X (g⁻¹ • x) = y) :
    orbitPointRestriction G X y x hx ≫ pointDeckMap G X g x =
      orbitComplementDeckMap G X y g ≫ orbitPointRestriction G X y (g⁻¹ • x) hgx := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext t <;> rfl

lemma orbit_fixed_class_detected_at_one_point [Finite G] [T2Space X]
    [ContinuousConstSMul G X] (y : orbitSpace G X) (x₀ : X)
    (hx₀ : orbitMap G X x₀ = y) (n : ℕ)
    (c : RelativeHomology ℚ (orbitComplementPair G X y) n)
    (hfixed : ∀ g, relativeHomologyMap ℚ n (orbitComplementDeckMap G X y g) c = c)
    (hzero : relativeHomologyMap ℚ n (orbitPointRestriction G X y x₀ hx₀) c = 0) :
    c = 0 := by
  apply finite_support_detects_zero X {x : X | orbitMap G X x = y}
    (orbit_fiber_finite G X y) n c
  intro x hx
  change relativeHomologyMap ℚ n (orbitPointRestriction G X y x hx) c = 0
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact (hx.trans hx₀.symm))
  have hmove : (g⁻¹)⁻¹ • x₀ = x := by simpa only [inv_inv] using hg
  have hxg : orbitMap G X ((g⁻¹)⁻¹ • x₀) = y := by rw [hmove]; exact hx
  have hs := congrArg (fun f => relativeHomologyMap ℚ n f c)
    (orbitPointRestriction_deck G X y g⁻¹ x₀ hx₀ hxg)
  simp only [relativeHomologyMap_comp, LinearMap.comp_apply, hzero, map_zero, hfixed] at hs
  cases hmove
  exact hs.symm

lemma orbit_fixed_class_scalar [Finite G] [T2Space X] [ContinuousConstSMul G X]
    (n : ℕ) (cX : Homology ℚ X n)
    (hlocal : ∀ x, Function.Surjective (orientationLine X n cX x))
    (hpreserve : ∀ g : G, homologyMap ℚ n (deckMap G X g) cX = cX)
    (y : orbitSpace G X) (c : RelativeHomology ℚ (orbitComplementPair G X y) n)
    (hfixed : ∀ g, relativeHomologyMap ℚ n (orbitComplementDeckMap G X y g) c = c) :
    ∃ r : ℚ, c = r • (relativeHomologyProjection ℚ (orbitComplementPair G X y) n).hom cX := by
  obtain ⟨x₀, hx₀⟩ := Quotient.mk_surjective y
  obtain ⟨r, hr⟩ := hlocal x₀
    (relativeHomologyMap ℚ n (orbitPointRestriction G X y x₀ hx₀) c)
  change r • localOrientation X n cX x₀ =
    relativeHomologyMap ℚ n (orbitPointRestriction G X y x₀ hx₀) c at hr
  refine ⟨r, sub_eq_zero.mp ?_⟩
  apply orbit_fixed_class_detected_at_one_point G X y x₀ hx₀ n
  · intro g
    rw [map_sub, map_smul, hfixed g,
      orbit_relative_projection_preserved G X y g n cX (hpreserve g)]
  · rw [map_sub, map_smul, orbitPointRestriction_global, ← hr, sub_self]

end HodgeLean.Foundations.QuotientDuality
