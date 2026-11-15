import HodgeLean.Foundations.Program.SchoenHomogeneousLocalizationAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The powers of an actual fixed ring element form an action-stable submonoid. -/
theorem s2_fixedElement_powers_stable {A G : Type} [CommRing A] [Group G] [MulSemiringAction G A]
    (a : FixedPoints.subring A G) (g : G) (b : A) (hb : b ∈ Submonoid.powers a.val) :
    g • b ∈ Submonoid.powers a.val := by
  obtain ⟨n, rfl⟩ := hb
  rw [smul_pow', a.property g]
  exact ⟨n, rfl⟩

/-- The actual homogeneous chart ring away from a fixed element carries the induced action. -/
def s2_homogeneousAwayAction {A G : Type} [CommRing A] [Group G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) : MulSemiringAction G (HomogeneousLocalization.Away 𝒜 a.val) :=
  s2_homogeneousLocalizationAction 𝒜 hgrade (Submonoid.powers a.val)
    (s2_fixedElement_powers_stable a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual homogeneous chart action applies the original action to the numerator
and leaves a fixed power denominator unchanged. -/
theorem s2_homogeneousAwayAction_mk {A G : Type} [CommRing A] [Group G] [MulSemiringAction G A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (a : FixedPoints.subring A G) {d : ℕ} (ha : a.val ∈ 𝒜 d)
    (g : G) (n : ℕ) (b : A) (hb : b ∈ 𝒜 (n • d)) :
    letI := s2_homogeneousAwayAction 𝒜 hgrade a
    g • HomogeneousLocalization.Away.mk 𝒜 ha n b hb =
      HomogeneousLocalization.Away.mk 𝒜 ha n (g • b) (hgrade g (n • d) b hb) := by
  letI := s2_homogeneousAwayAction 𝒜 hgrade a
  change HomogeneousLocalization.map (s2_gradedActionHom 𝒜 hgrade g) _
    (HomogeneousLocalization.Away.mk 𝒜 ha n b hb) = _
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.mk, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, s2_gradedActionHom, smul_pow', a.property g]

end HodgeLean.Foundations.Program
