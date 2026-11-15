import HodgeLean.Foundations.Program.SchoenPowerSubalgebraGrading
import HodgeLean.Foundations.Program.SchoenFixedRingGrading
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HomogeneousLocalization
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A numerator power lying in the actual graded subring lifts the same fraction power on a chart. -/
theorem s2_away_power_lift {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (R : Subring A)
    [GradedRing (s2_subringGradedPiece 𝒜 R)]
    {f : R} {d : ℕ} (hf : f ∈ s2_subringGradedPiece 𝒜 R d)
    {a : A} {k : ℕ} (ha : a ∈ 𝒜 (k • d)) (E : ℕ) (hmem : a ^ E ∈ R) :
    ∃ z : Away (s2_subringGradedPiece 𝒜 R) f,
      Away.map (s2_subringGradedInclusion 𝒜 R) f z =
        (Away.mk 𝒜 hf k a ha) ^ E := by
  let b : R := ⟨a ^ E, hmem⟩
  have hb : b ∈ s2_subringGradedPiece 𝒜 R ((k * E) • d) := by
    change a ^ E ∈ 𝒜 ((k * E) • d)
    have h := SetLike.pow_mem_graded E ha
    convert h using 1 <;> simp only [smul_eq_mul] <;> congr 1 <;> ac_rfl
  refine ⟨Away.mk (s2_subringGradedPiece 𝒜 R) hf (k * E) b hb, ?_⟩
  rw [Away.map_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_pow, Localization.mk_pow]
  congr 1
  apply Subtype.ext
  exact pow_mul (f : A) k E

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A positive numerator power in the graded subring makes the actual chart fraction integral. -/
theorem s2_away_isIntegral_of_power_mem {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (R : Subring A)
    [GradedRing (s2_subringGradedPiece 𝒜 R)]
    {f : R} {d : ℕ} (hf : f ∈ s2_subringGradedPiece 𝒜 R d)
    {a : A} {k : ℕ} (ha : a ∈ 𝒜 (k • d)) (E : ℕ) (hE : 0 < E)
    (hmem : a ^ E ∈ R) :
    letI : Algebra (Away (s2_subringGradedPiece 𝒜 R) f) (Away 𝒜 (f : A)) :=
      (Away.map (s2_subringGradedInclusion 𝒜 R) f).toAlgebra
    IsIntegral (Away (s2_subringGradedPiece 𝒜 R) f) (Away.mk (f := (f : A)) 𝒜 hf k a ha) := by
  letI : Algebra (Away (s2_subringGradedPiece 𝒜 R) f) (Away 𝒜 (f : A)) :=
      (Away.map (s2_subringGradedInclusion 𝒜 R) f).toAlgebra
  apply IsIntegral.of_pow hE
  obtain ⟨z, hz⟩ := s2_away_power_lift 𝒜 R hf ha E hmem
  rw [← hz]
  exact isIntegral_algebraMap (x := z)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual homogeneous chart inclusion preserves every degree-zero coefficient. -/
theorem s2_away_map_fromZero {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (R : Subring A)
    [GradedRing (s2_subringGradedPiece 𝒜 R)] (f : R)
    (c : s2_subringGradedPiece 𝒜 R 0) :
    Away.map (s2_subringGradedInclusion 𝒜 R) f
      (fromZeroRingHom (s2_subringGradedPiece 𝒜 R) (Submonoid.powers f) c) =
    fromZeroRingHom 𝒜 (Submonoid.powers (f : A)) ⟨c.val.val, c.property⟩ := by
  apply HomogeneousLocalization.val_injective
  rfl

end HodgeLean.Foundations.Program
