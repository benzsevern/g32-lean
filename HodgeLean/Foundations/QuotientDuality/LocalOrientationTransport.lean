import HodgeLean.Foundations.QuotientDuality.LocalHomeomorphPairIso
import HodgeLean.Foundations.QuotientDuality.LocalOrientationOfGlobal

/-! Coherent local orientations transported with actual global homology classes. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem homeomorph_pushforward_coherent_orientation
    (X Y : TopCat.{0}) (n : ℕ) (oX : LocalRationalOrientation X n)
    (c : Homology ℚ X n) (hc : ∀ x, localOrientation X n c x = oX.generator x)
    (H : X ≃ₜ Y) :
    ∃ oY : LocalRationalOrientation Y n,
      (∀ y, localOrientation Y n (homologyMap ℚ n (TopCat.ofHom ⟨H, H.continuous⟩) c) y =
        oY.generator y) ∧
      ∀ x, relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H x)
        (oX.generator x) = oY.generator (H x) := by
  let f := TopCat.ofHom ⟨H, H.continuous⟩
  have hn (x : X) : relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H x)
      (oX.generator x) = localOrientation Y n (homologyMap ℚ n f c) (H x) := by
    rw [← hc x]
    exact localOrientation_map n x (H x) (pointComplementHomeomorphPairMap H x) c
  have hgen : ∀ y, Function.Bijective (orientationLine Y n (homologyMap ℚ n f c) y) := by
    intro y
    obtain ⟨x, rfl⟩ := H.surjective y
    have ht := pointComplement_homeomorph_homology_bijective H x n
    have he : (fun q : ℚ => relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H x)
        (q • oX.generator x)) =
        (fun q : ℚ => q • localOrientation Y n (homologyMap ℚ n f c) (H x)) := by
      funext q
      rw [map_smul, hn x]
    change Function.Bijective (fun q : ℚ => q • localOrientation Y n (homologyMap ℚ n f c) (H x))
    rw [← he]
    exact ht.comp (oX.generates x)
  have hv : ∀ y i, i ≠ n → Subsingleton (orientationGroup Y i y) := by
    intro y i hi
    obtain ⟨x, rfl⟩ := H.surjective y
    letI := oX.vanishes x i hi
    exact (pointComplement_homeomorph_homology_bijective H x i).2.subsingleton
  exact ⟨localOrientationOfGlobal Y n (homologyMap ℚ n f c) hgen hv,
    fun _ => rfl, hn⟩

#print axioms homeomorph_pushforward_coherent_orientation
end HodgeLean.Foundations.QuotientDuality
