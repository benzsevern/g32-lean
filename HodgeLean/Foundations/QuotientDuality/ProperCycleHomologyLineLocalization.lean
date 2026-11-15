import HodgeLean.Foundations.QuotientDuality.ProperCycleSingletonOrientation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Detection of actual top homology on a normalized local orientation -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Localization at a point detects every class on a rational homology line carrying a nonzero local orientation.
Source: Hatcher, Algebraic Topology, section 3.3, localization of fundamental classes.
HC no distance; AV milestone no distance. -/
lemma properCycle_homology_line_local_orientation_injective
    (X : TopCat.{0}) (n : ℕ) (x : X) (c : Homology ℚ X n)
    (hc : localOrientation X n c x ≠ 0)
    (hdim : Module.finrank ℚ (Homology ℚ X n) = 1) :
    Function.Injective (fun a : Homology ℚ X n => localOrientation X n a x) := by
  have hcz : c ≠ 0 := by
    intro h
    apply hc
    rw [h]
    exact map_zero (relativeHomologyProjection ℚ (pointComplementPair x) n).hom
  intro a b hab
  obtain ⟨r, hr⟩ := (finrank_eq_one_iff_of_nonzero' c hcz).mp hdim a
  obtain ⟨s, hs⟩ := (finrank_eq_one_iff_of_nonzero' c hcz).mp hdim b
  have hsc : r • localOrientation X n c x = s • localOrientation X n c x := by
    change r • (relativeHomologyProjection ℚ (pointComplementPair x) n) c =
      s • (relativeHomologyProjection ℚ (pointComplementPair x) n) c
    rw [← map_smul, ← map_smul, hr, hs]
    exact hab
  have hrs := smul_left_injective ℚ hc hsc
  rw [← hr, ← hs, hrs]

end HodgeLean.Foundations.QuotientDuality
