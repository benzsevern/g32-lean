import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalTriadNaturality

/-! # Naturality of the actual point-excision cap -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Pulling back the normal class and pushing the ambient local class commute with the original point-excision cap.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, excision and cap naturality.
HC no distance; AV milestone no distance. -/
lemma properCycle_local_triad_cap_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D)
    (hAo : IsOpen A) (hBo : IsOpen B) (hCo : IsOpen C) (hDo : IsOpen D)
    (x : X) (y : Y) (hU : A ∪ B = ({x} : Set X)ᶜ)
    (hV : C ∪ D = ({y} : Set Y)ᶜ)
    (hf : Set.MapsTo f ({x} : Set X)ᶜ ({y} : Set Y)ᶜ) (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) C) p)
    (c : orientationGroup X (p + q) x) :
    relativeHomologyMap ℚ q (TopPair.ofSubsetHom f hB)
      (triadCapCohomologyLinear ℚ X A B p q
        (relativeCohomologyMap ℚ p (TopPair.ofSubsetHom f hA) a)
        ((properCycle_triad_local_homology_iso X A B hAo hBo x hU (p + q)).inv.hom c)) =
    triadCapCohomologyLinear ℚ Y C D p q a
      ((properCycle_triad_local_homology_iso Y C D hCo hDo y hV (p + q)).inv.hom
        (relativeHomologyMap ℚ (p + q) (TopPair.ofSubsetHom f hf) c)) := by
  rw [properCycle_triad_cap_naturality,
    properCycle_triad_point_inverse_comparison f A B C D hA hB hAo hBo hCo hDo x y hU hV hf]

end HodgeLean.Foundations.QuotientDuality
