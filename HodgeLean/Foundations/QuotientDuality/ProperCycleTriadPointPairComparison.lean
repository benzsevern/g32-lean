import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalTriadNaturality

/-! # Original point-pair maps in inverse triad excision comparisons
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The inverse original point-excision comparison commutes with an actual point-pair map preserving both triad subspaces.
Source: properCycle_triad_point_inverse_comparison; TopPair.Hom.w.
HC no distance; AV milestone no distance. -/
lemma properCycle_triad_point_pair_inverse_comparison
    {X Y : TopCat.{0}} (x : X) (y : Y)
    (g : pointComplementPair x ⟶ pointComplementPair y)
    (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo (TopPair.Hom.fst g) A C) (hB : Set.MapsTo (TopPair.Hom.fst g) B D)
    (hAo : IsOpen A) (hBo : IsOpen B) (hCo : IsOpen C) (hDo : IsOpen D)
    (hUX : A ∪ B = ({x} : Set X)ᶜ) (hUY : C ∪ D = ({y} : Set Y)ᶜ)
    (n : ℕ) (c : orientationGroup X n x) :
    (HomologicalComplex.homologyMap
        (properCycle_triad_relative_chain_map (TopPair.Hom.fst g) A B C D hA hB) n).hom
      ((properCycle_triad_local_homology_iso X A B hAo hBo x hUX n).inv.hom c) =
    (properCycle_triad_local_homology_iso Y C D hCo hDo y hUY n).inv.hom
      (relativeHomologyMap ℚ n g c) := by
  have hf : Set.MapsTo (TopPair.Hom.fst g) ({x} : Set X)ᶜ ({y} : Set Y)ᶜ := by
    intro u hu
    have he := ConcreteCategory.congr_hom g.w (⟨u, hu⟩ : {u : X | u ≠ x})
    exact he ▸ ((TopPair.Hom.snd g) ⟨u, hu⟩).property
  have hg : TopPair.ofSubsetHom (TopPair.Hom.fst g) hf = g := by
    ext u : 2
    · apply Subtype.ext
      exact (ConcreteCategory.congr_hom g.w u).symm
    · rfl
  have h := properCycle_triad_point_inverse_comparison
    (TopPair.Hom.fst g) A B C D hA hB hAo hBo hCo hDo x y hUX hUY hf n c
  rw [hg] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
