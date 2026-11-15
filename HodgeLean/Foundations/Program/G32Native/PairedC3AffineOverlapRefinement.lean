import HodgeLean.Foundations.Program.G32Native.PairedC3QuotientOverlapExt

/-! # Simultaneous affine refinements on the base and the blow-up -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A point of two source charts above two base charts has simultaneous
affine refinements. Neither intersection is assumed affine, and the point
need not be a closed point. -/
theorem pairedC3_affine_overlap_refinement
    {X Y : Scheme} (p : X ⟶ Y) (x : X)
    (U U' : Y.affineOpens) (V V' : X.affineOpens)
    (hxU : p x ∈ U.1) (hxU' : p x ∈ U'.1)
    (hxV : x ∈ V.1) (hxV' : x ∈ V'.1) :
    ∃ (W : Y.affineOpens) (Z : X.affineOpens),
      p x ∈ W.1 ∧ x ∈ Z.1 ∧ W.1 ≤ U.1 ∧ W.1 ≤ U'.1 ∧
      Z.1 ≤ V.1 ∧ Z.1 ≤ V'.1 ∧ Z.1 ≤ p ⁻¹ᵁ W.1 := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWle⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show p x ∈ U.1 ⊓ U'.1 from ⟨hxU, hxU'⟩) (U.1 ⊓ U'.1).2
  obtain ⟨_, ⟨Z, hZ, rfl⟩, hxZ, hZle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (V.1 ⊓ V'.1) ⊓ p ⁻¹ᵁ W from ⟨⟨hxV, hxV'⟩, hxW⟩)
      ((V.1 ⊓ V'.1) ⊓ p ⁻¹ᵁ W).2
  exact ⟨⟨W, hW⟩, ⟨Z, hZ⟩, hxW, hxZ,
    (fun _ hz => (hWle hz).1), (fun _ hz => (hWle hz).2),
    (fun _ hz => (hZle hz).1.1), (fun _ hz => (hZle hz).1.2),
    (fun _ hz => (hZle hz).2)⟩

/-- Pullback of a coefficient and restriction to the common source affine
commute with first restricting the coefficient to the common base affine. -/
theorem pairedC3_affine_overlap_coefficient_square
    {X Y : Scheme} (p : X ⟶ Y) (U W : Y.Opens) (V Z : X.Opens)
    (hWU : W ≤ U) (hZV : Z ≤ V) (hV : V ≤ p ⁻¹ᵁ U) (hZ : Z ≤ p ⁻¹ᵁ W) :
    ((X.presheaf.map (homOfLE hZV).op).hom).comp (p.appLE U V hV).hom =
      ((p.appLE W Z hZ).hom).comp (Y.presheaf.map (homOfLE hWU).op).hom := by
  change (p.appLE U V hV ≫ X.presheaf.map (homOfLE hZV).op).hom =
    (Y.presheaf.map (homOfLE hWU).op ≫ p.appLE W Z hZ).hom
  rw [p.appLE_map, p.map_appLE]

#print axioms pairedC3_affine_overlap_coefficient_square
#print axioms pairedC3_affine_overlap_refinement
end HodgeLean.Foundations.Program.G32Native
