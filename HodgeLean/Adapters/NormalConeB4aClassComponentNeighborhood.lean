import HodgeLean.Adapters.NormalConeB4aClassRegularLocus

/-! # Isolating a single component in the analytic support

Route: remove the finitely many other component supports. Their analytic
preimages are closed, so the remaining neighborhood is open and the total
support there agrees with the selected component.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- A point lying on no other cycle component has arbitrarily small open
neighborhoods where the total support equals the selected component. -/
theorem a3b4a_classSupport_local_eq_component
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact q]
    (γ : AlgebraicCycle Z ℚ) (ξ : Z) (hξ : ξ ∈ γ.support)
    (x : ComplexPoint (Over.mk q))
    (hother : ∀ η ∈ γ.support, η ≠ ξ → x.underlying ∉ closure ({η} : Set Z))
    (V : Opens (ComplexPoint (Over.mk q))) (hxV : x ∈ V) :
    ∃ W : Opens (ComplexPoint (Over.mk q)), W ≤ V ∧ x ∈ W ∧
      ∀ y ∈ W, y ∈ a3b4_cycleSupport q γ ↔ y.underlying ∈ closure ({ξ} : Set Z) := by
  classical
  letI : CompactSpace Z := a3b4_compactSpace q
  let ι := {η : Z // η ∈ γ.support}
  letI : Fintype ι := (a3b2_support_finite γ).fintype
  let C : ι → Closeds (ComplexPoint (Over.mk q)) := fun η =>
    (⟨closure {η.1}, isClosed_closure⟩ : Closeds Z).preimage
      (ComplexPoint.continuous_underlying_to_zariski (Over.mk q))
  let i : ι := ⟨ξ, hξ⟩
  have hmem (y : ComplexPoint (Over.mk q)) :
      y ∈ (⨆ j, C j) ↔ y ∈ a3b4_cycleSupport q γ := by
    rw [ccm5_mem_finiteClosedSup]
    change (∃ j : ι, y.underlying ∈ closure ({j.1} : Set Z)) ↔ _
    constructor
    · rintro ⟨j, hj⟩
      exact Set.mem_iUnion₂.mpr ⟨j.1, j.2, hj⟩
    · intro hy
      obtain ⟨η, hη, hyη⟩ := Set.mem_iUnion₂.mp hy
      exact ⟨⟨η, hη⟩, hyη⟩
  obtain ⟨W, hWV, hxW, hW⟩ := ccm5_finiteSupport_local_eq C i x
    (fun j hj => hother j.1 j.2 (fun he => hj (Subtype.ext he))) V hxV
  exact ⟨W, hWV, hxW, fun y hy => (hmem y).symm.trans (hW y hy)⟩

end HodgeLean.Adapters
