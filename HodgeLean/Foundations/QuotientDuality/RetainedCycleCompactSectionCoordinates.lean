import HodgeLean.Foundations.QuotientDuality.RetainedCycleSectionCoordinates

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology AlgebraicTopology.Singular
open scoped Simplicial
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Compactness supplies finitely many actual chain representatives for all section germs. -/
theorem retained_compact_section_finite_germ_representatives (X : TopCat.{0}) [T2Space X]
    [CompactSpace X] (n : ℕ) (s : (singularChainSheaf ℚ X n).presheaf.obj (op ⊤)) :
    ∃ C : Finset (Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) n),
      ∀ x : X, ∃ c ∈ C,
        (singularChainSheaf ℚ X n).presheaf.germ ⊤ x (by trivial)
            ((retainedChainSheafSectionMap X ⊤).f n c) =
          (singularChainSheaf ℚ X n).presheaf.germ ⊤ x (by trivial) s := by
  classical
  have hl : ∀ x : X, ∃ (V : Opens X) (c : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) n),
      x ∈ V ∧ ∀ y (hy : y ∈ V),
        (singularChainSheaf ℚ X n).presheaf.germ ⊤ y (by trivial)
            ((retainedChainSheafSectionMap X ⊤).f n c) =
          (singularChainSheaf ℚ X n).presheaf.germ ⊤ y (by trivial) s := by
    intro x
    obtain ⟨V, hV, hx, c, hc⟩ := retained_chain_section_local_representative X ⊤ n s x (by trivial)
    exact ⟨V, c, hx, hc⟩
  choose V c hxV hc using hl
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (by intro x hx; exact Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨T.image c, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hT (Set.mem_univ x))
  obtain ⟨hiT, hxi⟩ := Set.mem_iUnion.mp hi
  exact ⟨c i, Finset.mem_image.mpr ⟨i, hiT, rfl⟩, hc i x hxi⟩

/-- The actual constant simplex coefficients of a section have finite support on a compact space. -/
theorem retained_compact_section_coefficient_support_finite (X : TopCat.{0}) [T2Space X]
    [CompactSpace X] (n : ℕ) (s : (singularChainSheaf ℚ X n).presheaf.obj (op ⊤)) :
    (Function.support (retainedGlobalSectionCoefficient X n s)).Finite := by
  classical
  obtain ⟨C, hC⟩ := retained_compact_section_finite_germ_representatives X n s
  let S := C.biUnion (fun c => (retainedChainCoordinates (TopCat.toSSet.obj X) n c).support)
  apply S.finite_toSet.subset
  intro σ hσ
  change retainedGlobalSectionCoefficient X n s σ ≠ 0 at hσ
  by_contra hs
  let t : SimplexCategory.toTop.{0}.obj ⦋n⦌ := Classical.choice inferInstance
  obtain ⟨c, hc, hg⟩ := hC (retainedSimplexAt X n σ t)
  have he := retained_global_section_simplex_coordinate_of_germ X n s c σ t hg
  have hz : retainedChainCoordinates (TopCat.toSSet.obj X) n c σ = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    exact hs (Finset.mem_biUnion.mpr ⟨c, hc, hmem⟩)
  have he' := (retained_global_section_coefficient_at X n s σ t).symm.trans he
  exact hσ (he'.trans hz)

end HodgeLean.Foundations.QuotientDuality
