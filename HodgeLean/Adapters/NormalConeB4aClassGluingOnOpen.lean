import HodgeLean.Adapters.NormalConeB4aClassGluing

/-! # Gluing supported classes over an ambient open subset

Route: add the support complement to the prescribed local cover, glue the
sheaf sections over the chosen open, and use lower purity to lift the glued
section to relative cohomology with its exact local restrictions.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace Opposite

/-- Compatible relative classes on an open cover of the support inside `U`
glue to a class on `U` under lower supported cohomology vanishing. -/
theorem a3b4a_classRelative_glue_onOpen
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (S : Closeds X) (n : ℕ)
    (hlower : ∀ j : ℕ, j < n → IsZero (supportRelativeCohomologySheaf X S j))
    (U : Opens X) {ι : Type} (V : ι → Opens X) (hVU : ∀ i, V i ≤ U)
    (a : ∀ i, RelativeCohomology ℚ (neighborhoodSupportComplementPair (V i : Set X) S) n)
    (hcover : ∀ x ∈ U, x ∈ S → ∃ i, x ∈ V i)
    (hcompat : ∀ i j x (hi : x ∈ V i) (hj : x ∈ V j), x ∈ S →
      supportRelativeCohomologyGerm X S n (V i) x hi (a i) =
      supportRelativeCohomologyGerm X S n (V j) x hj (a j)) :
    ∃ b : RelativeCohomology ℚ (neighborhoodSupportComplementPair (U : Set X) S) n,
      ∀ i, (supportRelativeCohomologyPresheaf X S n).map (homOfLE (hVU i)).op b = a i := by
  classical
  let F := supportRelativeCohomologySheaf X S n
  let O : Option ι → Opens X := fun o => match o with
    | none => U ⊓ S.compl
    | some i => V i
  have hOU : ∀ o, O o ≤ U := by
    intro o
    cases o with
    | none => exact inf_le_left
    | some i => exact hVU i
  let sec : ∀ o, F.presheaf.obj (op (O o)) := fun o => match o with
    | none => 0
    | some i => (supportRelativeCohomologyToSheaf X S n).app _ (a i)
  have hcompatible : TopCat.Presheaf.IsCompatible F.presheaf O sec := by
    intro i j
    apply TopCat.Presheaf.section_ext
    intro x hx
    rw [F.presheaf.germ_res_apply, F.presheaf.germ_res_apply]
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j =>
        change F.presheaf.germ (U ⊓ S.compl) x hx.1 0 =
          supportRelativeCohomologyGerm X S n (V j) x hx.2 (a j)
        rw [map_zero]
        exact (supportRelativeCohomologyGerm_eq_zero_of_not_mem X S n S.isClosed
          (V j) x hx.2 hx.1.2 (a j)).symm
    | some i =>
      cases j with
      | none =>
        change supportRelativeCohomologyGerm X S n (V i) x hx.1 (a i) =
          F.presheaf.germ (U ⊓ S.compl) x hx.2 0
        rw [map_zero]
        exact supportRelativeCohomologyGerm_eq_zero_of_not_mem X S n S.isClosed
          (V i) x hx.1 hx.2.2 (a i)
      | some j =>
        change supportRelativeCohomologyGerm X S n (V i) x hx.1 (a i) =
          supportRelativeCohomologyGerm X S n (V j) x hx.2 (a j)
        by_cases hxS : x ∈ S
        · exact hcompat i j x hx.1 hx.2 hxS
        · rw [supportRelativeCohomologyGerm_eq_zero_of_not_mem X S n S.isClosed
            (V i) x hx.1 hxS (a i),
            supportRelativeCohomologyGerm_eq_zero_of_not_mem X S n S.isClosed
            (V j) x hx.2 hxS (a j)]
  have hcov : U ≤ iSup O := by
    intro x hx
    rw [Opens.mem_iSup]
    by_cases hxS : x ∈ S
    · obtain ⟨i, hi⟩ := hcover x hx hxS
      exact ⟨some i, hi⟩
    · exact ⟨none, hx, hxS⟩
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' O U (fun o => homOfLE (hOU o)) hcov sec hcompatible
  have hH (W : Opens X) (j : ℕ) (hj : j < n) : IsZero
      ((W.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
        (supportRelativeCohomologySheaf X S j)) :=
    (W.isOpenEmbedding.sheafPullback AddCommGrpCat).map_isZero (hlower j hj)
  letI (W : Opens X) : IsIso (C := AddCommGrpCat)
      ((supportRelativeCohomologyToSheaf X S n).app (op W)) :=
    ccm5_relativeToSheaf_isIso_of_lowerVanishing X S W n (hH W)
  obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso
    ((supportRelativeCohomologyToSheaf X S n).app (op U))).2 s
  refine ⟨b, fun i => ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    ((supportRelativeCohomologyToSheaf X S n).app (op (V i)))).1
  have hnat := ConcreteCategory.congr_hom
    ((supportRelativeCohomologyToSheaf X S n).naturality (homOfLE (hVU i)).op) b
  exact hnat.trans (by simpa only [ConcreteCategory.comp_apply, hb] using hs (some i))

end HodgeLean.Adapters
