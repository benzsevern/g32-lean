import HodgeLean.Adapters.NormalConeB4aClassGlobal

/-! # Gluing supported relative classes from compatible germs

Route: glue the prescribed germs as sections of the supported cohomology
sheaf. Lower purity identifies these sections with relative cohomology on
each open, giving a global relative class and its exact restrictions.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Relative classes on an open cover of the support glue when their germs
agree and all lower supported cohomology sheaves vanish. -/
theorem a3b4a_classRelative_glue_of_compatible_germs
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (S : Closeds X) (n : ℕ)
    (hlower : ∀ j : ℕ, j < n → IsZero (supportRelativeCohomologySheaf X S j))
    {ι : Type} (U : ι → Opens X)
    (a : ∀ i, RelativeCohomology ℚ (neighborhoodSupportComplementPair (U i : Set X) S) n)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ U i)
    (hcompat : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), x ∈ S →
      supportRelativeCohomologyGerm X S n (U i) x hi (a i) =
      supportRelativeCohomologyGerm X S n (U j) x hj (a j)) :
    ∃ b : RelativeCohomology ℚ (neighborhoodSupportComplementPair (Set.univ : Set X) S) n,
      ∀ i, (supportRelativeCohomologyPresheaf X S n).map
        (homOfLE (show U i ≤ ⊤ from le_top)).op b = a i := by
  classical
  let F := supportRelativeCohomologySheaf X S n
  let g : ∀ x : X, F.presheaf.stalk x := fun x =>
    if hx : x ∈ S then
      supportRelativeCohomologyGerm X S n (U (hcover x hx).choose) x
        (hcover x hx).choose_spec (a (hcover x hx).choose)
    else 0
  have hg (i : ι) (x : X) (hx : x ∈ U i) :
      g x = supportRelativeCohomologyGerm X S n (U i) x hx (a i) := by
    by_cases hxS : x ∈ S
    · dsimp only [g]
      rw [dif_pos hxS]
      exact hcompat _ i x _ hx hxS
    · dsimp only [g]
      rw [dif_neg hxS]
      exact (supportRelativeCohomologyGerm_eq_zero_of_not_mem X S n S.isClosed
        (U i) x hx hxS (a i)).symm
  have hloc : ∀ x : X, ∃ (V : Opens X) (_ : x ∈ V)
      (s : F.presheaf.obj (op V)),
      ∀ (y : X) (hy : y ∈ V), F.presheaf.germ V y hy s = g y := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨i, hi⟩ := hcover x hx
      refine ⟨U i, hi, (supportRelativeCohomologyToSheaf X S n).app _ (a i), ?_⟩
      exact fun y hy => (hg i y hy).symm
    · refine ⟨S.compl, hx, 0, ?_⟩
      intro y hy
      rw [map_zero]
      dsimp only [g]
      have hyS : y ∉ S := hy
      rw [dif_neg hyS]
  let s := TopCat.Sheaf.sectionOfLocallyRepresentable F g hloc
  have hs (x : X) : F.presheaf.Γgerm x s = g x :=
    TopCat.Sheaf.sectionOfLocallyRepresentable_germ F g hloc x
  have hH (V : Opens X) (j : ℕ) (hj : j < n) : IsZero
      ((V.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
        (supportRelativeCohomologySheaf X S j)) :=
    (V.isOpenEmbedding.sheafPullback AddCommGrpCat).map_isZero (hlower j hj)
  letI : IsIso (C := AddCommGrpCat)
      ((supportRelativeCohomologyToSheaf X S n).app (op ⊤)) :=
    ccm5_relativeToSheaf_isIso_of_lowerVanishing X S ⊤ n (hH ⊤)
  obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso
    ((supportRelativeCohomologyToSheaf X S n).app (op ⊤))).2 s
  refine ⟨b, fun i => ?_⟩
  apply ccm5_relativeGerms_injective_of_lowerVanishing X S (U i) n (hH (U i))
  funext x
  dsimp only
  rw [supportRelativeCohomologyPresheaf_map_apply,
    supportRelativeCohomologyGerm_restrict]
  change F.presheaf.Γgerm x.1
    ((supportRelativeCohomologyToSheaf X S n).app (op ⊤) b) = _
  rw [hb]
  exact (hs x.1).trans (hg i x.1 x.2)

end HodgeLean.Adapters
