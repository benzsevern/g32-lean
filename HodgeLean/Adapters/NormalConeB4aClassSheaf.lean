import HodgeLean.Adapters.NormalConeB4aClassLocal
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.RelativeCohomologySheaf
import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.CohomologyStalkVanishing

/-! # Lower supported cohomology sheaves on flattened supports

Route: cofinal chart neighborhoods give zero presheaf stalks. The sheafification
unit preserves stalks, so the supported cohomology sheaf is zero. Applied on
the smooth layers, this supplies the local input for support localization.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace Opposite

/-- A closed support locally flattened in normal codimension at least `c` has
zero relative-cohomology sheaves below degree `2 * c`. -/
theorem a3b4a_classSheaf_vanishing_of_flatteningCharts
    (X : TopCat.{0}) (S : Set X) (hS : IsClosed S) (c : ℕ)
    (hcharts : ∀ x ∈ S, ∃ (r d : ℕ)
      (e : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin d → ℂ))),
      c ≤ d ∧ x ∈ e.source ∧ ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (n : ℕ) (hn : n < 2 * c) :
    IsZero (supportRelativeCohomologySheaf X S n) := by
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro x
  let P := supportRelativeCohomologyPresheaf X S n
  have hP : IsZero (P.stalk x) := by
    apply TopCat.Presheaf.isZero_stalk_of_cofinal_sections
    intro U hxU
    by_cases hxS : x ∈ S
    · obtain ⟨r, d, e, hcd, hx, he⟩ := hcharts x hxS
      obtain ⟨W, hWo, hxW, hWU, _, hW⟩ :=
        a3b4a_classLocal_vanishing_basis e S he x hx hxS U U.isOpen hxU
      refine ⟨⟨W, hWo⟩, hWU, hxW, ?_⟩
      letI : Subsingleton (P.obj (op (⟨W, hWo⟩ : Opens X))) :=
        ModuleCat.subsingleton_of_isZero (hW n (by omega))
      exact AddCommGrpCat.isZero_of_subsingleton _
    · let W : Opens X := U ⊓ ⟨Sᶜ, hS.isOpen_compl⟩
      refine ⟨W, inf_le_left, ⟨hxU, hxS⟩, ?_⟩
      letI : Subsingleton (P.obj (op W)) :=
        neighborhoodSupportRelativeCohomology_subsingleton X S n W
        (fun _ hy => hy.2)
      exact AddCommGrpCat.isZero_of_subsingleton _
  let η := supportRelativeCohomologyToSheaf X S n
  have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P
  exact hP.of_iso (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η)).symm

end HodgeLean.Adapters
