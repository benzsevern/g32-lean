import HodgeLean.Adapters.NormalConeB4aClassPurityLocal

/-! # Nonprojective lower support purity

Route: cofinal local vanishing annihilates the relative-cohomology presheaf
stalks and hence its sheafification. The supported singular section comparison
also yields relative vanishing on every analytic open.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace Opposite
open HodgeLean.Foundations.Analytic

/-- The cohomology sheaves supported on an algebraic subset vanish below twice
its codimension in any smooth separated finite-type complex scheme. -/
theorem a3b4a_classSheaf_purity_vanishing
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    [QuasiCompact q] [IsSeparated q] (S : Closeds Z) (c : ℕ)
    (hc : ∀ z ∈ S, (c : ℕ∞) ≤ Order.coheight z)
    (n : ℕ) (hn : n < 2 * c) :
    IsZero (supportRelativeCohomologySheaf (a3b4_an q)
      (Point.underlying ⁻¹' (S : Set Z)) n) := by
  let X := a3b4_an q
  let B : Set X := Point.underlying ⁻¹' (S : Set Z)
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro x
  let P := supportRelativeCohomologyPresheaf X B n
  have hP : IsZero (P.stalk x) := by
    apply TopCat.Presheaf.isZero_stalk_of_cofinal_sections
    intro V hxV
    obtain ⟨W, hWV, hxW, hW⟩ := a3b4a_classRelative_purity_vanishing_basis q S c hc x V hxV
    refine ⟨W, hWV, hxW, ?_⟩
    letI : Subsingleton (P.obj (op W)) := ModuleCat.subsingleton_of_isZero (hW n hn)
    exact AddCommGrpCat.isZero_of_subsingleton _
  let η := supportRelativeCohomologyToSheaf X B n
  letI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P
  exact hP.of_iso (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η)).symm

/-- Relative cohomology with an algebraic support vanishes below twice its
codimension on every analytic open of a smooth separated finite-type scheme. -/
theorem a3b4a_classRelative_purity_vanishing
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    [QuasiCompact q] [IsSeparated q] (S : Closeds Z) (c : ℕ)
    (hc : ∀ z ∈ S, (c : ℕ∞) ≤ Order.coheight z)
    (U : Opens (ComplexPoint (Over.mk q))) (n : ℕ) (hn : n < 2 * c) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set (ComplexPoint (Over.mk q)))
        (Point.underlying ⁻¹' (S : Set Z))) n) := by
  letI : LocallyOfFiniteType (Over.mk q).hom := inferInstanceAs (LocallyOfFiniteType q)
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  letI : T2Space (ComplexPoint (Over.mk q)) := f4_t2Space (Over.mk q)
  letI (V : Opens (ComplexPoint (Over.mk q))) : ParacompactSpace V :=
    a3b4a_class_openParacompact q V
  let B : Closeds (a3b4_an q) := S.preimage
    (ComplexPoint.continuous_underlying_to_zariski (Over.mk q))
  apply a3b4a_classRelative_vanishing_of_cofinal_local_vanishing (a3b4_an q) B U n
  intro j hj x hx V hxV
  obtain ⟨W, hWV, hxW, hW⟩ := a3b4a_classRelative_purity_vanishing_basis q S c hc x V hxV
  exact ⟨W, hWV, hxW, hW j (hj.trans_lt hn)⟩

end HodgeLean.Adapters
