import HodgeLean.Adapters.NormalConeB4aClassSheaf
import HodgeLean.Adapters.CycleClassSmoothChartsProofs

/-! # From lower local vanishing to relative cohomology on opens

Route: the lowest-degree relative-to-sheaf comparison is invertible when all
lower supported cohomology sheaves vanish. The degree in question also has
zero sheaf, so its relative cohomology on every open is zero.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Smoothly flattened supports of normal codimension at least `c` have no
relative cohomology below degree `2 * c`, on every open of the ambient space. -/
theorem a3b4a_classRelative_vanishing_of_flatteningCharts
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (S : Closeds X) (c : ℕ)
    (hcharts : ∀ x ∈ S, ∃ (r d : ℕ)
      (e : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin d → ℂ))),
      c ≤ d ∧ x ∈ e.source ∧ ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (n : ℕ) (hn : n < 2 * c) (U : Opens X) :
    IsZero (RelativeCohomology ℚ (neighborhoodSupportComplementPair (U : Set X) S) n) := by
  have hz (j : ℕ) (hj : j < 2 * c) :
      IsZero (supportRelativeCohomologySheaf X S j) :=
    a3b4a_classSheaf_vanishing_of_flatteningCharts X S S.isClosed c hcharts j hj
  have hH (j : ℕ) (hj : j < n) : IsZero
      ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
        (supportRelativeCohomologySheaf X S j)) :=
    (U.isOpenEmbedding.sheafPullback AddCommGrpCat).map_isZero (hz j (hj.trans hn))
  letI : IsIso (C := AddCommGrpCat) ((toSheafify (Opens.grothendieckTopology X)
      (supportRelativeCohomologyPresheaf X S n)).app (op U)) :=
    ccm5_relativeToSheaf_isIso_of_lowerVanishing X S U n hH
  have hU : IsZero ((supportRelativeCohomologySheaf X S n).obj.obj (op U)) :=
    (TopCat.Sheaf.supportEvaluation X U).map_isZero (hz n hn)
  have hP : IsZero ((supportRelativeCohomologyPresheaf X S n).obj (op U)) :=
    hU.of_iso (asIso (C := AddCommGrpCat) ((toSheafify (Opens.grothendieckTopology X)
      (supportRelativeCohomologyPresheaf X S n)).app (op U)))
  letI : Subsingleton (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set X) S) n) :=
    AddCommGrpCat.subsingleton_of_isZero hP
  exact ModuleCat.isZero_of_subsingleton _

end HodgeLean.Adapters
