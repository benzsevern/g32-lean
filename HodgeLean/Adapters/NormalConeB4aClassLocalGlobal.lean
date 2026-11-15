import HodgeLean.Adapters.NormalConeB4aClassFiltration
import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.OpenRestrictedVanishing

/-! # Global vanishing from cofinal local calculations on an open

Route: translate relative cohomology to the supported flasque singular section
complex, use cofinal lower vanishing there, and translate back. The hypotheses
can be checked in different charts at different points of a stratum.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Cofinal local relative vanishing through degree `n` implies vanishing on
the specified open, without a global choice of flattening chart. -/
theorem a3b4a_classRelative_vanishing_of_cofinal_local_vanishing
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (S : Closeds X) (U : Opens X) (n : ℕ)
    (hlocal : ∀ j : ℕ, j ≤ n → ∀ x : X, x ∈ U → ∀ V : Opens X, x ∈ V →
      ∃ W : Opens X, W ≤ V ∧ x ∈ W ∧ IsZero (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W : Set X) S) j)) :
    IsZero (RelativeCohomology ℚ (neighborhoodSupportComplementPair (U : Set X) S) n) := by
  let K := supportedRationalSingularCochainComplex X S.compl
  letI : K.IsStrictlyGE 0 := by
    dsimp only [K, supportedRationalSingularCochainComplex]
    infer_instance
  have hK : ∀ j, (K.X j).IsFlasque := fun j =>
    TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque X S.compl
      ((rationalSingularCochainComplex X).X j)
  have hsec : IsZero ((((TopCat.Sheaf.supportEvaluation X U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).homology (n : ℤ)) := by
    apply TopCat.Sheaf.sectionCohomology_isZero_of_cofinal_lower_vanishing X K U 0 n hK
    intro j hj x hx V hxV
    by_cases hjneg : j < 0
    · refine ⟨V, le_rfl, hxV, ?_⟩
      apply ShortComplex.isZero_homology_of_isZero_X₂
      exact (TopCat.Sheaf.supportEvaluation X V).map_isZero
        (K.isZero_of_isStrictlyGE 0 j hjneg)
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hjneg)
      obtain ⟨W, hWV, hxW, hW⟩ := hlocal k (by exact_mod_cast hj) x hx V hxV
      refine ⟨W, hWV, hxW, ?_⟩
      letI := ModuleCat.subsingleton_of_isZero hW
      exact @AddCommGrpCat.isZero_of_subsingleton _
        (supportedRationalSingularSectionCohomologyEquivSupportComplement X S S.isClosed W k).injective.subsingleton
  letI : Subsingleton ((((TopCat.Sheaf.supportEvaluation X U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (supportedRationalSingularCochainComplex X
        ⟨(S : Set X)ᶜ, S.isClosed.isOpen_compl⟩)).homology (n : ℤ)) :=
    AddCommGrpCat.subsingleton_of_isZero hsec
  letI : Subsingleton (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set X) S) n) :=
    (supportedRationalSingularSectionCohomologyEquivSupportComplement X S S.isClosed U n).symm.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end HodgeLean.Adapters
