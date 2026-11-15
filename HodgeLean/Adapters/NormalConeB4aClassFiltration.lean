import HodgeLean.Adapters.NormalConeB4aClassSupport
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.FiniteFiltrationVanishing
import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularSectionCohomology

/-! # Relative singular cohomology through a finite support filtration

Route: convert each relative group to supported singular section cohomology,
apply finite support localization to the flasque singular cochain complex,
and convert back. This keeps the layer calculations explicit.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Vanishing on the open layers of a finite closed-support filtration implies
vanishing on its initial support. -/
theorem a3b4a_classRelative_vanishing_of_finiteFiltration
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (S : ℕ → Closeds X) (hS : Antitone S) (N : ℕ) (hN : S N = ⊥)
    (n : ℕ)
    (hlayer : ∀ k, k < N → IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair ((S (k + 1)).compl : Set X) (S k)) n)) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (Set.univ : Set X) (S 0)) n) := by
  let O : ℕ → Opens X := fun k => (S k).compl
  have hO : Monotone O := fun i j hij => by
    intro x hx hxS
    exact hx (hS hij hxS)
  have hON : O N = ⊤ := by
    ext x
    simp [O, hN]
  have hL (k : ℕ) (hk : k < N) : IsZero
      ((((TopCat.Sheaf.supportEvaluation X (O (k + 1))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (supportedRationalSingularCochainComplex X (O k))).homology (n : ℤ)) := by
    letI := ModuleCat.subsingleton_of_isZero (hlayer k hk)
    exact @AddCommGrpCat.isZero_of_subsingleton _
      (supportedRationalSingularSectionCohomologyEquivSupportComplement X
        (S k) (S k).isClosed (O (k + 1)) n).injective.subsingleton
  have hzero := TopCat.Sheaf.finiteNestedSupport_homology_isZero X O hO N hON
    (rationalSingularCochainComplex X) (fun _ => inferInstance) (n : ℤ) hL 0 (Nat.zero_le N)
  letI : Subsingleton ((((TopCat.Sheaf.supportEvaluation X ⊤).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (supportedRationalSingularCochainComplex X
        ⟨(S 0 : Set X)ᶜ, (S 0).isClosed.isOpen_compl⟩)).homology (n : ℤ)) :=
    AddCommGrpCat.subsingleton_of_isZero hzero
  letI : Subsingleton (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (Set.univ : Set X) (S 0)) n) :=
    (supportedRationalSingularSectionCohomologyEquivSupportComplement X
      (S 0) (S 0).isClosed ⊤ n).symm.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end HodgeLean.Adapters
