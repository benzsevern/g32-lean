import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.MayerVietoris

/-! Homology vanishing passes through two open subsets by Mayer–Vietoris. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem two_open_homology_vanishing (X : TopCat.{0}) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hHU : Subsingleton (Homology ℚ (TopCat.of U) (n + 1)))
    (hHV : Subsingleton (Homology ℚ (TopCat.of V) (n + 1)))
    (hHI : Subsingleton (Homology ℚ (TopCat.of ↥(U ∩ V)) n)) :
    Subsingleton (Homology ℚ X (n + 1)) := by
  have hsum : IsZero ((singularMayerVietorisShortComplex X U V).X₂.homology (n + 1)) := by
    have H := (biprod_isZero_iff (Homology ℚ (TopCat.of U) (n + 1))
      (Homology ℚ (TopCat.of V) (n + 1))).mpr
        ⟨@ModuleCat.isZero_of_subsingleton ℚ _ _ hHU,
          @ModuleCat.isZero_of_subsingleton ℚ _ _ hHV⟩
    exact H.of_iso (singularMayerVietorisHomologySumIso X U V (n + 1))
  exact ModuleCat.subsingleton_of_isZero
    ((singularMayerVietoris_exact_ambient X U V hU hV hUV n).isZero_of_both_isZero hsum
      (@ModuleCat.isZero_of_subsingleton ℚ _ _ hHI))

#print axioms two_open_homology_vanishing
end HodgeLean.Foundations.QuotientDuality
