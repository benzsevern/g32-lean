import HodgeLean.Adapters.NormalConeB4aClassCycleExtension

/-! # Uniqueness from normalization off a higher-codimension boundary

Route: lower support purity makes relative classes detectable by their germs
on the boundary complement. The frozen normalization makes the difference
vanish there. Boundary restriction injectivity then identifies the classes.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations.Analytic

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Normalization determines a cycle class once the support is holomorphically
flattened off an algebraic boundary of strictly higher codimension. -/
theorem a3b4a_cycleClass_unique_of_regularBoundary
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    [QuasiCompact q] [IsSeparated q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ)
    (B : Closeds Z) (hBS : B ≤ a3b4a_classAlgebraicSupport q γ)
    (hcB : ∀ z ∈ B, ((c + 1 : ℕ) : ℕ∞) ≤ Order.coheight z)
    (hcharts : ∀ x ∈ a3b4_cycleSupport q γ, x.underlying ∉ B → ∃ (r : ℕ)
      (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q)) ((Fin r → ℂ) × (Fin c → ℂ))),
      x ∈ e.source ∧ a3b4_IsHolChart q e ∧
        ∀ y ∈ e.source, y ∈ a3b4_cycleSupport q γ ↔ (e y).2 = 0)
    (β β' : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * c))
    (hβ : a3b4_IsCycleClass q γ c β) (hβ' : a3b4_IsCycleClass q γ c β') :
    β = β' := by
  letI : LocallyOfFiniteType (Over.mk q).hom := inferInstanceAs (LocallyOfFiniteType q)
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  letI : T2Space (ComplexPoint (Over.mk q)) := f4_t2Space (Over.mk q)
  letI (V : Opens (ComplexPoint (Over.mk q))) : ParacompactSpace V :=
    a3b4a_class_openParacompact q V
  let X := a3b4_an q
  let S : Closeds X := ⟨a3b4_cycleSupport q γ, a3b4a_classSupport_isClosed q γ⟩
  let U : Opens X := (B.preimage (ComplexPoint.continuous_underlying_to_zariski (Over.mk q))).compl
  have hH (j : ℕ) (hj : j < 2 * c) : IsZero
      ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
        (supportRelativeCohomologySheaf X S j)) :=
    (U.isOpenEmbedding.sheafPullback AddCommGrpCat).map_isZero
      (a3b4a_classSheaf_purity_vanishing q (a3b4a_classAlgebraicSupport q γ) c
        (a3b4a_classAlgebraicSupport_coheight q γ c hc) j hj)
  apply sub_eq_zero.mp
  apply (a3b4a_classCycle_restriction_bijective_of_boundary_codimension q γ c B hBS hcB).1
  rw [map_zero]
  apply ccm5_relativeGerms_injective_of_lowerVanishing X S U (2 * c) hH
  funext x
  dsimp only
  have hzero : supportRelativeCohomologyGerm X S (2 * c) U x.1 x.2 0 = 0 := by
    simp only [supportRelativeCohomologyGerm, map_zero]
  rw [hzero]
  by_cases hxS : x.1 ∈ S
  · obtain ⟨r, e, hx, he, hS⟩ := hcharts x.1 hxS x.2
    obtain ⟨W, _, hWo, hxW, hW⟩ :=
      a3b4a_classLocal_difference_vanishes q γ c β β' hβ hβ' r e hS x.1 hx hxS he
    have hW' : relativeCohomologyMap ℚ (2 * c)
        (a3b4_neighborhoodPairMap (M := X) W (S : Set X)) (β - β') = 0 := hW
    let T : Opens X := ⟨W, hWo⟩ ⊓ U
    have hxT : x.1 ∈ T := ⟨hxW, x.2⟩
    have hT : relativeCohomologyMap ℚ (2 * c)
        (a3b4_neighborhoodPairMap (T : Set X) (S : Set X)) (β - β') = 0 := by
      rw [← a3b4a_classLocal_restriction_comp (S : Set X)
        (show (T : Set X) ⊆ W from fun _ h => h.1) (2 * c) (β - β'), hW', map_zero]
    rw [← supportRelativeCohomologyGerm_restrict X S (2 * c)
      (show T ≤ U from inf_le_right) x.1 hxT]
    have hr := (a3b4a_classLocal_restriction_comp (S : Set X)
      (show (T : Set X) ⊆ U from fun _ h => h.2) (2 * c) (β - β')).trans hT
    exact (congrArg (supportRelativeCohomologyGerm X S (2 * c) T x.1 hxT) hr).trans
      (by simp only [supportRelativeCohomologyGerm, map_zero])
  · exact supportRelativeCohomologyGerm_eq_zero_of_not_mem X S (2 * c)
      S.isClosed U x.1 x.2 hxS _

end HodgeLean.Adapters
