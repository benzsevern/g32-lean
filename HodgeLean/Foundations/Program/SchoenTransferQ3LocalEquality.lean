import HodgeLean.Adapters.NormalConeB4aClassUniqueBoundary
import HodgeLean.Adapters.NormalConeB4aClassExistsPure

/-! Extend actual local supported equalities across the retained algebraic boundary. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.Program

/-- Local supported equality off a higher-codimension boundary identifies the
original global classes, without assuming either class is already normalized. -/
theorem s4_q3_supported_eq_of_boundary_local_equality
    {Z : Scheme.{0}} (q : Z ⟶ Spec ↧ℂ) [Smooth q] [QuasiCompact q] [IsSeparated q]
    (γ : AlgebraicCycle Z ℚ) (k : ℕ)
    (hc : ∀ p ∈ γ.support, (k : ℕ∞) ≤ Order.coheight p)
    (B : Closeds Z) (hBS : B ≤ a3b4a_classAlgebraicSupport q γ)
    (hBc : ∀ p ∈ B, ((k + 1 : ℕ) : ℕ∞) ≤ Order.coheight p)
    (β β' : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * k))
    (hlocal : ∀ x ∈ a3b4_cycleSupport q γ, x.underlying ∉ B →
      ∃ W : Set (ComplexPoint (Over.mk q)), IsOpen W ∧ x ∈ W ∧
        relativeCohomologyMap ℚ (2 * k)
          (a3b4_neighborhoodPairMap W (a3b4_cycleSupport q γ)) (β - β') = 0) :
    β = β' := by
  letI : LocallyOfFiniteType (Over.mk q).hom := inferInstanceAs (LocallyOfFiniteType q)
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  letI : T2Space (ComplexPoint (Over.mk q)) := f4_t2Space (Over.mk q)
  letI (V : Opens (ComplexPoint (Over.mk q))) : ParacompactSpace V :=
    a3b4a_class_openParacompact q V
  let X := a3b4_an q
  let S : Closeds X := ⟨a3b4_cycleSupport q γ, a3b4a_classSupport_isClosed q γ⟩
  let U : Opens X := (B.preimage (ComplexPoint.continuous_underlying_to_zariski (Over.mk q))).compl
  have hH (j : ℕ) (hj : j < 2 * k) : IsZero
      ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
        (supportRelativeCohomologySheaf X S j)) :=
    (U.isOpenEmbedding.sheafPullback AddCommGrpCat).map_isZero
      (a3b4a_classSheaf_purity_vanishing q (a3b4a_classAlgebraicSupport q γ) k
        (a3b4a_classAlgebraicSupport_coheight q γ k hc) j hj)
  apply sub_eq_zero.mp
  apply (a3b4a_classCycle_restriction_bijective_of_boundary_codimension q γ k B hBS hBc).1
  rw [map_zero]
  apply ccm5_relativeGerms_injective_of_lowerVanishing X S U (2 * k) hH
  funext x
  dsimp only
  have hzero : supportRelativeCohomologyGerm X S (2 * k) U x.1 x.2 0 = 0 := by
    simp only [supportRelativeCohomologyGerm, map_zero]
  rw [hzero]
  by_cases hxS : x.1 ∈ S
  · obtain ⟨W, hWo, hxW, hW⟩ := hlocal x.1 hxS x.2
    have hW' : relativeCohomologyMap ℚ (2 * k)
        (a3b4_neighborhoodPairMap (M := X) W (S : Set X)) (β - β') = 0 := hW
    let T : Opens X := ⟨W, hWo⟩ ⊓ U
    have hxT : x.1 ∈ T := ⟨hxW, x.2⟩
    have hT : relativeCohomologyMap ℚ (2 * k)
        (a3b4_neighborhoodPairMap (T : Set X) (S : Set X)) (β - β') = 0 := by
      rw [← a3b4a_classLocal_restriction_comp (S : Set X)
        (show (T : Set X) ⊆ W from fun _ h => h.1) (2 * k) (β - β'), hW', map_zero]
    rw [← supportRelativeCohomologyGerm_restrict X S (2 * k)
      (show T ≤ U from inf_le_right) x.1 hxT]
    have hr := (a3b4a_classLocal_restriction_comp (S : Set X)
      (show (T : Set X) ⊆ U from fun _ h => h.2) (2 * k) (β - β')).trans hT
    exact (congrArg (supportRelativeCohomologyGerm X S (2 * k) T x.1 hxT) hr).trans
      (by simp only [supportRelativeCohomologyGerm, map_zero])
  · exact supportRelativeCohomologyGerm_eq_zero_of_not_mem X S (2 * k)
      S.isClosed U x.1 x.2 hxS _

end HodgeLean.Foundations.Program
