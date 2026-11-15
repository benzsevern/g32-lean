import HodgeLean.Foundations.QuotientDuality.PersistenceAmbientCollapseComparison
import HodgeLean.Foundations.QuotientDuality.PersistenceGoodPairComparison
import HodgeLean.Foundations.QuotientDuality.PersistenceRelativeDuality

/-! Original-pair comparison through actual ambient deformations on both sides. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_ambient_pair_relative_cohomology_bijective
    (K : Type) [Field K] [Algebra ℚ K]
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hclosed : IsClosedMap f) (A : Set Y) (hA : IsClosed A)
    (hfibre : ∀ y, y ∉ A → ∃! x, f x = y) (x : X) (hx : f x ∈ A)
    (PX : Set X) (hPX : IsOpen PX) (hBPX : f ⁻¹' A ⊆ PX) (rX : C(X, X))
    (HX : ContinuousMap.Homotopy (ContinuousMap.id X) rX)
    (hfixedX : ∀ (t : unitInterval) a, a ∈ f ⁻¹' A → HX (t, a) = a)
    (hretX : ∀ z ∈ PX, rX z ∈ f ⁻¹' A)
    (PY : Set Y) (hPY : IsOpen PY) (hAPY : A ⊆ PY) (rY : C(Y, Y))
    (HY : ContinuousMap.Homotopy (ContinuousMap.id Y) rY)
    (hfixedY : ∀ (t : unitInterval) a, a ∈ A → HY (t, a) = a)
    (hretY : ∀ z ∈ PY, rY z ∈ A) (n : ℕ) :
    Function.Bijective (relativeCohomologyMap K n (persistencePairMap (TopCat.ofHom f) A)) := by
  have hsource := persistence_relative_cohomology_bijective_of_homology K
    (persistenceCollapseLocusPairMap (f ⁻¹' A) x hx) n
    (persistence_ambient_collapse_relative_homology_bijective K (f ⁻¹' A) PX
      (hA.preimage f.continuous) hPX hBPX rX HX hfixedX hretX x hx n)
  have htarget := persistence_relative_cohomology_bijective_of_homology K
    (persistenceCollapseLocusPairMap A (f x) hx) n
    (persistence_ambient_collapse_relative_homology_bijective K A PY
      hA hPY hAPY rY HY hfixedY hretY (f x) hx n)
  have hcollapse := persistence_collapse_map_isHomeomorph f f.continuous hclosed A hA
    ⟨x, hx⟩ hfibre
  have hmiddle := persistence_point_pair_relative_cohomology_bijective K
    (TopCat.ofHom (persistenceCollapseContinuousMap f f.continuous A)) hcollapse
    (Quotient.mk (persistenceCollapseSetoid (f ⁻¹' A)) x) n
  have heq := congrArg (relativeCohomologyMap K n)
    (persistence_good_pair_quotient_square f A x hx)
  rw [relativeCohomologyMap_comp, relativeCohomologyMap_comp] at heq
  have hb : Function.Bijective
      ((relativeCohomologyMap K n (persistencePairMap (TopCat.ofHom f) A)) ∘
        (relativeCohomologyMap K n (persistenceCollapseLocusPairMap A (f x) hx))) := by
    change Function.Bijective
      ((relativeCohomologyMap K n (persistencePairMap (TopCat.ofHom f) A)) ∘ₗ
        (relativeCohomologyMap K n (persistenceCollapseLocusPairMap A (f x) hx)))
    rw [heq]
    exact hsource.comp hmiddle
  exact (Function.Bijective.of_comp_iff _ htarget).mp hb


end HodgeLean.Foundations.QuotientDuality
