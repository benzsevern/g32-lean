import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalTransport
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.EuclideanVanishing

/-! # Actual local homology concentration in original complex charts -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Original complex coordinate local homology vanishes outside its literal real dimension.
Source: standardComplexRealPairIso; standardLocalHomology_isZero_of_ne.
HC no distance; AV milestone no distance. -/
theorem properCycle_complex_local_homology_vanishes (d n : ℕ) (hn : n ≠ 2*d) :
    Subsingleton (RelativeHomology ℚ (puncturedPair ℂ d) n) := by
  let e := (relativeHomologyFunctor ℚ n).mapIso (standardComplexRealPairIso d)
  letI : Subsingleton (RelativeHomology ℚ (puncturedPair ℝ (d*2)) n) :=
    ModuleCat.subsingleton_of_isZero (standardLocalHomology_isZero_of_ne (d*2) n (by omega))
  exact e.toLinearEquiv.injective.subsingleton

/-- Every original complex chart gives actual local homology concentration in its own literal real dimension.
Source: properCycle_open_local_homology_iso; properCycle_local_homology_homeomorph_iso; properCycle_complex_local_homology_vanishes.
HC no distance; AV milestone no distance. -/
theorem properCycle_chart_local_homology_vanishes
    (X : TopCat.{0}) [T1Space X] (d : ℕ)
    (e : OpenPartialHomeomorph X (Fin d → ℂ)) (x : X) (hx : x ∈ e.source)
    (n : ℕ) (hn : n ≠ 2*d) : Subsingleton (orientationGroup X n x) := by
  let E := Fin d → ℂ
  let U : TopologicalSpace.Opens X := ⟨e.source, e.open_source⟩
  let V : TopologicalSpace.Opens E := ⟨e.target, e.open_target⟩
  let z : U := ⟨x, hx⟩
  let e0 : U ≃ₜ V := e.toHomeomorphSourceTarget
  let H := (properCycle_open_local_homology_iso X U z n).symm ≪≫
    properCycle_local_homology_homeomorph_iso (X := TopCat.of U) (Y := TopCat.of V) e0 z n ≪≫
      properCycle_open_local_homology_iso (TopCat.of E) V (e0 z) n
  let t : E ≃ₜ E :=
    { toFun := fun v => v - e x
      invFun := fun v => v + e x
      left_inv := by intro v; simp
      right_inv := by intro v; simp
      continuous_toFun := continuous_id.sub continuous_const
      continuous_invFun := continuous_id.add continuous_const }
  have ht : t (e x) = 0 := sub_self _
  let Ht := properCycle_local_homology_homeomorph_iso (X := TopCat.of E) (Y := TopCat.of E) t (e x) n
  rw [ht] at Ht
  letI : Subsingleton (orientationGroup (TopCat.of E) n 0) :=
    properCycle_complex_local_homology_vanishes d n hn
  exact (H ≪≫ Ht).toLinearEquiv.injective.subsingleton

end HodgeLean.Foundations.QuotientDuality
