import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.HolomorphicMaps
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceFinite
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertMain

/-! # Analytic images in holomorphic chart coordinates

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Set Filter Topology HodgeLean.Foundations.Analytic
namespace AlgebraicGeometry.SingularCycles

/-- A holomorphic chart is a proper holomorphic map between its source and target open subspaces.
Source: Grauert–Remmert, Coherent Analytic Sheaves, §1.1.5; coordinate holomorphicity and a chart homeomorphism. -/
theorem holomorphic_chart_isProperHom {M : Type*} [TopologicalSpace M]
    (S : an_ReducedSpace M) {n : ℕ} (e : OpenPartialHomeomorph M (Fin n → ℂ))
    (hcoords : ∀ j, S.IsHolFun (fun x : e.source => e x j)) :
    an_IsProperHom (anrem_openSpace S e.open_source)
      (anrem_openSpace (an_euclidSpace n) e.open_target) e.toHomeomorphSourceTarget := by
  have hc : Continuous (fun x : e.source => e x) :=
    e.continuousOn.comp_continuous continuous_subtype_val (fun x => x.2)
  have hmap : an_IsHom (anrem_openSpace S e.open_source) (an_euclidSpace n)
      (fun x : e.source => e x) :=
    holomorphic_map_euclid _ _ hc (fun j => open_holFun_univ S e.open_source _ (hcoords j))
  exact ⟨e.toHomeomorphSourceTarget.isProperMap,
    anrem_isHom_corestrict _ _ hmap e.open_target (fun x => e.map_source x.2)⟩

/-- Images of analytic subsets under holomorphic charts have local analytic equations.
Source: Grauert–Remmert, Coherent Analytic Sheaves, Ch. 2; the finite mapping theorem. -/
theorem holomorphic_chart_image_localEquations {M : Type*} [TopologicalSpace M]
    (S : an_ReducedSpace M) {n : ℕ} (e : OpenPartialHomeomorph M (Fin n → ℂ))
    (hcoords : ∀ j, S.IsHolFun (fun x : e.source => e x j)) (A : Set e.source)
    (hA : an_IsClosedAnalytic (anrem_openSpace S e.open_source) A)
    (y : e.target) (hy : y ∈ e.toHomeomorphSourceTarget '' A) :
    anrem_LocEq (Subtype.val '' (e.toHomeomorphSourceTarget '' A)) y.1 := by
  have hfin (w : e.target) : (A ∩ e.toHomeomorphSourceTarget ⁻¹' {w}).Finite := by
    apply Set.Subsingleton.finite
    intro x hx z hz
    exact e.toHomeomorphSourceTarget.injective (hx.2.trans hz.2.symm)
  have himage := an_finite_mapping
    (anrem_openSpace S e.open_source)
    (anrem_openSpace (an_euclidSpace n) e.open_target)
    e.toHomeomorphSourceTarget (holomorphic_chart_isProperHom S e hcoords) hA hfin
  have hnear := (anrem_anNear_openSpace_iff (an_euclidSpace n) e.open_target
    (e.toHomeomorphSourceTarget '' A) y).mp (himage.2 y hy)
  have hloc := anrem_anNear_chart (an_euclidSpace n) hnear PUnit.unit (mem_univ _)
  change anrem_LocEq (id '' (Subtype.val '' (e.toHomeomorphSourceTarget '' A) ∩ univ)) y.1 at hloc
  simpa only [Set.inter_univ, Set.image_id] using hloc

/-- A closed analytic subset has local analytic equations in any holomorphic chart image.
Source: Grauert–Remmert, Coherent Analytic Sheaves, Ch. 2; finite mapping on open chart domains. -/
theorem holomorphic_chart_image_ambient {M : Type*} [TopologicalSpace M]
    (S : an_ReducedSpace M) {n : ℕ} (e : OpenPartialHomeomorph M (Fin n → ℂ))
    (hcoords : ∀ j, S.IsHolFun (fun x : e.source => e x j))
    (A : Set M) (hA : an_IsClosedAnalytic S A) (x : M) (hx : x ∈ e.source) (hxA : x ∈ A) :
    anrem_LocEq (e '' (A ∩ e.source)) (e x) := by
  let A' : Set e.source := Subtype.val ⁻¹' A
  have hA' : an_IsClosedAnalytic (anrem_openSpace S e.open_source) A' :=
    anrem_isClosedAnalytic_openSpace S e.open_source hA
  have h := holomorphic_chart_image_localEquations S e hcoords A' hA'
    (e.toHomeomorphSourceTarget ⟨x, hx⟩) ⟨⟨x, hx⟩, hxA, rfl⟩
  have himg : (Subtype.val '' (e.toHomeomorphSourceTarget '' A') : Set (Fin n → ℂ)) =
      e '' (A ∩ e.source) := by
    ext z
    constructor
    · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, ⟨hv, v.2⟩, rfl⟩
    · rintro ⟨v, ⟨hvA, hvS⟩, rfl⟩
      exact ⟨e.toHomeomorphSourceTarget ⟨v, hvS⟩, ⟨⟨v, hvS⟩, hvA, rfl⟩, rfl⟩
  rw [himg] at h
  exact h

end AlgebraicGeometry.SingularCycles
