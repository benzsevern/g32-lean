import HodgeLean.Adapters.NormalConeB4aClassChartPullback
import HodgeLean.Adapters.NormalConeB4aClassManifoldOverlap
import HodgeLean.Adapters.NormalConeB4aClassPurityLocal

/-! # Analytic transitions for the frozen holomorphic charts

Route: choose a standard-smooth affine neighborhood of the point in the
original scheme. Pull both charts back to it, use manifold inverse
regularity, and identify the transition germ with the original transition.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false in
/-- Transitions between frozen holomorphic charts are analytic even when the
smooth ambient scheme has varying dimension. -/
theorem a3b4a_classHolomorphicChart_transition_analytic
    (X : Over (Spec (CommRingCat.of ℂ))) [Smooth X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] {r s c d : ℕ}
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (e' : OpenPartialHomeomorph (ComplexPoint X) ((Fin s → ℂ) × (Fin d → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (he' : a3b4_IsHolChart X.hom e') :
    AnalyticOnNhd ℂ (e.symm.trans e') (e.symm.trans e').source := by
  intro z hz
  change z ∈ e.target ∧ e.symm z ∈ e'.source at hz
  let x := e.symm z
  have hx : x ∈ e.source := e.map_target hz.1
  have hx' : x ∈ e'.source := hz.2
  obtain ⟨U, hU, hxU, hs⟩ := Smooth.exists_affine_isStandardSmooth X.hom x.underlying
  obtain ⟨m, hd⟩ := RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension hs
  let Y := ComplexPoint.openScheme X U
  letI : IsAffine Y.left := hU
  letI : SmoothOfRelativeDimension m Y.hom :=
    smoothOfRelativeDimension_affineOpen_of_isStandardSmooth X.hom hU hd
  letI : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
  letI : QuasiCompact Y.hom := (quasiCompact_iff_compactSpace Y.hom).2 inferInstance
  letI : IsSeparated Y.hom := inferInstanceAs (IsSeparated (U.ι ≫ X.hom))
  let xU := ComplexPoint.asOpenPoint X U x hxU
  let f := Point.map (ComplexPoint.openInclusion X U)
  have hfx : f xU = x := Over.OverMorphism.ext (ComplexPoint.liftToOpen_fac X U x hxU)
  letI : Nonempty (ComplexPoint Y) := ⟨xU⟩
  obtain ⟨a, ha, hasource, haval⟩ := a3b4a_classHolomorphicChart_openPullback X U r c e he
  obtain ⟨b, hb, hbsource, hbval⟩ := a3b4a_classHolomorphicChart_openPullback X U s d e' he'
  have hxa : xU ∈ a.source := by
    rw [hasource]
    change f xU ∈ e.source
    rwa [hfx]
  have hxb : xU ∈ b.source := by
    rw [hbsource]
    change f xU ∈ e'.source
    rwa [hfx]
  have hax : a xU = z := by
    rw [haval]
    change e (f xU) = z
    rw [hfx]
    exact e.right_inv hz.1
  have hzA : z ∈ a.target := hax ▸ a.map_source hxa
  have hzB : a.symm z ∈ b.source := by
    rw [← hax, a.left_inv hxa]
    exact hxb
  have har := a3b4a_classHolomorphicChart_contMDiffOn Y m r c a ha
  have hai := a3b4a_classManifoldChart_inverse a har
  have hbr := a3b4a_classHolomorphicChart_contMDiffOn Y m s d b hb
  let t := a.symm.trans b
  have ht : AnalyticOnNhd ℂ t t.source := by
    intro v hv
    have h₁ := (hai v hv.1).contMDiffAt (a.open_target.mem_nhds hv.1)
    have h₂ := (hbr (a.symm v) hv.2).contMDiffAt (b.open_source.mem_nhds hv.2)
    exact (h₂.comp v h₁).contDiffAt.analyticAt
  have hzT : z ∈ t.source := ⟨hzA, hzB⟩
  have hlocal : (e.symm.trans e') =ᶠ[𝓝 z] t := by
    filter_upwards [a.open_target.mem_nhds hzA] with v hv
    have hva : a.symm v ∈ a.source := a.map_target hv
    have hvas : f (a.symm v) ∈ e.source := by
      rw [hasource] at hva
      exact hva
    have hfv : f (a.symm v) = e.symm v := by
      calc
        f (a.symm v) = e.symm (e (f (a.symm v))) := (e.left_inv hvas).symm
        _ = e.symm (a (a.symm v)) := by rw [haval]
        _ = e.symm v := by rw [a.right_inv hv]
    change e' (e.symm v) = b (a.symm v)
    rw [hbval]
    change e' (e.symm v) = e' (f (a.symm v))
    rw [hfv]
  exact (ht z hzT).congr hlocal.symm

end HodgeLean.Adapters
