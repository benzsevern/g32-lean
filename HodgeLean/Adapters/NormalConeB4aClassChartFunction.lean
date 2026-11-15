import HodgeLean.Adapters.NormalConeB4aClassHolomorphicTransition

/-! # Holomorphic functions in the frozen chart coordinates

Route: pull the chart and function to one standard-smooth affine open,
apply analytic inverse regularity, and identify their coordinate germs.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry Set Filter Topology TopologicalSpace
open HodgeLean.Foundations.Analytic
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false in
/-- A holomorphic function remains analytic when expressed in any frozen
holomorphic normal chart. -/
theorem a3b4a_classHolomorphicChart_function_analytic
    (X : Over (Spec (CommRingCat.of ℂ))) [Smooth X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] {r c : ℕ}
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (W : Set (ComplexPoint X)) (hW : IsOpen W)
    (g : ComplexPoint X → ℂ) (hg : (f4_analytification X).IsHolFun (fun x : W => g x))
    (z : (Fin r → ℂ) × (Fin c → ℂ)) (hz : z ∈ e.target) (hzW : e.symm z ∈ W) :
    AnalyticAt ℂ (fun v => g (e.symm v)) z := by
  let x := e.symm z
  have hx : x ∈ e.source := e.map_target hz
  obtain ⟨U, hU, hxU, hs⟩ := Smooth.exists_affine_isStandardSmooth X.hom x.underlying
  obtain ⟨d, hd⟩ := RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension hs
  let Y := ComplexPoint.openScheme X U
  letI : IsAffine Y.left := hU
  letI : SmoothOfRelativeDimension d Y.hom :=
    smoothOfRelativeDimension_affineOpen_of_isStandardSmooth X.hom hU hd
  letI : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
  letI : QuasiCompact Y.hom := (quasiCompact_iff_compactSpace Y.hom).2 inferInstance
  letI : IsSeparated Y.hom := inferInstanceAs (IsSeparated (U.ι ≫ X.hom))
  let xU := ComplexPoint.asOpenPoint X U x hxU
  let f := Point.map (ComplexPoint.openInclusion X U)
  have hfx : f xU = x := Over.OverMorphism.ext (ComplexPoint.liftToOpen_fac X U x hxU)
  letI : Nonempty (ComplexPoint Y) := ⟨xU⟩
  obtain ⟨a, ha, hasource, haval⟩ := a3b4a_classHolomorphicChart_openPullback X U r c e he
  have hxa : xU ∈ a.source := by
    rw [hasource]
    change f xU ∈ e.source
    rwa [hfx]
  have hax : a xU = z := by
    rw [haval]
    change e (f xU) = z
    rw [hfx]
    exact e.right_inv hz
  have hzA : z ∈ a.target := hax ▸ a.map_source hxa
  have hmap := f4_map_isHom (ComplexPoint.openInclusion X U)
  have hfW : IsOpen (f ⁻¹' W) := hW.preimage hmap.1
  have hgY : ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω (fun y => g (f y)) (f ⁻¹' W) :=
    (f4_isHolFun_iff_contMDiffOn Y d (fun y => g (f y)) hfW).mp
      (hmap.2 W hW (fun w : W => g w) hg)
  have hzY : a.symm z ∈ f ⁻¹' W := by
    rw [← hax, a.left_inv hxa]
    change f xU ∈ W
    rwa [hfx]
  have hai := a3b4a_classManifoldChart_inverse a
    (a3b4a_classHolomorphicChart_contMDiffOn Y d r c a ha)
  have hanalytic : AnalyticAt ℂ (fun v => g (f (a.symm v))) z :=
    ((hgY _ hzY).contMDiffAt (hfW.mem_nhds hzY) |>.comp z
      ((hai z hzA).contMDiffAt (a.open_target.mem_nhds hzA))).contDiffAt.analyticAt
  apply hanalytic.congr
  filter_upwards [a.open_target.mem_nhds hzA] with v hv
  have hva : f (a.symm v) ∈ e.source := by
    have h := a.map_target hv
    rw [hasource] at h
    exact h
  have hfv : f (a.symm v) = e.symm v := by
    calc
      f (a.symm v) = e.symm (e (f (a.symm v))) := (e.left_inv hva).symm
      _ = e.symm (a (a.symm v)) := by rw [haval]
      _ = e.symm v := by rw [a.right_inv hv]
  rw [hfv]

end HodgeLean.Adapters
