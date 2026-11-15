import HodgeLean.Adapters.NormalConeB4aClassChartFunction

/-! # Original chart functions near a smooth affine open of a singular ambient scheme -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Set Filter Topology TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- The inverse of an original holomorphic chart preserves holomorphic functions near any point contained in a smooth affine open, without global ambient smoothness.
Source: Gunning and Rossi, Analytic Functions of Several Complex Variables, chapter II, inverse regularity on complex manifolds.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_function_analytic_on_smooth_affine_open
    (X : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U)
    [Smooth (ComplexPoint.openScheme X U).hom] {r c : ℕ}
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (W : Set (ComplexPoint X)) (hW : IsOpen W)
    (g : ComplexPoint X → ℂ) (hg : (f4_analytification X).IsHolFun (fun x : W => g x))
    (z : (Fin r → ℂ) × (Fin c → ℂ)) (hz : z ∈ e.target) (hzW : e.symm z ∈ W)
    (hzU : (e.symm z).underlying ∈ U) :
    AnalyticAt ℂ (fun v => g (e.symm v)) z := by
  let Y := ComplexPoint.openScheme X U
  letI : IsAffine Y.left := hU
  letI : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
  letI : QuasiCompact Y.hom := (quasiCompact_iff_compactSpace Y.hom).2 inferInstance
  letI : IsSeparated Y.hom := inferInstanceAs (IsSeparated (U.ι ≫ X.hom))
  let x := e.symm z
  let xU := ComplexPoint.asOpenPoint X U x hzU
  let f := Point.map (ComplexPoint.openInclusion X U)
  have hfx : f xU = x := Over.OverMorphism.ext (ComplexPoint.liftToOpen_fac X U x hzU)
  letI : Nonempty (ComplexPoint Y) := ⟨xU⟩
  obtain ⟨a, ha, hasource, haval⟩ := a3b4a_classHolomorphicChart_openPullback X U r c e he
  have hxa : xU ∈ a.source := by
    rw [hasource]
    change f xU ∈ e.source
    rw [hfx]
    exact e.map_target hz
  have hax : a xU = z := by
    rw [haval]
    change e (f xU) = z
    rw [hfx]
    exact e.right_inv hz
  have hzA : z ∈ a.target := hax ▸ a.map_source hxa
  have hmap := f4_map_isHom (ComplexPoint.openInclusion X U)
  have hfW : IsOpen (f ⁻¹' W) := hW.preimage hmap.1
  have hgY : (f4_analytification Y).IsHolFun (fun y : f ⁻¹' W => g (f y)) :=
    hmap.2 W hW (fun w : W => g w) hg
  have hzY : a.symm z ∈ f ⁻¹' W := by
    rw [← hax, a.left_inv hxa]
    change f xU ∈ W
    rwa [hfx]
  have hanalytic := a3b4a_classHolomorphicChart_function_analytic Y a ha
    (f ⁻¹' W) hfW (fun y => g (f y)) hgY z hzA hzY
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

end HodgeLean.Foundations.QuotientDuality
