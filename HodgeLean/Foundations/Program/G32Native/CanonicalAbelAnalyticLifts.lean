import HodgeLean.Foundations.Program.G32Native.CanonicalAbelHolomorphic
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.TorusLocalLift

/-! # Analytic lifts in the retained ambient coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open scoped BigOperators Topology Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- Analytic coordinate lifts of the retained symmetric Abel sum on the specified sheet. -/
theorem canonical_abel_analytic_lifts (G : CanonicalAbelGeometry) (p : ComplexPoint G.Z) :
    ∃ (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ)),
      ∀ x : ComplexPoint G.Q,
      AnalyticAt ℂ (F x)
        (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)) ∧
      ∀ᶠ w in 𝓝 (Point.map G.ι x), ∀ z : Fin (2 * G.k) → ComplexPoint G.Z,
        Point.map G.γ (s2_lift (2 * G.k) z) = Point.map G.β w →
        canonicalPeriodQuotient G (F x (localChart G.W (G.k + G.k) (Point.map G.ι x) w)) =
          ∑ i, analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p (z i) := by
  classical
  let h := Module.finrank_fin_fun (n := 1) ℂ
  letI := b3_periodLattice_finite (C := ComplexPoint G.Z) h
  letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint G.Z)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint G.Z) h)
  let s := canonicalSymmetricAbel G p
  let a := fun w : ComplexPoint G.W => s (Point.map G.β w)
  have ha : ContMDiff 𝓘(ℂ, Fin (G.k + G.k) → ℂ)
      𝓘(ℂ, b3Rest2_VJ (Fin 1 → ℂ) (ComplexPoint G.Z)) ω a :=
    (canonicalSymmetricAbel_contMDiff G p).comp
      (spec_contMDiff_pointMap G.W G.B (G.k + G.k) (G.k + G.k) G.β)
  let C := fun x : ComplexPoint G.Q => localChart G.W (G.k + G.k) (Point.map G.ι x)
  let A := fun x : ComplexPoint G.Q => a ∘ (C x).symm
  have hA (x : ComplexPoint G.Q) : ContMDiffAt 𝓘(ℂ, Fin (G.k + G.k) → ℂ)
      𝓘(ℂ, b3Rest2_VJ (Fin 1 → ℂ) (ComplexPoint G.Z)) ω (A x)
      (C x (Point.map G.ι x)) := by
    have hh := contMDiffAt_iff_source.mp (ha (Point.map G.ι x))
    change ContMDiffWithinAt 𝓘(ℂ, Fin (G.k + G.k) → ℂ)
      𝓘(ℂ, b3Rest2_VJ (Fin 1 → ℂ) (ComplexPoint G.Z)) ω (A x)
      (Set.range 𝓘(ℂ, Fin (G.k + G.k) → ℂ)) (C x (Point.map G.ι x)) at hh
    simpa only [modelWithCornersSelf_coe, Set.range_id, contMDiffWithinAt_univ] using hh
  let g := fun x : ComplexPoint G.Q =>
    (torus_localLift (b3_periodF (Fin 1 → ℂ) (ComplexPoint G.Z))
      (A x) (C x (Point.map G.ι x)) (hA x)).choose
  have hg (x : ComplexPoint G.Q) :=
    (torus_localLift (b3_periodF (Fin 1 → ℂ) (ComplexPoint G.Z))
      (A x) (C x (Point.map G.ι x)) (hA x)).choose_spec
  let L := (quotientBasisEquiv h (canonicalFormBasis G)).toLinearMap.comp
    (b2_coord (b3Rest2_QJ (Fin 1 → ℂ) (ComplexPoint G.Z))).symm.toLinearMap
  let F := fun x u => L (g x u)
  refine ⟨F, fun x => ⟨?_, ?_⟩⟩
  · exact (L.toContinuousLinearMap.analyticAt _).comp (hg x).1.contDiffAt.analyticAt
  · have hs : Point.map G.ι x ∈ (C x).source := mem_localChart_source _ _ _
    have hc := (C x).continuousAt hs
    have he := hc.eventually (hg x).2
    filter_upwards [he, (C x).open_source.mem_nhds hs] with w hw hwC
    intro z hz
    have hcoord (v : b3Rest2_VJ (Fin 1 → ℂ) (ComplexPoint G.Z)) :
        canonicalPeriodQuotient G (L v) = b2_torusCover
          (b3_periodLattice (Fin 1 → ℂ) (ComplexPoint G.Z))
          (b3_periodF (Fin 1 → ℂ) (ComplexPoint G.Z)) v := by
      change QuotientAddGroup.mk ((quotientBasisEquiv h (canonicalFormBasis G)).symm
        ((quotientBasisEquiv h (canonicalFormBasis G))
          ((b2_coord (b3Rest2_QJ (Fin 1 → ℂ) (ComplexPoint G.Z))).symm v))) = _
      rw [LinearEquiv.symm_apply_apply]
      rfl
    change canonicalPeriodQuotient G (L (g x (C x w))) = _
    change A x (C x w) = b2_torusCover
      (b3_periodLattice (Fin 1 → ℂ) (ComplexPoint G.Z))
      (b3_periodF (Fin 1 → ℂ) (ComplexPoint G.Z)) (g x (C x w)) at hw
    rw [hcoord, ← hw]
    change s (Point.map G.β ((C x).symm (C x w))) = _
    rw [(C x).left_inv hwC, ← hz]
    exact canonicalSymmetricAbel_tuple G p z

#print axioms canonical_abel_analytic_lifts
end HodgeLean.Foundations.Program.G32Native
