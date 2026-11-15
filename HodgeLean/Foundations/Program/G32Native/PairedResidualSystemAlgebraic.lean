import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemProjective
import HodgeLean.Foundations.Program.SchoenCycleCanonicalGraphAlgebraic
import HodgeLean.Foundations.Program.SchoenCyclePairedProjective
import HodgeLean.Foundations.Program.SchoenCyclePairedEvaluation
import HodgeLean.Foundations.Program.SchoenCycleGenusTransport

/-! # Algebraization of the full differential system -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold Filter Topology CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Adapters HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
  [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] (k s : ℕ)
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)
variable
  (y : Fin (2 * s) → ComplexPoint Z) (hy : Function.Injective y)
  (W : Submodule ℂ (TangentBundle 𝓘(ℂ, Fin 1 → ℂ) (ComplexPoint Z) → ℂ))
  (hW : ∀ q : W, b4c_IsMeroForm hOne q.val ∧
    (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hOne q.val p) 0) ∧
    (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hOne q.val p) 0) ∧
    ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
  (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * s)
  (γ : g3_power Z (2 * k) ⟶ B) (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "F₀" => (residualProjectiveSystemPoint hOne y hy W hW hgenus γ id)
include hy hW hgenus hγ


variable [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
  [FiniteDimensional ℂ W] (l : ℕ) (hd : Module.finrank ℂ W = l + 1)
include hd

/-- Pullbacks of the full-system evaluation graph are closed analytic sets. -/
theorem residual_system_divisor_graph
    (T : Over (Spec ↧ℂ)) (t : ℕ) [SmoothOfRelativeDimension t T.hom]
    (u : T ⟶ Over.mk (ProjectiveSpace.toBase (Fin (l + 1)) (Spec ↧ℂ)))
    (v : T ⟶ B) :
    let ep := s2e_finiteDimensionalProjectivePointEquiv (V := W) l hd
    let F := residualProjectiveSystemPoint hOne y hy W hW hgenus γ id
    IsClosedAnalytic (Fin t → ℂ)
      {x : ComplexPoint T | F (ep.symm (Point.map u x)) = Point.map v x} := by
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  let d := l + 1
  let q := TopologicalSpace.dim B.left
  letI : IsIntegral (ProjectiveSpace (Fin (l + 1)) (Spec ↧ℂ)) :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral l
  let e := TopologicalSpace.dim (ProjectiveSpace (Fin (l + 1)) (Spec ↧ℂ))
  letI : Smooth (ProjectiveSpace.toBase (Fin (l + 1)) (Spec ↧ℂ)) :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_smooth l
  letI : SmoothOfRelativeDimension d
      (Over.mk (complexAffineSpace (Fin (l + 1)) ↘ Spec ↧ℂ)).hom :=
    AffineSpace.smoothOfRelativeDimension_of_card_eq (Spec ↧ℂ) (by simp [d])
  letI : SmoothOfRelativeDimension e
      (Over.mk (ProjectiveSpace.toBase (Fin (l + 1)) (Spec ↧ℂ))).hom :=
    SmoothOfRelativeDimension.of_isIntegral (ProjectiveSpace.toBase (Fin (l + 1)) (Spec ↧ℂ))
  letI : SmoothOfRelativeDimension q B.hom := SmoothOfRelativeDimension.of_isIntegral B.hom
  classical
  letI : FiniteDimensional ℂ (W) :=
    Module.finite_of_finrank_pos (by rw [hd]; omega)
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (l + 1)) (Spec ↧ℂ))
  let ep := s2e_finiteDimensionalProjectivePointEquiv
    (V := W) l hd
  let g := fun R => residualProjectiveSystemPoint hOne y hy W hW hgenus γ id (ep.symm R)
  have hgcont : Continuous g := residual_system_projective_continuous Z B k s y hy W hW hgenus γ hγ l hd
  apply isClosedAnalytic_iff_finite.mpr
  refine ⟨isClosed_eq (hgcont.comp (Point.continuous_map u)) (Point.continuous_map v), ?_⟩
  intro x hx
  change g (Point.map u x) = Point.map v x at hx
  let C := localChart T t x
  let D := localChart PP e (Point.map u x)
  let E := localChart B q (g (Point.map u x))
  have hxC : x ∈ C.source := mem_localChart_source T t x
  have hxD : Point.map u x ∈ D.source := mem_localChart_source PP e _
  have hxE : g (Point.map u x) ∈ E.source := mem_localChart_source B q _
  have hu : AnalyticAt ℂ (fun w => D (Point.map u (C.symm w))) (C x) := by
    apply analyticAt_localChart_symm_map T PP u t e x (C.map_source hxC)
    rw [C.left_inv hxC]
    exact hxD
  have hv : AnalyticAt ℂ (fun w => E (Point.map v (C.symm w))) (C x) := by
    have hh := analyticAt_localChart_symm_map T B v t q x (C.map_source hxC)
      (by rw [C.left_inv hxC]; exact mem_localChart_source B q _)
    simpa only [E, hx] using hh
  let φ := fun w => (E (Point.map v (C.symm w)), D (Point.map u (C.symm w)))
  have hφ : AnalyticAt ℂ φ (C x) := hv.prod hu
  have hφx : φ (C x) = (E (g (Point.map u x)), D (Point.map u x)) := by
    simp only [φ, C.left_inv hxC, hx]
  have hgraph := residual_system_projective_chart_graph_analytic Z B k s y hy W hW hgenus γ hγ l hd d e q (Point.map u x)
  have hp := s2e_analyticNear_preimage_at φ (C x) _ hφ (by rw [hφx]; exact hgraph)
  have hcu : ContinuousAt (fun w => Point.map u (C.symm w)) (C x) :=
    (Point.continuous_map u).continuousAt.comp (C.continuousAt_symm (C.map_source hxC))
  have hcv : ContinuousAt (fun w => Point.map v (C.symm w)) (C x) :=
    (Point.continuous_map v).continuousAt.comp (C.continuousAt_symm (C.map_source hxC))
  have hcg := hgcont.continuousAt.comp hcu
  have hDu : ∀ᶠ w in nhds (C x), Point.map u (C.symm w) ∈ D.source :=
    hcu.eventually (D.open_source.mem_nhds (by simpa only [C.left_inv hxC] using hxD))
  have hEg : ∀ᶠ w in nhds (C x), g (Point.map u (C.symm w)) ∈ E.source :=
    hcg.eventually (E.open_source.mem_nhds (by simpa only [Function.comp_apply, C.left_inv hxC] using hxE))
  have hEv : ∀ᶠ w in nhds (C x), Point.map v (C.symm w) ∈ E.source :=
    hcv.eventually (E.open_source.mem_nhds (by simpa only [C.left_inv hxC, hx] using hxE))
  have hlocal : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {w | g (Point.map u (C.symm w)) = Point.map v (C.symm w)} (C x) := by
    apply hp.congr
    filter_upwards [hDu, hEg, hEv] with w hdu heg hev
    change E (g (D.symm (D (Point.map u (C.symm w))))) = E (Point.map v (C.symm w)) ↔ _
    rw [D.left_inv hdu]
    exact ⟨fun h => E.injOn heg hev h, fun h => congrArg E h⟩
  obtain ⟨U, hU, hxU, κ, hκ, f, hf, heq⟩ := hlocal
  refine ⟨U ∩ C.target, hU.inter C.open_target, ⟨hxU, C.map_source hxC⟩,
    Set.inter_subset_right, κ, hκ, f, fun j => (hf j).mono Set.inter_subset_left, ?_⟩
  intro w hw
  exact heq w hw.1

#print axioms residual_system_divisor_graph
/-- The full normalized differential system defines an algebraic map to the supplied quotient. -/
theorem residual_system_divisor_morphism :
    let ep := s2e_finiteDimensionalProjectivePointEquiv (V := W) l hd
    let F := residualProjectiveSystemPoint hOne y hy W hW hgenus γ id
    ∃ f : Over.mk (ProjectiveSpace.toBase (Fin (l + 1)) (Spec ↧ℂ)) ⟶ B,
      Point.map f = fun R => F (ep.symm R) := by
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (l + 1)) (Spec ↧ℂ))
  letI : IsIntegral PP.left := HodgeLean.Adapters.IntersectionProductScaf_projective_integral l
  letI : Smooth PP.hom := HodgeLean.Adapters.IntersectionProductScaf_projective_smooth l
  letI : IsProjective PP.hom := ⟨⟨⟨l, 𝟙 _, Category.id_comp _⟩⟩⟩
  let ep := s2e_finiteDimensionalProjectivePointEquiv
    (V := W) l hd
  let F := residualProjectiveSystemPoint hOne y hy W hW hgenus γ id
  let g := fun R => F (ep.symm R)
  let T := HodgeLean.Adapters.gagam_product PP B
  letI : SmoothOfRelativeDimension (TopologicalSpace.dim T.left) T.hom :=
    SmoothOfRelativeDimension.of_isIntegral T.hom
  obtain ⟨C, hC, heq⟩ := chowG_setLevel T _
    (residual_system_divisor_graph Z B k s y hy W hW hgenus γ hγ l hd T (TopologicalSpace.dim T.left)
      (CartesianMonoidalCategory.fst PP B) (CartesianMonoidalCategory.snd PP B))
  apply HodgeLean.Adapters.gagam_morphism_of_closed_graph PP B g C hC
  rw [← heq]
  ext x
  exact eq_comm

#print axioms residual_system_divisor_morphism
end HodgeLean.Foundations.Program.G32Native
