import HodgeLean.Foundations.Program.SchoenCyclePairedProjective
import HodgeLean.Foundations.Program.SchoenCycleGenusTransport
import HodgeLean.Foundations.Program.SchoenCycleCanonicalGraphAlgebraic

/-! # S1 cycle chain statements
Implication from the native paired differential family to its analytic incidence
and algebraic map. First unit only; tangent and branch-ideal geometry are deferred.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program

theorem s2e_chain_paired_divisor_graph_aux
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r : ℕ) (hr : 0 < r)
    [FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))]
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (w : Fin r → b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint Z)
      (Module.finrank_fin_fun (n := 1) ℂ))
    (hres : ∀ i j, b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
      (w i) (y ⟨2 * j.val + 1, by omega⟩) = if i = j then 1 else 0)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) = k + 1)
    (γ : g3_power Z (2 * k) ⟶ B)
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (T : Over (Spec ↧ℂ)) (t : ℕ) [SmoothOfRelativeDimension t T.hom]
    (u : T ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (v : T ⟶ B) :
    letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k hd
    let F := s2e_projectiveDifferentialQuotientPoint
      (Module.finrank_fin_fun (n := 1) ℂ) w
      (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus γ id
    IsClosedAnalytic (Fin t → ℂ)
      {x : ComplexPoint T | F (ep.symm (Point.map u x)) = Point.map v x} := by
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  let d := k + 1
  let q := TopologicalSpace.dim B.left
  letI : IsIntegral (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)) :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral k
  let e := TopologicalSpace.dim (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ))
  letI : Smooth (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_smooth k
  letI : SmoothOfRelativeDimension d
      (Over.mk (complexAffineSpace (Fin (k + 1)) ↘ Spec ↧ℂ)).hom :=
    AffineSpace.smoothOfRelativeDimension_of_card_eq (Spec ↧ℂ) (by simp [d])
  letI : SmoothOfRelativeDimension e
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom :=
    SmoothOfRelativeDimension.of_isIntegral (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  letI : SmoothOfRelativeDimension q B.hom := SmoothOfRelativeDimension.of_isIntegral B.hom
  classical
  letI : FiniteDimensional ℂ ((b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ))) :=
    Module.finite_of_finrank_pos (by rw [hd]; omega)
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  let ep := s2e_finiteDimensionalProjectivePointEquiv
    (V := (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ))) k hd
  let g := fun R => s2e_projectiveDifferentialQuotientPoint (Module.finrank_fin_fun (n := 1) ℂ) w
    (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus γ id (ep.symm R)
  have hgcont : Continuous g := s2e_pairedProjective_continuous Z B k r w (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus γ hγ hd
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
  have hgraph := s2e_pairedProjective_chart_graph_analytic Z B k r w (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus γ hγ hd d e q (Point.map u x)
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


theorem s2e_chain_paired_divisor_morphism_aux
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r : ℕ) (hr : 0 < r)
    [FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))]
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (w : Fin r → b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint Z)
      (Module.finrank_fin_fun (n := 1) ℂ))
    (hres : ∀ i j, b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
      (w i) (y ⟨2 * j.val + 1, by omega⟩) = if i = j then 1 else 0)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) = k + 1)
    (γ : g3_power Z (2 * k) ⟶ B)
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    :
    letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k hd
    let F := s2e_projectiveDifferentialQuotientPoint
      (Module.finrank_fin_fun (n := 1) ℂ) w
      (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus γ id
    ∃ ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B,
      Point.map ℓ = fun R => F (ep.symm R) := by
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  letI : IsIntegral PP.left := HodgeLean.Adapters.IntersectionProductScaf_projective_integral k
  letI : Smooth PP.hom := HodgeLean.Adapters.IntersectionProductScaf_projective_smooth k
  letI : IsProjective PP.hom := ⟨⟨⟨k, 𝟙 _, Category.id_comp _⟩⟩⟩
  let ep := s2e_finiteDimensionalProjectivePointEquiv
    (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k hd
  let F := s2e_projectiveDifferentialQuotientPoint
    (Module.finrank_fin_fun (n := 1) ℂ) w
    (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus γ id
  let g := fun R => F (ep.symm R)
  let T := HodgeLean.Adapters.gagam_product PP B
  letI : SmoothOfRelativeDimension (TopologicalSpace.dim T.left) T.hom :=
    SmoothOfRelativeDimension.of_isIntegral T.hom
  obtain ⟨C, hC, heq⟩ := chowG_setLevel T _
    (s2e_chain_paired_divisor_graph_aux Z B k r hr y hy w hres horder hout hgenus hd
      γ hγ T (TopologicalSpace.dim T.left)
      (CartesianMonoidalCategory.fst PP B) (CartesianMonoidalCategory.snd PP B))
  apply HodgeLean.Adapters.gagam_morphism_of_closed_graph PP B g C hC
  rw [← heq]
  ext x
  exact eq_comm

end HodgeLean.Foundations.Program
