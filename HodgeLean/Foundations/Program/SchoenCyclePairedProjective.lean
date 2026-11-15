import HodgeLean.Foundations.Program.SchoenCyclePairedEvaluation
import HodgeLean.Foundations.Program.SchoenCycleProjectiveGraph
import HodgeLean.Foundations.Program.SchoenCycleGenusTransport

/-! # Evaluation of adjusted divisor clusters -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold Filter Topology CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Adapters HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program
variable (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
  [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] (k s : ℕ)
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)
local notation "V₀" => (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin s → ℂ))
variable (forms : Fin s → b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint Z) hOne)
  (x : Fin s → ComplexPoint Z)
  (hres : ∀ i j, b4c_res (hE := hOne) (forms i) (x j) = if i = j then 1 else 0)
  (y : Fin (2 * s) → ComplexPoint Z) (hy : Function.Injective y)
  (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hOne (forms i) p) 0)
  (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ (HurwitzPrymRR_loc hOne (forms i) p) 0)
  (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * s)
  (γ : g3_power Z (2 * k) ⟶ B) (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
variable [FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))]
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "F₀" => (s2e_projectiveDifferentialQuotientPoint hOne forms x hres y hy horder hout hgenus γ id)
include hres hy horder hout hgenus hγ

variable (hd : Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin s → ℂ)) = k + 1)
include hd
theorem s2e_pairedFamily_updated_chart_graph_analytic
    (q : ℕ) [SmoothOfRelativeDimension q B.hom]
    {m : ℕ} (b : Fin m → (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin s → ℂ)))
    (a : Fin m → ℂ) (hne : (∑ j, a j • b j) ≠ 0) (i : Fin m) (hai : a i = 1) :
    let Q := s2e_projectiveDifferentialQuotientPoint hOne forms x hres y hy horder hout hgenus γ id (Projectivization.mk ℂ (∑ j, a j • b j) hne)
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {p : (Fin q → ℂ) × (Fin m → ℂ) |
        ∃ hn : (∑ j, (Function.update p.2 i 1) j • b j) ≠ 0,
          localChart B q Q (s2e_projectiveDifferentialQuotientPoint hOne forms x hres y hy horder hout hgenus γ id
            (Projectivization.mk ℂ (∑ j, (Function.update p.2 i 1) j • b j) hn)) = p.1}
      (localChart B q Q Q, a) := by
  classical
  let Q := s2e_projectiveDifferentialQuotientPoint hOne forms x hres y hy horder hout hgenus γ id (Projectivization.mk ℂ (∑ j, a j • b j) hne)
  let φ := fun p : (Fin q → ℂ) × (Fin m → ℂ) => (Function.update p.2 i 1 - a, p.1)
  have hu : Function.update a i 1 = a := by
    funext j
    by_cases h : j = i
    · subst j; simp [hai]
    · simp [h]
  have hupdate : AnalyticAt ℂ (fun p : (Fin q → ℂ) × (Fin m → ℂ) => Function.update p.2 i 1)
      (localChart B q Q Q, a) := by
    apply AnalyticAt.pi
    intro j
    by_cases h : j = i
    · subst j
      simpa only [Function.update_self] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : (Fin q → ℂ) × (Fin m → ℂ) => (1 : ℂ)) _)
    · simp only [Function.update_of_ne h]
      exact ((ContinuousLinearMap.proj j : (Fin m → ℂ) →L[ℂ] ℂ).analyticAt a).comp_of_eq
        analyticAt_snd rfl
  have hφ : AnalyticAt ℂ φ (localChart B q Q Q, a) :=
    (hupdate.sub analyticAt_const).prod analyticAt_fst
  have hφ0 : φ (localChart B q Q Q, a) = (0, localChart B q Q Q) := by simp [φ, hu]
  have hfam := s2e_pairedFamily_chart_graph_analytic Z B k s forms x hres y hy horder hout hgenus γ hγ q b a hne
  have hp := s2e_analyticNear_preimage_at φ (localChart B q Q Q, a) _ hφ
    (by rw [hφ0]; exact hfam)
  apply hp.congr
  apply Filter.Eventually.of_forall
  intro p
  have he : a + (Function.update p.2 i 1 - a) = Function.update p.2 i 1 := by abel
  change (∃ hn : (∑ j, (a + (Function.update p.2 i 1 - a)) j • b j) ≠ 0,
    localChart B q Q (s2e_projectiveDifferentialQuotientPoint hOne forms x hres y hy horder hout hgenus γ id
      (Projectivization.mk ℂ (∑ j, (a + (Function.update p.2 i 1 - a)) j • b j) hn)) = p.1) ↔ _
  simp only [he, Set.mem_ofPred_eq, Q]



theorem s2e_pairedProjective_chart_graph_analytic
    (d e q : ℕ)
    [SmoothOfRelativeDimension d (Over.mk (complexAffineSpace (Fin (k + 1)) ↘ Spec ↧ℂ)).hom]
    [SmoothOfRelativeDimension e (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom]
    [SmoothOfRelativeDimension q B.hom]
    (P : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))) :
    letI : FiniteDimensional ℂ ((b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin s → ℂ))) :=
      Module.finite_of_finrank_pos (by rw [hd]; omega)
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin s → ℂ))) k hd
    let g := fun R => s2e_projectiveDifferentialQuotientPoint hOne forms x hres y hy horder hout hgenus γ id (ep.symm R)
    let Q := g P
    let D := localChart (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) e P
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {p : (Fin q → ℂ) × (Fin e → ℂ) | localChart B q Q (g (D.symm p.2)) = p.1}
      (localChart B q Q Q, D P) := by
  letI : FiniteDimensional ℂ ((b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin s → ℂ))) :=
    Module.finite_of_finrank_pos (by rw [hd]; omega)
  let V := (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin s → ℂ))
  let ep := s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd
  let β := Module.finBasisOfFinrankEq ℂ V hd
  let g := fun R => s2e_projectiveDifferentialQuotientPoint hOne forms x hres y hy horder hout hgenus γ id (ep.symm R)
  let Q := g P
  let f := fun R => localChart B q Q (g R)
  apply s2e_projective_graph_descent k d e q f P
  intro i z hzi hzP
  let v := affineSpaceEquiv (Fin (k + 1)) z
  have hu : Function.update v i 1 = v := by
    funext j
    by_cases h : j = i
    · subst j; simpa only [Function.update_self] using hzi.symm
    · simp [h]
  obtain ⟨h0, he0⟩ := s2e_finiteDimensionalProjectivePointEquiv_symm_affineChart (V := V) k hd i v
  simp only [hu] at h0 he0
  have hzv : (affineSpaceEquiv (Fin (k + 1))).symm v = z :=
    (affineSpaceEquiv (Fin (k + 1))).symm_apply_apply z
  rw [hzv, hzP] at he0
  have hQ : s2e_projectiveDifferentialQuotientPoint hOne forms x hres y hy horder hout hgenus γ id
      (Projectivization.mk ℂ (∑ j, v j • β j) h0) = Q := by
    change _ = s2e_projectiveDifferentialQuotientPoint hOne forms x hres y hy horder hout hgenus γ id (ep.symm P)
    rw [he0]
  have hfam := s2e_pairedFamily_updated_chart_graph_analytic Z B k s forms x hres y hy horder hout hgenus γ hγ hd q
    (fun j => β j) v h0 i hzi
  dsimp only at hfam
  rw [hQ] at hfam
  rw [hzP]
  apply hfam.congr
  apply Filter.Eventually.of_forall
  intro p
  obtain ⟨hp, hep⟩ := s2e_finiteDimensionalProjectivePointEquiv_symm_affineChart (V := V) k hd i p.2
  constructor
  · rintro ⟨hn, hval⟩
    change localChart B q Q
      (s2e_projectiveDifferentialQuotientPoint hOne forms x hres y hy horder hout hgenus γ id
        (ep.symm (chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (k + 1))).symm p.2)))) = p.1
    rw [hep]
    exact hval
  · intro hval
    refine ⟨hp, ?_⟩
    change localChart B q Q
      (s2e_projectiveDifferentialQuotientPoint hOne forms x hres y hy horder hout hgenus γ id
        (ep.symm (chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (k + 1))).symm p.2)))) = p.1 at hval
    rw [hep] at hval
    exact hval



theorem s2e_pairedProjective_continuous :
    letI : FiniteDimensional ℂ ((b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin s → ℂ))) :=
      Module.finite_of_finrank_pos (by rw [hd]; omega)
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin s → ℂ))) k hd
    Continuous (fun R => s2e_projectiveDifferentialQuotientPoint hOne forms x hres y hy horder hout hgenus γ id (ep.symm R)) := by
  classical
  letI : FiniteDimensional ℂ ((b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin s → ℂ))) :=
    Module.finite_of_finrank_pos (by rw [hd]; omega)
  let V := (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin s → ℂ))
  let ep := s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd
  let β := Module.finBasisOfFinrankEq ℂ V hd
  let g := fun R => s2e_projectiveDifferentialQuotientPoint hOne forms x hres y hy horder hout hgenus γ id (ep.symm R)
  apply continuous_iff_continuousAt.mpr
  intro P
  obtain ⟨i, U, r, hU, hP, hr, he⟩ := s2e_projectivePoint_local_normalized_section k P
  have hrep (Q) (hQ : Q ∈ U) : ∃ hn : (∑ j, r Q j • β j : V) ≠ 0,
      ep.symm Q = Projectivization.mk ℂ (∑ j, r Q j • β j : V) hn := by
    obtain ⟨hv, hvQ⟩ := (he Q hQ).2
    have hh := s2e_finiteDimensionalProjectivePointEquiv_symm_vector (V := V) k hd (r Q) hv
    rw [hvQ] at hh
    have hn : (∑ j, r Q j • β j : V) ≠ 0 := by
      simpa only [Module.Basis.equivFun_symm_apply] using β.equivFun.symm.map_ne_zero_iff.mpr hv
    exact ⟨hn, by simpa only [Module.Basis.equivFun_symm_apply] using hh⟩
  obtain ⟨hnP, hlineP⟩ := hrep P hP
  let f : (Fin (k + 1) → ℂ) → ComplexPoint B := fun v =>
    if hv : (∑ j, v j • β j : V) ≠ 0 then
      s2e_projectiveDifferentialQuotientPoint hOne forms x hres y hy horder hout hgenus γ id (Projectivization.mk ℂ (∑ j, v j • β j : V) hv)
    else g P
  have hf : ContinuousAt f (r P) := by
    apply s2e_pairedFamily_evaluation_continuousAt Z B k s forms x hres y hy horder hout hgenus γ hγ (fun j => β j) (r P) hnP f
    filter_upwards [s2e_linear_family_eventually_ne_zero (fun j => β j) (r P) hnP] with v hv
    exact ⟨hv, dif_pos hv⟩
  apply (hf.comp (hr.continuousAt (hU.mem_nhds hP))).congr
  filter_upwards [hU.mem_nhds hP] with Q hQ
  obtain ⟨hn, hline⟩ := hrep Q hQ
  change f (r Q) = g Q
  dsimp only [f, g]
  rw [dif_pos hn, hline]



end HodgeLean.Foundations.Program
