import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Defs
import HodgeLean.Foundations.AnalyticDivisorAlgebraic3
import HodgeLean.Foundations.Port.Analysis.Complex.Polynomial.HolomorphicFactor

/-! # Holomorphic functions and simple polynomial roots

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Set Filter Topology HodgeLean.Foundations.Analytic
namespace AlgebraicGeometry.SingularCycles

/-- Analytic functions of finitely many holomorphic functions are holomorphic.
Source: Grauert–Remmert, Coherent Analytic Sheaves, §1.1.5; analytic composition in an atlas. -/
theorem holFun_analytic_comp {M : Type*} [TopologicalSpace M] (S : an_ReducedSpace M)
    {U : Set M} {n : ℕ} (g : U → (Fin n → ℂ))
    (hg : ∀ j, S.IsHolFun (fun y => g y j))
    (F : (Fin n → ℂ) → ℂ) (hF : ∀ y : U, AnalyticAt ℂ F (g y)) :
    S.IsHolFun (fun y => F (g y)) := by
  intro x i hxi
  choose N hNo hxN G hG heq using fun j => hg j x i hxi
  let V : Set M := ⋂ j, N j
  have hxV : (x : M) ∈ V := Set.mem_iInter.mpr hxN
  have hVo : IsOpen V := isOpen_iInter_of_finite hNo
  let H : (Fin (S.atlas.chart i).n → ℂ) → (Fin n → ℂ) := fun w j => G j w
  have hHx : H ((S.atlas.chart i).toFun x) = g x := by
    funext j
    exact (heq j x ⟨hxN j, hxi⟩).symm
  refine ⟨V, hVo, hxV, F ∘ H, (hF x).comp_of_eq (.pi hG) hHx, ?_⟩
  intro y hy
  change F (g y) = F (H ((S.atlas.chart i).toFun y))
  apply congrArg F
  funext j
  exact heq j y ⟨Set.mem_iInter.mp hy.1 j, hy.2⟩

/-- A continuous simple root of a holomorphic polynomial family is holomorphic.
Source: Gunning–Rossi, Analytic Functions of Several Complex Variables, Ch. I, §B, Theorem 4. -/
theorem holFun_of_continuous_simple_root {M : Type*} [TopologicalSpace M]
    (S : an_ReducedSpace M) {U : Set M} (hU : IsOpen U) {n : ℕ}
    (p : Polynomial (MvPolynomial (Fin n) ℂ)) (g : U → (Fin n → ℂ))
    (hg : ∀ j, S.IsHolFun (fun y => g y j)) (r : U → ℂ) (hr : Continuous r)
    (hroot : ∀ y, Polynomial.mvFamilyEquation p (g y, r y) = 0)
    (hsimple : ∀ y, (Polynomial.mvFamilySpecialization p (g y)).derivative.eval (r y) ≠ 0) :
    S.IsHolFun r := by
  intro x i hxi
  choose N hNo hxN G hG heq using fun j => hg j x i hxi
  let V : Set M := ⋂ j, N j
  have hxV : (x : M) ∈ V := Set.mem_iInter.mpr hxN
  have hVo : IsOpen V := isOpen_iInter_of_finite hNo
  let H : (Fin (S.atlas.chart i).n → ℂ) → (Fin n → ℂ) := fun w j => G j w
  let w₀ := (S.atlas.chart i).toFun x
  have hHx : H w₀ = g x := by
    funext j
    exact (heq j x ⟨hxN j, hxi⟩).symm
  let F : (Fin (S.atlas.chart i).n → ℂ) × ℂ → ℂ :=
    fun w => Polynomial.mvFamilyEquation p (H w.1, w.2)
  have hH : AnalyticAt ℂ H w₀ := .pi hG
  have hpr : AnalyticAt ℂ
      (Prod.fst : (Fin (S.atlas.chart i).n → ℂ) × ℂ → (Fin (S.atlas.chart i).n → ℂ))
      (w₀, r x) := analyticAt_fst
  have hcomp : AnalyticAt ℂ (fun w : (Fin (S.atlas.chart i).n → ℂ) × ℂ => H w.1)
      (w₀, r x) := hH.comp (f := Prod.fst) (x := (w₀, r x)) hpr
  have hprod : AnalyticAt ℂ
      (fun w : (Fin (S.atlas.chart i).n → ℂ) × ℂ => (H w.1, w.2)) (w₀, r x) :=
    hcomp.prod analyticAt_snd
  have hFa : AnalyticAt ℂ F (w₀, r x) :=
    (Polynomial.analyticAt_mvFamilyEquation p _).comp hprod
  have hFx : F (w₀, r x) = 0 := by
    change Polynomial.mvFamilyEquation p (H w₀, r x) = 0
    rw [hHx]
    exact hroot x
  have hder : fderiv ℂ F (w₀, r x) (0, 1) =
      (Polynomial.mvFamilySpecialization p (g x)).derivative.eval (r x) := by
    have h₁ := hFa.differentiableAt.hasFDerivAt.comp (r x)
      (hasFDerivAt_prodMk_right w₀ (r x))
    have h₂ : HasFDerivAt (fun t => F (w₀, t))
        ((1 : ℂ →L[ℂ] ℂ).smulRight
          ((Polynomial.mvFamilySpecialization p (g x)).derivative.eval (r x))) (r x) := by
      convert (Polynomial.hasDerivAt (Polynomial.mvFamilySpecialization p (g x)) (r x)).hasFDerivAt using 1
      · funext t
        change Polynomial.mvFamilyEquation p (H w₀, t) = _
        rw [hHx]
        rfl
      · ext t
        rfl
    have h := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) (h₁.unique h₂)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul] using h
  obtain ⟨τ, hτ, _, hτeq⟩ :=
    HodgeLean.Foundations.AnalyticDivisorAlgebraic3.spec_exists_analytic_implicit
      hFa hFx (by rw [hder]; exact hsimple x)
  have htend : Tendsto (fun y : U => ((S.atlas.chart i).toFun y, r y)) (𝓝 x)
      (𝓝 (w₀, r x)) :=
    ((anb_continuousAt_toFun (S.atlas.chart i) hxi).comp
      continuous_subtype_val.continuousAt).prodMk hr.continuousAt
  have hnear : ∀ᶠ y : U in 𝓝 x, r y = τ ((S.atlas.chart i).toFun y) := by
    have hmem : ∀ᶠ y : U in 𝓝 x, (y : M) ∈ V ∩ (S.atlas.chart i).dom :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        ((hVo.inter (S.atlas.chart i).isOpen_dom).mem_nhds ⟨hxV, hxi⟩)
    filter_upwards [htend.eventually hτeq, hmem] with y hy hyV
    have hHy : H ((S.atlas.chart i).toFun y) = g y := by
      funext j
      exact (heq j y ⟨Set.mem_iInter.mp hyV.1 j, hyV.2⟩).symm
    apply (hy.mp ?_).symm
    change Polynomial.mvFamilyEquation p (H ((S.atlas.chart i).toFun y), r y) = 0
    rw [hHy]
    exact hroot y
  obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.mp hnear
  refine ⟨Subtype.val '' W, hU.isOpenMap_subtype_val _ hWo, ⟨x, hxW, rfl⟩, τ, hτ, ?_⟩
  intro y hy
  obtain ⟨y', hy', he⟩ := hy.1
  have hyy : y' = y := Subtype.ext he
  subst y'
  exact hW y hy'

end AlgebraicGeometry.SingularCycles
