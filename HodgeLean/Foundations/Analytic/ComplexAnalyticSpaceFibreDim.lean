import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Finite fibres bound the dimension

Helpers prefixed `anb_`: an analytic map from an open subset of `ℂᵈ` to `ℂᵉ` all of whose fibres
are finite has `d ≤ e`. At a point of maximal rank `r`, a linear map `L` makes `L ∘ g` a
submersion onto `ℂʳ`; by the inverse function theorem its level set through the point is
parametrized by a ball of the kernel, along which `g` has zero derivative (the kernels of the
derivatives of `g` and `L ∘ g` agree by maximality of the rank). If `r < d` that ball is infinite
and lies in one fibre.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace HodgeLean.Foundations.Analytic

/-- **Finite fibres bound the dimension.** -/
theorem anb_le_of_finite_fibres {d e : ℕ} {V : Set (Fin d → ℂ)} (hV : IsOpen V)
    (hne : V.Nonempty) {g : (Fin d → ℂ) → (Fin e → ℂ)} (hg : AnalyticOnNhd ℂ g V)
    (hfin : ∀ w, {v | v ∈ V ∧ g v = w}.Finite) : d ≤ e := by
  by_contra hlt'
  have hlt : e < d := by omega
  let rk : (Fin d → ℂ) → ℕ := fun v ↦
    Module.finrank ℂ (LinearMap.range (fderiv ℂ g v : (Fin d → ℂ) →ₗ[ℂ] (Fin e → ℂ)))
  have hrk_le : ∀ v, rk v ≤ e := fun v ↦ (Submodule.finrank_le _).trans (by simp)
  have hbdd : BddAbove (rk '' V) := ⟨e, by rintro _ ⟨v, -, rfl⟩; exact hrk_le v⟩
  obtain ⟨v0, hv0, hv0r⟩ := Nat.sSup_mem (hne.image rk) hbdd
  set r := sSup (rk '' V)
  have hmax : ∀ v ∈ V, rk v ≤ r := fun v hv ↦ le_csSup hbdd ⟨v, hv, rfl⟩
  have hre : r ≤ e := hv0r ▸ hrk_le v0
  -- a linear map making `L ∘ g` a submersion at `v0`
  set D0 := fderiv ℂ g v0
  let R0 := LinearMap.range (D0 : (Fin d → ℂ) →ₗ[ℂ] (Fin e → ℂ))
  obtain ⟨prj, hprj⟩ := R0.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype R0)
  have hR0 : Module.finrank ℂ R0 = Module.finrank ℂ (Fin r → ℂ) := by
    rw [Module.finrank_fin_fun, ← hv0r]
  let eqv : R0 ≃ₗ[ℂ] (Fin r → ℂ) := LinearEquiv.ofFinrankEq _ _ hR0
  let L : (Fin e → ℂ) →L[ℂ] (Fin r → ℂ) := LinearMap.toContinuousLinearMap (eqv.toLinearMap ∘ₗ prj)
  have hLsurj : Function.Surjective (L ∘L D0) := by
    intro y
    obtain ⟨u, hu⟩ := (eqv.symm y).2
    refine ⟨u, ?_⟩
    have h1 : D0 u = R0.subtype (eqv.symm y) := hu
    rw [ContinuousLinearMap.comp_apply]
    change eqv (prj (D0 u)) = y
    rw [h1, ← LinearMap.comp_apply prj, hprj, LinearMap.id_apply, LinearEquiv.apply_symm_apply]
  -- the kernel and a projection onto it
  let K := LinearMap.ker ((L ∘L D0 : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ)) :
    (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))
  have hrange : LinearMap.range ((L ∘L D0 : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ)) :
      (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ)) = ⊤ := LinearMap.range_eq_top.2 hLsurj
  have hK : Module.finrank ℂ K + r = d := by
    have h0 := LinearMap.finrank_range_add_finrank_ker
      ((L ∘L D0 : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ)) : (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    have h1 : Module.finrank ℂ (LinearMap.range ((L ∘L D0 : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ)) :
        (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))) = r := by
      rw [hrange, finrank_top, Module.finrank_fin_fun]
    have h2 : Module.finrank ℂ (Fin d → ℂ) = d := Module.finrank_fin_fun ℂ
    have h3 : Module.finrank ℂ (LinearMap.range ((L ∘L D0 : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ)) :
        (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))) + Module.finrank ℂ K = Module.finrank ℂ (Fin d → ℂ) :=
      h0
    omega
  obtain ⟨Pr₀, hPr₀⟩ := K.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype K)
  let Pr : (Fin d → ℂ) →L[ℂ] K := LinearMap.toContinuousLinearMap Pr₀
  have hPrK : ∀ k : K, Pr k = k := fun k ↦ by
    change Pr₀ (K.subtype k) = k
    rw [← LinearMap.comp_apply, hPr₀, LinearMap.id_apply]
  -- the map `Φ = (L ∘ g, Pr)` and its derivative
  let Φ : (Fin d → ℂ) → (Fin r → ℂ) × K := fun v ↦ (L (g v), Pr v)
  have hΦa : AnalyticOnNhd ℂ Φ V := fun v hv ↦
    ((L.analyticAt _).comp (hg v hv)).prod (Pr.analyticAt v)
  have hΦd : ∀ v ∈ V, HasFDerivAt Φ ((L ∘L fderiv ℂ g v).prod Pr) v := fun v hv ↦
    (L.hasFDerivAt.comp v ((hg v hv).differentiableAt.hasFDerivAt)).prodMk Pr.hasFDerivAt
  have hdimΦ : Module.finrank ℂ (Fin d → ℂ) = Module.finrank ℂ ((Fin r → ℂ) × K) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]; omega
  have hinj0 : Function.Injective ((L ∘L D0).prod Pr) := by
    refine (injective_iff_map_eq_zero _).2 fun u hu ↦ ?_
    have h1 : (L ∘L D0) u = 0 := congrArg Prod.fst hu
    have h2 : Pr u = 0 := congrArg Prod.snd hu
    have huK : u ∈ K := h1
    have := hPrK ⟨u, huK⟩
    rw [h2] at this
    exact congrArg Subtype.val this.symm
  let e0 : (Fin d → ℂ) ≃L[ℂ] (Fin r → ℂ) × K :=
    (LinearMap.linearEquivOfInjective _ hinj0 hdimΦ).toContinuousLinearEquiv
  have he0 : ((e0 : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ) × K)) = (L ∘L D0).prod Pr := by
    exact ContinuousLinearMap.ext fun u ↦ rfl
  -- the local inverse of `Φ` at `v0`
  have hΦc : ContDiffAt ℂ ω Φ v0 := (hΦa v0 hv0).contDiffAt
  have hΦd0 : HasFDerivAt Φ (e0 : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ) × K) v0 := by
    rw [he0]; exact hΦd v0 hv0
  let T := hΦc.toOpenPartialHomeomorph Φ hΦd0 (by simp)
  have hTcoe : (T : (Fin d → ℂ) → (Fin r → ℂ) × K) = Φ := rfl
  have hv0T : v0 ∈ T.source := hΦc.mem_toOpenPartialHomeomorph_source hΦd0 (by simp)
  let Inv := range ((↑) : ((Fin d → ℂ) ≃L[ℂ] (Fin r → ℂ) × K) →
    ((Fin d → ℂ) →L[ℂ] (Fin r → ℂ) × K))
  have hInv : IsOpen Inv := ContinuousLinearEquiv.isOpen
  let U1 := (V ∩ fderiv ℂ Φ ⁻¹' Inv) ∩ T.source
  have hU1 : IsOpen U1 :=
    (hΦa.fderiv.continuousOn.isOpen_inter_preimage hV hInv).inter T.open_source
  have hv0U1 : v0 ∈ U1 := ⟨⟨hv0, ⟨e0, hΦd0.fderiv.symm⟩⟩, hv0T⟩
  let sl : K → (Fin r → ℂ) × K := fun k ↦ (L (g v0), k)
  have hsl : Continuous sl := continuous_const.prodMk continuous_id
  have hslv0 : sl (Pr v0) = Φ v0 := rfl
  have hQ : {k | sl k ∈ T.target ∧ T.symm (sl k) ∈ U1} ∈ 𝓝 (Pr v0) := by
    have h1 : T.target ∈ 𝓝 (Φ v0) := T.open_target.mem_nhds (T.map_source hv0T)
    have h2 : T.symm ⁻¹' U1 ∈ 𝓝 (Φ v0) := by
      refine (T.continuousAt_symm (T.map_source hv0T)).preimage_mem_nhds ?_
      rw [T.left_inv hv0T]
      exact hU1.mem_nhds hv0U1
    exact hsl.continuousAt.preimage_mem_nhds (hslv0 ▸ Filter.inter_mem h1 h2)
  obtain ⟨ε, hε, hεQ⟩ := Metric.mem_nhds_iff.1 hQ
  let Γ : K → (Fin d → ℂ) := fun k ↦ T.symm (sl k)
  -- along the level set, `g` has zero derivative
  have hzero : ∀ k ∈ Metric.ball (Pr v0) ε,
      HasFDerivAt (g ∘ Γ) (0 : K →L[ℂ] (Fin e → ℂ)) k := by
    intro k hk
    obtain ⟨hkT, hkU⟩ := hεQ hk
    set x := Γ k
    obtain ⟨⟨hxV, ex, hex⟩, -⟩ := hkU
    have hfdx : fderiv ℂ Φ x = (L ∘L fderiv ℂ g x).prod Pr := (hΦd x hxV).fderiv
    have hΦx : HasFDerivAt Φ (ex : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ) × K) x := by
      rw [hex]; exact (hΦd x hxV).differentiableAt.hasFDerivAt
    have hexu : ∀ u, ex u = ((L ∘L fderiv ℂ g x) u, Pr u) := fun u ↦ by
      have := congrArg (fun F : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ) × K ↦ F u) (hex.trans hfdx)
      exact this
    -- the kernels of `Dg x` and `L ∘ Dg x` agree
    let A : (Fin d → ℂ) →ₗ[ℂ] (Fin e → ℂ) := fderiv ℂ g x
    let B : (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ) := (L ∘L fderiv ℂ g x : (Fin d → ℂ) →L[ℂ] _)
    have hBsurj : LinearMap.range B = ⊤ := by
      refine LinearMap.range_eq_top.2 fun y ↦ ⟨ex.symm (y, 0), ?_⟩
      have := hexu (ex.symm (y, 0))
      rw [ContinuousLinearEquiv.apply_symm_apply] at this
      exact (congrArg Prod.fst this).symm
    have hBA : B = (L : (Fin e → ℂ) →ₗ[ℂ] (Fin r → ℂ)) ∘ₗ A := rfl
    have hrB : Module.finrank ℂ (LinearMap.range B) = r := by
      rw [hBsurj, finrank_top, Module.finrank_fin_fun]
    have hrA : Module.finrank ℂ (LinearMap.range A) = r := by
      refine le_antisymm (hmax x hxV) ?_
      rw [← hrB, hBA, LinearMap.range_comp]
      exact Submodule.finrank_map_le _ _
    have hker : LinearMap.ker A = LinearMap.ker B := by
      refine Submodule.eq_of_le_of_finrank_eq (hBA ▸ LinearMap.ker_le_ker_comp A _) ?_
      have h1 := LinearMap.finrank_range_add_finrank_ker A
      have h2 := LinearMap.finrank_range_add_finrank_ker B
      omega
    -- the derivative of `Γ` and of `g ∘ Γ`
    have hsld : HasFDerivAt sl ((0 : K →L[ℂ] (Fin r → ℂ)).prod (ContinuousLinearMap.id ℂ K)) k :=
      (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
    have hΓd : HasFDerivAt Γ ((ex.symm : (Fin r → ℂ) × K →L[ℂ] (Fin d → ℂ)) ∘L
        ((0 : K →L[ℂ] (Fin r → ℂ)).prod (ContinuousLinearMap.id ℂ K))) k :=
      (T.hasFDerivAt_symm hkT hΦx).comp k hsld
    have hgΓ := ((hg x hxV).differentiableAt.hasFDerivAt).comp k hΓd
    convert hgΓ using 1
    ext1 κ
    simp only [zero_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply]
    set u := ex.symm (0, κ)
    have hu := hexu u
    rw [ContinuousLinearEquiv.apply_symm_apply] at hu
    have huB : u ∈ LinearMap.ker B := (congrArg Prod.fst hu).symm
    rw [← hker] at huB
    exact huB.symm
  -- hence `g` is constant along the level set
  have hΓ0 : Γ (Pr v0) = v0 := T.left_inv hv0T
  have hconst : ∀ k ∈ Metric.ball (Pr v0) ε, g (Γ k) = g v0 := by
    intro k hk
    rw [← hΓ0]
    refine (convex_ball (Pr v0) ε).is_const_of_fderivWithin_eq_zero
      (fun k' hk' ↦ (hzero k' hk').differentiableAt.differentiableWithinAt) (fun k' hk' ↦ ?_)
      hk (Metric.mem_ball_self hε)
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hk']
    exact (hzero k' hk').fderiv
  -- the ball is infinite and `Γ` is injective on it
  have hKpos : 0 < Module.finrank ℂ K := by omega
  obtain ⟨k1, hk1⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hKpos
  have hk1n : 0 < ‖k1‖ := norm_pos_iff.2 hk1
  let c : ℕ → ℝ := fun m ↦ ε / (2 * ‖k1‖ * (m + 1))
  let f : ℕ → K := fun m ↦ Pr v0 + ((c m : ℝ) : ℂ) • k1
  have hfball : ∀ m, f m ∈ Metric.ball (Pr v0) ε := by
    intro m
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [f, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hc : 0 < c m := by positivity
    rw [abs_of_pos hc]
    calc c m * ‖k1‖ = ε / (2 * (m + 1)) := by
          simp only [c]; field_simp
      _ < ε := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hfinj : Function.Injective (Γ ∘ f) := by
    intro m m' hmm'
    have h1 : sl (f m) = sl (f m') :=
      T.symm.injOn (hεQ (hfball m)).1 (hεQ (hfball m')).1 hmm'
    have h2 : ((c m : ℝ) : ℂ) • k1 = ((c m' : ℝ) : ℂ) • k1 := by
      have := congrArg Prod.snd h1
      simpa [sl, f] using this
    have h3 : ((c m : ℝ) : ℂ) = ((c m' : ℝ) : ℂ) := smul_left_injective ℂ hk1 h2
    have h4 : c m = c m' := Complex.ofReal_injective h3
    simp only [c] at h4
    have : (2 * ‖k1‖ * (m + 1) : ℝ) = 2 * ‖k1‖ * (m' + 1) := by
      field_simp at h4
      nlinarith [h4]
    have : (m : ℝ) = m' := by nlinarith [this]
    exact_mod_cast this
  refine (Set.infinite_of_injective_forall_mem hfinj fun m ↦ ?_) (hfin (g v0))
  exact ⟨(hεQ (hfball m)).2.1.1, hconst _ (hfball m)⟩

end HodgeLean.Foundations.Analytic
