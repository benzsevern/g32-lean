import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian9
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

noncomputable section
open Set Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Adapters

private theorem bh10_irreducible_germ_of_irreducibleAt {n : ℕ} {p : Fin n → ℂ}
    {f : (Fin n → ℂ) → ℂ} (hf : AnalyticAt ℂ f p) (hi : IsIrreducibleAt f p) :
    Irreducible (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p) := by
  constructor
  · intro hu
    exact (hu.map (analyticGermAtValue n p)).ne_zero hi.1
  · intro a b hab
    obtain ⟨A, hA, ha⟩ := a.2
    obtain ⟨B, hB, hb⟩ := b.2
    have he : f =ᶠ[𝓝 p] fun z ↦ A z * B z := by
      apply Filter.Germ.coe_eq.mp
      calc
        ↑f = (⟨↑f, f, hf, rfl⟩ : AnalyticGermAt n p).1 := rfl
        _ = (a * b).1 := congrArg Subtype.val hab
        _ = a.1 * b.1 := rfl
        _ = ↑A * ↑B := congrArg₂ (· * ·) ha.symm hb.symm
        _ = ↑(fun z ↦ A z * B z) := rfl
    rcases hi.2 A B hA hB he with h | h
    · left
      apply isUnit_iff_exists_inv.mpr
      let c : AnalyticGermAt n p :=
        ⟨↑(fun z ↦ (A z)⁻¹), fun z ↦ (A z)⁻¹, hA.inv h, rfl⟩
      refine ⟨c, ?_⟩
      apply Subtype.ext
      change a.1 * c.1 = 1
      rw [← ha]
      exact Filter.Germ.coe_eq.mpr <| (hA.continuousAt.eventually_ne h).mono fun z hz ↦
        mul_inv_cancel₀ hz
    · right
      apply isUnit_iff_exists_inv.mpr
      let c : AnalyticGermAt n p :=
        ⟨↑(fun z ↦ (B z)⁻¹), fun z ↦ (B z)⁻¹, hB.inv h, rfl⟩
      refine ⟨c, ?_⟩
      apply Subtype.ext
      change b.1 * c.1 = 1
      rw [← hb]
      exact Filter.Germ.coe_eq.mpr <| (hB.continuousAt.eventually_ne h).mono fun z hz ↦
        mul_inv_cancel₀ hz

/-- No irreducible factor of a reduced equation divides all its directional derivatives.
Source: Gunning--Rossi, Analytic Functions of Several Complex Variables, Chapter II.B,
unique factorization of convergent power series; the product rule and
`bh9_irreducible_derivative_aux`. -/
theorem bh10_reduced_factor_derivative_aux (n : ℕ) (p : Fin n → ℂ)
    (f g : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hred : Squarefree (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p))
    (hi : IsIrreducibleAt g p)
    (hdiv : ∃ h : (Fin n → ℂ) → ℂ, AnalyticAt ℂ h p ∧
      f =ᶠ[𝓝 p] (fun z ↦ g z * h z)) :
    ∃ v : Fin n → ℂ, ¬ ∃ h : (Fin n → ℂ) → ℂ,
      AnalyticAt ℂ h p ∧
      (fun z ↦ fderiv ℂ f z v) =ᶠ[𝓝 p] (fun z ↦ g z * h z) := by
  obtain ⟨h, hh, hfac⟩ := hdiv
  obtain ⟨v, hvg⟩ := bh9_irreducible_derivative_aux n p g hg hi
  classical
  obtain ⟨e, -, -⟩ := spec_germ_translation_equiv n p
  letI : UniqueFactorizationMonoid (AnalyticGermAt n p) :=
    e.symm.toMulEquiv.uniqueFactorizationMonoid
      (spec_analyticGerm_ufd n)
  refine ⟨v, ?_⟩
  rintro ⟨q, hq, hqdiv⟩
  let F : AnalyticGermAt n p := ⟨↑f, f, hf, rfl⟩
  let G : AnalyticGermAt n p := ⟨↑g, g, hg, rfl⟩
  let H : AnalyticGermAt n p := ⟨↑h, h, hh, rfl⟩
  have hGi : Irreducible G := bh10_irreducible_germ_of_irreducibleAt hg hi
  have hGp : Prime G := UniqueFactorizationMonoid.irreducible_iff_prime.mp hGi
  have hFG : F = G * H := by
    apply Subtype.ext
    exact Filter.Germ.coe_eq.mpr hfac
  have hG_not_dvd_H : ¬ G ∣ H := by
    intro hGH
    apply hGi.not_isUnit (hred G ?_)
    change G * G ∣ F
    rw [hFG]
    exact mul_dvd_mul_left G hGH
  have hdf : AnalyticAt ℂ (fun z ↦ fderiv ℂ f z v) p :=
    by
      have hv := ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt
        (fderiv ℂ f p)).comp hf.fderiv
      change AnalyticAt ℂ (fun z ↦ fderiv ℂ f z v) p at hv
      exact hv
  have hdg : AnalyticAt ℂ (fun z ↦ fderiv ℂ g z v) p :=
    by
      have hv := ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt
        (fderiv ℂ g p)).comp hg.fderiv
      change AnalyticAt ℂ (fun z ↦ fderiv ℂ g z v) p at hv
      exact hv
  have hdh : AnalyticAt ℂ (fun z ↦ fderiv ℂ h z v) p :=
    by
      have hv := ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt
        (fderiv ℂ h p)).comp hh.fderiv
      change AnalyticAt ℂ (fun z ↦ fderiv ℂ h z v) p at hv
      exact hv
  let Df : AnalyticGermAt n p :=
    ⟨↑(fun z ↦ fderiv ℂ f z v), fun z ↦ fderiv ℂ f z v, hdf, rfl⟩
  let Dg : AnalyticGermAt n p :=
    ⟨↑(fun z ↦ fderiv ℂ g z v), fun z ↦ fderiv ℂ g z v, hdg, rfl⟩
  let Dh : AnalyticGermAt n p :=
    ⟨↑(fun z ↦ fderiv ℂ h z v), fun z ↦ fderiv ℂ h z v, hdh, rfl⟩
  have hG_Df : G ∣ Df := by
    refine ⟨⟨↑q, q, hq, rfl⟩, ?_⟩
    apply Subtype.ext
    exact Filter.Germ.coe_eq.mpr hqdiv
  have hderiv : Df = Dg * H + G * Dh := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hfac.fderiv (𝕜 := ℂ), hg.eventually_analyticAt,
      hh.eventually_analyticAt] with z hz hga hha
    rw [hz]
    change (fderiv ℂ (g * h) z) v = _
    rw [fderiv_mul hga.differentiableAt hha.differentiableAt]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    ring
  have hG_DgH : G ∣ Dg * H := by
    obtain ⟨R, hR⟩ := hG_Df
    refine ⟨R - Dh, ?_⟩
    rw [hderiv] at hR
    calc
      Dg * H = (Dg * H + G * Dh) - G * Dh := by abel
      _ = G * R - G * Dh := congrArg (· - G * Dh) hR
      _ = G * (R - Dh) := (mul_sub G R Dh).symm
  have hG_Dg : G ∣ Dg := (hGp.dvd_mul.mp hG_DgH).resolve_right hG_not_dvd_H
  apply hvg
  obtain ⟨Q, hQ⟩ := hG_Dg
  obtain ⟨a, ha, hQa⟩ := Q.2
  refine ⟨a, ha, ?_⟩
  apply Filter.Germ.coe_eq.mp
  calc
    ↑(fun z ↦ fderiv ℂ g z v) = Dg.1 := rfl
    _ = (G * Q).1 := congrArg Subtype.val hQ
    _ = G.1 * Q.1 := rfl
    _ = ↑g * ↑a := congrArg₂ (· * ·) rfl hQa.symm
    _ = ↑(fun z ↦ g z * a z) := rfl

/-- A regular zero admits a holomorphic coordinate chart whose last coordinate is the equation.
Source: Gunning--Rossi, Chapter I.B, the holomorphic implicit function theorem. -/
theorem bh10_equation_chart_aux (n : ℕ) (p : Fin (n + 1) → ℂ)
    (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticAt ℂ f p)
    (hp : f p = 0) (hd : fderiv ℂ f p ≠ 0) :
    ∃ e : OpenPartialHomeomorph (Fin (n + 1) → ℂ)
        ((Fin n → ℂ) × (Fin 1 → ℂ)),
      p ∈ e.source ∧ AnalyticOnNhd ℂ e e.source ∧
      AnalyticOnNhd ℂ e.symm e.target ∧
      ∀ y ∈ e.source, (e y).2 0 = f y := by
  let d := fderiv ℂ f p
  have hdx : ∃ x, d x ≠ 0 := by
    by_contra h
    push Not at h
    apply hd
    ext x
    exact h x
  obtain ⟨x, hx⟩ := hdx
  have hx0 : x ≠ 0 := fun h => hx (h ▸ map_zero d)
  let u : Fin (n + 1) → ℂ := fun i => if i = 0 then 1 else 0
  have hu : u ≠ 0 := by
    intro h
    have := congr_fun h 0
    simp [u] at this
  obtain ⟨A, hAx⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq
    (R := ℂ) (V := Fin (n + 1) → ℂ) hx0 hu
  let t : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi (fun j =>
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) j.succ).comp
        A.toContinuousLinearMap)
  let q : (Fin (n + 1) → ℂ) →L[ℂ] (Fin 1 → ℂ) :=
    ContinuousLinearMap.pi (fun _ => d)
  let L : (Fin (n + 1) → ℂ) →L[ℂ] ((Fin n → ℂ) × (Fin 1 → ℂ)) := t.prod q
  have hLinj : Function.Injective L := by
    intro y z hyz
    apply sub_eq_zero.mp
    let w := y - z
    have hLw : L w = 0 := by
      rw [map_sub, hyz, sub_self]
    have ht : ∀ j : Fin n, A w j.succ = 0 := by
      intro j
      have := congr_fun (congr_arg Prod.fst hLw) j
      exact this
    have hn : d w = 0 := by
      have := congr_fun (congr_arg Prod.snd hLw) 0
      exact this
    have hwrepr : w = (A w 0) • x := by
      apply A.injective
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hAx, u]
      · simp [hAx, u, ht j]
    have hc : A w 0 = 0 := by
      have hm : A w 0 * d x = 0 := by
        rw [← smul_eq_mul, ← map_smul, ← hwrepr, hn]
      exact (mul_eq_zero.mp hm).resolve_right hx
    show w = 0
    rw [hwrepr, hc, zero_smul]
  have hdim : Module.finrank ℂ (Fin (n + 1) → ℂ) =
      Module.finrank ℂ ((Fin n → ℂ) × (Fin 1 → ℂ)) := by simp
  have hLsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hLinj
  let Le : (Fin (n + 1) → ℂ) ≃L[ℂ] ((Fin n → ℂ) × (Fin 1 → ℂ)) :=
    ContinuousLinearEquiv.ofBijective L
      (LinearMap.ker_eq_bot.mpr hLinj) (LinearMap.range_eq_top.mpr hLsurj)
  let F : (Fin (n + 1) → ℂ) → ((Fin n → ℂ) × (Fin 1 → ℂ)) :=
    fun y => (t y, fun _ => f y)
  have hFa : AnalyticAt ℂ F p := by
    exact (t.analyticAt p).prod (AnalyticAt.pi fun _ => hf)
  have hFd : HasStrictFDerivAt F (Le : _ →L[ℂ] _) p := by
    have ht' : HasStrictFDerivAt (fun y => t y) t p := t.hasStrictFDerivAt
    have hq' : HasStrictFDerivAt (fun y => fun _ : Fin 1 => f y) q p := by
      apply hasStrictFDerivAt_pi.2
      intro i
      exact hf.hasStrictFDerivAt
    change HasStrictFDerivAt F L p
    exact ht'.prodMk hq'
  let e0 := hFd.toOpenPartialHomeomorph F
  have hp0 : p ∈ e0.source := hFd.mem_toOpenPartialHomeomorph_source
  have hinv : AnalyticAt ℂ e0.symm (F p) := by
    apply e0.analyticAt_symm' (i := Le) hp0 hFa
    exact hFd.hasFDerivAt.fderiv
  let v := {y | AnalyticAt ℂ e0.symm y}
  have hvopen : IsOpen v := isOpen_analyticAt ℂ e0.symm
  let e1 := e0.trans (OpenPartialHomeomorph.ofSet v hvopen)
  let s := {y | AnalyticAt ℂ F y}
  have hsopen : IsOpen s := isOpen_analyticAt ℂ F
  let e := e1.restrOpen s hsopen
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨hp0, hinv⟩, hFa⟩
  · intro y hy
    exact hy.2
  · intro y hy
    change AnalyticAt ℂ e0.symm y
    exact hy.1.1
  · intro y hy
    rfl

end HodgeLean.Adapters
