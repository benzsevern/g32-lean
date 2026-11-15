import HodgeLean.Foundations.Program.CurveJacobianUnimodLevel
import HodgeLean.Foundations.Program.CurveJacobianRest2Shift

/-! # Track B3, lane Unimod: intersection numbers with vertical loops

* `b3Unimod_sign_orient`: where a path `Γ` with `θ(Γ, Γ') = -i T` (`T > 0`) meets a path `δ`,
  the orientation of `(Γ', δ')` has the sign of `Re θ(δ, δ')`: in the chart coordinate,
  `Γ' = -i T / g` and `δ' = θ(δ, δ') / g` for the coefficient `g` of `θ`, and
  `Im (conj (-i T / g) · X / g) = T Re X / |g|²`;
* `b3Unimod_loop`: a vertical curve of period `T`, run at speed `T`, is a `C¹` loop;
* `b3Unimod_sum_intersection`: for finitely many such loops with disjoint orbits covering a set
  `L`, and a loop `δ` with `Re θ(δ, δ') ≠ 0` wherever `δ` meets `L`, the loops are transverse to
  `δ` and their intersection numbers with `δ` add up to the signed count of the (finitely many) parameters
  `t ∈ [0, 1)` with `δ t ∈ L`, with the signs of `Re θ(δ, δ')`.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ComplexConjugate
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  {hE : Module.finrank ℂ E = 1} {θ : b3_HolForm E C}

/-- **The sign of a crossing with a vertical path.** -/
theorem b3Unimod_sign_orient (Fl : b3Unimod_Flat hE θ) {Γ δ : ℝ → C}
    (hΓ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 Γ) (hδ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 δ) {s t : ℝ}
    (heq : Γ s = δ t) (hsrc : Γ s ∈ Fl.F.source) {T : ℝ} (hT : 0 < T)
    (hΓθ : θ.1 ⟨Γ s, b3_velocity E C Γ s⟩ = -Complex.I * T) :
    SignType.sign (b3_orient E (b3_velocity E C Γ s) (b3_velocity E C δ t)) =
      SignType.sign ((θ.1 ⟨δ t, b3_velocity E C δ t⟩).re) := by
  set q := Fl.q
  have hq : Γ s ∈ (chartAt E q).source := Fl.source_sub hsrc
  rw [← b3Rest2_sign_orient hE hΓ hδ heq hq, b3Unimod_L_symm, b3Unimod_L_symm]
  set κ := b3Unimod_κ hE
  set u := b3Rest_e hE
  set A := κ (deriv (chartAt E q ∘ Γ) s)
  set B := κ (deriv (chartAt E q ∘ δ) t)
  set g := b3A_coef θ.1 q u (Γ s)
  have hg : g ≠ 0 := Fl.coef_ne _ hsrc
  have hA : θ.1 ⟨Γ s, b3_velocity E C Γ s⟩ = A * g :=
    b3Unimod_integrand_chart θ.2 κ u (b3Unimod_κ_spec hE) Γ q s (hΓ s) hq
  have hB : θ.1 ⟨δ t, b3_velocity E C δ t⟩ = B * g := by
    have := b3Unimod_integrand_chart θ.2 κ u (b3Unimod_κ_spec hE) δ q t (hδ t) (heq ▸ hq)
    rw [this, ← heq]
  set X := θ.1 ⟨δ t, b3_velocity E C δ t⟩
  have hkey : conj A * B * (Complex.normSq g : ℂ) = Complex.I * T * X := by
    have h1 : conj A * B * (Complex.normSq g : ℂ) = conj (A * g) * (B * g) := by
      rw [Complex.normSq_eq_conj_mul_self, map_mul]
      ring
    rw [h1, ← hA, ← hB, hΓθ]
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    ring
  have him : (conj A * B).im * Complex.normSq g = T * X.re := by
    have := congrArg Complex.im hkey
    simpa [Complex.mul_im] using this
  have hpos : 0 < Complex.normSq g := Complex.normSq_pos.2 hg
  rw [← b3Rest2_sign_pos_mul hpos, mul_comm, him, b3Rest2_sign_pos_mul hT]

/-- **The loop of a periodic vertical curve**, `u ↦ τ (T u)`. -/
def b3Unimod_loop {τ : ℝ → C} (hτ : b3Unimod_Vertical hE θ τ) {T : ℝ}
    (hper : Function.Periodic τ T) : b3_SmoothLoop E C :=
  ⟨fun u ↦ τ (T * u), fun u ↦ by simp only [mul_add, mul_one, hper (T * u)],
    hτ.contMDiff.comp (contDiff_const.mul contDiff_id).contMDiff⟩

theorem b3Unimod_loop_apply {τ : ℝ → C} (hτ : b3Unimod_Vertical hE θ τ) {T : ℝ}
    (hper : Function.Periodic τ T) (u : ℝ) : (b3Unimod_loop hτ hper).1 u = τ (T * u) := rfl

/-- `θ(Γ, Γ') = -i T` along the loop of a vertical curve. -/
theorem b3Unimod_loop_integrand {τ : ℝ → C} (hτ : b3Unimod_Vertical hE θ τ) {T : ℝ}
    (hper : Function.Periodic τ T) (u : ℝ) :
    θ.1 ⟨(b3Unimod_loop hτ hper).1 u, b3_velocity E C (b3Unimod_loop hτ hper).1 u⟩ =
      -Complex.I * T := by
  have hv := b3A_velocity_reparam τ hτ.contMDiff (fun u ↦ T * u)
    (differentiable_const _ |>.mul differentiable_id) u
  have hd : deriv (fun u : ℝ ↦ T * u) u = T := by simp
  rw [hd] at hv
  show θ.1 ⟨τ (T * u), b3A_vel (E := E) (τ ∘ fun u ↦ T * u) u⟩ = _
  rw [hv]
  have h := b3A_holForm_smul_apply θ.2 (τ (T * u)) (T : ℂ) (b3A_vel (E := E) τ (T * u))
  refine h.trans ?_
  have h2 := hτ.integrand (T * u)
  change θ.1 ⟨τ (T * u), b3A_vel (E := E) τ (T * u)⟩ = -Complex.I at h2
  rw [h2]
  ring

/-- **Vertical loops against a loop crossing their union regularly.** -/
theorem b3Unimod_sum_intersection [T2Space C] {ι : Type} [Fintype ι] {τ : ι → ℝ → C}
    (hτ : ∀ i, b3Unimod_Vertical hE θ (τ i)) {T : ι → ℝ} (hT : ∀ i, 0 < T i)
    (hper : ∀ i, Function.Periodic (τ i) (T i))
    (hinj : ∀ i, ∀ s₁ ∈ Ico (0 : ℝ) (T i), ∀ s₂ ∈ Ico (0 : ℝ) (T i), τ i s₁ = τ i s₂ → s₁ = s₂)
    (hdisj : Pairwise fun i j ↦ Disjoint (range (τ i)) (range (τ j))) {L : Set C}
    (hcover : ⋃ i, range (τ i) = L) (δ : b3_SmoothLoop E C)
    (htr : ∀ t, δ.1 t ∈ L → (θ.1 ⟨δ.1 t, b3_velocity E C δ.1 t⟩).re ≠ 0) :
    (∀ i, b3_Transverse E (b3Unimod_loop (hτ i) (hper i)) δ) ∧
      {t | t ∈ Ico (0 : ℝ) 1 ∧ δ.1 t ∈ L}.Finite ∧
      ∑ i, b3_intersection E (b3Unimod_loop (hτ i) (hper i)) δ =
        ∑ᶠ t ∈ {t | t ∈ Ico (0 : ℝ) 1 ∧ δ.1 t ∈ L},
          ((SignType.sign (θ.1 ⟨δ.1 t, b3_velocity E C δ.1 t⟩).re : SignType) : ℤ) := by
  set Γ := fun i ↦ b3Unimod_loop (hτ i) (hper i)
  set σ : ℝ → ℤ := fun t ↦
    ((SignType.sign (θ.1 ⟨δ.1 t, b3_velocity E C δ.1 t⟩).re : SignType) : ℤ)
  have hinL : ∀ i s, (Γ i).1 s ∈ L := fun i s ↦
    hcover ▸ mem_iUnion.2 ⟨i, T i * s, rfl⟩
  have hsign : ∀ i s t, (Γ i).1 s = δ.1 t →
      SignType.sign (b3_orient E (b3_velocity E C (Γ i).1 s) (b3_velocity E C δ.1 t)) =
        SignType.sign (θ.1 ⟨δ.1 t, b3_velocity E C δ.1 t⟩).re := by
    intro i s t heq
    obtain ⟨Fl, hFl, -⟩ := hτ i (T i * s)
    exact b3Unimod_sign_orient Fl (Γ i).2.2 δ.2.2 heq hFl (hT i)
      (b3Unimod_loop_integrand (hτ i) (hper i) s)
  have htrans : ∀ i, b3_Transverse E (Γ i) δ := by
    intro i s t heq h0
    have h := hsign i s t heq
    rw [h0, sign_zero, eq_comm, sign_eq_zero_iff] at h
    exact htr t (heq ▸ hinL i s) h
  refine ⟨htrans, ?_⟩
  suffices h : {t | t ∈ Ico (0 : ℝ) 1 ∧ δ.1 t ∈ L}.Finite ∧
      ∑ i, b3_intersection E (Γ i) δ = ∑ᶠ t ∈ {t | t ∈ Ico (0 : ℝ) 1 ∧ δ.1 t ∈ L}, σ t from h
  set Ti : ι → Set ℝ := fun i ↦ {t | t ∈ Ico (0 : ℝ) 1 ∧ δ.1 t ∈ range (τ i)}
  have hbij : ∀ i, BijOn Prod.snd (b3_crossings E (Γ i) δ) (Ti i) := by
    intro i
    refine ⟨fun p hp ↦ ⟨hp.2.1, T i * p.1, hp.2.2⟩, fun p hp p' hp' h ↦ ?_, fun t ht ↦ ?_⟩
    · have hmem : ∀ x ∈ Ico (0 : ℝ) 1, T i * x ∈ Ico (0 : ℝ) (T i) := fun x hx ↦
        ⟨mul_nonneg (hT i).le hx.1, mul_lt_of_lt_one_right (hT i) hx.2⟩
      have he : τ i (T i * p.1) = τ i (T i * p'.1) := by
        have h1 : τ i (T i * p.1) = δ.1 p.2 := hp.2.2
        have h2 : τ i (T i * p'.1) = δ.1 p'.2 := hp'.2.2
        rw [h1, h2, h]
      have := hinj i _ (hmem _ hp.1) _ (hmem _ hp'.1) he
      exact Prod.ext (mul_left_cancel₀ (hT i).ne' this) h
    · obtain ⟨htI, x, hx⟩ := ht
      refine ⟨(Int.fract (x / T i), t), ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, htI, ?_⟩, rfl⟩
      show τ i (T i * Int.fract (x / T i)) = δ.1 t
      rw [← hx, Int.fract, mul_sub, mul_div_cancel₀ _ (hT i).ne', mul_comm]
      exact (hper i).sub_int_mul_eq _
  have hfin : ∀ i, (Ti i).Finite := fun i ↦
    (hbij i).image_eq ▸ (b3A_crossings_finite (Γ i) δ (htrans i)).image _
  have hcount : ∀ i, b3_intersection E (Γ i) δ = ∑ᶠ t ∈ Ti i, σ t := by
    intro i
    unfold b3_intersection
    rw [finsum_mem_congr rfl fun p hp ↦ by rw [hsign i p.1 p.2 hp.2.2]]
    exact finsum_mem_eq_of_bijOn Prod.snd (hbij i) fun p _ ↦ rfl
  have hdisjT : Pairwise (Function.onFun Disjoint Ti) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro t hti htj
    exact Set.disjoint_left.1 (hdisj hij) hti.2 htj.2
  have hunion : ⋃ i, Ti i = {t | t ∈ Ico (0 : ℝ) 1 ∧ δ.1 t ∈ L} := by
    ext t
    simp only [Ti, mem_iUnion, mem_ofPred_eq, ← hcover]
    constructor
    · rintro ⟨i, h1, h2⟩; exact ⟨h1, i, h2⟩
    · rintro ⟨h1, i, h2⟩
      exact ⟨i, h1, h2⟩
  refine ⟨hunion ▸ Set.finite_iUnion hfin, ?_⟩
  rw [← hunion, finsum_mem_iUnion hdisjT hfin, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun i _ ↦ hcount i

end HodgeLean.Foundations.Program
