import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cReparam

noncomputable section

namespace HodgeLean.Foundations.Program

open scoped Polynomial

theorem b6m_affine_circle_times_finite (a v c : ℂ) (r : ℝ) (hv : v ≠ 0) :
    {s : ℝ | dist (a + s • v) c = r}.Finite := by
  let P : ℝ[X] := Polynomial.C (Complex.normSq v) * Polynomial.X ^ 2 +
    Polynomial.C (2 * ((a - c).re * v.re + (a - c).im * v.im)) * Polynomial.X +
    Polynomial.C (Complex.normSq (a - c) - r ^ 2)
  have hP : P ≠ 0 := by
    intro h
    have H := congrArg (fun Q : ℝ[X] ↦ Q.coeff 2) h
    norm_num only [P, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
      Polynomial.coeff_zero] at H
    exact hv (Complex.normSq_eq_zero.mp (by simpa using H))
  apply (Polynomial.finite_setOfPred_isRoot hP).subset
  intro s hs
  change P.eval s = 0
  have H : Complex.normSq (a + s • v - c) = r ^ 2 := by
    rw [← Complex.sq_norm, ← dist_eq_norm, hs]
  simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add] at H ⊢
  nlinarith [H]

theorem b6m_affine_tent_times_finite (b : Fin 10 → ℂ) (a v : ℂ) (hv : v ≠ 0) :
    {s : ℝ | s ∈ Set.Icc 0 1 ∧ ∃ i,
      a + s • v = b i ∨ dist (a + s • v) (b i) = b6t_radius b}.Finite := by
  have hc (i : Fin 10) : {s : ℝ | a + s • v = b i}.Finite := by
    simpa only [dist_eq_zero] using b6m_affine_circle_times_finite a v (b i) 0 hv
  have h : (⋃ i : Fin 10, {s : ℝ | a + s • v = b i} ∪
      {s : ℝ | dist (a + s • v) (b i) = b6t_radius b}).Finite :=
    Set.finite_iUnion fun i ↦ (hc i).union
      (b6m_affine_circle_times_finite a v (b i) (b6t_radius b) hv)
  apply h.subset
  intro s hs
  obtain ⟨i, hi⟩ := hs.2
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

theorem b6m_segment_tent_exceptional_finite (b : Fin 10 → ℂ) (a v : ℂ) :
    {z : ℂ | z ∈ segment ℝ a (a + v) ∧
      ∃ i, z = b i ∨ dist z (b i) = b6t_radius b}.Finite := by
  by_cases hv : v = 0
  · subst v
    apply (Set.finite_singleton a).subset
    intro z hz
    simpa using hz.1
  apply ((b6m_affine_tent_times_finite b a v hv).image (fun s : ℝ ↦ a + s • v)).subset
  intro z hz
  have hseg := hz.1
  rw [segment_eq_image'] at hseg
  obtain ⟨s, hs, he⟩ := hseg
  have he' : a + s • v = z := by simpa using he
  exact ⟨s, ⟨hs, by rw [he']; exact hz.2⟩, he'⟩

theorem b6m_lifted_segment_exceptional_finite {X : Type*}
    (b : Fin 10 → ℂ) (a v : ℂ) (f : X → OnePoint ℂ) (ι : ℂ → X) (γ : ℝ → X)
    (hproj : ∀ z ∈ segment ℝ a (a + v), f (ι z) = (z : OnePoint ℂ))
    (hrange : ∀ s, γ s ∈ ι '' segment ℝ a (a + v)) :
    {x : X | x ∈ Set.range γ ∧ ¬∃ z : ℂ, (z : OnePoint ℂ) = f x ∧
      ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b}.Finite := by
  classical
  apply ((b6m_segment_tent_exceptional_finite b a v).image ι).subset
  rintro x ⟨⟨s, rfl⟩, hx⟩
  obtain ⟨z, hz, hzs⟩ := hrange s
  refine ⟨z, ⟨hz, ?_⟩, hzs⟩
  by_contra hbad
  push_neg at hbad
  apply hx
  refine ⟨z, ?_, hbad⟩
  rw [← hzs, hproj z hz]

open Filter
open scoped Topology

theorem b6m_orient_positive_real_smul (v w : ℂ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    SignType.sign (b3_orient ℂ (a • v) (c • w)) = SignType.sign (b3_orient ℂ v w) := by
  obtain ⟨κ, _, hκ⟩ := b6m_orient_complex_coordinates
  have H : b3_orient ℂ (a • v) (c • w) = (a * c) * b3_orient ℂ v w := by
    rw [hκ, hκ]
    simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [H, sign_mul, sign_pos (mul_pos ha hc), one_mul]

theorem b6m_plane_good_segment (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart) (a v : ℂ) :
    ∃ γ : ℝ → ℂ, b3A_IsGoodPath (E := ℂ) γ a (a + v) ∧
      b3A_IsGoodPath (E := ℂ) (b6t_plane b t ∘ γ)
        (b6t_plane b t a) (b6t_plane b t (a + v)) ∧
      (∀ s, γ s ∈ segment ℝ a (a + v)) ∧
      (∀ s, γ s ≠ a → γ s ≠ a + v →
        (∀ i, γ s ≠ b i ∧ dist (γ s) (b i) ≠ b6t_radius b) →
        ∃ d : ℝ, 0 < d ∧ deriv γ s = d • v) := by
  by_cases hv : v = 0
  · subst v
    refine ⟨fun _ ↦ a, ?_, ?_, ?_, ?_⟩
    · simpa using b3A_isGoodPath_const (E := ℂ) a
    · simpa [Function.comp_def] using b3A_isGoodPath_const (E := ℂ) (b6t_plane b t a)
    · simp
    · intro s hs
      exact (hs rfl).elim
  let p : ℝ → ℂ := fun s ↦ a + s • v
  have hp : ContDiff ℝ 1 p := contDiff_const.add (contDiff_id.smul contDiff_const)
  obtain ⟨σ, hd, hr, h0, h1, htrans, hpos⟩ := b6m_plane_finite_reparam b t hb p hp
    (b6m_affine_tent_times_finite b a v hv)
  have hg0 : ∀ᶠ s in 𝓝 0, (p ∘ σ) s = a := by
    filter_upwards [h0] with s hs
    simp [Function.comp_apply, p, hs]
  have hg1 : ∀ᶠ s in 𝓝 1, (p ∘ σ) s = a + v := by
    filter_upwards [h1] with s hs
    simp [Function.comp_apply, p, hs]
  refine ⟨p ∘ σ, ⟨(hp.comp hd).contMDiff, hg0, hg1⟩,
    ⟨htrans.contMDiff, hg0.mono (fun s hs ↦ congrArg (b6t_plane b t) hs),
      hg1.mono (fun s hs ↦ congrArg (b6t_plane b t) hs)⟩, ?_, ?_⟩
  · intro s
    rw [segment_eq_image']
    exact ⟨σ s, hr s, by simp [p]⟩
  · intro s hs0 hs1 hreg
    have hσ0 : σ s ≠ 0 := by intro h; apply hs0; simp [p, h]
    have hσ1 : σ s ≠ 1 := by intro h; apply hs1; simp [p, h]
    refine ⟨deriv σ s, hpos s ⟨lt_of_le_of_ne (hr s).1 (Ne.symm hσ0),
      lt_of_le_of_ne (hr s).2 hσ1⟩ hreg, ?_⟩
    have H := ((hd.differentiable one_ne_zero s).hasDerivAt.smul_const v).const_add a
    exact H.deriv

theorem b6m_plane_good_segment_pair (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (ht : t ∈ b6t_polydisc b) (a v c w : ℂ) :
    ∃ γ δ : ℝ → ℂ,
      b3A_IsGoodPath (E := ℂ) γ a (a + v) ∧
      b3A_IsGoodPath (E := ℂ) δ c (c + w) ∧
      b3A_IsGoodPath (E := ℂ) (b6t_plane b t ∘ γ)
        (b6t_plane b t a) (b6t_plane b t (a + v)) ∧
      b3A_IsGoodPath (E := ℂ) (b6t_plane b t ∘ δ)
        (b6t_plane b t c) (b6t_plane b t (c + w)) ∧
      (∀ s, γ s ∈ segment ℝ a (a + v)) ∧
      (∀ s, δ s ∈ segment ℝ c (c + w)) ∧
      (∀ s u, γ s = δ u → γ s ≠ a → γ s ≠ a + v → δ u ≠ c → δ u ≠ c + w →
        (∀ i, γ s ≠ b i ∧ dist (γ s) (b i) ≠ b6t_radius b) →
        SignType.sign (b3_orient ℂ (deriv γ s) (deriv δ u)) =
          SignType.sign (b3_orient ℂ v w) ∧
        SignType.sign (b3_orient ℂ (deriv (b6t_plane b t ∘ γ) s)
          (deriv (b6t_plane b t ∘ δ) u)) = SignType.sign (b3_orient ℂ v w)) := by
  obtain ⟨γ, hγ, hγt, hγr, hγv⟩ := b6m_plane_good_segment b t hb a v
  obtain ⟨δ, hδ, hδt, hδr, hδv⟩ := b6m_plane_good_segment b t hb c w
  refine ⟨γ, δ, hγ, hδ, hγt, hδt, hγr, hδr, ?_⟩
  intro s u he hs0 hs1 hu0 hu1 hreg
  obtain ⟨d, hd, hdγ⟩ := hγv s hs0 hs1 hreg
  obtain ⟨r, hr, hrδ⟩ := hδv u hu0 hu1 (by simpa [← he] using hreg)
  have hor : SignType.sign (b3_orient ℂ (deriv γ s) (deriv δ u)) =
      SignType.sign (b3_orient ℂ v w) := by
    rw [hdγ, hrδ]
    exact b6m_orient_positive_real_smul v w hd hr
  refine ⟨hor, ?_⟩
  obtain ⟨hf, hfo⟩ := b6m_plane_regular_orientation b t hb ht (γ s) hreg
  have hγd := hγ.1.contDiff.differentiable one_ne_zero s
  have hδd := hδ.1.contDiff.differentiable one_ne_zero u
  have Hγ := (hf.hasFDerivAt.comp_hasDerivAt s hγd.hasDerivAt).deriv
  have hfδ : DifferentiableAt ℝ (b6t_plane b t) (δ u) := he ▸ hf
  have Hδ := (hfδ.hasFDerivAt.comp_hasDerivAt u hδd.hasDerivAt).deriv
  rw [Hγ, Hδ, ← he, hfo]
  exact hor

open Manifold
open scoped Manifold ContDiff
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6m_filling_good_segment {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (a v : ℂ) (ι : ℂ → C)
    (hi : ∀ z ∈ segment ℝ a (a + v), ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω ι z)
    (hproj : ∀ z ∈ segment ℝ a (a + v), f (ι z) = (z : OnePoint ℂ))
    (hkd : ∀ z ∈ segment ℝ a (a + v), mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k (e (ι z)) ≠ 0) :
    ∃ γ : ℝ → C, b3A_IsGoodPath (E := ℂ) γ (ι a) (ι (a + v)) ∧
      b3A_IsGoodPath (E := ℂ) (e ∘ γ) (e (ι a)) (e (ι (a + v))) ∧
      (∀ s, γ s ∈ ι '' segment ℝ a (a + v)) ∧
      (Set.range γ \ {x | ∃ z : ℂ, (z : OnePoint ℂ) = f x ∧
        ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b}).Finite := by
  obtain ⟨θ, hθ, htrans, hr, _⟩ := b6m_plane_good_segment b t hb a v
  have hg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (ι ∘ θ) := by
    intro s
    have H : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 ι (θ s) :=
      (b3A_contMDiffWithinAt_real (hi (θ s) (hr s))).of_le le_top
    exact H.comp s (hθ.1 s)
  have H := b3A_contMDiff_comp_real (fun z : ℂ ↦ (z : OnePoint ℂ))
    b4cov_coe_contMDiff (b6t_plane b t ∘ θ) htrans.1
  have hcomp : k ∘ (e ∘ (ι ∘ θ)) =
      (fun z : ℂ ↦ (z : OnePoint ℂ)) ∘ (b6t_plane b t ∘ θ) := by
    funext s
    change k (e (ι (θ s))) = (b6t_plane b t (θ s) : OnePoint ℂ)
    rw [he, hproj (θ s) (hr s)]
    rfl
  have hge : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (e ∘ (ι ∘ θ)) := by
    intro s
    apply b6m_contMDiffAt_path_of_unramified_comp _ k s
      (e.continuous.comp hg.continuous).continuousAt hk (hkd (θ s) (hr s))
    rw [hcomp]
    exact H s
  have hrange : ∀ s, (ι ∘ θ) s ∈ ι '' segment ℝ a (a + v) :=
    fun s ↦ ⟨θ s, hr s, rfl⟩
  refine ⟨ι ∘ θ, ⟨hg, hθ.2.1.mono (fun s hs ↦ congrArg ι hs),
    hθ.2.2.mono (fun s hs ↦ congrArg ι hs)⟩,
    ⟨hge, hθ.2.1.mono (fun s hs ↦ congrArg (e ∘ ι) hs),
      hθ.2.2.mono (fun s hs ↦ congrArg (e ∘ ι) hs)⟩, hrange,
    b6m_lifted_segment_exceptional_finite b a v f ι (ι ∘ θ) hproj hrange⟩

end HodgeLean.Foundations.Program
