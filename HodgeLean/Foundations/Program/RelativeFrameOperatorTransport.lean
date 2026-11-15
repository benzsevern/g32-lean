import HodgeLean.Foundations.Program.RelativeFrameOperatorObstruction

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem rf4_atlas_transition_analytic {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (a b : OpenPartialHomeomorph X ℂ)
    (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (hb : b ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (z : ℂ) (hz : z ∈ a.target) (hp : a.symm z ∈ b.source) :
    AnalyticAt ℂ (b ∘ a.symm) z := by
  exact ((contMDiffAt_of_mem_maximalAtlas hb hp).comp z
    (contMDiffAt_symm_of_mem_maximalAtlas ha hz)).contDiffAt.analyticAt

theorem rf4_atlas_transition_deriv {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (a b c : OpenPartialHomeomorph X ℂ)
    (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (hb : b ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (z : ℂ) (hz : z ∈ a.target) (hpb : a.symm z ∈ b.source)
    (hpc : a.symm z ∈ c.source) :
    deriv (c ∘ a.symm) z =
      deriv (c ∘ b.symm) (b (a.symm z)) * deriv (b ∘ a.symm) z := by
  have hab := rf4_atlas_transition_analytic a b ha hb z hz hpb
  have hbc := rf4_atlas_transition_analytic b c hb hc (b (a.symm z))
    (b.map_source hpb) (by simpa only [b.left_inv hpb] using hpc)
  have he : c ∘ a.symm =ᶠ[𝓝 z] (c ∘ b.symm) ∘ (b ∘ a.symm) := by
    filter_upwards [(a.isOpen_inter_preimage_symm b.open_source).mem_nhds
      (show z ∈ a.target ∩ a.symm ⁻¹' b.source from ⟨hz, hpb⟩)] with u hu
    simp only [Function.comp_apply, b.left_inv hu.2]
  rw [he.deriv_eq]
  exact (hbc.differentiableAt.hasDerivAt.comp z hab.differentiableAt.hasDerivAt).deriv

def rf4_chartTensor {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (f : ℂ → ℂ) (p q : ℕ) : rf2_Coeff X := by
  classical
  exact fun x z ↦ if (chartAt ℂ x).symm z ∈ e.source then
    f (e ((chartAt ℂ x).symm z)) * deriv (e ∘ (chartAt ℂ x).symm) z ^ p *
      star (deriv (e ∘ (chartAt ℂ x).symm) z) ^ q else 0

theorem rf4_chartTensor_smooth {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ e.target) (p q : ℕ) (x : X) :
    ∃ g : ℂ → ℂ, ContDiffOn ℝ ∞ g (chartAt ℂ x).target ∧
      ∀ z, rf4_chartTensor e f p q x z = g z := by
  classical
  let a := chartAt ℂ x
  let g : ℂ → ℂ := fun z ↦ if a.symm z ∈ e.source then
    f (e (a.symm z)) * deriv (e ∘ a.symm) z ^ p *
      star (deriv (e ∘ a.symm) z) ^ q else 0
  refine ⟨g, ?_, fun _ ↦ rfl⟩
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  by_cases hp : a.symm z ∈ e.source
  · have ht := rf4_atlas_transition_analytic a e (IsManifold.chart_mem_maximalAtlas x) he z hz hp
    have hlocal : ContDiffAt ℝ ∞ (fun u ↦ f (e (a.symm u)) *
        deriv (e ∘ a.symm) u ^ p * star (deriv (e ∘ a.symm) u) ^ q) z :=
      ((hf.contDiffAt.comp z (ht.contDiffAt.restrict_scalars ℝ)).mul
        ((ht.deriv.contDiffAt.restrict_scalars ℝ).pow p)).mul
        ((Complex.conjCLE.contDiff.contDiffAt.comp z
          (ht.deriv.contDiffAt.restrict_scalars ℝ)).pow q)
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [(a.isOpen_inter_preimage_symm e.open_source).mem_nhds
      (show z ∈ a.target ∩ a.symm ⁻¹' e.source from ⟨hz, hp⟩)] with u hu
    exact if_pos hu.2
  · let K := e.symm '' tsupport f
    have hK : IsCompact K := hc.image_of_continuousOn (e.continuousOn_symm.mono hs)
    have hzK : a.symm z ∉ K := by
      rintro ⟨u, hu, heu⟩
      exact hp (heu ▸ e.map_target (hs hu))
    have hN := a.isOpen_inter_preimage_symm hK.isClosed.isOpen_compl
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hN.mem_nhds
      (show z ∈ a.target ∩ a.symm ⁻¹' Kᶜ from ⟨hz, hzK⟩)] with u hu
    dsimp [g]
    split_ifs with heU
    · have hfu : f (e (a.symm u)) = 0 := by
        by_contra hne
        have hts : e (a.symm u) ∈ tsupport f := subset_closure hne
        exact hu.2 ⟨e (a.symm u), hts, e.left_inv heU⟩
      rw [hfu, zero_mul, zero_mul]
    · rfl

theorem rf4_chartTensor_transition {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (f : ℂ → ℂ) (p q : ℕ) (x y : X)
    (z : (chartAt ℂ x).target) (w : (chartAt ℂ y).target)
    (hzw : (chartAt ℂ x).symm z = (chartAt ℂ y).symm w) :
    rf4_chartTensor e f p q x z = rf4_chartTensor e f p q y w *
      deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) z ^ p *
      star (deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) z) ^ q := by
  classical
  by_cases hp : (chartAt ℂ x).symm z ∈ e.source
  · have hp' : (chartAt ℂ y).symm w ∈ e.source := hzw ▸ hp
    have hb : (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source := by
      rw [hzw]
      exact (chartAt ℂ y).map_target w.property
    have hw : chartAt ℂ y ((chartAt ℂ x).symm z) = w := by
      rw [hzw, (chartAt ℂ y).right_inv w.property]
    have hd := rf4_atlas_transition_deriv (chartAt ℂ x) (chartAt ℂ y) e
      (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas y) he z z.property hb hp
    rw [hw] at hd
    simp only [rf4_chartTensor, if_pos hp, if_pos hp', hd, hzw, mul_pow, star_mul]
    ring
  · have hp' : (chartAt ℂ y).symm w ∉ e.source := hzw ▸ hp
    simp only [rf4_chartTensor, if_neg hp, if_neg hp', zero_mul]

theorem rf4_chartTensor_mem {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ e.target) (p q : ℕ) :
    rf4_chartTensor e f p q ∈ rf2_smoothForms X p q :=
  ⟨rf4_chartTensor_smooth e he f hf hc hs p q,
    rf4_chartTensor_transition e he f p q⟩

def rf4_chartTensorLinear {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (p q : ℕ) : (ℂ → ℂ) →ₗ[ℂ] rf2_Coeff X where
  toFun f := rf4_chartTensor e f p q
  map_add' f g := by
    classical
    funext x z
    simp only [rf4_chartTensor, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c f := by
    classical
    funext x z
    simp only [rf4_chartTensor, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem rf4_chartTensor_zero_off {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (f : ℂ → ℂ) (p q : ℕ) (x : X)
    (z : (chartAt ℂ x).target)
    (hz : (chartAt ℂ x).symm z ∉ e.symm '' tsupport f) :
    rf4_chartTensor e f p q x z = 0 := by
  classical
  unfold rf4_chartTensor
  split_ifs with hp
  · have hzero : f (e ((chartAt ℂ x).symm z)) = 0 := by
      by_contra hne
      exact hz ⟨e ((chartAt ℂ x).symm z), subset_closure hne, e.left_inv hp⟩
    rw [hzero, zero_mul, zero_mul]
  · rfl

theorem rf4_annulus_density_map {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X) (n : ℕ) (r : ℝ)
    (ht : b63r_annulus n r ⊆ e.target) (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport (wirtingerDbar χ))
    (hs : tsupport (wirtingerDbar χ) ⊆ b63r_annulus n r) :
    ∃ L : b63r_bddHol (b63r_annulus n r) →ₗ[ℂ] rf2_smoothForms X 1 1,
      (∀ φ, (L φ).val = rf4_chartTensor e
        (fun u ↦ rf4_extendBdd φ u * wirtingerDbar χ u) 1 1) ∧
      ∀ φ x (z : (chartAt ℂ x).target),
        (chartAt ℂ x).symm z ∉ e.symm '' b63r_annulus n r → (L φ).val x z = 0 := by
  let A : b63r_bddHol (b63r_annulus n r) →ₗ[ℂ] (ℂ → ℂ) :=
    { toFun := fun φ u ↦ rf4_extendBdd φ u * wirtingerDbar χ u
      map_add' := by
        intro φ ψ
        funext u
        simp only [rf4_extendBdd_add, Pi.add_apply]
        ring
      map_smul' := by
        intro c φ
        funext u
        simp only [rf4_extendBdd_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  let B := (rf4_chartTensorLinear e 1 1).comp A
  have hm (φ : b63r_bddHol (b63r_annulus n r)) : B φ ∈ rf2_smoothForms X 1 1 := by
    obtain ⟨hd, hcd, hsd⟩ := rf4_annulus_density_smooth n r χ hχ hc hs φ
    exact rf4_chartTensor_mem e he _ hd hcd (hsd.trans ht) 1 1
  let L := B.codRestrict (rf2_smoothForms X 1 1) hm
  refine ⟨L, fun _ ↦ rfl, ?_⟩
  intro φ x z hz
  apply rf4_chartTensor_zero_off
  intro h
  apply hz
  obtain ⟨u, hu, heq⟩ := h
  exact ⟨u, (rf4_annulus_density_smooth n r χ hχ hc hs φ).2.2 hu, heq⟩

end HodgeLean.Foundations.Program
