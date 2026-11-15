import HodgeLean.Foundations.Program.PrymParabolicIntersectionLocalSection
import HodgeLean.Foundations.Program.HurwitzPrymCovLoop

set_option linter.unusedSectionVars false

noncomputable section
open Set Filter Manifold Metric
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold b3Forms_isManifold_real

section Real

variable {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
variable {C' : Type} [TopologicalSpace C'] [ChartedSpace ℂ C']

/-- A map holomorphic at a point is real `C¹` there. -/
theorem hga_contMDiffAt_real (g : C → C') (x : C)
    (hg : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g x) : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 g x := by
  have h := (contMDiffAt_iff.1 hg)
  rw [contMDiffAt_iff]
  refine ⟨h.1, ?_⟩
  have h2 := (h.2.restrict_scalars ℝ).of_le (show ((1 : ℕ∞) : WithTop ℕ∞) ≤ ω from le_top)
  simp only [modelWithCornersSelf_coe, range_id] at h2 ⊢
  rw [show extChartAt 𝓘(ℝ, ℂ) (g x) ∘ g ∘ (extChartAt 𝓘(ℝ, ℂ) x).symm =
    extChartAt 𝓘(ℂ, ℂ) (g x) ∘ g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm by
      simp only [b4cov_extChartAt_real, b4cov_extChartAt_real_symm],
    b4cov_extChartAt_real]
  exact h2

/-- The real and complex derivatives of a map holomorphic at a point agree. -/
theorem hga_mfderiv_real_at (g : C → C') (x : C) (hg : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g x)
    (v : ℂ) : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x v = mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g x v := by
  have hc : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g x := hg.mdifferentiableAt (by simp)
  have hr : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x :=
    (hga_contMDiffAt_real g x hg).mdifferentiableAt (by simp)
  rw [hr.mfderiv_abuse, hc.mfderiv_abuse]
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ, b4cov_written_real,
    b4cov_extChartAt_real]
  have hd : DifferentiableAt ℂ (writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x g)
      (extChartAt 𝓘(ℂ, ℂ) x x) := by
    have := hc.differentiableWithinAt_writtenInExtChartAt
    rw [modelWithCornersSelf_coe, range_id, differentiableWithinAt_univ] at this
    exact this
  rw [hd.fderiv_restrictScalars ℝ]
  rfl

/-- The velocity of `g ∘ γ` at a point where `g` is holomorphic. -/
theorem hga_velocity_comp_at (g : C → C') (γ : ℝ → C) (s : ℝ)
    (hg : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g (γ s))
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ s) :
    b3_velocity ℂ C' (g ∘ γ) s =
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g (γ s) (b3_velocity ℂ C γ s) := by
  have hgr : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g (γ s) :=
    (hga_contMDiffAt_real g (γ s) hg).mdifferentiableAt (by simp)
  have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ s := hγ.mdifferentiableAt (by simp)
  rw [b3_velocity, mfderiv_comp s hgr hγd, ContinuousLinearMap.comp_apply]
  exact hga_mfderiv_real_at g (γ s) hg _

end Real

/-- The velocity of a `C¹` curve in the plane is its derivative. -/
theorem hga_velocity_plane (c : ℝ → ℂ) (s : ℝ) (_hc : DifferentiableAt ℝ c s) :
    b3_velocity ℂ ℂ c s = deriv c s := by
  rw [b3_velocity, mfderiv_eq_fderiv]
  rfl

/-- A holomorphic map that is injective near a point has an injective derivative there. -/
theorem hga_mfderiv_injective_of_injOn {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y] (q : ℂ → Y) (x : ℂ) (hq : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω q x)
    (s : Set ℂ) (hs : s ∈ 𝓝 x) (hi : Set.InjOn q s) :
    Function.Injective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) q x) := by
  obtain ⟨e, hxe, hex, heq, he, hes⟩ := RiemannRochTop_injective_holomorphic_coordinates q x hq s hs hi
  have hd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) q x = mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e x := heq.symm.mfderiv_eq
  rw [hd]
  have hc : (e.symm ∘ e : ℂ → ℂ) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hxe] with z hz
    exact e.left_inv hz
  have hl : Function.LeftInverse (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm (e x))
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e x) := by
    intro v
    have h1 : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm (e x) := by rw [hex]; exact hes
    have h := mfderiv_comp_apply x (h1.mdifferentiableAt (by simp))
      (he.mdifferentiableAt (by simp)) v
    rw [hc.mfderiv_eq, mfderiv_id] at h
    exact h.symm
  exact hl.injective

section Fibre

variable {G : Type} [Group G] (U : Type) [TopologicalSpace U] [MulAction G U]
  (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π G)
  (C : Type) [TopologicalSpace C] (f : C → OnePoint ℂ)
  (ι : U → C) (hι : Topology.IsOpenEmbedding ι)
  (hιr : Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ)
  (hfι : ∀ u, f (ι u) = π u)
  (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
  [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
  [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
  [CompactSpace (b63l_parameterFibre mr_base C V hV t)]
  [ConnectedSpace (b63l_parameterFibre mr_base C V hV t)]
  [T2Space (b63l_parameterFibre mr_base C V hV t)]
  (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))

include hπ hι hιr hfι hk in
/-- A holomorphic section of the projection through any point over the region `|Im| ≥ 1`. -/
theorem hga_fibre_section (x : b63l_parameterFibre mr_base C V hV t) (P : ℂ)
    (hx : f (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩ x) = (P : OnePoint ℂ))
    (hP : 1 ≤ |P.im|) :
    ∃ r > 0, ∃ e : C(ℂ, b63l_parameterFibre mr_base C V hV t), e P = x ∧
      (∀ z ∈ ball P r, b63d_projection mr_base C f V hV t (e z) = (z : OnePoint ℂ)) ∧
      IsOpen (e '' ball P r) ∧ ∀ z ∈ ball P r, ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e z := by
  have hfar : ∀ z ∈ closedBall P (1 / 2), 1 / 2 ≤ |z.im| := by
    intro z hz
    have h1 : |(z - P).im| ≤ 1 / 2 := by
      have := Complex.abs_im_le_norm (z - P)
      rw [← dist_eq_norm] at this
      exact this.trans (mem_closedBall.mp hz)
    rw [Complex.sub_im] at h1
    have := abs_sub_abs_le_abs_sub P.im z.im
    rw [abs_sub_comm] at h1
    linarith
  obtain ⟨r, hr, -, e, heP, he, ho⟩ := hga_exists_local_section U π hπ C f ι hι hιr hfι V hV t
    x P (1 / 2) (by norm_num) hx hfar
  exact ⟨r, hr, e, heP, he, ho, hga_section_contMDiffAt _ hk e P r hr he⟩

/-- The projection of a point over the region `|Im| ≥ 1/2` is its plane coordinate. -/
theorem hga_projection_offAxis (x : b63l_parameterFibre mr_base C V hV t) (P : ℂ)
    (hx : f (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩ x) = (P : OnePoint ℂ))
    (hP : 1 / 2 ≤ |P.im|) :
    b63d_projection mr_base C f V hV t x = (P : OnePoint ℂ) := by
  change b6t_sphere mr_base x.val.1.val (f x.val.2) = _
  rw [show x.val.1.val = t.val from congrArg Subtype.val x.property]
  change b6t_sphere mr_base t.val (f (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩ x)) = _
  rw [hx]
  exact hga_offAxis_fixed _ (hV t.property) P hP

include hπ hι hιr hfι hk in
/-- **Lifts of plane curves.** A continuous path of the fibre over a `C¹` curve of the region
`|Im| ≥ 1` agrees near every parameter with a holomorphic section composed with the curve; in
particular it is `C¹`. -/
theorem hga_lift_local (γ : ℝ → b63l_parameterFibre mr_base C V hV t) (hγ : Continuous γ)
    (c : ℝ → ℂ) (hc : ContDiff ℝ 1 c)
    (hγc : ∀ s, f (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩ (γ s)) = (c s : OnePoint ℂ))
    (him : ∀ s, 1 ≤ |(c s).im|) (s₀ : ℝ) (r : ℝ) (hr : 0 < r)
    (e : C(ℂ, b63l_parameterFibre mr_base C V hV t)) (he0 : e (c s₀) = γ s₀)
    (he : ∀ z ∈ ball (c s₀) r, b63d_projection mr_base C f V hV t (e z) = (z : OnePoint ℂ))
    (ho : IsOpen (e '' ball (c s₀) r)) :
    γ =ᶠ[𝓝 s₀] e ∘ c := by
  have hcc : Continuous c := hc.continuous
  have hpre : c ⁻¹' ball (c s₀) r ∈ 𝓝 s₀ :=
    hcc.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))
  obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhds_iff.mp hpre
  let X := ball s₀ ε
  haveI : PreconnectedSpace X := Subtype.preconnectedSpace (convex_ball s₀ ε).isPreconnected
  have hagree := hga_section_agree (X := X) (b63d_projection mr_base C f V hV t) e (c s₀) r he ho
    ⟨fun a ↦ γ a, hγ.comp continuous_subtype_val⟩ (fun a ↦ c a) (hcc.comp continuous_subtype_val)
    (fun a ↦ hεb a.2)
    (fun a ↦ hga_projection_offAxis C f V hV t _ _ (hγc a) ((by norm_num : (1 / 2 : ℝ) ≤ 1).trans (him a)))
    ⟨s₀, mem_ball_self hε⟩ he0.symm
  filter_upwards [ball_mem_nhds s₀ hε] with s hs
  exact hagree ⟨s, hs⟩

include hπ hι hιr hfι hk in
theorem hga_lift_contMDiff (γ : ℝ → b63l_parameterFibre mr_base C V hV t) (hγ : Continuous γ)
    (c : ℝ → ℂ) (hc : ContDiff ℝ 1 c)
    (hγc : ∀ s, f (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩ (γ s)) = (c s : OnePoint ℂ))
    (him : ∀ s, 1 ≤ |(c s).im|) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ := by
  intro s₀
  obtain ⟨r, hr, e, heP, he, ho, hhol⟩ :=
    hga_fibre_section U π hπ C f ι hι hιr hfι V hV t hk (γ s₀) (c s₀) (hγc s₀) (him s₀)
  have hloc := hga_lift_local U π hπ C f ι hι hιr hfι V hV t hk γ hγ c hc hγc him s₀ r hr e heP he ho
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (e ∘ c) s₀ :=
    (hga_contMDiffAt_real e (c s₀) (hhol _ (mem_ball_self hr))).comp s₀
      (hc.contMDiff s₀)
  exact hcomp.congr_of_eventuallyEq hloc

include hπ hι hιr hfι hk in
/-- **Signs of crossings of lifts.** Where two lifts of `C¹` plane curves meet, the orientation
of their velocities has the sign of the orientation of the plane derivatives. -/
theorem hga_lift_crossing_sign (γ₁ γ₂ : ℝ → b63l_parameterFibre mr_base C V hV t)
    (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂) (c₁ c₂ : ℝ → ℂ)
    (hc₁ : ContDiff ℝ 1 c₁) (hc₂ : ContDiff ℝ 1 c₂)
    (h₁ : ∀ s, f (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩ (γ₁ s)) = (c₁ s : OnePoint ℂ))
    (h₂ : ∀ s, f (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩ (γ₂ s)) = (c₂ s : OnePoint ℂ))
    (him₁ : ∀ s, 1 ≤ |(c₁ s).im|) (him₂ : ∀ s, 1 ≤ |(c₂ s).im|) (s₁ s₂ : ℝ)
    (hx : γ₁ s₁ = γ₂ s₂) :
    SignType.sign (b3_orient ℂ (b3_velocity ℂ _ γ₁ s₁) (b3_velocity ℂ _ γ₂ s₂)) =
      SignType.sign (b3_orient ℂ (deriv c₁ s₁) (deriv c₂ s₂)) := by
  have hP : c₁ s₁ = c₂ s₂ := by
    have := (h₁ s₁).symm.trans ((congrArg _ (congrArg _ hx)).trans (h₂ s₂))
    exact OnePoint.coe_injective this
  obtain ⟨r, hr, e, heP, he, ho, hhol⟩ :=
    hga_fibre_section U π hπ C f ι hι hιr hfι V hV t hk (γ₁ s₁) (c₁ s₁) (h₁ s₁) (him₁ s₁)
  have hl₁ := hga_lift_local U π hπ C f ι hι hιr hfι V hV t hk γ₁ hγ₁ c₁ hc₁ h₁ him₁ s₁ r hr e
    heP he ho
  have heP₂ : e (c₂ s₂) = γ₂ s₂ := by rw [← hP, heP, hx]
  have he₂ : ∀ z ∈ ball (c₂ s₂) r, b63d_projection mr_base C f V hV t (e z) = (z : OnePoint ℂ) := by
    rw [← hP]; exact he
  have ho₂ : IsOpen (e '' ball (c₂ s₂) r) := by rw [← hP]; exact ho
  have hl₂ := hga_lift_local U π hπ C f ι hι hιr hfι V hV t hk γ₂ hγ₂ c₂ hc₂ h₂ him₂ s₂ r hr e
    heP₂ he₂ ho₂
  have hhol₀ := hhol _ (mem_ball_self hr)
  have hv₁ : b3_velocity ℂ _ γ₁ s₁ = mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e (c₁ s₁) (deriv c₁ s₁) := by
    rw [b3Forms_velocity_eq_b3, b3Forms_velocity_congr hl₁, ← b3Forms_velocity_eq_b3,
      hga_velocity_comp_at e c₁ s₁ hhol₀ (hc₁.contMDiff s₁),
      hga_velocity_plane c₁ s₁ (hc₁.differentiable one_ne_zero s₁)]
    rfl
  have hhol₀' : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e (c₂ s₂) := hP ▸ hhol₀
  have hv₂ : b3_velocity ℂ _ γ₂ s₂ = mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e (c₂ s₂) (deriv c₂ s₂) := by
    rw [b3Forms_velocity_eq_b3, b3Forms_velocity_congr hl₂, ← b3Forms_velocity_eq_b3,
      hga_velocity_comp_at e c₂ s₂ hhol₀' (hc₂.contMDiff s₂),
      hga_velocity_plane c₂ s₂ (hc₂.differentiable one_ne_zero s₂)]
    rfl
  have hinj : Function.Injective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e (c₁ s₁)) := by
    apply hga_mfderiv_injective_of_injOn e (c₁ s₁) hhol₀ (ball (c₁ s₁) r)
      (ball_mem_nhds _ hr)
    intro a ha b hb hab
    have := congrArg (b63d_projection mr_base C f V hV t) hab
    rw [he a ha, he b hb] at this
    exact OnePoint.coe_injective this
  rw [hv₁, hv₂, ← hP]
  exact b6m_orient_sign_complexLinear (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e (c₁ s₁)) hinj _ _

end Fibre

#print axioms hga_lift_crossing_sign
#print axioms hga_lift_contMDiff
#print axioms hga_lift_local
#print axioms hga_projection_offAxis
#print axioms hga_fibre_section
#print axioms hga_mfderiv_injective_of_injOn
#print axioms hga_velocity_plane
#print axioms hga_velocity_comp_at
#print axioms hga_mfderiv_real_at
#print axioms hga_contMDiffAt_real
end HodgeLean.Foundations.Program
