import HodgeLean.Foundations.Program.PeriodMultiplicationVariationProofs
import HodgeLean.Foundations.Program.RelativeFrameAssembly

noncomputable section
open Set Filter Topology Manifold ContinuousAlternatingMap
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b3Forms_isManifold_real

section TangentForms
variable {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
  [IsManifold 𝓘(ℂ, ℂ) ω C]
  (F : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
  (hadd : ∀ (p : C) (v w : ℂ), F ⟨p, v + w⟩ = F ⟨p, v⟩ + F ⟨p, w⟩)
  (hsmul : ∀ (p : C) (c : ℝ) (v : ℂ), F ⟨p, c • v⟩ = c • F ⟨p, v⟩)

/-- A real linear tangent function as a continuous covector. -/
def b66m_tangentCLM (p : C) : ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => F ⟨p, v⟩
      map_add' := hadd p
      map_smul' := hsmul p }

/-- Scalar components of a real linear complex-valued tangent form. -/
def b66m_scalarTangentForm (L : ℂ →L[ℝ] ℝ) : C → ℂ [⋀^Fin 1]→L[ℝ] ℝ :=
  fun p => ofSubsingleton ℝ ℂ ℝ (0 : Fin 1)
    (L.comp (b66m_tangentCLM F hadd hsmul p))

theorem b66m_scalarTangentForm_apply (L : ℂ →L[ℝ] ℝ) (p : C) (v : ℂ) :
    b66m_scalarTangentForm F hadd hsmul L p (fun _ => v) = L (F ⟨p, v⟩) := rfl

theorem b66m_scalarTangentForm_loc (L : ℂ →L[ℝ] ℝ) (x : C) (u v : ℂ)
    (hu : u ∈ (chartAt ℂ x).target) :
    b3Forms_loc (b66m_scalarTangentForm F hadd hsmul L) x u (fun _ => v) =
      L (F (b3Forms_chartVec x v u)) := by
  simp only [b3Forms_loc, compContinuousLinearMap_apply]
  rw [b3Forms_fderiv_tr_real (b3Forms_mem_trDom_self hu)]
  rfl

/-- Scalar projection preserves smoothness of real tangent forms. -/
theorem b66m_scalarTangentForm_smooth (L : ℂ →L[ℝ] ℝ)
    (hF : ContMDiff 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞ F) :
    b3Forms_IsSmooth (b66m_scalarTangentForm F hadd hsmul L) := by
  let : ChartedSpace (ℂ × ℂ) (TangentBundle 𝓘(ℂ, ℂ) C) :=
    inferInstanceAs (ChartedSpace (ModelProd ℂ ℂ) (TangentBundle 𝓘(ℂ, ℂ) C))
  intro x
  refine b3Forms_contDiffOn_of_apply fun v => ?_
  have hc : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ).tangent ∞
      (b3Forms_chartVec x v) (chartAt ℂ x).target := by
    intro u hu
    have h := b3Forms_contMDiffOn_chartVec x v u hu
    simp only [ModelWithCorners.tangent, ← modelWithCornersSelf_prod] at h ⊢
    exact (b3A_contMDiffWithinAt_real h).of_le (by simp)
  have h := L.contDiff.comp_contDiffOn (hF.comp_contMDiffOn hc).contDiffOn
  exact h.congr fun u hu => b66m_scalarTangentForm_loc F hadd hsmul L x u v hu

end TangentForms

section ChartPrimitives
variable {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
  [IsManifold 𝓘(ℂ, ℂ) ω C]

theorem b66m_chart_symm_mfderiv (x : C) (u : ℂ)
    (hu : u ∈ (chartAt ℂ x).target) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartAt ℂ x).symm u =
      fderiv ℝ (b3Forms_tr x ((chartAt ℂ x).symm u)) u := by
  have hd := ((contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := x)).contMDiffAt
    ((chartAt ℂ x).open_target.mem_nhds hu)).mdifferentiableAt (by simp)
  rw [hd.mfderiv_abuse]
  simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ]
  rfl

theorem b66m_primitive_chart_derivative (G : C → ℂ) (L : ℂ →L[ℝ] ℝ)
    (x : C) (u : ℂ) (hu : u ∈ (chartAt ℂ x).target)
    (hG : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G ((chartAt ℂ x).symm u)) :
    fderiv ℝ (L ∘ G ∘ (chartAt ℂ x).symm) u =
      L.comp ((show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) G ((chartAt ℂ x).symm u)).comp
        (fderiv ℝ (b3Forms_tr x ((chartAt ℂ x).symm u)) u)) := by
  have hs := ((contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := x)).contMDiffAt
    ((chartAt ℂ x).open_target.mem_nhds hu)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp u (hG.mdifferentiableAt (by simp)) hs
  rw [b66m_chart_symm_mfderiv x u hu] at hd
  have hc := L.hasFDerivAt.comp u
    (((hG.mdifferentiableAt (by simp)).hasMFDerivAt.comp u hs.hasMFDerivAt).hasFDerivAt)
  rw [b66m_chart_symm_mfderiv x u hu] at hc
  exact hc.fderiv

/-- A local complex primitive identifies the scalar form's chart differential. -/
theorem b66m_scalarTangentForm_loc_primitive
    (F : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (hadd : ∀ (p : C) (v w : ℂ), F ⟨p, v + w⟩ = F ⟨p, v⟩ + F ⟨p, w⟩)
    (hsmul : ∀ (p : C) (c : ℝ) (v : ℂ), F ⟨p, c • v⟩ = c • F ⟨p, v⟩)
    (L : ℂ →L[ℝ] ℝ) (G : C → ℂ) (x : C) (u : ℂ)
    (hu : u ∈ (chartAt ℂ x).target)
    (hG : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G ((chartAt ℂ x).symm u))
    (hprim : ∀ v : ℂ, F ⟨(chartAt ℂ x).symm u, v⟩ =
      (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) G ((chartAt ℂ x).symm u)) v) :
    b3Forms_loc (b66m_scalarTangentForm F hadd hsmul L) x u =
      extDeriv (fun w => constOfIsEmpty ℝ ℂ (Fin 0) ((L ∘ G ∘ (chartAt ℂ x).symm) w)) u := by
  rw [extDeriv_constOfIsEmpty]
  ext v
  have hv : v = fun _ => v 0 := by funext i; fin_cases i; rfl
  rw [hv, b66m_scalarTangentForm_loc F hadd hsmul L x u (v 0) hu]
  change L (F ⟨_, _⟩) = _
  rw [hprim, b66m_primitive_chart_derivative G L x u hu hG]
  rw [b3Forms_fderiv_tr_real (b3Forms_mem_trDom_self hu)]
  rfl

/-- Smooth local primitives give zero exterior derivative for every scalar component. -/
theorem b66m_scalarTangentForm_d
    (F : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (hadd : ∀ (p : C) (v w : ℂ), F ⟨p, v + w⟩ = F ⟨p, v⟩ + F ⟨p, w⟩)
    (hsmul : ∀ (p : C) (c : ℝ) (v : ℂ), F ⟨p, c • v⟩ = c • F ⟨p, v⟩)
    (L : ℂ →L[ℝ] ℝ)
    (hprim : ∀ p : C, ∃ (V : Set C) (G : C → ℂ), IsOpen V ∧ p ∈ V ∧
      (∀ y ∈ V, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G y) ∧
      ∀ y ∈ V, ∀ v : ℂ, F ⟨y, v⟩ =
        (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) G y) v) :
    b3Forms_d (b66m_scalarTangentForm F hadd hsmul L) = 0 := by
  funext p
  obtain ⟨V, G, hV, hpV, hG, hdG⟩ := hprim p
  have hp := mem_chart_source ℂ p
  have hpt := (chartAt ℂ p).map_source hp
  have hS := (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := p)).contMDiffAt
    ((chartAt ℂ p).open_target.mem_nhds hpt)
  have hp' : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv hp
  have hG' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G
      ((chartAt ℂ p).symm (chartAt ℂ p p)) := hp'.symm ▸ hG p hpV
  have hc : ContDiffAt ℝ ∞ (L ∘ G ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) :=
    L.contDiff.contDiffAt.comp _ (contMDiffAt_iff_contDiffAt.mp (hG'.comp _ hS))
  have hn : ∀ᶠ u in 𝓝 (chartAt ℂ p p), u ∈ (chartAt ℂ p).target ∧
      (chartAt ℂ p).symm u ∈ V :=
    inter_mem ((chartAt ℂ p).open_target.mem_nhds hpt)
      ((chartAt ℂ p).tendsto_symm hp (hV.mem_nhds hpV))
  have he : b3Forms_loc (b66m_scalarTangentForm F hadd hsmul L) p =ᶠ[𝓝 (chartAt ℂ p p)]
      extDeriv (fun u => constOfIsEmpty ℝ ℂ (Fin 0) ((L ∘ G ∘ (chartAt ℂ p).symm) u)) := by
    filter_upwards [hn] with u hu
    exact b66m_scalarTangentForm_loc_primitive F hadd hsmul L G p u hu.1
      (hG _ hu.2) (hdG _ hu.2)
  change extDeriv _ _ = 0
  rw [he.extDeriv_eq]
  apply extDeriv_extDeriv_apply _ b3Forms_minSmoothness_le
  exact (constOfIsEmptyLIE ℝ ℂ ℝ (Fin 0)).toContinuousLinearEquiv.contDiff.contDiffAt.comp _ hc


theorem b66m_scalarTangentForm_lineIntegral
    (F : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    (hadd : ∀ (p : C) (v w : ℂ), F ⟨p, v + w⟩ = F ⟨p, v⟩ + F ⟨p, w⟩)
    (hsmul : ∀ (p : C) (c : ℝ) (v : ℂ), F ⟨p, c • v⟩ = c • F ⟨p, v⟩)
    (L : ℂ →L[ℝ] ℝ)
    (hF : ContMDiff 𝓘(ℝ, ℂ).tangent 𝓘(ℝ, ℂ) ∞ F)
    (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ) :
    b3Forms_lineIntegral (b66m_scalarTangentForm F hadd hsmul L) γ 0 1 =
      L (b3_pathIntegral ℂ C γ F) := by
  change (∫ s in (0 : ℝ)..1, L (F ⟨γ s, b3_velocity ℂ C γ s⟩)) = _
  exact L.intervalIntegral_comp_comm
    ((hF.continuous.comp (b3A_continuous_velocity γ hγ)).intervalIntegrable _ _)

end ChartPrimitives
section LatticeNormalization
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful
/-- Pairing with the lattice harmonic form evaluates a smooth real cohomology representative. -/
theorem b66m_closedForm_lattice_pairing (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (α : rf8_fibre R.C t → ℂ [⋀^Fin 1]→L[ℝ] ℝ) (hα : b3Forms_IsSmooth α)
    (hdα : b3Forms_d α = 0) (γ : b3_SmoothLoop ℂ (rf8_fibre R.C t)) :
    b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ)) α
      (b3Forms_reForm (b3Rest2_θ (Module.finrank_self ℂ)
        (b3_latticePeriod ℂ (rf8_fibre R.C t) γ))) =
      b3Forms_lineIntegral α γ.val 0 1 := by
  letI : Fact (Module.finrank ℂ ℂ = 1) := ⟨Module.finrank_self ℂ⟩
  obtain ⟨η, hη, hdη, hdual⟩ := b3Rest2_exists_dual (Module.finrank_self ℂ) γ
  obtain ⟨φ, g, hg, heq⟩ := b3Rest_hodge hη hdη
  have hφ := b3Rest2_θ_eq_of_dual (Module.finrank_self ℂ) γ hη hdual hg heq
  have hp := hdual α hα hdα
  change b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ)) α η = _ at hp
  rw [heq, hφ, b3Forms_pairing_add_right _ hα (b3Forms_isSmooth_reForm _) hg.d,
    b3Forms_pairing_comm _ (b3Forms_d (b3Forms_fun (E := ℂ) g)) α,
    b3Forms_integral_wedge_d_eq_zero _ b3Forms_oriented_complex hg hα hdα,
    neg_zero, add_zero] at hp
  exact hp


/-- The supplied intersection form has its original harmonic integral normalization. -/
theorem b66m_intersection_lattice_W (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (l k : b3_periodLattice ℂ (rf8_fibre R.C t)) :
    (R.Q t l k : ℝ) = b3Rest2_W (Module.finrank_self ℂ)
      (b3Rest2_θ (Module.finrank_self ℂ) l) (b3Rest2_θ (Module.finrank_self ℂ) k) := by
  have he := b3Rest_intersectionForm_unique (Module.finrank_self ℂ) (R.Q t)
    (b3Rest2_QZ (Module.finrank_self ℂ) (b3Rest2_key (Module.finrank_self ℂ)))
    (R.hQ t) (b3Rest2_isIntersectionForm (Module.finrank_self ℂ)
      (b3Rest2_key (Module.finrank_self ℂ)))
  rw [he, b3Rest2_QZ_apply, b3Rest2_Q_eq_W]

/-- The supplied intersection form evaluates the original lattice period on its harmonic form. -/
theorem b66m_intersection_lattice_period (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (l k : b3_periodLattice ℂ (rf8_fibre R.C t)) :
    (R.Q t l k : ℝ) = (k.val (b3Rest2_θ (Module.finrank_self ℂ) l)).re := by
  rw [b66m_intersection_lattice_W, b3Rest2_W_θ]

/-- The singular primitive restriction uses the same supplied intersection form. -/
theorem b66m_singular_intersection_W (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (x y : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) t) :
    ((b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
      t (R.P t) (R.Q t) x y : ℤ) : ℝ) =
      b3Rest2_W (Module.finrank_self ℂ)
        (b3Rest2_θ (Module.finrank_self ℂ) (R.P t x.val))
        (b3Rest2_θ (Module.finrank_self ℂ) (R.P t y.val)) := by
  exact b66m_intersection_lattice_W R t (R.P t x.val) (R.P t y.val)


/-- The original marked polarization agrees with the harmonic intersection integral on cycles. -/
theorem b66m_marked_intersection_W (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (x y : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s) :
    b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
      (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] y)) =
      (b3Rest2_W (Module.finrank_self ℂ)
        (b3Rest2_θ (Module.finrank_self ℂ) (R.P s x.val))
        (b3Rest2_θ (Module.finrank_self ℂ) (R.P s y.val)) : ℂ) := by
  rw [b64b_complex_pairing _ _ m hpol, LinearMap.BilinForm.baseChange_tmul]
  simp only [one_mul, zsmul_eq_mul, mul_one]
  have he := congrArg (fun a : ℝ => (a : ℂ)) (b66m_singular_intersection_W R s x y)
  simpa only [Complex.ofReal_intCast] using he

/-- Pairing a starred real form with a holomorphic real part moves the complex scalar. -/
theorem b66m_pairing_star_reForm (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (α : rf8_fibre R.C t → ℂ [⋀^Fin 1]→L[ℝ] ℝ)
    (η : b3_HolForm ℂ (rf8_fibre R.C t)) :
    b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ)) (b3Forms_star α) (b3Forms_reForm η) =
      b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ)) α (b3Forms_reForm (Complex.I • η)) := by
  have he : b3Forms_wedgeForm (b3Forms_star α) (b3Forms_reForm η) =
      (-1 : ℝ) • b3Forms_wedgeForm α (b3Forms_imForm η) := by
    rw [← b3Forms_star_reForm]
    funext p
    change b3Forms_wedge (b3Forms_starPt (α p)) (b3Forms_reForm η p) =
      (-1 : ℝ) • b3Forms_wedge (α p) (b3Forms_starPt (b3Forms_reForm η p))
    rw [b3Forms_wedge_comm (b3Forms_reForm η p),
      b3Forms_wedge_starPt_comm (Module.finrank_self ℂ)]
    simp only [neg_one_smul]
  rw [b3Forms_pairing, he, b3Forms_integral_smul, b3Rest2_reForm_I,
    b3Forms_pairing_smul_right]
  rfl


/-- Flat transport preserves the original harmonic intersection integral. -/
theorem b66m_transport_intersection_W (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (x y : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s) :
    b3Rest2_W (Module.finrank_self ℂ)
      (b3Rest2_θ (Module.finrank_self ℂ)
        (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.P s t x))
      (b3Rest2_θ (Module.finrank_self ℂ)
        (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.P s t y)) =
    b3Rest2_W (Module.finrank_self ℂ)
      (b3Rest2_θ (Module.finrank_self ℂ) (R.P s x.val))
      (b3Rest2_θ (Module.finrank_self ℂ) (R.P s y.val)) := by
  rw [← b66m_intersection_lattice_W, ← b66m_intersection_lattice_W]
  have he := b63e_pairing_constant mr_base R.C (b6t_polydisc mr_base) (Subset.refl _)
    mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj R.hk
    R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP s t x.val y.val
  exact congrArg (fun z : ℤ => (z : ℝ)) he

/-- The marked polarization retains its integral normalization at every transported fibre. -/
theorem b66m_marked_transport_intersection_W (R : rf8_SharedFamily)
    (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (x y : b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) s) :
    b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
      (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] y)) =
      (b3Rest2_W (Module.finrank_self ℂ)
        (b3Rest2_θ (Module.finrank_self ℂ)
          (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.P s t x))
        (b3Rest2_θ (Module.finrank_self ℂ)
          (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.P s t y)) : ℂ) := by
  rw [b66m_transport_intersection_W]
  exact b66m_marked_intersection_W R s m hpol x y

/-- Every fibre holomorphic differential has an actual local relative extension. -/
theorem b66m_relative_extension (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (φ : b3_HolForm ℂ (rf8_fibre R.C t)) :
    ∃ (U : Set (Fin 10 → ℂ)), IsOpen U ∧ t.val ∈ U ∧ U ⊆ b6t_polydisc mr_base ∧
      ∃ θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U,
        b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) θ t = φ := by
  obtain ⟨U, hU, ht, hsub, f, hf⟩ := rf8_root_relForm_frame R t
  let E : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U →ₗ[ℂ]
      b3_HolForm ℂ (rf8_fibre R.C t) :=
    { toFun := fun θ => b63e_relFormAt mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) θ t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hspan := (hf t ht).2
  have hr : Submodule.span ℂ (Set.range fun i => E (f i)) ≤ LinearMap.range E := by
    apply Submodule.span_le.mpr
    rintro φ ⟨i, rfl⟩
    exact ⟨f i, rfl⟩
  change Submodule.span ℂ (Set.range fun i => E (f i)) = ⊤ at hspan
  rw [hspan] at hr
  obtain ⟨θ, hθ⟩ := (LinearMap.range_eq_top.mp (top_unique hr)) φ
  exact ⟨U, hU, ht, hsub, θ, hθ⟩

/-- Retained holomorphic coefficients have local relative extensions with their literal chart law. -/
theorem b66m_coefficient_relative_extension (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q : b66g_forms R t 1) :
    ∃ (U : Set (Fin 10 → ℂ)), IsOpen U ∧ t.val ∈ U ∧ U ⊆ b6t_polydisc mr_base ∧
      ∃ θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U,
        ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
          θ.val t ⟨p, w⟩ = q.val a p.val.2 * b66m_sc_sliceD R t a p w := by
  obtain ⟨M, hM, _⟩ := (b66g_primitive_comparison R t).1
  obtain ⟨U, hU, ht, hsub, θ, hθ⟩ := b66m_relative_extension R t (M q)
  refine ⟨U, hU, ht, hsub, θ, ?_⟩
  intro a p hp w
  have he := congrArg (fun φ : b3_HolForm ℂ (rf8_fibre R.C t) => φ.val ⟨p, w⟩) hθ
  exact he.trans (hM q a p hp w)

end LatticeNormalization

section CorrectedForms
set_option backward.isDefEq.respectTransparency false
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful
variable (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) {U : Set (Fin 10 → ℂ)}
  (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
  (q : b66g_Coeff R) (h : Fin 10 → ℂ)
  (ρ : SmoothPartitionOfUnity (b66k_Index R) 𝓘(ℝ, ℂ) (rf8_fibre R.C t) univ)

/-- The actual corrected parameter form is additive in tangent vectors. -/
theorem b66m_correctedParameterForm_add (p : rf8_fibre R.C t) (v w : ℂ) :
    b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
      (b66m_parameterLocalForm R t θ h) ⟨p, v + w⟩ =
    b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
      (b66m_parameterLocalForm R t θ h) ⟨p, v⟩ +
    b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
      (b66m_parameterLocalForm R t θ h) ⟨p, w⟩ := by
  have hD := (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
    (b66m_sc_tau R t ρ (b66g_contract R q (b66k_cocycle R t h)) p.val) p).map_add v w
  simp only [b66m_correctedLocalForm, b66m_parameterLocalForm]
  rw [hD, map_add, mul_add]
  ring

/-- Real scalar linearity holds directly for the corrected parameter expression. -/
theorem b66m_correctedParameterForm_smul (p : rf8_fibre R.C t) (c : ℝ) (v : ℂ) :
    b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
      (b66m_parameterLocalForm R t θ h) ⟨p, c • v⟩ =
    c • b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
      (b66m_parameterLocalForm R t θ h) ⟨p, v⟩ := by
  simp only [b66m_correctedLocalForm, b66m_parameterLocalForm]
  have hD := (show ℂ →L[ℝ] ℂ from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
    (b66m_sc_tau R t ρ (b66g_contract R q (b66k_cocycle R t h)) p.val) p).map_smul c v
  have hS := ((b66m_sc_sliceD R t p.val p).restrictScalars ℝ).map_smul c v
  change b66m_sc_sliceD R t p.val p (c • v) = c • b66m_sc_sliceD R t p.val p v at hS
  rw [hD, hS]
  simp only [Complex.real_smul]
  ring

/-- A scalar component of the actual corrected parameter form. -/
def b66m_correctedParameterScalarForm (L : ℂ →L[ℝ] ℝ) :
    rf8_fibre R.C t → ℂ [⋀^Fin 1]→L[ℝ] ℝ :=
  b66m_scalarTangentForm
    (b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
      (b66m_parameterLocalForm R t θ h))
    (b66m_correctedParameterForm_add R t θ q h ρ)
    (b66m_correctedParameterForm_smul R t θ q h ρ) L

theorem b66m_correctedParameterScalarForm_apply (L : ℂ →L[ℝ] ℝ)
    (p : rf8_fibre R.C t) (v : ℂ) :
    b66m_correctedParameterScalarForm R t θ q h ρ L p (fun _ => v) =
      L (b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
        (b66m_parameterLocalForm R t θ h) ⟨p, v⟩) := rfl

variable (hU : IsOpen U) (ht : t.val ∈ U) (hqf : q ∈ b66g_forms R t 1)
    (hq : ∀ a (p : rf8_fibre R.C t), p.val ∈ (R.atlas.A a).source → ∀ w : ℂ,
      θ.val t ⟨p, w⟩ = q a p.val.2 * b66m_sc_sliceD R t a p w)
    (hρ : ρ.IsSubordinate fun a => {p | p.val ∈ (R.atlas.A a).source})
include hU ht hqf hq hρ

theorem b66m_correctedParameterScalarForm_smooth (L : ℂ →L[ℝ] ℝ) :
    b3Forms_IsSmooth (b66m_correctedParameterScalarForm R t θ q h ρ L) :=
  b66m_scalarTangentForm_smooth _ _ _ L
    (b66m_correctedParameterForm_smooth R t hU ht θ q hqf hq h ρ hρ)

theorem b66m_correctedParameterScalarForm_d (L : ℂ →L[ℝ] ℝ) :
    b3Forms_d (b66m_correctedParameterScalarForm R t θ q h ρ L) = 0 :=
  b66m_scalarTangentForm_d _ _ _ L
    (b66m_correctedParameterForm_local_primitive R t hU ht θ q hqf hq h ρ hρ)


/-- A scalar component of the parameter variation as a de Rham representative. -/
def b66m_correctedParameterClosedForm (L : ℂ →L[ℝ] ℝ) :
    b3Forms_closed ℂ (rf8_fibre R.C t) 0 :=
  ⟨⟨b66m_correctedParameterScalarForm R t θ q h ρ L,
      b66m_correctedParameterScalarForm_smooth R t θ q h ρ hU ht hqf hq hρ L⟩,
    LinearMap.mem_ker.mpr (Subtype.ext
      (b66m_correctedParameterScalarForm_d R t θ q h ρ hU ht hqf hq hρ L))⟩

/-- The de Rham class of a scalar component of the parameter variation. -/
def b66m_correctedParameterClass (L : ℂ →L[ℝ] ℝ) :
    b3Forms_deRham ℂ (rf8_fibre R.C t) 0 :=
  Submodule.Quotient.mk
    (b66m_correctedParameterClosedForm R t θ q h ρ hU ht hqf hq hρ L)


/-- The scalar de Rham class computes the actual complex form's loop integral. -/
theorem b66m_correctedParameterClass_period (L : ℂ →L[ℝ] ℝ)
    (γ : b3Forms_Loop ℂ (rf8_fibre R.C t)) :
    b3Forms_periodMap
      (b66m_correctedParameterClass R t θ q h ρ hU ht hqf hq hρ L) γ =
      L (b3_pathIntegral ℂ (rf8_fibre R.C t) γ.val
        (b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
          (b66m_parameterLocalForm R t θ h))) := by
  change b3Forms_lineIntegral (b66m_correctedParameterScalarForm R t θ q h ρ L)
    γ.val 0 1 = _
  exact b66m_scalarTangentForm_lineIntegral _ _ _ L
    (b66m_correctedParameterForm_smooth R t hU ht θ q hqf hq h ρ hρ) γ.val γ.property.2

/-- The scalar de Rham representative has a holomorphic Hodge component and an exact part. -/
theorem b66m_correctedParameterScalarForm_hodge (L : ℂ →L[ℝ] ℝ) :
    ∃ (φ : b3_HolForm ℂ (rf8_fibre R.C t)) (g : rf8_fibre R.C t → ℝ),
      b3Forms_IsSmooth (b3Forms_fun (E := ℂ) g) ∧
      b66m_correctedParameterScalarForm R t θ q h ρ L =
        b3Forms_reForm φ + b3Forms_d (b3Forms_fun (E := ℂ) g) := by
  letI : Fact (Module.finrank ℂ ℂ = 1) := ⟨Module.finrank_self ℂ⟩
  exact b3Rest_hodge
    (b66m_correctedParameterScalarForm_smooth R t θ q h ρ hU ht hqf hq hρ L)
    (b66m_correctedParameterScalarForm_d R t θ q h ρ hU ht hqf hq hρ L)

/-- The scalar class evaluates to the derivative of the original fixed-cycle periods. -/
theorem b66m_correctedParameterClass_flat_period (s : b6t_polydisc mr_base)
    (L : ℂ →L[ℝ] ℝ) {c : ℝ → R.C} (hc : Continuous c)
    (hcp : Function.Periodic c 1)
    (K : b63e_Cover mr_base R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66k_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k))
    (ha : ∀ k, a (k + K.N) = a k) :
    b3Forms_periodMap
      (b66m_correctedParameterClass R t θ q h ρ hU ht hqf hq hρ L)
      (K.loopF (b6t_polydisc mr_base) (Subset.refl _) t (R.hincl t) K.cond_u₀) =
      L (fderiv ℂ (b63e_periodFunction mr_base R.C (b6t_polydisc mr_base) (Subset.refl _)
        R.P θ s (b63e_fibreLoopClass mr_base R.C s hc hcp)) t.val h) := by
  rw [b66m_correctedParameterClass_period R t θ q h ρ hU ht hqf hq hρ]
  rw [b66m_correctedParameterForm_flat_period R s t hU ht θ q hqf hq h ρ hρ
    hc hcp K a hφ ha]

/-- The scalar Dolbeault representative of contraction as an actual smooth form. -/
def b66m_contractionSmooth01 : b4c_Smooth01 ℂ (rf8_fibre R.C t) :=
  ⟨b66m_sc_gamma R t ρ (b66g_contract R q (b66k_cocycle R t h)),
    b66m_sc_gamma_mem R t ρ hρ (b66m_rs_contract_mem R t hqf (b66k_cocycle_mem R t h))⟩

omit hU ht hq in
/-- The real Dolbeault representative fixes the sign relative to the real parameter form. -/
theorem b66m_contraction_re01 :
    RiemannRochAna_re01 (b66m_contractionSmooth01 R t q h ρ hqf hρ) =
      (-1 / 2 : ℝ) • (b66m_correctedParameterScalarForm R t θ q h ρ Complex.reCLM +
        b3Forms_star (b66m_correctedParameterScalarForm R t θ q h ρ Complex.imCLM)) := by
  funext p
  ext v
  have hv : v = fun _ => v 0 := by funext i; fin_cases i; rfl
  rw [hv]
  change (b66m_sc_gamma R t ρ (b66g_contract R q (b66k_cocycle R t h)) ⟨p, v 0⟩).re = _
  simp only [Pi.smul_apply, Pi.add_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, b3Forms_star, b3Forms_starPt_apply,
    b66m_correctedParameterScalarForm_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    smul_eq_mul]
  have he := congrArg Complex.re (b66m_correctedParameterForm_antilinear R t θ q h ρ p (v 0))
  simp at he
  linarith



/-- The contraction trace is expressed in the real parameter representative's integral pairings. -/
theorem b66m_contraction_dolbeault_pairing (η : b3_HolForm ℂ (rf8_fibre R.C t)) :
    b66m_dolbeaultIntegral R t (b66m_contractionSmooth01 R t q h ρ hqf hρ) η =
      -(b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
        (b66m_correctedParameterScalarForm R t θ q h ρ Complex.reCLM) (b3Forms_reForm η) : ℂ) -
      (b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
        (b66m_correctedParameterScalarForm R t θ q h ρ Complex.imCLM)
        (b3Forms_reForm (Complex.I • η)) : ℂ) +
      Complex.I * ((b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
        (b66m_correctedParameterScalarForm R t θ q h ρ Complex.reCLM)
        (b3Forms_reForm (Complex.I • η)) : ℂ) -
        (b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
          (b66m_correctedParameterScalarForm R t θ q h ρ Complex.imCLM)
          (b3Forms_reForm η) : ℂ)) := by
  let α := b66m_correctedParameterScalarForm R t θ q h ρ Complex.reCLM
  let δ := b66m_correctedParameterScalarForm R t θ q h ρ Complex.imCLM
  have hα := b66m_correctedParameterScalarForm_smooth R t θ q h ρ hU ht hqf hq hρ Complex.reCLM
  have hδ := b66m_correctedParameterScalarForm_smooth R t θ q h ρ hU ht hqf hq hρ Complex.imCLM
  change 2 * ((b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
      (RiemannRochAna_re01 (b66m_contractionSmooth01 R t q h ρ hqf hρ))
      (b3Forms_reForm η) : ℂ) - Complex.I *
      (b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
        (RiemannRochAna_re01 (b66m_contractionSmooth01 R t q h ρ hqf hρ))
        (b3Forms_reForm (Complex.I • η)) : ℂ)) = _
  rw [b66m_contraction_re01 R t θ q h ρ hqf hρ]
  rw [b3Forms_pairing_smul_left, b3Forms_pairing_smul_left,
    b3Forms_pairing_add_left _ hα hδ.star (b3Forms_isSmooth_reForm η),
    b3Forms_pairing_add_left _ hα hδ.star (b3Forms_isSmooth_reForm (Complex.I • η)),
    b66m_pairing_star_reForm R t _ η, b66m_pairing_star_reForm R t _ (Complex.I • η),
    b3Rest2_I_I]
  have hn : b3Forms_reForm (-η) = (-1 : ℝ) • b3Forms_reForm η := by
    rw [← b3Forms_reForm_smul, neg_one_smul]
  rw [hn, b3Forms_pairing_smul_right]
  push_cast
  ring


/-- Real and imaginary parts of the actual Cech contraction trace use the de Rham representatives. -/
theorem b66m_contraction_cech_pairing (η : b3_HolForm ℂ (rf8_fibre R.C t)) :
    (b66m_cechTrace R t ρ hρ (b66m_sc_cechProjection R t
      ⟨b66g_contract R q (b66k_cocycle R t h),
        b66m_rs_contract_mem R t hqf (b66k_cocycle_mem R t h)⟩) η).re =
      -b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
        (b66m_correctedParameterScalarForm R t θ q h ρ Complex.reCLM) (b3Forms_reForm η) -
      b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
        (b66m_correctedParameterScalarForm R t θ q h ρ Complex.imCLM)
        (b3Forms_reForm (Complex.I • η)) ∧
    (b66m_cechTrace R t ρ hρ (b66m_sc_cechProjection R t
      ⟨b66g_contract R q (b66k_cocycle R t h),
        b66m_rs_contract_mem R t hqf (b66k_cocycle_mem R t h)⟩) η).im =
      b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
        (b66m_correctedParameterScalarForm R t θ q h ρ Complex.reCLM)
        (b3Forms_reForm (Complex.I • η)) -
      b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
        (b66m_correctedParameterScalarForm R t θ q h ρ Complex.imCLM)
        (b3Forms_reForm η) := by
  rw [b66m_cechTrace_cycle]
  change (b66m_dolbeaultIntegral R t (b66m_contractionSmooth01 R t q h ρ hqf hρ) η).re = _ ∧
    (b66m_dolbeaultIntegral R t (b66m_contractionSmooth01 R t q h ρ hqf hρ) η).im = _
  have he := b66m_contraction_dolbeault_pairing R t θ q h ρ hU ht hqf hq hρ η
  constructor
  · simpa using congrArg Complex.re he
  · simpa using congrArg Complex.im he

/-- Pairing the actual scalar representative with a lattice harmonic form computes its loop period. -/
theorem b66m_correctedParameterScalarForm_lattice_pairing (L : ℂ →L[ℝ] ℝ)
    (γ : b3_SmoothLoop ℂ (rf8_fibre R.C t)) :
    b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
      (b66m_correctedParameterScalarForm R t θ q h ρ L)
      (b3Forms_reForm (b3Rest2_θ (Module.finrank_self ℂ)
        (b3_latticePeriod ℂ (rf8_fibre R.C t) γ))) =
      L (b3_pathIntegral ℂ (rf8_fibre R.C t) γ.val
        (b66m_correctedLocalForm R t ρ (b66g_contract R q (b66k_cocycle R t h))
          (b66m_parameterLocalForm R t θ h))) := by
  rw [b66m_closedForm_lattice_pairing R t _
    (b66m_correctedParameterScalarForm_smooth R t θ q h ρ hU ht hqf hq hρ L)
    (b66m_correctedParameterScalarForm_d R t θ q h ρ hU ht hqf hq hρ L)]
  exact b66m_scalarTangentForm_lineIntegral _ _ _ L
    (b66m_correctedParameterForm_smooth R t hU ht θ q hqf hq h ρ hρ) γ.val γ.property.2

/-- The original fixed-cycle derivative equals the actual harmonic integral pairing. -/
theorem b66m_correctedParameterScalarForm_flat_pairing (s : b6t_polydisc mr_base)
    (L : ℂ →L[ℝ] ℝ) {c : ℝ → R.C} (hc : Continuous c)
    (hcp : Function.Periodic c 1)
    (K : b63e_Cover mr_base R.C t.val (fun τ => (t, c τ)))
    (a : ℤ → b66k_Index R) (hφ : ∀ k, K.φ k = R.atlas.A (a k))
    (ha : ∀ k, a (k + K.N) = a k) :
    b3Forms_pairing (b3Rest_b (Module.finrank_self ℂ))
      (b66m_correctedParameterScalarForm R t θ q h ρ L)
      (b3Forms_reForm (b3Rest2_θ (Module.finrank_self ℂ)
        (b3_latticePeriod ℂ (rf8_fibre R.C t)
          (K.loopF (b6t_polydisc mr_base) (Subset.refl _) t (R.hincl t) K.cond_u₀)))) =
      L (fderiv ℂ (b63e_periodFunction mr_base R.C (b6t_polydisc mr_base) (Subset.refl _)
        R.P θ s (b63e_fibreLoopClass mr_base R.C s hc hcp)) t.val h) := by
  rw [b66m_correctedParameterScalarForm_lattice_pairing R t θ q h ρ hU ht hqf hq hρ]
  rw [b66m_correctedParameterForm_flat_period R s t hU ht θ q hqf hq h ρ hρ hc hcp K a hφ ha]

end CorrectedForms



end HodgeLean.Foundations.Program
