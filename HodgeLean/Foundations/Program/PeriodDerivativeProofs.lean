import HodgeLean.Foundations.Program.PeriodDerivativeDefs

noncomputable section
open scoped TensorProduct Matrix Topology
open HodgeLean.Papers Filter Set
namespace HodgeLean.Foundations.Program
attribute [local instance] b64c_RootFamily.topC b64c_RootFamily.chartC b64c_RootFamily.manC
  b64c_RootFamily.t2C b64c_RootFamily.compactC b64c_RootFamily.connectedC
  b64c_RootFamily.actionC b64c_RootFamily.totalChart b64c_RootFamily.totalMan
  b64c_RootFamily.fibreChart b64c_RootFamily.fibreMan b64c_RootFamily.fibreT2
  b64c_RootFamily.fibreCompact b64c_RootFamily.fibreConnected b64c_RootFamily.fibreFaithful

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful


theorem b66_matrix_mul_diff (A B : (Fin 10 → ℂ) → Matrix (Fin 3) (Fin 3) ℂ)
    (t : Fin 10 → ℂ) (ha : DifferentiableAt ℂ A t) (hb : DifferentiableAt ℂ B t) :
    DifferentiableAt ℂ (fun x => A x * B x) t := by
  apply differentiableAt_pi.2
  intro i
  apply differentiableAt_pi.2
  intro j
  change DifferentiableAt ℂ (fun x => ∑ k, A x i k * B x k j) t
  exact DifferentiableAt.fun_sum fun k _ =>
    (differentiableAt_pi.mp (differentiableAt_pi.mp ha i) k).mul
      (differentiableAt_pi.mp (differentiableAt_pi.mp hb k) j)

theorem b66_matrix_mul_fderiv (A B : (Fin 10 → ℂ) → Matrix (Fin 3) (Fin 3) ℂ)
    (t h : Fin 10 → ℂ) (ha : DifferentiableAt ℂ A t) (hb : DifferentiableAt ℂ B t) :
    fderiv ℂ (fun x => A x * B x) t h =
      A t * fderiv ℂ B t h + fderiv ℂ A t h * B t := by
  ext i j
  have hd := b66_matrix_mul_diff A B t ha hb
  have he (C : (Fin 10 → ℂ) → Matrix (Fin 3) (Fin 3) ℂ)
      (hc : DifferentiableAt ℂ C t) (i j : Fin 3) :
      fderiv ℂ (fun x => C x i j) t h = fderiv ℂ C t h i j := by
    rw [fderiv_apply (differentiableAt_pi.mp hc i) j, fderiv_apply hc i]
    rfl
  rw [← he _ hd i j]
  change (fderiv ℂ (fun x => ∑ k, A x i k * B x k j) t) h = _
  erw [fderiv_fun_sum (u := Finset.univ) (A := fun k x => A x i k * B x k j)
    (fun k _ => (differentiableAt_pi.mp (differentiableAt_pi.mp ha i) k).mul
      (differentiableAt_pi.mp (differentiableAt_pi.mp hb k) j))]
  simp only [sum_apply, fderiv_fun_mul
    (differentiableAt_pi.mp (differentiableAt_pi.mp ha i) _)
    (differentiableAt_pi.mp (differentiableAt_pi.mp hb _) j), add_apply,
    smul_apply, smul_eq_mul, he A ha, he B hb,
    Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _


theorem b66_matrix_inv_diff (A : (Fin 10 → ℂ) → Matrix (Fin 3) (Fin 3) ℂ)
    (t : Fin 10 → ℂ) (ha : DifferentiableAt ℂ A t) (hi : IsUnit (A t)) :
    DifferentiableAt ℂ (fun x => (A x)⁻¹) t := by
  have hd : DifferentiableAt ℂ
      (fun M : Fin 3 → Fin 3 → ℂ => fun i j => (Matrix.of M)⁻¹ i j)
      (fun i j => A t i j) := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    have hh := b64_analytic_inv_entry (fun M : Fin 3 → Fin 3 → ℂ => Matrix.of M)
      {M | IsUnit (Matrix.of M)} (fun i j => by
        exact ((ContinuousLinearMap.proj j : (Fin 3 → ℂ) →L[ℂ] ℂ).comp
          (ContinuousLinearMap.proj i :
            (Fin 3 → Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ))).analyticOnNhd _)
      (fun _ h => h) i j
    exact (hh (A t) hi).differentiableAt
  have ha' : DifferentiableAt ℂ (fun x i j => A x i j) t := by
    exact differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j =>
      differentiableAt_pi.mp (differentiableAt_pi.mp ha i) j
  have hd' := hd.comp t ha'
  exact differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j =>
    differentiableAt_pi.mp (differentiableAt_pi.mp hd' i) j

theorem b66_flatten_diff (A : (Fin 10 → ℂ) → Matrix (Fin 3) (Fin 3) ℂ)
    (t : Fin 10 → ℂ) (ha : DifferentiableAt ℂ A t) :
    DifferentiableAt ℂ (fun x => b60c_matrixCoordinates (A x)) t := by
  apply differentiableAt_pi.mpr
  intro k
  exact differentiableAt_pi.mp (differentiableAt_pi.mp ha _) _

theorem b66_flatten_fderiv (A : (Fin 10 → ℂ) → Matrix (Fin 3) (Fin 3) ℂ)
    (t h : Fin 10 → ℂ) (ha : DifferentiableAt ℂ A t) :
    fderiv ℂ (fun x => b60c_matrixCoordinates (A x)) t h =
      b60c_matrixCoordinates (fderiv ℂ A t h) := by
  ext k
  rw [show (fderiv ℂ (fun x => b60c_matrixCoordinates (A x)) t h) k =
    fderiv ℂ (fun x => b60c_matrixCoordinates (A x) k) t h from
      (congrArg (fun L => L h) (fderiv_apply (b66_flatten_diff A t ha) k)).symm]
  simp only [b60c_matrixCoordinates]
  rw [fderiv_apply (differentiableAt_pi.mp ha _) _, fderiv_apply ha _]
  rfl

theorem b66_fderiv_graphCoord_aux (u : (Fin 10 → ℂ) → Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (t₀ : Fin 10 → ℂ)
    (hh : DifferentiableAt ℂ (fun t => b64_headBlock (u t)) t₀)
    (ht : DifferentiableAt ℂ (fun t => b64_tailBlock (u t)) t₀)
    (hi : IsUnit (b64_headBlock (u t₀))) :
    DifferentiableAt ℂ (fun t => b64_graphCoord (u t)) t₀ ∧
    ∀ h, fderiv ℂ (fun t => b64_graphCoord (u t)) t₀ h =
      b60c_matrixCoordinates (b66_graphVariation u t₀ h) := by
  let A := fun t => b64_headBlock (u t)
  let B := fun t => b64_tailBlock (u t)
  let Z := fun t => B t * (A t)⁻¹
  have hZ : DifferentiableAt ℂ Z t₀ :=
    b66_matrix_mul_diff B _ t₀ ht (b66_matrix_inv_diff A t₀ hh hi)
  refine ⟨b66_flatten_diff Z t₀ hZ, ?_⟩
  intro h
  have hc : ContinuousAt (fun t => (A t).det) t₀ := by
    have hcA := hh.continuousAt
    have he : ∀ i j, ContinuousAt (fun t => A t i j) t₀ := fun i j =>
      (continuousAt_pi.mp (continuousAt_pi.mp hcA i) j)
    simp only [Matrix.det_apply']
    fun_prop
  have hn := hc.eventually_ne ((Matrix.isUnit_iff_isUnit_det _).mp hi).ne_zero
  have heq : (fun t => Z t * A t) =ᶠ[𝓝 t₀] B := by
    filter_upwards [hn] with t ht
    exact Matrix.nonsing_inv_mul_cancel_right (A t) (B t) (isUnit_iff_ne_zero.mpr ht)
  have hd := congrArg (fun L => L h) (heq.fderiv_eq (𝕜 := ℂ))
  rw [b66_matrix_mul_fderiv Z A t₀ h hZ hh] at hd
  have hs : fderiv ℂ Z t₀ h =
      (fderiv ℂ B t₀ h - Z t₀ * fderiv ℂ A t₀ h) * (A t₀)⁻¹ := by
    rw [← hd, add_sub_cancel_left]
    exact (Matrix.mul_nonsing_inv_cancel_right _ _
      ((Matrix.isUnit_iff_isUnit_det _).mp hi)).symm
  rw [show (fun t => b64_graphCoord (u t)) =
    (fun t => b60c_matrixCoordinates (Z t)) from rfl, b66_flatten_fderiv Z t₀ h hZ, hs]
  simp only [b66_graphVariation, b64_graphCoord, b60c_toMat_matrixCoordinates]
  rfl

theorem b66_graphCoord_toMatrix_aux (u : (Fin 10 → ℂ) → Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (t₀ : Fin 10 → ℂ)
    (hh : DifferentiableAt ℂ (fun t => b64_headBlock (u t)) t₀)
    (ht : DifferentiableAt ℂ (fun t => b64_tailBlock (u t)) t₀)
    (hi : IsUnit (b64_headBlock (u t₀))) :
    LinearMap.toMatrix' (fderiv ℂ (fun t => b64_graphCoord (u t)) t₀).toLinearMap =
      b66_variationMatrix u t₀ := by
  ext i j
  exact congrFun ((b66_fderiv_graphCoord_aux u t₀ hh ht hi).2 (Pi.single j 1)) i

theorem b66_coordOf_local_derivative_aux {ι : Type*} [Fintype ι]
    (u : (Fin 10 → ℂ) → ι → ℂ ⊗[ℤ] b60_Lattice)
    (F : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice))
    (W : Set (Fin 10 → ℂ)) (hW : IsOpen W)
    (hu : ∀ k p, AnalyticOnNhd ℂ (fun t => b60c_eigenBasis.repr (u t k) p) W)
    (hs : ∀ t ∈ W, Submodule.span ℂ (Set.range (u t)) = F t)
    (hc : ∀ t ∈ W, ∃ z, F t = b60_F z)
    (t₀ : Fin 10 → ℂ) (h₀ : t₀ ∈ W) :
    ∃ W' : Set (Fin 10 → ℂ), IsOpen W' ∧ t₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ σ : Fin 3 → ι,
        (∀ t ∈ W', IsUnit (b64_headBlock (fun j => b64_negPart (u t (σ j)))) ∧
          Submodule.span ℂ (Set.range (fun j => b64_negPart (u t (σ j)))) =
            F t ⊓ b64_Eminus) ∧
        ∀ h, fderiv ℂ (fun t => b64_coordOf (F t)) t₀ h =
          b60c_matrixCoordinates
            (b66_graphVariation (fun t j => b64_negPart (u t (σ j))) t₀ h) := by
  obtain ⟨W', hopen, hmem, hsub, σ, hσ⟩ := b64_local_subframe u F W hW
    (fun k p => (hu k p).continuousOn) hs hc t₀ h₀
  let v := fun t j => b64_negPart (u t (σ j))
  have hh : DifferentiableAt ℂ (fun t => b64_headBlock (v t)) t₀ := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    simpa only [v, b64_headBlock, Matrix.of_apply, b64_negPart_repr, ite_true] using
      (hu (σ j) (0, Fin.castAdd 3 i) t₀ h₀).differentiableAt
  have ht : DifferentiableAt ℂ (fun t => b64_tailBlock (v t)) t₀ := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    simpa only [v, b64_tailBlock, Matrix.of_apply, b64_negPart_repr, ite_true] using
      (hu (σ j) (0, Fin.natAdd 3 i) t₀ h₀).differentiableAt
  have heq : (fun t => b64_coordOf (F t)) =ᶠ[𝓝 t₀] (fun t => b64_graphCoord (v t)) := by
    filter_upwards [hopen.mem_nhds hmem] with t ht
    obtain ⟨z, hz⟩ := hc t (hsub ht)
    have hspan : Submodule.span ℂ (Set.range (v t)) =
        Submodule.span ℂ (Set.range (b64_negFrame z)) := by
      rw [(hσ t ht).2, hz, b64_negFrame_span]
    rw [hz, b64_coordOf_eq, (b64_graphCoord_of_span z _ hspan).2]
  refine ⟨W', hopen, hmem, hsub, σ, hσ, ?_⟩
  intro h
  rw [heq.fderiv_eq (𝕜 := ℂ)]
  exact (b66_fderiv_graphCoord_aux v t₀ hh ht (hσ t₀ hmem).1).2 h

theorem b66_period_frame_derivative_aux (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (v : (Fin 10 → ℂ) → Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (t₀ : Fin 10 → ℂ) (h₀ : t₀ ∈ b6t_polydisc mr_base)
    (hv : ∀ᶠ t in 𝓝 t₀, Submodule.span ℂ (Set.range (v t)) =
      b64c_markedF _ m (rf8_transportedFamily R s) t ⊓ b64_Eminus) :
    fderiv ℂ (b64i_period R s m) t₀ =
      fderiv ℂ (fun t => b64_graphCoord (v t)) t₀ := by
  apply Filter.EventuallyEq.fderiv_eq (𝕜 := ℂ)
  filter_upwards [hv, (rf5_polydisc_isOpen mr_base).mem_nhds h₀] with t ht htD
  have hs : Submodule.span ℂ (Set.range (v t)) =
      Submodule.span ℂ (Set.range (b64_negFrame (b64i_period R s m t))) := by
    rw [ht, ← (b64i_chart R s m hJ hpol t htD).2, b64_negFrame_span]
  exact (b64_graphCoord_of_span _ _ hs).2.symm

theorem b66_period_toMatrix_aux (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (v : (Fin 10 → ℂ) → Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (t₀ : Fin 10 → ℂ) (h₀ : t₀ ∈ b6t_polydisc mr_base)
    (hv : ∀ᶠ t in 𝓝 t₀, Submodule.span ℂ (Set.range (v t)) =
      b64c_markedF _ m (rf8_transportedFamily R s) t ⊓ b64_Eminus)
    (hh : DifferentiableAt ℂ (fun t => b64_headBlock (v t)) t₀)
    (ht : DifferentiableAt ℂ (fun t => b64_tailBlock (v t)) t₀) :
    LinearMap.toMatrix' (fderiv ℂ (b64i_period R s m) t₀).toLinearMap =
      b66_variationMatrix v t₀ := by
  have hs : Submodule.span ℂ (Set.range (v t₀)) =
      Submodule.span ℂ (Set.range (b64_negFrame (b64i_period R s m t₀))) := by
    rw [hv.self_of_nhds, ← (b64i_chart R s m hJ hpol t₀ h₀).2, b64_negFrame_span]
  have hi := (b64_graphCoord_of_span _ _ hs).1
  rw [b66_period_frame_derivative_aux R s m hJ hpol v t₀ h₀ hv]
  exact b66_graphCoord_toMatrix_aux v t₀ hh ht hi

end HodgeLean.Foundations.Program
