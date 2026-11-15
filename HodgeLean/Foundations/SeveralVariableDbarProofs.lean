import HodgeLean.Foundations.SeveralVariableDbarDefs

/-! # Proof obligations for several-variable ∂̄ -/

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace HodgeLean.Foundations

private lemma dbar_coord_congr_of_eventuallyEq {n : ℕ} {j : Fin n}
    {f g : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (h : f =ᶠ[𝓝 z] g) :
    dbar_coord n j f z = dbar_coord n j g z := by
  unfold dbar_coord
  rw [h.fderiv_eq]

/-- Smooth partition of unity splits an analytic additive cocycle.
Source: Gunning--Rossi, Chapter VIII, the partition-of-unity construction of Cousin I. -/
theorem dbar_smooth_split_aux (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (a : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (ha : ∀ p q, AnalyticOnNhd ℂ (a p q) (U p ∩ U q))
    (hcocycle : ∀ p q r z, z ∈ U p ∩ U q ∩ U r →
      a p q z + a q r z = a p r z) :
    ∃ b : (Fin n → ℂ) → (Fin n → ℂ) → ℂ,
      (∀ p z, z ∈ U p → ContDiffAt ℝ ∞ (b p) z) ∧
      (∀ p q z, z ∈ U p ∩ U q → a p q z = b q z - b p z) := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Fin n → ℂ)) isClosed_univ U hU
    (fun z _ ↦ mem_iUnion.mpr ⟨z, hcover z⟩)
  let b : (Fin n → ℂ) → (Fin n → ℂ) → ℂ :=
    fun p z ↦ ∑ᶠ r, ρ r z • a r p z
  refine ⟨b, ?_, ?_⟩
  · intro p z hz
    apply ρ.contDiffAt_finsum
    intro r hr
    exact (ha r p z ⟨hρ r hr, hz⟩).contDiffAt.restrict_scalars ℝ
  · intro p q z hz
    change a p q z = (∑ᶠ r, ρ r z • a r q z) - ∑ᶠ r, ρ r z • a r p z
    rw [← ρ.sum_finsupport_smul_eq_finsum z (fun r ↦ a r q),
      ← ρ.sum_finsupport_smul_eq_finsum z (fun r ↦ a r p), ← Finset.sum_sub_distrib]
    calc
      a p q z = (∑ r ∈ ρ.finsupport z, ρ r z) • a p q z := by
        rw [ρ.sum_finsupport z (mem_univ z), one_smul]
      _ = ∑ r ∈ ρ.finsupport z, ρ r z • a p q z := Finset.sum_smul
      _ = ∑ r ∈ ρ.finsupport z, (ρ r z • a r q z - ρ r z • a r p z) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrU : z ∈ U r := hρ r (subset_closure ((ρ.mem_finsupport z).mp hr))
        rw [← smul_sub, ← hcocycle r p q z ⟨⟨hrU, hz.1⟩, hz.2⟩,
          add_sub_cancel_left]

private lemma dbar_coord_contDiffAt (n : ℕ) (j : Fin n)
    {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (dbar_coord n j f) z := by
  unfold dbar_coord
  fun_prop

private lemma fderiv_dbar_coord (n : ℕ) (j : Fin n)
    {f : (Fin n → ℂ) → ℂ} {z v : Fin n → ℂ} (hf : ContDiffAt ℝ ∞ f z) :
    fderiv ℝ (dbar_coord n j f) z v =
      (fderiv ℝ (fderiv ℝ f) z v (Pi.single j 1) +
        Complex.I * fderiv ℝ (fderiv ℝ f) z v (Pi.single j Complex.I)) / 2 := by
  let D := fderiv ℝ (fderiv ℝ f) z
  have hD : HasFDerivAt (fderiv ℝ f) D z :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
  have h1 := hD.clm_apply (hasFDerivAt_const (x := z) (c := Pi.single j (1 : ℂ)))
  have hI := hD.clm_apply
    (hasFDerivAt_const (x := z) (c := Pi.single j Complex.I))
  have hsum := h1.add (hI.const_mul Complex.I)
  have hfinal := hsum.mul_const (2 : ℂ)⁻¹
  have hh := congrArg (fun L : (Fin n → ℂ) →L[ℝ] ℂ ↦ L v) hfinal.fderiv
  change fderiv ℝ (fun x ↦ (fderiv ℝ f x (Pi.single j 1) +
    Complex.I * fderiv ℝ f x (Pi.single j Complex.I)) / 2) z v = _
  have hh' := hh
  simp [D, ContinuousLinearMap.flip_apply, div_eq_mul_inv] at hh'
  simp only [div_eq_mul_inv]
  rw [hh']
  ring

private lemma dbar_coord_comm (n : ℕ) (j k : Fin n)
    {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (hf : ContDiffAt ℝ ∞ f z) :
    dbar_coord n k (dbar_coord n j f) z = dbar_coord n j (dbar_coord n k f) z := by
  change (fderiv ℝ (dbar_coord n j f) z (Pi.single k 1) +
    Complex.I * fderiv ℝ (dbar_coord n j f) z (Pi.single k Complex.I)) / 2 =
    (fderiv ℝ (dbar_coord n k f) z (Pi.single j 1) +
    Complex.I * fderiv ℝ (dbar_coord n k f) z (Pi.single j Complex.I)) / 2
  rw [fderiv_dbar_coord n j hf, fderiv_dbar_coord n j hf,
    fderiv_dbar_coord n k hf, fderiv_dbar_coord n k hf]
  have hs := hf.isSymmSndFDerivAt (by simp)
  rw [hs (Pi.single k 1) (Pi.single j 1),
    hs (Pi.single k Complex.I) (Pi.single j 1),
    hs (Pi.single k 1) (Pi.single j Complex.I),
    hs (Pi.single k Complex.I) (Pi.single j Complex.I)]
  ring

/-- The anchored coefficients glue smoothly and are closed.
Source: Gunning--Rossi, Chapter VIII, Dolbeault construction; symmetry of second derivatives. -/
theorem dbar_glue_aux (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (a : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (ha : ∀ p q, AnalyticOnNhd ℂ (a p q) (U p ∩ U q))
    (c : (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hc : ∀ p z, z ∈ U p → ContDiffAt ℝ ∞ (c p) z)
    (he : ∀ p q z, z ∈ U p ∩ U q → a p q z = c q z - c p z) :
    (∀ j, ContDiff ℝ ∞ (dbar_glued n c j)) ∧
      (∀ p j z, z ∈ U p → dbar_glued n c j z = dbar_coord n j (c p) z) ∧
      (∀ j k z, dbar_coord n k (dbar_glued n c j) z =
        dbar_coord n j (dbar_glued n c k) z) := by
  have hlocal : ∀ p j z, z ∈ U p →
      dbar_glued n c j z = dbar_coord n j (c p) z := by
    intro p j z hz
    have hzz := hcover z
    have hopen := (hU p).inter (hU z)
    have hevent : c z =ᶠ[𝓝 z] fun y ↦ a p z y + c p y := by
      filter_upwards [hopen.mem_nhds ⟨hz, hzz⟩] with y hy
      rw [he p z y hy]
      ring
    unfold dbar_glued dbar_coord
    rw [Filter.EventuallyEq.fderiv_eq hevent]
    have haC : DifferentiableAt ℂ (a p z) z :=
      (ha p z z ⟨hz, hzz⟩).differentiableAt
    have haR : DifferentiableAt ℝ (a p z) z :=
      DifferentiableAt.restrictScalars (𝕜 := ℝ) haC
    have hcR := (hc p z hz).differentiableAt (by simp)
    rw [fderiv_fun_add haR hcR]
    simp only [ContinuousLinearMap.add_apply]
    have hz0 : dbar_coord n j (a p z) z = 0 := by
      unfold dbar_coord
      rw [haC.fderiv_restrictScalars ℝ]
      have heq : Pi.single j Complex.I = Complex.I • Pi.single j (1 : ℂ) := by
        ext i
        simp [Pi.single_apply]
      change ((fderiv ℂ (a p z) z) (Pi.single j 1) +
        Complex.I * (fderiv ℂ (a p z) z) (Pi.single j Complex.I)) / 2 = 0
      rw [heq, map_smul]
      simp only [smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
      ring
    unfold dbar_coord at hz0
    linear_combination hz0
  refine ⟨?_, hlocal, ?_⟩
  · intro j
    rw [contDiff_iff_contDiffAt]
    intro z
    have hz := hcover z
    have hevent : dbar_glued n c j =ᶠ[𝓝 z] dbar_coord n j (c z) :=
      Filter.Eventually.mono ((hU z).mem_nhds hz) (fun y hy ↦ hlocal z j y hy)
    exact (dbar_coord_contDiffAt n j (hc z z hz)).congr_of_eventuallyEq hevent
  · intro j k z
    have hz := hcover z
    have hej : dbar_glued n c j =ᶠ[𝓝 z] dbar_coord n j (c z) :=
      Filter.Eventually.mono ((hU z).mem_nhds hz) (fun y hy ↦ hlocal z j y hy)
    have hek : dbar_glued n c k =ᶠ[𝓝 z] dbar_coord n k (c z) :=
      Filter.Eventually.mono ((hU z).mem_nhds hz) (fun y hy ↦ hlocal z k y hy)
    unfold dbar_coord
    rw [Filter.EventuallyEq.fderiv_eq hej, Filter.EventuallyEq.fderiv_eq hek]
    exact dbar_coord_comm n j k (hc z z hz)

private theorem dbar_transform_contDiff (n : ℕ) (j : Fin n)
    (f : (Fin n → ℂ) → ℂ) (hf : ContDiff ℝ ∞ f)
    (R : ℝ) (hs : ∀ z, R ≤ ‖z j‖ → f z = 0) :
    ContDiff ℝ ∞ (dbar_transform n j f) := by
  let g : (Fin n → ℂ) → ℂ → ℂ := fun z w ↦ f (Function.update z j w)
  have hg : ContDiff ℝ ∞ (Function.uncurry g) := by
    apply hf.comp
    apply contDiff_pi.mpr
    intro k
    by_cases hkj : k = j
    · subst k
      simpa [Function.uncurry_apply_pair, g, Function.update] using
        (contDiff_snd : ContDiff ℝ ∞ (fun p : (Fin n → ℂ) × ℂ ↦ p.2))
    · convert (contDiff_apply ℝ ℂ k).comp contDiff_fst using 1
      funext x
      simp [Function.uncurry_apply_pair, g, Function.update, hkj, ne_comm.mp hkj]
  have hconv : ContDiff ℝ ∞
      (fun z : Fin n → ℂ ↦ convolution (g z) (fun w : ℂ ↦ w⁻¹)
        (ContinuousLinearMap.mul ℝ ℂ) volume (z j)) := by
    rw [← contDiffOn_univ]
    apply contDiffOn_convolution_left_with_param_comp
      (L := ContinuousLinearMap.mul ℝ ℂ)
      (f := fun w : ℂ ↦ w⁻¹) (g := g) (k := Metric.closedBall 0 R)
      (s := Set.univ) (contDiff_apply ℝ ℂ j).contDiffOn isOpen_univ
      (isCompact_closedBall (0 : ℂ) R)
    · intro z w _ hw
      apply hs (Function.update z j w)
      have hw' : R < ‖w‖ := by
        simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hw
      simpa [Function.update] using hw'.le
    · exact spec_locallyIntegrable_inv_aux
    · change ContDiffOn ℝ ∞ (Function.uncurry g) (Set.univ ×ˢ Set.univ)
      simpa only [Set.univ_prod_univ] using hg.contDiffOn
  change ContDiff ℝ ∞ (fun z ↦ cauchyTransform (g z) (z j))
  simp_rw [cauchyTransform_eq_convolution]
  exact contDiff_const.mul hconv

private theorem dbar_coord_eq_wirtinger_slice (n : ℕ) (j : Fin n)
    (F : (Fin n → ℂ) → ℂ) (hF : Differentiable ℝ F) (z : Fin n → ℂ) :
    dbar_coord n j F z = wirtingerDbar (fun w ↦ F (Function.update z j w)) (z j) := by
  have hz : Function.update z j (z j) = z := by
    funext k
    by_cases hkj : k = j <;> simp [Function.update, hkj]
  have hd := ((hF (Function.update z j (z j))).hasFDerivAt.comp (z j)
    (hasFDerivAt_update (i := j) z (z j))).fderiv
  rw [hz] at hd
  have hd' : fderiv ℝ (fun w ↦ F (Function.update z j w)) (z j) =
      fderiv ℝ F z ∘L ContinuousLinearMap.pi
        (Pi.single j (ContinuousLinearMap.id ℝ ℂ)) := by
    simpa only [Function.comp_def] using hd
  have hpi (a : ℂ) : (fun i ↦ (if i = j then ContinuousLinearMap.id ℝ ℂ else 0) a) =
      Pi.single j a := by
    funext i
    by_cases hij : i = j <;> simp [Pi.single_apply, hij]
  rw [dbar_coord, wirtingerDbar, hd', antiLinearPart_apply]
  simp [ContinuousLinearMap.comp_apply, Pi.single_apply]
  rw [hpi, hpi]
  ring

private def dbar_updateCLM (n : ℕ) (j : Fin n) :
    ((Fin n → ℂ) × ℂ) →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi (fun i ↦ if i = j then ContinuousLinearMap.snd ℝ _ _
    else (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _))

private theorem dbar_updateCLM_apply (n : ℕ) (j : Fin n) (z : Fin n → ℂ) (w : ℂ) :
    dbar_updateCLM n j (z, w) = Function.update z j w := by
  ext i
  simp only [dbar_updateCLM, ContinuousLinearMap.pi_apply, Function.update_apply]
  split <;> rfl

private theorem dbar_updateCLM_transverse (n : ℕ) (j k : Fin n) (hk : k ≠ j) (a : ℂ) :
    dbar_updateCLM n j (Pi.single k a, 0) = Pi.single k a := by
  rw [dbar_updateCLM_apply]
  apply Function.update_eq_self_iff.mpr
  simp only [Pi.single_apply, if_neg (Ne.symm hk)]

private theorem dbar_slice_fderiv (n : ℕ) (j : Fin n)
    (f : (Fin n → ℂ) → ℂ) (hf : ContDiff ℝ ∞ f) (q : (Fin n → ℂ) × ℂ) :
    fderiv ℝ (f ∘ dbar_updateCLM n j) q =
      (fderiv ℝ f (dbar_updateCLM n j q)).comp (dbar_updateCLM n j) := by
  exact ((hf.differentiable (by simp) _).hasFDerivAt.comp q
    (dbar_updateCLM n j).hasFDerivAt).fderiv

private theorem dbar_slice_derivative_support (n : ℕ) (j : Fin n)
    (f : (Fin n → ℂ) → ℂ) (R : ℝ)
    (hs : ∀ z, R ≤ ‖z j‖ → f z = 0) (z : Fin n → ℂ) :
    HasCompactSupport (fun w : ℂ ↦ fderiv ℝ (f ∘ dbar_updateCLM n j) (z, w)) := by
  apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro w hw
  by_contra hn
  have hlt : R < ‖w‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn
  apply hw
  apply (hasFDerivAt_zero_of_eventually_const 0 _).fderiv
  have hopen : IsOpen {q : (Fin n → ℂ) × ℂ | R < ‖q.2‖} :=
    isOpen_lt continuous_const continuous_snd.norm
  filter_upwards [hopen.mem_nhds hlt] with q hq
  exact hs _ (by rw [dbar_updateCLM_apply, Function.update_self]; exact hq.le)

private theorem dbar_transform_convolution (n : ℕ) (j : Fin n)
    (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    dbar_transform n j f z = (Real.pi : ℂ)⁻¹ *
      convolution (fun w : ℂ ↦ w⁻¹) (fun w ↦ f (dbar_updateCLM n j (z, w)))
        (ContinuousLinearMap.mul ℝ ℂ) volume (z j) := by
  change cauchyTransform (fun w ↦ f (Function.update z j w)) (z j) = _
  rw [cauchyTransform_eq_convolution]
  have hsymm : (ContinuousLinearMap.mul ℝ ℂ).flip = ContinuousLinearMap.mul ℝ ℂ := by
    ext a b
    exact mul_comm b a
  rw [convolution_symm (ContinuousLinearMap.mul ℝ ℂ) hsymm]
  simp only [dbar_updateCLM_apply]

private theorem dbar_param_hasFDerivAt (n : ℕ) (j : Fin n)
    (f : (Fin n → ℂ) → ℂ) (hf : ContDiff ℝ ∞ f)
    (R : ℝ) (hs : ∀ z, R ≤ ‖z j‖ → f z = 0) (q : (Fin n → ℂ) × ℂ) :
    HasFDerivAt
      (fun p : (Fin n → ℂ) × ℂ ↦ convolution (fun w : ℂ ↦ w⁻¹)
        (fun w ↦ f (dbar_updateCLM n j (p.1, w)))
        (ContinuousLinearMap.mul ℝ ℂ) volume p.2)
      (convolution (fun w : ℂ ↦ w⁻¹)
        (fun w ↦ fderiv ℝ (f ∘ dbar_updateCLM n j) (q.1, w))
        ((ContinuousLinearMap.mul ℝ ℂ).precompR ((Fin n → ℂ) × ℂ)) volume q.2) q := by
  apply hasFDerivAt_convolution_right_with_param (ContinuousLinearMap.mul ℝ ℂ)
    (g := fun z w ↦ f (dbar_updateCLM n j (z, w)))
    (s := Set.univ) (k := Metric.closedBall 0 R) isOpen_univ
    (isCompact_closedBall (0 : ℂ) R)
  · intro z w _ hw
    apply hs
    rw [dbar_updateCLM_apply, Function.update_self]
    exact le_of_lt (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hw)
  · exact spec_locallyIntegrable_inv_aux
  · exact (hf.comp (dbar_updateCLM n j).contDiff).contDiffOn.of_le (by simp)
  · exact Set.mem_univ _

private theorem dbar_transform_transverse_fderiv (n : ℕ) (j k : Fin n) (hk : k ≠ j)
    (f : (Fin n → ℂ) → ℂ) (hf : ContDiff ℝ ∞ f)
    (R : ℝ) (hs : ∀ z, R ≤ ‖z j‖ → f z = 0) (z : Fin n → ℂ) (a : ℂ) :
    fderiv ℝ (dbar_transform n j f) z (Pi.single k a) = (Real.pi : ℂ)⁻¹ *
      convolution (fun w : ℂ ↦ w⁻¹)
        (fun w ↦ fderiv ℝ f (Function.update z j w) (Pi.single k a))
        (ContinuousLinearMap.mul ℝ ℂ) volume (z j) := by
  let D : ((Fin n → ℂ) × ℂ) →L[ℝ] ℂ :=
    convolution (fun w : ℂ ↦ w⁻¹)
      (fun w ↦ fderiv ℝ (f ∘ dbar_updateCLM n j) (z, w))
      ((ContinuousLinearMap.mul ℝ ℂ).precompR ((Fin n → ℂ) × ℂ)) volume (z j)
  have hD : HasFDerivAt (dbar_transform n j f)
      ((Real.pi : ℂ)⁻¹ • (D.comp ((ContinuousLinearMap.id ℝ _).prod
        (ContinuousLinearMap.proj j)))) z := by
    have h := ((dbar_param_hasFDerivAt n j f hf R hs (z, z j)).comp z
      ((hasFDerivAt_id (𝕜 := ℝ) z).prodMk (hasFDerivAt_apply (𝕜 := ℝ) j z))).const_mul (Real.pi : ℂ)⁻¹
    convert h using 1
    funext p
    exact dbar_transform_convolution n j f p
  rw [hD.fderiv]
  change (Real.pi : ℂ)⁻¹ * D (Pi.single k a, (Pi.single k a : Fin n → ℂ) j) = _
  have hz : (Pi.single k a : Fin n → ℂ) j = 0 := by
    simp only [Pi.single_apply, if_neg (Ne.symm hk)]
  rw [hz]
  congr 1
  rw [show D (Pi.single k a, 0) = _ from convolution_precompR_apply
    (ContinuousLinearMap.mul ℝ ℂ) spec_locallyIntegrable_inv_aux
    (dbar_slice_derivative_support n j f R hs z)
    (((hf.comp (dbar_updateCLM n j).contDiff).continuous_fderiv (by simp)).comp
      (continuous_const.prodMk continuous_id)) (z j) (Pi.single k a, 0)]
  congr 1
  funext w
  rw [dbar_slice_fderiv n j f hf, ContinuousLinearMap.comp_apply,
    dbar_updateCLM_transverse n j k hk, dbar_updateCLM_apply]

private theorem dbar_convolution_combine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℂ → E →L[ℝ] ℂ) (hc : HasCompactSupport g) (hg : Continuous g)
    (v u : E) (z : ℂ) :
    (convolution (fun w : ℂ ↦ w⁻¹) (fun w ↦ g w v)
        (ContinuousLinearMap.mul ℝ ℂ) volume z +
      Complex.I * convolution (fun w : ℂ ↦ w⁻¹) (fun w ↦ g w u)
        (ContinuousLinearMap.mul ℝ ℂ) volume z) / 2 =
    convolution (fun w : ℂ ↦ w⁻¹) (fun w ↦ (g w v + Complex.I * g w u) / 2)
      (ContinuousLinearMap.mul ℝ ℂ) volume z := by
  have hInt := hc.convolutionExists_right ((ContinuousLinearMap.mul ℝ ℂ).precompR E)
    spec_locallyIntegrable_inv_aux hg z
  have hi (a : E) : Integrable (fun t : ℂ ↦ t⁻¹ * g (z - t) a) volume :=
    (ContinuousLinearMap.apply ℝ ℂ a).integrable_comp hInt
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_const_mul, ← integral_add (hi v) ((hi u).const_mul Complex.I),
    ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

private theorem dbar_transform_transverse (n : ℕ) (j k : Fin n) (hk : k ≠ j)
    (f : (Fin n → ℂ) → ℂ) (hf : ContDiff ℝ ∞ f)
    (R : ℝ) (hs : ∀ z, R ≤ ‖z j‖ → f z = 0) (z : Fin n → ℂ) :
    dbar_coord n k (dbar_transform n j f) z =
      dbar_transform n j (dbar_coord n k f) z := by
  let g : ℂ → ((Fin n → ℂ) × ℂ) →L[ℝ] ℂ :=
    fun w ↦ fderiv ℝ (f ∘ dbar_updateCLM n j) (z, w)
  have hc : HasCompactSupport g := dbar_slice_derivative_support n j f R hs z
  have hg : Continuous g :=
    ((hf.comp (dbar_updateCLM n j).contDiff).continuous_fderiv (by simp)).comp
      (continuous_const.prodMk continuous_id)
  have he (a : ℂ) : (fun w ↦ g w (Pi.single k a, 0)) =
      (fun w ↦ fderiv ℝ f (Function.update z j w) (Pi.single k a)) := by
    funext w
    dsimp only [g]
    rw [dbar_slice_fderiv n j f hf, ContinuousLinearMap.comp_apply,
      dbar_updateCLM_transverse n j k hk, dbar_updateCLM_apply]
  have hd : (fun w ↦ (g w (Pi.single k 1, 0) +
      Complex.I * g w (Pi.single k Complex.I, 0)) / 2) =
      (fun w ↦ dbar_coord n k f (dbar_updateCLM n j (z, w))) := by
    funext w
    rw [congrFun (he 1) w, congrFun (he Complex.I) w, dbar_updateCLM_apply]
    rfl
  have hcomb := dbar_convolution_combine g hc hg (Pi.single k 1, 0)
    (Pi.single k Complex.I, 0) (z j)
  rw [hd, he 1, he Complex.I] at hcomb
  rw [dbar_coord, dbar_transform_transverse_fderiv n j k hk f hf R hs z 1,
    dbar_transform_transverse_fderiv n j k hk f hf R hs z Complex.I,
    dbar_transform_convolution, ← hcomb]
  ring

/-- The coordinate Cauchy transform is smooth and commutes with transverse derivatives.
Source: Hörmander, 3rd ed., §2.3, Cauchy transform with parameters;
Mathlib, hasFDerivAt_integral_of_dominated_of_fderiv_le. -/
theorem dbar_transform_calculus_aux (n : ℕ) (j : Fin n)
    (f : (Fin n → ℂ) → ℂ) (hf : ContDiff ℝ ∞ f)
    (R : ℝ) (hR : 0 < R) (hs : ∀ z, R ≤ ‖z j‖ → f z = 0) :
    ContDiff ℝ ∞ (dbar_transform n j f) ∧
      (∀ k, k ≠ j → ∀ z, dbar_coord n k (dbar_transform n j f) z =
        dbar_transform n j (dbar_coord n k f) z) := by
  clear hR
  exact ⟨dbar_transform_contDiff n j f hf R hs,
    fun k hk z ↦ dbar_transform_transverse n j k hk f hf R hs z⟩

/-- The coordinate Cauchy transform solves the selected component equation.
Source: Hörmander, 3rd ed., Theorem 1.2.2;
HodgeLean.Foundations.spec_wirtingerDbar_cauchyTransform. -/
theorem dbar_transform_equation_aux (n : ℕ) (j : Fin n)
    (f : (Fin n → ℂ) → ℂ) (hf : ContDiff ℝ ∞ f)
    (R : ℝ) (hR : 0 < R) (hs : ∀ z, R ≤ ‖z j‖ → f z = 0) :
    ∀ z, dbar_coord n j (dbar_transform n j f) z = f z := by
  have hT := dbar_transform_contDiff n j f hf R hs
  intro z
  let g : ℂ → ℂ := fun w ↦ f (Function.update z j w)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_update ∞ z j)
  have hgc : HasCompactSupport g := by
    apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset (isClosed_tsupport g)
    apply closure_minimal _ Metric.isClosed_closedBall
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hn
    exact hw (hs (Function.update z j w) (by simpa [Function.update] using le_of_not_ge hn))
  rw [dbar_coord_eq_wirtinger_slice n j _ (hT.differentiable (by simp)) z]
  have heq : (fun w ↦ dbar_transform n j f (Function.update z j w)) = cauchyTransform g := by
    funext w
    simp [dbar_transform, g, Function.update]
  rw [heq, spec_wirtingerDbar_cauchyTransform (hg.of_le (by simp)) hgc]
  simp [g, Function.update]

private lemma dbar_coord_comm_c {n : ℕ} (j k : Fin n)
    (u : (Fin n → ℂ) → ℂ) (hu : ContDiff ℝ ∞ u) (z : Fin n → ℂ) :
    dbar_coord n j (dbar_coord n k u) z = dbar_coord n k (dbar_coord n j u) z := by
  unfold dbar_coord
  have hdiff : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.contDiffAt.fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero
  simp only [div_eq_mul_inv]
  rw [fderiv_mul_const (by fun_prop)]
  rw [fderiv_mul_const (by fun_prop)]
  simp only [ContinuousLinearMap.smul_apply]
  rw [show (fun z ↦ (fderiv ℝ u z) (Pi.single k 1) +
      Complex.I * (fderiv ℝ u z) (Pi.single k Complex.I)) =
      (fun z ↦ (fderiv ℝ u z) (Pi.single k 1)) +
        (fun z ↦ Complex.I * (fderiv ℝ u z) (Pi.single k Complex.I)) by rfl]
  rw [fderiv_add (by fun_prop) (by fun_prop), fderiv_const_mul (by fun_prop)]
  rw [show (fun z ↦ (fderiv ℝ u z) (Pi.single j 1) +
      Complex.I * (fderiv ℝ u z) (Pi.single j Complex.I)) =
      (fun z ↦ (fderiv ℝ u z) (Pi.single j 1)) +
        (fun z ↦ Complex.I * (fderiv ℝ u z) (Pi.single j Complex.I)) by rfl]
  rw [fderiv_add (by fun_prop) (by fun_prop), fderiv_const_mul (by fun_prop)]
  simp only [ContinuousLinearMap.add_apply]
  rw [fderiv_clm_apply hdiff (by fun_prop), fderiv_clm_apply hdiff (by fun_prop),
    fderiv_clm_apply hdiff (by fun_prop), fderiv_clm_apply hdiff (by fun_prop)]
  simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_zero, ContinuousLinearMap.smul_apply,
    add_zero, zero_add]
  have hs := (hu.contDiffAt : ContDiffAt ℝ ∞ u z).isSymmSndFDerivAt
    (show minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) by simp)
  rw [hs.eq (Pi.single k 1) (Pi.single j 1),
    hs.eq (Pi.single k Complex.I) (Pi.single j 1),
    hs.eq (Pi.single k 1) (Pi.single j Complex.I),
    hs.eq (Pi.single k Complex.I) (Pi.single j Complex.I)]
  ring

private lemma dbar_coord_add {n : ℕ} (j : Fin n) (f g : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbar_coord n j (f + g) z = dbar_coord n j f z + dbar_coord n j g z := by
  unfold dbar_coord
  rw [fderiv_add hf hg]
  simp only [ContinuousLinearMap.add_apply, Pi.add_apply]
  ring

private lemma dbar_coord_sub {n : ℕ} (j : Fin n) (f g : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbar_coord n j (f - g) z = dbar_coord n j f z - dbar_coord n j g z := by
  unfold dbar_coord
  rw [fderiv_sub hf hg]
  simp only [ContinuousLinearMap.sub_apply, Pi.sub_apply]
  ring

private lemma dbar_coord_mul {n : ℕ} (j : Fin n) (f g : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbar_coord n j (fun y ↦ f y * g y) z =
      f z * dbar_coord n j g z + dbar_coord n j f z * g z := by
  unfold dbar_coord
  rw [show (fun y ↦ f y * g y) = f * g by rfl]
  rw [fderiv_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private lemma dbar_coord_apply_ne {n : ℕ} (j k : Fin n) (hjk : j ≠ k)
    (b : ℂ → ℝ) (hb : ContDiff ℝ ∞ b) (z : Fin n → ℂ) :
    dbar_coord n j (fun y ↦ (b (y k) : ℂ)) z = 0 := by
  unfold dbar_coord
  have ha : DifferentiableAt ℝ (fun y : Fin n → ℂ ↦ b (y k)) z :=
    (hb.differentiable (by simp)).differentiableAt.comp z (by fun_prop)
  have h1 : fderiv ℝ (fun y : Fin n → ℂ ↦ (b (y k) : ℂ)) z (Pi.single j 1) = 0 := by
    rw [show (fun y : Fin n → ℂ ↦ (b (y k) : ℂ)) =
      (fun x : ℝ ↦ (x : ℂ)) ∘ (fun y ↦ b (y k)) by rfl]
    rw [fderiv_comp z (by fun_prop) ha, ContinuousLinearMap.comp_apply]
    rw [show (fun y : Fin n → ℂ ↦ b (y k)) = b ∘ (fun y ↦ y k) by rfl,
      fderiv_comp z (hb.differentiable (by simp) |>.differentiableAt) (by fun_prop),
      ContinuousLinearMap.comp_apply]
    rw [(hasFDerivAt_apply k z).fderiv]
    simp [Pi.single_apply, hjk]
  have hI : fderiv ℝ (fun y : Fin n → ℂ ↦ (b (y k) : ℂ)) z
      (Pi.single j Complex.I) = 0 := by
    rw [show (fun y : Fin n → ℂ ↦ (b (y k) : ℂ)) =
      (fun x : ℝ ↦ (x : ℂ)) ∘ (fun y ↦ b (y k)) by rfl]
    rw [fderiv_comp z (by fun_prop) ha, ContinuousLinearMap.comp_apply]
    rw [show (fun y : Fin n → ℂ ↦ b (y k)) = b ∘ (fun y ↦ y k) by rfl,
      fderiv_comp z (hb.differentiable (by simp) |>.differentiableAt) (by fun_prop),
      ContinuousLinearMap.comp_apply]
    rw [(hasFDerivAt_apply k z).fderiv]
    simp [Pi.single_apply, hjk]
  rw [h1, hI]
  ring

/-- One coordinate correction preserves the previously solved components on a smaller polydisc.
Source: Hörmander, 3rd ed., §2.3, successive Cauchy transforms; Gunning--Rossi, I.D. -/
theorem dbar_eliminate_coordinate_aux (n : ℕ) (k : Fin n)
    (w : Fin n → (Fin n → ℂ) → ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hw : ∀ j z, z ∈ Metric.ball 0 R → ContDiffAt ℝ ∞ (w j) z)
    (hclosed : ∀ j l z, z ∈ Metric.ball 0 R →
      dbar_coord n l (w j) z = dbar_coord n j (w l) z)
    (u : (Fin n → ℂ) → ℂ) (hu : ContDiff ℝ ∞ u)
    (hprev : ∀ j : Fin n, j.val < k.val → ∀ z, z ∈ Metric.ball 0 R →
      dbar_coord n j u z = w j z) :
    ∃ v : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ v ∧
      ∀ j : Fin n, j.val ≤ k.val → ∀ z, z ∈ Metric.ball 0 r →
        dbar_coord n j v z = w j z := by
  let s : ℝ := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  let b : ContDiffBump (0 : ℂ) :=
    { rIn := r, rOut := s, rIn_pos := hr, rIn_lt_rOut := hrs }
  let χ : (Fin n → ℂ) → ℝ := fun z ↦ ∏ i, b (z i)
  let f : (Fin n → ℂ) → ℂ := fun z ↦ χ z • (w k z - dbar_coord n k u z)
  let q := dbar_transform n k f
  have hb : ContDiff ℝ ∞ (b : ℂ → ℝ) := b.contDiff
  have hχ : ContDiff ℝ ∞ χ := by
    dsimp [χ]
    fun_prop
  have hres : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) R,
      ContDiffAt ℝ ∞ (fun z ↦ w k z - dbar_coord n k u z) z := by
    intro z hz
    apply (hw k z hz).sub
    unfold dbar_coord
    fun_prop
  have hf : ContDiff ℝ ∞ f := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ Metric.ball (0 : Fin n → ℂ) R
    · exact (hχ.contDiffAt.smul (hres z hz))
    · have hRnorm : R ≤ ‖z‖ := by
        rw [Metric.mem_ball, dist_zero_right] at hz
        exact le_of_not_gt hz
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ
        (⟨k, Finset.mem_univ k⟩) (fun i ↦ ‖z i‖₊)
      have hnorm : ‖z‖ = ‖z i‖ := by rw [Pi.norm_def, hi]; rfl
      have his : s < ‖z i‖ := by rw [← hnorm]; exact hsR.trans_le hRnorm
      have hev_b : ∀ᶠ y in nhds z, b (y i) = 0 := by
        filter_upwards [isOpen_lt continuous_const
          (continuous_norm.comp
            (continuous_apply i : Continuous (fun y : Fin n → ℂ ↦ y i))) |>.mem_nhds
            (show z ∈ {y | s < ‖y i‖} from his)] with y hy
        exact b.zero_of_le_dist (by simpa using hy.le)
      have hev : f =ᶠ[nhds z] 0 := by
        filter_upwards [hev_b] with y hy
        have hχy : χ y = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hy
        simp [f, hχy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hsupport : ∀ z, s ≤ ‖z k‖ → f z = 0 := by
    intro z hz
    have hbk : b (z k) = 0 := b.zero_of_le_dist (by simpa using hz)
    have hχz : χ z = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ k) hbk
    simp [f, hχz]
  refine ⟨u + q, hu.add
    (dbar_transform_calculus_aux n k f hf s (lt_trans hr hrs) hsupport).1, ?_⟩
  intro j hj z hz
  have hq : ContDiff ℝ ∞ q :=
    (dbar_transform_calculus_aux n k f hf s (lt_trans hr hrs) hsupport).1
  rw [dbar_coord_add j u q z (hu.differentiable (by simp)).differentiableAt
    (hq.differentiable (by simp)).differentiableAt]
  rcases lt_or_eq_of_le hj with hjk | hjk
  · have hjne : j ≠ k := Fin.ne_of_lt hjk
    rw [(dbar_transform_calculus_aux n k f hf s (lt_trans hr hrs) hsupport).2 j hjne z]
    have hslice : ∀ ζ : ℂ,
        dbar_coord n j f (Function.update z k ζ) = 0 := by
      intro ζ
      let x := Function.update z k ζ
      by_cases hζ : s < ‖ζ‖
      · have hev_b : ∀ᶠ y in nhds x, b (y k) = 0 := by
          filter_upwards [isOpen_lt continuous_const
            (continuous_norm.comp
              (continuous_apply k : Continuous (fun y : Fin n → ℂ ↦ y k))) |>.mem_nhds
              (show x ∈ {y | s < ‖y k‖} by simpa [x])] with y hy
          exact b.zero_of_le_dist (by simpa using hy.le)
        have hev : f =ᶠ[nhds x] 0 := by
          filter_upwards [hev_b] with y hy
          have hχy : χ y = 0 := Finset.prod_eq_zero (Finset.mem_univ k) hy
          simp [f, hχy]
        rw [dbar_coord_congr_of_eventuallyEq hev]
        simp [dbar_coord]
      · have hζs : ‖ζ‖ ≤ s := le_of_not_gt hζ
        have hzcoord : ∀ i, ‖z i‖ < r := by
          intro i
          have hi : ‖z i‖ ≤ ‖z‖ := by
            rw [Pi.norm_def]
            exact_mod_cast Finset.le_sup (f := fun l ↦ ‖z l‖₊) (Finset.mem_univ i)
          exact hi.trans_lt (by simpa [Metric.mem_ball] using hz)
        have hxcoord : ∀ i, ‖x i‖ < R := by
          intro i
          by_cases hik : i = k
          · subst i
            simpa [x] using hζs.trans_lt hsR
          · have := (hzcoord i).trans hrs
            simpa [x, hik] using this.trans hsR
        have hx : x ∈ Metric.ball (0 : Fin n → ℂ) R := by
          rw [Metric.mem_ball, dist_zero_right]
          obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ
            (⟨k, Finset.mem_univ k⟩) (fun i ↦ ‖x i‖₊)
          have hnorm : ‖x‖ = ‖x i‖ := by rw [Pi.norm_def, hi]; rfl
          rw [hnorm]
          exact hxcoord i
        have hevprev : dbar_coord n j u =ᶠ[nhds x] w j := by
          filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
          exact hprev j hjk y hy
        have hkprev : dbar_coord n k (dbar_coord n j u) x = dbar_coord n k (w j) x :=
          dbar_coord_congr_of_eventuallyEq hevprev
        have hdres : dbar_coord n j (fun y ↦ w k y - dbar_coord n k u y) x = 0 := by
          rw [show (fun y ↦ w k y - dbar_coord n k u y) = w k - dbar_coord n k u by rfl]
          have hdu : DifferentiableAt ℝ (dbar_coord n k u) x := by
            have hfd : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (m := ∞) (by simp)
            unfold dbar_coord
            have hfdiff : DifferentiableAt ℝ (fderiv ℝ u) x :=
              (hfd.differentiable (by simp)).differentiableAt
            have hk1 : DifferentiableAt ℝ (fun z ↦ fderiv ℝ u z (Pi.single k 1)) x :=
              hfdiff.clm_apply (by fun_prop)
            have hkI : DifferentiableAt ℝ
                (fun z ↦ fderiv ℝ u z (Pi.single k Complex.I)) x :=
              hfdiff.clm_apply (by fun_prop)
            fun_prop
          rw [dbar_coord_sub j (w k) (dbar_coord n k u) x
            ((hw k x hx).differentiableAt (by simp)) hdu]
          rw [hclosed k j x hx, dbar_coord_comm_c j k u hu x, hkprev]
          ring
        have hevi : ∀ i ∈ Finset.univ, ∀ᶠ y in nhds x, i ≠ k → b (y i) = 1 := by
          intro i _
          by_cases hik : i = k
          · filter_upwards with y
            exact fun h ↦ (h hik).elim
          · have hxi : ‖x i‖ < r := by simpa [x, hik] using hzcoord i
            filter_upwards [isOpen_lt
              (continuous_norm.comp
                (continuous_apply i : Continuous (fun y : Fin n → ℂ ↦ y i)))
              continuous_const |>.mem_nhds hxi] with y hy _
            exact b.one_of_mem_closedBall (by simpa [Metric.mem_closedBall] using hy.le)
        have hall : ∀ᶠ y in nhds x, ∀ i ∈ Finset.univ, i ≠ k → b (y i) = 1 :=
          (Filter.eventually_all_finset Finset.univ).mpr hevi
        have hevχ : χ =ᶠ[nhds x] fun y ↦ b (y k) := by
          filter_upwards [hall] with y hy
          dsimp [χ]
          calc
            ∏ i, b (y i) = b (y k) * ∏ i ∈ Finset.univ.erase k, b (y i) := by
              rw [Finset.mul_prod_erase Finset.univ (fun i ↦ b (y i)) (Finset.mem_univ k)]
            _ = b (y k) := by
              rw [Finset.prod_eq_one]
              · simp
              · intro i hi
                exact hy i (Finset.mem_univ i) (Finset.ne_of_mem_erase hi)
        have hevf : f =ᶠ[nhds x] fun y ↦
            (b (y k) : ℂ) * (w k y - dbar_coord n k u y) := by
          filter_upwards [hevχ] with y hy
          simp only [f, hy, Complex.real_smul]
        rw [dbar_coord_congr_of_eventuallyEq hevf]
        have hbcomplex : DifferentiableAt ℝ (fun y : Fin n → ℂ ↦ (b (y k) : ℂ)) x :=
          Complex.ofRealCLM.differentiableAt.comp x
            ((hb.differentiable (by simp)).differentiableAt.comp x (by fun_prop))
        rw [dbar_coord_mul j (fun y ↦ (b (y k) : ℂ))
          (fun y ↦ w k y - dbar_coord n k u y) x hbcomplex
          ((hres x hx).differentiableAt (by simp))]
        rw [hdres, dbar_coord_apply_ne j k hjne b hb x]
        ring
    simp [dbar_transform, cauchyTransform, hslice]
    exact hprev j hjk z (Metric.ball_subset_ball (le_of_lt hrR) hz)
  · have hjeq : j = k := Fin.ext hjk
    subst j
    rw [dbar_transform_equation_aux n k f hf s (lt_trans hr hrs) hsupport z]
    have hχz : χ z = 1 := by
      dsimp [χ]
      apply Finset.prod_eq_one
      intro i _
      apply b.one_of_mem_closedBall
      rw [Metric.mem_closedBall, dist_zero_right]
      have hi : ‖z i‖ ≤ ‖z‖ := by
        rw [Pi.norm_def]
        exact_mod_cast Finset.le_sup (f := fun j ↦ ‖z j‖₊) (Finset.mem_univ i)
      exact hi.trans (le_of_lt (by simpa [Metric.mem_ball] using hz))
    simp only [f, hχz, one_smul]
    ring

/-- A closed smooth form has a smooth primitive on a smaller polydisc.
Source: Hörmander, 3rd ed., §2.3, the polydisc ∂̄ lemma; Gunning--Rossi, I.D. -/
theorem dbar_polydisc_aux (n : ℕ) (w : Fin n → (Fin n → ℂ) → ℂ)
    (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hw : ∀ j z, z ∈ Metric.ball 0 R → ContDiffAt ℝ ∞ (w j) z)
    (hclosed : ∀ j k z, z ∈ Metric.ball 0 R →
      dbar_coord n k (w j) z = dbar_coord n j (w k) z) :
    ∃ u : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ u ∧
      ∀ j z, z ∈ Metric.ball 0 r → dbar_coord n j u z = w j z := by
  have hstep : ∀ m : ℕ, m ≤ n →
      ∃ s : ℝ, r < s ∧ s ≤ R ∧
        ∃ u : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ u ∧
          ∀ j : Fin n, j.val < m → ∀ z, z ∈ Metric.ball 0 s →
            dbar_coord n j u z = w j z := by
    intro m hm
    induction m with
    | zero =>
        exact ⟨R, hrR, le_rfl, fun _ ↦ 0, contDiff_const, by simp⟩
    | succ m ih =>
        have hmn : m ≤ n := Nat.le_trans (Nat.le_succ m) hm
        obtain ⟨s, hrs, hsR, u, hu, he⟩ := ih hmn
        have hmn' : m < n := Nat.lt_of_succ_le hm
        let t : ℝ := (r + s) / 2
        have hrt : r < t := by dsimp [t]; linarith
        have hts : t < s := by dsimp [t]; linarith
        have hws : ∀ j z, z ∈ Metric.ball 0 s → ContDiffAt ℝ ∞ (w j) z := by
          intro j z hz
          exact hw j z (Metric.ball_subset_ball hsR hz)
        have hcs : ∀ j k z, z ∈ Metric.ball 0 s →
            dbar_coord n k (w j) z = dbar_coord n j (w k) z := by
          intro j k z hz
          exact hclosed j k z (Metric.ball_subset_ball hsR hz)
        obtain ⟨v, hv, hev⟩ := dbar_eliminate_coordinate_aux n ⟨m, hmn'⟩ w t s (hr.trans hrt) hts
          hws hcs u hu he
        refine ⟨t, hrt, le_trans (le_of_lt hts) hsR, v, hv, ?_⟩
        intro j hj z hz
        exact hev j (Nat.lt_succ_iff.mp hj) z hz
  obtain ⟨s, hrs, hsR, u, hu, he⟩ := hstep n le_rfl
  refine ⟨u, hu, ?_⟩
  intro j z hz
  exact he j j.isLt z (Metric.ball_subset_ball (le_of_lt hrs) hz)

private theorem dbar_exists_monomial_polynomial (n m : ℕ)
    (L : ContinuousMultilinearMap ℂ (fun _ : Fin m ↦ Fin n → ℂ) ℂ) :
    ∃ P : MvPolynomial (Fin n) ℂ,
      ∀ z, MvPolynomial.eval z P = L (fun _ ↦ z) := by
  classical
  let P : MvPolynomial (Fin n) ℂ :=
    ∑ a : Fin m → Fin n,
      MvPolynomial.C (L (fun k ↦ Pi.single (a k) 1)) *
        ∏ k : Fin m, MvPolynomial.X (a k)
  refine ⟨P, fun z ↦ ?_⟩
  rw [show (fun _ : Fin m ↦ z) =
      fun k ↦ ∑ i : Fin n, z i • Pi.single i 1 by
        funext k i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        simp, ContinuousMultilinearMap.map_sum]
  simp only [P, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_mul,
    MvPolynomial.eval_prod, MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro a ha
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [smul_eq_mul]
  ring

private theorem dbar_polynomial_approximation_of_power_series (n : ℕ)
    (f : (Fin n → ℂ) → ℂ) (p : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ)
    (r R : ℝ) (hr : 0 ≤ r) (hrR : r < R)
    (hp : HasFPowerSeriesOnBall f p 0 (ENNReal.ofReal R)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin n) ℂ,
      ∀ z, z ∈ Metric.closedBall 0 r → ‖f z - MvPolynomial.eval z P‖ < ε := by
  classical
  choose q hq using fun m ↦ dbar_exists_monomial_polynomial n m (p m)
  let s : ℝ := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  have hs0 : 0 ≤ s := hr.trans (le_of_lt hrs)
  have hlt : (Real.toNNReal s : ENNReal) < ENNReal.ofReal R := by
    rw [ENNReal.coe_lt_ofReal]
    simpa only [Real.coe_toNNReal _ hs0] using hsR
  have ht := hp.tendstoUniformlyOn hlt
  rw [Metric.tendstoUniformlyOn_iff] at ht
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (ht ε hε))
  refine ⟨∑ m ∈ Finset.range N, q m, ?_⟩
  intro z hz
  have hz' : z ∈ Metric.ball (0 : Fin n → ℂ) (Real.toNNReal s) := by
    rw [Metric.mem_ball, Real.coe_toNNReal _ hs0]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hrs
  simpa only [zero_add, dist_eq_norm, FormalMultilinearSeries.partialSum, map_sum,
    MvPolynomial.eval_sum, hq] using hN N le_rfl z hz'

private theorem dbar_norm_prod_sub_prod_le : ∀ (n : ℕ) (a b : Fin n → ℂ) (C D : ℝ),
    1 ≤ C → 0 ≤ D → (∀ i, ‖a i‖ ≤ C) → (∀ i, ‖b i‖ ≤ C) →
      (∀ i, ‖a i - b i‖ ≤ D) →
      ‖∏ i, a i - ∏ i, b i‖ ≤ (n : ℝ) * C ^ n * D := by
  intro n
  induction n with
  | zero =>
      intro a b C D hC hD ha hb hd
      simp
  | succ n ih =>
      intro a b C D hC hD ha hb hd
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      rw [show a 0 * ∏ i : Fin n, a i.succ - b 0 * ∏ i : Fin n, b i.succ =
          (a 0 - b 0) * ∏ i : Fin n, a i.succ +
            b 0 * (∏ i : Fin n, a i.succ - ∏ i : Fin n, b i.succ) by ring]
      calc
        _ ≤ ‖a 0 - b 0‖ * ‖∏ i : Fin n, a i.succ‖ +
            ‖b 0‖ * ‖∏ i : Fin n, a i.succ - ∏ i : Fin n, b i.succ‖ := by
              simpa only [norm_mul] using
                (norm_add_le ((a 0 - b 0) * ∏ i : Fin n, a i.succ)
                  (b 0 * (∏ i : Fin n, a i.succ - ∏ i : Fin n, b i.succ)))
        _ ≤ D * C ^ n + C * ((n : ℝ) * C ^ n * D) := by
              gcongr
              · exact hd 0
              · rw [norm_prod]
                calc
                  _ ≤ ∏ _i : Fin n, C := Finset.prod_le_prod₀
                    (fun i _ ↦ norm_nonneg _) (fun i _ ↦ ha i.succ)
                  _ = C ^ n := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
              · exact hb 0
              · exact ih (fun i => a i.succ) (fun i => b i.succ) C D hC hD
                  (fun i => ha i.succ) (fun i => hb i.succ) (fun i => hd i.succ)
        _ ≤ ((n + 1 : ℕ) : ℝ) * C ^ (n + 1) * D := by
              have hC0 : 0 ≤ C := le_trans (by norm_num) hC
              have hCn : 0 ≤ C ^ n := pow_nonneg hC0 _
              push_cast
              rw [pow_succ]
              nlinarith [mul_le_mul_of_nonneg_right hC (mul_nonneg hCn hD)]

private theorem dbar_line_series (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (p : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ)
    (hp : HasFPowerSeriesAt f p 0) (z : Fin n → ℂ) (s : NNReal)
    (hs : 0 < s)
    (hd : DifferentiableOn ℂ (fun t : ℂ ↦ f (t • z)) (Metric.closedBall 0 s)) :
    ∀ k, cauchyPowerSeries (fun t : ℂ ↦ f (t • z)) 0 s k (fun _ ↦ 1) =
      p k (fun _ ↦ z) := by
  let L : ℂ →L[ℂ] (Fin n → ℂ) := (ContinuousLinearMap.id ℂ ℂ).smulRight z
  have hp' : HasFPowerSeriesAt f p (L 0) := by simpa using hp
  have he := hp'.compContinuousLinearMap.eq_formalMultilinearSeries
    (hd.hasFPowerSeriesOnBall hs).hasFPowerSeriesAt
  intro k
  have he' := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ ↦ q k (fun _ ↦ 1)) he
  simpa [FormalMultilinearSeries.compContinuousLinearMap, L] using he'.symm

private theorem dbar_cauchy_coefficient_bound (g : ℂ → ℂ) (s : ℝ) (hs : 0 < s)
    (M : ℝ) (hg : ContinuousOn g (Metric.sphere 0 s))
    (hM : ∀ t ∈ Metric.sphere (0 : ℂ) s, ‖g t‖ ≤ M) (k : ℕ) :
    ‖cauchyPowerSeries g 0 s k (fun _ ↦ 1)‖ ≤ M * (s⁻¹) ^ k := by
  have hc : Continuous (fun θ : ℝ ↦ ‖g (circleMap 0 s θ)‖) :=
    (hg.comp_continuous (continuous_circleMap 0 s)
      (fun θ ↦ circleMap_mem_sphere 0 hs.le θ)).norm
  have hi : (∫ θ : ℝ in 0..2 * Real.pi, ‖g (circleMap 0 s θ)‖) ≤
      (2 * Real.pi) * M := by
    simpa using intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (hc.intervalIntegrable _ _) (intervalIntegrable_const (c := M))
      (fun θ _ ↦ hM _ (circleMap_mem_sphere 0 hs.le θ))
  calc
    _ ≤ ‖cauchyPowerSeries g 0 s k‖ := by
      simp
    _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ : ℝ in 0..2 * Real.pi,
        ‖g (circleMap 0 s θ)‖) * |s|⁻¹ ^ k :=
      norm_cauchyPowerSeries_le g 0 s k
    _ ≤ ((2 * Real.pi)⁻¹ * ((2 * Real.pi) * M)) * |s|⁻¹ ^ k := by
      gcongr
    _ = M * (s⁻¹) ^ k := by
      rw [inv_mul_cancel_left₀ (ne_of_gt Real.two_pi_pos), abs_of_pos hs]

/-- Taylor polynomials approximate on a strictly smaller closed polydisc.
Source: Gunning--Rossi, I, power series on polydiscs; Hörmander, 3rd ed., §2.2. -/
theorem dbar_polynomial_approximation_aux (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin n) ℂ,
      ∀ z, z ∈ Metric.closedBall 0 r → ‖f z - MvPolynomial.eval z P‖ < ε := by
  classical
  let s : ℝ := (r + R) / (2 * r)
  have hs1 : 1 < s := by dsimp [s]; apply (lt_div_iff₀ (by positivity)).2; linarith
  have hs0 : 0 < s := lt_trans zero_lt_one hs1
  have hsr : s * r < R := by
    dsimp [s]
    have he : (r + R) / (2 * r) * r = (r + R) / 2 := by field_simp
    rw [he]; linarith
  have hsub : Metric.closedBall (0 : Fin n → ℂ) (s * r) ⊆ Metric.ball 0 R :=
    fun z hz ↦ lt_of_le_of_lt hz hsr
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Fin n → ℂ) (s * r)).exists_bound_of_continuousOn
    (hf.continuousOn.mono hsub)
  obtain ⟨p, hp⟩ := hf 0 (Metric.mem_ball_self (hr.trans hrR))
  choose q hq using fun k ↦ dbar_exists_monomial_polynomial n k (p k)
  have hq0 : 0 ≤ s⁻¹ := inv_nonneg.mpr hs0.le
  have hq1 : s⁻¹ < 1 := (inv_lt_one₀ hs0).2 hs1
  have ht : Tendsto (fun N : ℕ ↦ M * (s⁻¹) ^ N / (1 - s⁻¹)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul M |>.div_const (1 - s⁻¹)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (ht.eventually (gt_mem_nhds hε)))
  refine ⟨∑ k ∈ Finset.range N, q k, ?_⟩
  intro z hz
  have hzNorm : ‖z‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hmap : ∀ t : ℂ, t ∈ Metric.closedBall 0 s → t • z ∈ Metric.closedBall 0 (s * r) := by
    intro t ht
    simp only [Metric.mem_closedBall, dist_zero_right] at ht ⊢
    rw [norm_smul]
    exact mul_le_mul ht hzNorm (norm_nonneg _) hs0.le
  have hd : DifferentiableOn ℂ (fun t : ℂ ↦ f (t • z)) (Metric.closedBall 0 s) := by
    intro t ht
    exact ((hf (t • z) (hsub (hmap t ht))).differentiableAt.comp t
      (differentiableAt_id.smul_const z)).differentiableWithinAt
  let s' : NNReal := ⟨s, hs0.le⟩
  have hs' : 0 < s' := hs0
  have he := dbar_line_series n f p hp z s' hs' hd
  have hb : ∀ k, ‖p k (fun _ ↦ z)‖ ≤ M * (s⁻¹) ^ k := by
    intro k
    rw [← he k]
    apply dbar_cauchy_coefficient_bound _ s hs0 M
    · exact hd.continuousOn.mono Metric.sphere_subset_closedBall
    · intro t ht
      exact hM _ (hmap t (Metric.sphere_subset_closedBall ht))
  have hsum : HasSum (fun k ↦ p k (fun _ ↦ z)) (f z) := by
    have h := (hd.hasFPowerSeriesOnBall (R := s') hs').hasSum (y := (1 : ℂ))
      (by
        rw [Metric.eball_coe]
        change dist (1 : ℂ) 0 < s
        simpa only [dist_zero_right, norm_one] using hs1)
    simpa only [he, zero_add, one_smul] using h
  have herr := norm_sub_le_of_geometric_bound_of_hasSum hq1 hb hsum N
  rw [norm_sub_rev] at herr
  have hpoly : MvPolynomial.eval z (∑ k ∈ Finset.range N, q k) =
      ∑ k ∈ Finset.range N, p k (fun _ ↦ z) := by
    simp only [map_sum, hq]
  rw [hpoly]
  exact herr.trans_lt (hN N le_rfl)

private lemma dbar_differentiableAt_complex_of_contDiffAt
    {n : ℕ} {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hf : ContDiffAt ℝ ∞ f z) (hd : ∀ j, dbar_coord n j f z = 0) :
    DifferentiableAt ℂ f z := by
  have hR : DifferentiableAt ℝ f z := hf.differentiableAt (by simp)
  let L := fderiv ℝ f z
  have hA : antiLinearPart L = 0 := by
    have hj (j : Fin n) : antiLinearPart L (Pi.single j (1 : ℂ)) = 0 := by
      rw [antiLinearPart_apply]
      have hsingle : Complex.I • Pi.single j (1 : ℂ) = Pi.single j Complex.I := by
        ext i
        by_cases h : i = j <;> simp [h]
      rw [hsingle]
      simpa only [dbar_coord, L, Complex.real_smul, Complex.ofReal_inv,
        Complex.ofReal_ofNat, div_eq_mul_inv, mul_comm] using hd j
    ext v
    have hv : v = ∑ j, ((v j).re • (Pi.single j (1 : ℂ) : Fin n → ℂ) +
        (v j).im • (Pi.single j Complex.I : Fin n → ℂ)) := by
      ext i
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
      rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [Pi.single_apply, hj])]
      · simpa only [Pi.single_eq_same, Complex.real_smul, mul_one] using
          (Complex.re_add_im (v i)).symm
      · simp
    rw [hv, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [map_add, map_smul, map_smul, hj]
    have hj0 : antiLinearPart L (Pi.single j (1 : ℂ)) = 0 := hj j
    have hsingle : Pi.single j Complex.I = Complex.I • Pi.single j (1 : ℂ) := by
      ext i
      by_cases h : i = j <;> simp [h]
    rw [hsingle, antiLinearPart_apply_I_smul, hj0]
    simp
  obtain ⟨L', hL'⟩ := exists_restrictScalars_eq_of_antiLinearPart_eq_zero L hA
  exact (hasFDerivAt_of_restrictScalars ℝ hR.hasFDerivAt (f' := L') hL').differentiableAt

private lemma dbar_analyticOnNhd_of_contDiff
    {n : ℕ} {f : (Fin n → ℂ) → ℂ} {V : Set (Fin n → ℂ)}
    (hV : IsOpen V) (hf : ContDiff ℝ ∞ f)
    (hd : ∀ j z, z ∈ V → dbar_coord n j f z = 0) : AnalyticOnNhd ℂ f V := by
  apply AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn_fin hV
  intro z hz
  exact (dbar_differentiableAt_complex_of_contDiffAt (hf.contDiffAt) (fun j ↦ hd j z hz)).differentiableWithinAt

private lemma dbar_coord_eq_zero_of_differentiableAt_complex
    {n : ℕ} {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hf : DifferentiableAt ℂ f z) (j : Fin n) : dbar_coord n j f z = 0 := by
  rw [dbar_coord, hf.fderiv_restrictScalars ℝ]
  have hsingle : Pi.single j Complex.I = Complex.I • Pi.single j (1 : ℂ) := by
    ext i
    by_cases h : i = j <;> simp [h]
  rw [hsingle]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [(fderiv ℂ f z).map_smul]
  rw [smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
  ring

private lemma dbar_coord_sub_e {n : ℕ} {f g : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (j : Fin n) :
    dbar_coord n j (fun x ↦ f x - g x) z = dbar_coord n j f z - dbar_coord n j g z := by
  rw [dbar_coord, dbar_coord, dbar_coord,
    show (fun x ↦ f x - g x) = f - g by rfl, fderiv_sub hf hg]
  simp only [ContinuousLinearMap.sub_apply]
  ring

private lemma dbar_analyticOnNhd_of_locallyUniform_limit
    {n : ℕ} {F : ℕ → (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) → ℂ}
    {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hF : ∀ m, AnalyticOnNhd ℂ (F m) U)
    (hf : TendstoLocallyUniformlyOn F f atTop U) :
    AnalyticOnNhd ℂ f U := by
  classical
  intro x hx
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU x hx
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hclosed : Metric.closedBall x r ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hR)).trans hRU
  have hfc : ContinuousOn f (Metric.closedBall x r) :=
    (hf.mono hclosed).continuousOn (.of_forall fun m => (hF m).continuousOn.mono hclosed)
  have hA := AnalyticDivisorAlgebraic2.spec_analyticAt_torusCauchyIntegral_aux hr hfc
  have hne : ((2 * Real.pi * Complex.I) ^ n : ℂ) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero)
  refine (hA.const_smul (c := ((2 * Real.pi * Complex.I) ^ n)⁻¹)).congr ?_
  filter_upwards [Metric.ball_mem_nhds x hr] with z hz
  have hzU : z ∈ U := hclosed (Metric.ball_subset_closedBall hz)
  have hFm : Tendsto (fun m => F m z) atTop (𝓝 (f z)) := hf.tendsto_at hzU
  have hC (m : ℕ) :
      (∯ w in T(x, fun _ => r), (∏ i, (w i - z i))⁻¹ • F m w) =
        (2 * Real.pi * Complex.I) ^ n • F m z := by
    exact AnalyticDivisorAlgebraic2.spec_torusIntegral_cauchy_aux hU
      (hF m).differentiableOn hclosed hz
  have hIcF (m : ℕ) := AnalyticDivisorAlgebraic2.torusIntegrable_cauchyKernel
    ((hF m).continuousOn.mono hclosed) hz
  have hIcf := AnalyticDivisorAlgebraic2.torusIntegrable_cauchyKernel hfc hz
  have hInt : Tendsto
      (fun m => ∯ w in T(x, fun _ => r), (∏ i, (w i - z i))⁻¹ • F m w)
      atTop (𝓝 (∯ w in T(x, fun _ => r), (∏ i, (w i - z i))⁻¹ • f w)) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    let q : ℝ := r / 2
    have hq : 0 < q := half_pos hr
    have hzr : ∀ i, ‖z i - x i‖ < r :=
      (AnalyticDivisorAlgebraic2.mem_ball_fin_iff hr).1 hz
    let C : ℝ := (2 * Real.pi) ^ n * r ^ n * ∏ i, (r - ‖z i - x i‖)⁻¹
    have hCpos : 0 < C := by
      dsimp [C]
      have hi : ∀ i : Fin n, 0 < (r - ‖z i - x i‖)⁻¹ := fun i => by
        exact inv_pos.mpr (sub_pos.mpr (hzr i))
      exact mul_pos (mul_pos (pow_pos (mul_pos (by norm_num) Real.pi_pos) _) (pow_pos hr _))
        (Finset.prod_pos fun i _ => hi i)
    have hunif := Metric.tendstoUniformlyOn_iff.1
      ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        (isCompact_closedBall x r)).1 (hf.mono hclosed))
        (ε / (2 * C)) (div_pos hε (mul_pos (by norm_num) hCpos))
    rcases (eventually_atTop.1 hunif) with ⟨N, hN⟩
    refine ⟨N, fun m hmN => ?_⟩
    have hm := hN m hmN
    rw [dist_eq_norm, ← torusIntegral_sub (hIcF m) hIcf]
    refine (norm_torusIntegral_le_of_norm_le_const (C :=
      (∏ i, (r - ‖z i - x i‖)⁻¹) * (ε / (2 * C))) ?_).trans_lt ?_
    · intro θ
      rw [← smul_sub, norm_smul, norm_inv, norm_prod]
      apply mul_le_mul
      · conv_lhs => rw [← Finset.prod_inv_distrib]
        apply Finset.prod_le_prod₀ (fun _ _ => inv_nonneg.mpr (norm_nonneg _))
        intro i _
        have hw : ‖torusMap x (fun _ => r) θ i - x i‖ = r := by
          simp [torusMap, Complex.norm_exp_ofReal_mul_I, abs_of_pos hr]
        have hl : r - ‖z i - x i‖ ≤
            ‖torusMap x (fun _ => r) θ i - z i‖ := by
          calc
            r - ‖z i - x i‖ =
                ‖torusMap x (fun _ => r) θ i - x i‖ - ‖z i - x i‖ := by rw [hw]
            _ ≤ ‖(torusMap x (fun _ => r) θ i - x i) - (z i - x i)‖ :=
              norm_sub_norm_le _ _
            _ = ‖torusMap x (fun _ => r) θ i - z i‖ := by ring_nf
        exact inv_anti₀ (sub_pos.mpr (hzr i)) hl
      · simpa only [dist_eq_norm, norm_sub_rev] using
          (hm _ ((AnalyticDivisorAlgebraic2.mem_closedBall_fin_iff hr.le).2 fun i => by
            simp [torusMap, Complex.norm_exp_ofReal_mul_I, abs_of_pos hr])).le
      · exact norm_nonneg _
      · exact Finset.prod_nonneg fun i _ => (inv_nonneg.mpr (sub_nonneg.mpr (hzr i).le))
    · dsimp [C]
      simp only [abs_of_pos hr, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hp : 0 < ∏ i, (r - ‖z i - x i‖)⁻¹ :=
        Finset.prod_pos fun i _ => inv_pos.mpr (sub_pos.mpr (hzr i))
      calc
        (2 * Real.pi) ^ n * r ^ n *
            ((∏ i, (r - ‖z i - x i‖)⁻¹) *
              (ε / (2 * ((2 * Real.pi) ^ n * r ^ n * ∏ i, (r - ‖z i - x i‖)⁻¹)))) =
            ε / 2 := by
              field_simp [Real.pi_ne_zero, ne_of_gt hr, ne_of_gt hp]
              exact div_self (ne_of_gt (by simpa only [one_div] using hp))
        _ < ε := by linarith
  have hlim' := (tendsto_const_nhds.smul hFm).congr' (.of_forall fun m => (hC m).symm)
  have heq := tendsto_nhds_unique hInt hlim'
  rw [Pi.smul_apply, heq, smul_smul, inv_mul_cancel₀ hne, one_smul]

set_option maxHeartbeats 400000 in
/-- Polynomial corrections produce primitives with summable successive differences.
Source: Hörmander, 3rd ed., §2.3, exhaustion argument;
the one-variable recursion bh7_cousin_step14 at f59a809. -/
theorem dbar_exhaustion_aux (n : ℕ) (w : Fin n → (Fin n → ℂ) → ℂ)
    (hw : ∀ j, ContDiff ℝ ∞ (w j))
    (hclosed : ∀ j k z, dbar_coord n k (w j) z = dbar_coord n j (w k) z) :
    ∃ u : ℕ → (Fin n → ℂ) → ℂ,
      (∀ m, ContDiff ℝ ∞ (u m)) ∧
      (∀ (m : ℕ) j z, z ∈ Metric.ball 0 ((m : ℝ) + 2) →
        dbar_coord n j (u m) z = w j z) ∧
      (∀ (m : ℕ) z, z ∈ Metric.ball 0 ((m : ℝ) + 1) →
        ‖u (m + 1) z - u m z‖ < (1 / 2 : ℝ) ^ m) := by
  classical
  have hex (m : ℕ) : ∃ f : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ f ∧
      ∀ j z, z ∈ Metric.ball 0 ((m : ℝ) + 2) → dbar_coord n j f z = w j z := by
    obtain ⟨f, hf, he⟩ := dbar_polydisc_aux n w ((m : ℝ) + 2) ((m : ℝ) + 3)
      (by positivity) (by linarith) (fun j z _ ↦ (hw j).contDiffAt) (fun j k z _ ↦ hclosed j k z)
    exact ⟨f, hf, he⟩
  let first : {f : (Fin n → ℂ) → ℂ // ContDiff ℝ ∞ f ∧
      ∀ j z, z ∈ Metric.ball 0 (((Nat.zero : ℕ) : ℝ) + 2) → dbar_coord n j f z = w j z} :=
    ⟨Classical.choose (hex 0), Classical.choose_spec (hex 0)⟩
  let next (m : ℕ)
      (s : {f : (Fin n → ℂ) → ℂ // ContDiff ℝ ∞ f ∧
        ∀ j z, z ∈ Metric.ball 0 ((m : ℝ) + 2) → dbar_coord n j f z = w j z}) :
      {f : (Fin n → ℂ) → ℂ // ContDiff ℝ ∞ f ∧
        ∀ j z, z ∈ Metric.ball 0 (((m + 1 : ℕ) : ℝ) + 2) →
          dbar_coord n j f z = w j z} := by
    let v := Classical.choose (hex (m + 1))
    have hv := Classical.choose_spec (hex (m + 1))
    have ha : AnalyticOnNhd ℂ (fun z ↦ v z - s.1 z) (Metric.ball 0 ((m : ℝ) + 2)) := by
      apply dbar_analyticOnNhd_of_contDiff (Metric.isOpen_ball) (hv.1.sub s.2.1)
      intro j z hz
      rw [dbar_coord_sub_e (hv.1.differentiable (by simp) z)
          (s.2.1.differentiable (by simp) z),
        hv.2 j z (Metric.ball_subset_ball (by norm_num) hz), s.2.2 j z hz, sub_self]
    have hexP := dbar_polynomial_approximation_aux n (fun z ↦ v z - s.1 z)
      ((m : ℝ) + 1) ((m : ℝ) + 2) (by positivity) (by linarith) ha
      ((1 / 2 : ℝ) ^ m) (by positivity)
    let P := Classical.choose hexP
    have hP := Classical.choose_spec hexP
    let p : (Fin n → ℂ) → ℂ := fun z ↦ MvPolynomial.eval z P
    have hpA : AnalyticOnNhd ℂ p Set.univ := AnalyticOnNhd.eval_mvPolynomial P
    have hp : ContDiff ℝ ∞ p := hpA.contDiff.restrict_scalars ℝ
    refine ⟨fun z ↦ v z - p z, hv.1.sub hp, ?_⟩
    intro j z hz
    rw [dbar_coord_sub_e (hv.1.differentiable (by simp) z) (hp.differentiable (by simp) z),
      hv.2 j z (Metric.ball_subset_ball (by norm_num) hz),
      dbar_coord_eq_zero_of_differentiableAt_complex (hpA z (Set.mem_univ z)).differentiableAt j,
      sub_zero]
  have hnext (m : ℕ)
      (s : {f : (Fin n → ℂ) → ℂ // ContDiff ℝ ∞ f ∧
        ∀ j z, z ∈ Metric.ball 0 ((m : ℝ) + 2) → dbar_coord n j f z = w j z})
      (z : Fin n → ℂ)
      (hz : z ∈ Metric.ball 0 ((m : ℝ) + 1)) :
      ‖(next m s).1 z - s.1 z‖ < (1 / 2 : ℝ) ^ m := by
    dsimp only [next]
    have hz' : z ∈ Metric.closedBall 0 ((m : ℝ) + 1) :=
      Metric.mem_closedBall.mpr (le_of_lt hz)
    convert Classical.choose_spec (dbar_polynomial_approximation_aux n
        (fun z ↦ Classical.choose (hex (m + 1)) z - s.1 z)
        ((m : ℝ) + 1) ((m : ℝ) + 2) (by positivity) (by linarith)
        (by
          apply dbar_analyticOnNhd_of_contDiff Metric.isOpen_ball
            ((Classical.choose_spec (hex (m + 1))).1.sub s.2.1)
          intro j y hy
          rw [dbar_coord_sub_e
              ((Classical.choose_spec (hex (m + 1))).1.differentiable (by simp) y)
              (s.2.1.differentiable (by simp) y),
            (Classical.choose_spec (hex (m + 1))).2 j y
              (Metric.ball_subset_ball (by norm_num) hy),
            s.2.2 j y hy, sub_self])
        ((1 / 2 : ℝ) ^ m) (by positivity)) z hz' using 1 <;> ring_nf
  let S : (m : ℕ) → {f : (Fin n → ℂ) → ℂ // ContDiff ℝ ∞ f ∧
      ∀ j z, z ∈ Metric.ball 0 ((m : ℝ) + 2) → dbar_coord n j f z = w j z} :=
    fun m ↦ Nat.rec first next m
  let u : ℕ → (Fin n → ℂ) → ℂ := fun m ↦ (S m).1
  refine ⟨u, fun m ↦ (S m).2.1, fun m ↦ (S m).2.2, ?_⟩
  intro m z hz
  simpa only [u, S, Nat.rec_add_one] using hnext m (Nat.rec first next m) z hz

/-- Controlled primitives converge locally uniformly to a smooth global primitive.
Source: Hörmander, 3rd ed., §2.3, exhaustion; holomorphic locally uniform limits;
the one-variable telescoping argument bh7_cousin_step15 at f59a809. -/
theorem dbar_exhaustion_limit_aux (n : ℕ) (w : Fin n → (Fin n → ℂ) → ℂ)
    (u : ℕ → (Fin n → ℂ) → ℂ) (hu : ∀ m, ContDiff ℝ ∞ (u m))
    (he : ∀ (m : ℕ) j z, z ∈ Metric.ball 0 ((m : ℝ) + 2) →
      dbar_coord n j (u m) z = w j z)
    (hc : ∀ (m : ℕ) z, z ∈ Metric.ball 0 ((m : ℝ) + 1) →
      ‖u (m + 1) z - u m z‖ < (1 / 2 : ℝ) ^ m) :
    ∃ g : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ g ∧
      TendstoLocallyUniformly u g atTop ∧
      ∀ j z, dbar_coord n j g z = w j z := by
  let d : ℕ → (Fin n → ℂ) → ℂ := fun k z ↦ u (k + 1) z - u k z
  have hgeom : Summable (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hb (N k : ℕ) (z : Fin n → ℂ) (hz : z ∈ Metric.ball 0 ((N : ℝ) + 1)) :
      ‖d (k + N) z‖ ≤ (1 / 2 : ℝ) ^ k := by
    have hz' : z ∈ Metric.ball 0 (((k + N : ℕ) : ℝ) + 1) := by
      apply Metric.ball_subset_ball _ hz
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hh := (hc (k + N) z hz').le
    apply hh.trans
    rw [pow_add]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  have hsum (z : Fin n → ℂ) : Summable (fun k ↦ d k z) := by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
    apply (summable_nat_add_iff N).mp
    apply hgeom.of_norm_bounded
    intro k
    apply hb N k z
    simpa only [Metric.mem_ball, dist_zero_right] using
      (show ‖z‖ < (N : ℝ) + 1 by linarith)
  let g : (Fin n → ℂ) → ℂ := fun z ↦ u 0 z + ∑' k, d k z
  have hg (N : ℕ) : g = fun z ↦ u N z + ∑' k, d (k + N) z := by
    funext z
    dsimp only [g]
    rw [← (hsum z).sum_add_tsum_nat_add N]
    have ht : ∑ k ∈ Finset.range N, d k z = u N z - u 0 z :=
      Finset.sum_range_sub (fun k ↦ u k z) N
    rw [ht]
    ring
  have htailUniform (N : ℕ) : HasSumUniformlyOn (fun k z ↦ d (k + N) z)
      (fun z ↦ ∑' k, d (k + N) z) (Metric.ball 0 ((N : ℝ) + 1)) := by
    apply HasSumUniformlyOn.of_norm_le_summable hgeom
    intro k z hz
    exact hb N k z hz
  have htailAnalytic (N : ℕ) :
      AnalyticOnNhd ℂ (fun z ↦ ∑' k, d (k + N) z) (Metric.ball 0 ((N : ℝ) + 1)) := by
    let p : ℕ → (Fin n → ℂ) → ℂ := fun m z ↦ ∑ k ∈ Finset.range m, d (k + N) z
    have hp (m : ℕ) : AnalyticOnNhd ℂ (p m) (Metric.ball 0 ((N : ℝ) + 1)) := by
      apply Finset.analyticOnNhd_fun_sum
      intro k hk
      apply dbar_analyticOnNhd_of_contDiff Metric.isOpen_ball
        ((hu (k + N + 1)).sub (hu (k + N)))
      intro j z hz
      rw [dbar_coord_sub_e ((hu (k + N + 1)).differentiable (by simp) z)
          ((hu (k + N)).differentiable (by simp) z),
        he (k + N + 1) j z (Metric.ball_subset_ball (by push_cast; linarith) hz),
        he (k + N) j z (Metric.ball_subset_ball (by
          push_cast
          linarith [Nat.cast_nonneg (α := ℝ) k]) hz), sub_self]
    have hplim : TendstoLocallyUniformlyOn p (fun z ↦ ∑' k, d (k + N) z) atTop
        (Metric.ball 0 ((N : ℝ) + 1)) := by
      have hfin := hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
        (htailUniform N).hasSumLocallyUniformlyOn
      intro e he' x hx
      obtain ⟨t, ht, H⟩ := hfin e he' x hx
      refine ⟨t, ht, ?_⟩
      exact Filter.tendsto_finset_range H
    exact dbar_analyticOnNhd_of_locallyUniform_limit Metric.isOpen_ball hp hplim
  have hgSmooth : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro z
    obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
    have hz : z ∈ Metric.ball 0 ((N : ℝ) + 1) := by
      simpa only [Metric.mem_ball, dist_zero_right] using
        (show ‖z‖ < (N : ℝ) + 1 by linarith)
    rw [hg N]
    exact (hu N).contDiffAt.add
      (((htailAnalytic N) z hz).contDiffAt.restrict_scalars ℝ)
  have hconv : TendstoLocallyUniformly u g atTop := by
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε z
    obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
    let B := Metric.ball (0 : Fin n → ℂ) ((N : ℝ) + 1)
    have hzB : z ∈ B := by
      simpa only [B, Metric.mem_ball, dist_zero_right] using
        (show ‖z‖ < (N : ℝ) + 1 by linarith)
    have hfin := hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
      (htailUniform N).hasSumLocallyUniformlyOn
    obtain ⟨t, ht, H⟩ := Metric.tendstoLocallyUniformlyOn_iff.1 hfin ε hε z hzB
    rw [Metric.isOpen_ball.nhdsWithin_eq hzB] at ht
    refine ⟨t, ht, ?_⟩
    have Hnat : ∀ᶠ q : ℕ in atTop, ∀ y ∈ t,
        dist ((fun z ↦ ∑' k, d (k + N) z) y)
          ((fun z ↦ ∑ k ∈ Finset.range q, d (k + N) z) y) < ε :=
      Filter.tendsto_finset_range H
    rcases (eventually_atTop.1 Hnat) with ⟨M, hM⟩
    filter_upwards [eventually_ge_atTop (M + N)] with m hm
    have hmn : N ≤ m := le_trans (Nat.le_add_left N M) hm
    let q := m - N
    have hmq : q + N = m := Nat.sub_add_cancel hmn
    have hsum : ∑ k ∈ Finset.range q, d (k + N) = fun y ↦ u m y - u N y := by
      funext y
      simp only [Finset.sum_apply]
      dsimp only [d]
      calc
        ∑ k ∈ Finset.range q, (u (k + N + 1) y - u (k + N) y) =
            ∑ k ∈ Finset.range q, (u (k + 1 + N) y - u (k + N) y) := by
              apply Finset.sum_congr rfl
              intro k _
              have hkn : k + N + 1 = k + 1 + N := by omega
              rw [hkn]
        _ = u (q + N) y - u N y := by
          simpa only [Nat.zero_add] using Finset.sum_range_sub (fun k ↦ u (k + N) y) q
        _ = u m y - u N y := by rw [hmq]
    intro y hy
    have hMq : M ≤ q := Nat.le_sub_of_add_le (by omega)
    have HH := hM q hMq y hy
    have hsumy := congrFun hsum y
    simp only [Finset.sum_apply] at hsumy
    rw [hg N]
    rw [show u m y = u N y + (u m y - u N y) by ring, ← hsumy]
    simpa only [Pi.add_apply, Finset.sum_apply, dist_add_left] using HH
  refine ⟨g, hgSmooth, hconv, ?_⟩
  intro j z
  obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
  have hz : z ∈ Metric.ball 0 ((N : ℝ) + 1) := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      (show ‖z‖ < (N : ℝ) + 1 by linarith)
  have htA := (htailAnalytic N) z hz
  have htR : DifferentiableAt ℝ (fun y ↦ ∑' k, d (k + N) y) z :=
    htA.differentiableAt.restrictScalars ℝ
  rw [hg N, dbar_coord]
  rw [show (fun z ↦ u N z + ∑' k, d (k + N) z) =
      u N + (fun z ↦ ∑' k, d (k + N) z) by rfl,
    fderiv_add ((hu N).differentiable (by simp) z) htR]
  simp only [ContinuousLinearMap.add_apply]
  have ht0 := dbar_coord_eq_zero_of_differentiableAt_complex htA.differentiableAt j
  unfold dbar_coord at ht0
  have heN := he N j z (Metric.ball_subset_ball (by norm_num) hz)
  unfold dbar_coord at heN
  linear_combination heN + ht0

/-- Vanishing coordinate conjugate derivatives give holomorphy on an open set.
Source: Hörmander, 3rd ed., §2.2, Cauchy--Riemann equations;
HodgeLean.Foundations.AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn_fin. -/
theorem dbar_holomorphic_aux (n : ℕ) (V : Set (Fin n → ℂ)) (hV : IsOpen V)
    (f : (Fin n → ℂ) → ℂ) (hf : ∀ z, z ∈ V → DifferentiableAt ℝ f z)
    (hd : ∀ j z, z ∈ V → dbar_coord n j f z = 0) :
    AnalyticOnNhd ℂ f V := by
  apply AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn_fin hV
  classical
  intro z hz
  have hreal := hf z hz
  let L := fderiv ℝ f z
  have hI : ∀ j : Fin n, L (Pi.single j Complex.I) =
      Complex.I * L (Pi.single j 1) := by
    intro j
    have h := hd j z hz
    simp only [dbar_coord, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] at h
    have h' := congrArg (fun w : ℂ => Complex.I * w) h
    simp only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul, mul_zero] at h'
    linear_combination -h'
  have hA : antiLinearPart L = 0 := by
    have hj : ∀ j : Fin n, antiLinearPart L (Pi.single j 1) = 0 := by
      intro j
      have heq : Complex.I • Pi.single j (1 : ℂ) = Pi.single j Complex.I := by
        ext i
        simp [Pi.single_apply]
      rw [antiLinearPart_apply, heq, hI]
      simp only [Complex.real_smul]
      rw [← mul_assoc, Complex.I_mul_I]
      ring
    have hjI : ∀ j : Fin n, antiLinearPart L (Pi.single j Complex.I) = 0 := by
      intro j
      have heq : Pi.single j Complex.I = Complex.I • Pi.single j (1 : ℂ) := by
        ext i
        simp [Pi.single_apply]
      rw [heq, antiLinearPart_apply_I_smul, hj, mul_zero, neg_zero]
    ext v
    have hv : v = ∑ j, (((v j).re • (Pi.single j (1 : ℂ) : Fin n → ℂ) :
        Fin n → ℂ) + ((v j).im • (Pi.single j Complex.I : Fin n → ℂ) : Fin n → ℂ)) := by
      ext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · simp [Pi.single_apply, Complex.re_add_im]
      · intro b _ hbi
        simp [Pi.single_apply, Ne.symm hbi]
      · simp
    rw [hv, map_sum]
    simp only [map_add, map_smul, hj, hjI, smul_zero, add_zero, Finset.sum_const_zero,
      zero_apply]
  obtain ⟨L', hL'⟩ := exists_restrictScalars_eq_of_antiLinearPart_eq_zero L hA
  exact ((differentiableAt_iff_restrictScalars ℝ hreal).2 ⟨L', hL'⟩).differentiableWithinAt

/-- Every smooth closed (0,1)-form on affine complex space has a global smooth primitive.
Source: Hörmander, 3rd ed., §2.3; composition of controlled exhaustion and its limit. -/
theorem dbar_global_aux (n : ℕ) (w : Fin n → (Fin n → ℂ) → ℂ)
    (hw : ∀ j, ContDiff ℝ ∞ (w j))
    (hclosed : ∀ j k z, dbar_coord n k (w j) z = dbar_coord n j (w k) z) :
    ∃ g : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ g ∧
      ∀ j z, dbar_coord n j g z = w j z := by
  obtain ⟨u, hu, he, hc⟩ := dbar_exhaustion_aux n w hw hclosed
  obtain ⟨g, hg, _, heq⟩ := dbar_exhaustion_limit_aux n w u hu he hc
  exact ⟨g, hg, heq⟩

/-- Additive holomorphic cocycles on affine complex space are coboundaries.
Source: Gunning--Rossi, Chapter VIII, Cartan theorem B and the first Cousin problem. -/
theorem dbar_cousin_additive_aux (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (a : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (ha : ∀ p q, AnalyticOnNhd ℂ (a p q) (U p ∩ U q))
    (hdiag : ∀ p z, z ∈ U p → a p p z = 0)
    (hcocycle : ∀ p q r z, z ∈ U p ∩ U q ∩ U r → a p q z + a q r z = a p r z) :
    ∃ b : (Fin n → ℂ) → (Fin n → ℂ) → ℂ,
      (∀ p, AnalyticOnNhd ℂ (b p) (U p)) ∧
      (∀ p q z, z ∈ U p ∩ U q → a p q z = b q z - b p z) := by
  have _ := hdiag
  obtain ⟨c, hc, he⟩ := dbar_smooth_split_aux n U hU hcover a ha hcocycle
  obtain ⟨hw, hlocal, hclosed⟩ := dbar_glue_aux n U hU hcover a ha c hc he
  obtain ⟨g, hg, hge⟩ := dbar_global_aux n (dbar_glued n c) hw hclosed
  refine ⟨fun p z ↦ c p z - g z, ?_, ?_⟩
  · intro p
    apply dbar_holomorphic_aux n (U p) (hU p) (fun z ↦ c p z - g z)
    · intro z hz
      exact ((hc p z hz).differentiableAt (by simp)).sub (hg.differentiable (by simp) z)
    · intro j z hz
      have hc' := (hc p z hz).differentiableAt (by simp)
      have hg' := hg.differentiable (by simp) z
      have heq : dbar_coord n j (c p) z = dbar_coord n j g z :=
        (hlocal p j z hz).symm.trans (hge j z).symm
      unfold dbar_coord at heq ⊢
      rw [fderiv_fun_sub hc' hg']
      simp only [sub_apply]
      linear_combination heq
  · intro p q z hz
    rw [he p q z hz]
    ring

end HodgeLean.Foundations
