import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRational
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cHolomorphic

noncomputable section

namespace HodgeLean.Foundations.Program

open scoped Manifold ContDiff

theorem b6m_orient_complex_smul (a v w : ℂ) :
    b3_orient ℂ (a • v) (a • w) = Complex.normSq a * b3_orient ℂ v w := by
  unfold b3_orient
  rw [(Module.finBasis ℂ ℂ).equivFun.map_smul a v,
    (Module.finBasis ℂ ℂ).equivFun.map_smul a w]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  have h : starRingEnd ℂ a * starRingEnd ℂ ((Module.finBasis ℂ ℂ).equivFun v i) *
      (a * (Module.finBasis ℂ ℂ).equivFun w i) =
      (Complex.normSq a : ℂ) *
        (starRingEnd ℂ ((Module.finBasis ℂ ℂ).equivFun v i) *
          (Module.finBasis ℂ ℂ).equivFun w i) := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [h, Complex.im_ofReal_mul]

theorem b6m_orient_sign_complexLinear (L : ℂ →L[ℂ] ℂ) (hL : Function.Injective L)
    (v w : ℂ) : SignType.sign (b3_orient ℂ (L v) (L w)) =
      SignType.sign (b3_orient ℂ v w) := by
  have hmul : ∀ z : ℂ, L z = L 1 • z := by
    intro z
    simpa only [smul_eq_mul, mul_one, mul_comm] using L.map_smul z 1
  have h1 : L 1 ≠ 0 := fun h ↦ one_ne_zero (hL (h.trans L.map_zero.symm))
  rw [hmul v, hmul w, b6m_orient_complex_smul, sign_mul,
    sign_pos (Complex.normSq_pos.mpr h1), one_mul]

section Maps

variable {C D : Type} [TopologicalSpace C] [TopologicalSpace D]
  [ChartedSpace ℂ C] [ChartedSpace ℂ D]
  [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]

theorem b6m_mfderiv_biholomorphic_injective (e : C ≃ₜ D)
    (he : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e)
    (hi : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm) (x : C) :
    Function.Injective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e x) := by
  have hc : (e.symm ∘ e : C → C) = id := funext e.symm_apply_apply
  have hl : Function.LeftInverse
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm (e x))
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e x) := by
    intro v
    have h := mfderiv_comp_apply x ((hi (e x)).mdifferentiableAt (by simp))
      ((he x).mdifferentiableAt (by simp)) v
    rw [hc, mfderiv_id] at h
    exact h.symm
  exact hl.injective

theorem b6m_sign_velocity_map (f : C → D)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hdf : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x))
    (γ δ : b3_SmoothLoop ℂ C) (s t : ℝ) (hst : γ.1 s = δ.1 t) :
    SignType.sign (b3_orient ℂ
      (b3_velocity ℂ D (b3A_mapLoop f hf γ).1 s)
      (b3_velocity ℂ D (b3A_mapLoop f hf δ).1 t)) =
    SignType.sign (b3_orient ℂ (b3_velocity ℂ C γ.1 s) (b3_velocity ℂ C δ.1 t)) := by
  change SignType.sign (b3_orient ℂ (b3_velocity ℂ D (f ∘ γ.1) s)
    (b3_velocity ℂ D (f ∘ δ.1) t)) = _
  rw [b3A_velocity_comp f hf γ.1 γ.2.2 s, b3A_velocity_comp f hf δ.1 δ.2.2 t,
    ← hst]
  exact b6m_orient_sign_complexLinear _ (hdf _) _ _

theorem b6m_transverse_map (f : C → D)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hinj : Function.Injective f)
    (hdf : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x))
    (γ δ : b3_SmoothLoop ℂ C) (htr : b3_Transverse ℂ γ δ) :
    b3_Transverse ℂ (b3A_mapLoop f hf γ) (b3A_mapLoop f hf δ) := by
  intro s t hst hzero
  have hc : γ.1 s = δ.1 t := hinj hst
  have hsign := b6m_sign_velocity_map f hf hdf γ δ s t hc
  rw [hzero, sign_zero] at hsign
  exact htr s t hc (sign_eq_zero_iff.mp hsign.symm)

theorem b6m_crossings_map (f : C → D)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hinj : Function.Injective f)
    (γ δ : b3_SmoothLoop ℂ C) :
    b3_crossings ℂ (b3A_mapLoop f hf γ) (b3A_mapLoop f hf δ) =
      b3_crossings ℂ γ δ := by
  ext p
  simp only [b3_crossings, Set.mem_setOf_eq, b3A_mapLoop, Function.comp_apply, hinj.eq_iff]

theorem b6m_intersection_map (f : C → D)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hinj : Function.Injective f)
    (hdf : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x))
    (γ δ : b3_SmoothLoop ℂ C) :
    b3_intersection ℂ (b3A_mapLoop f hf γ) (b3A_mapLoop f hf δ) =
      b3_intersection ℂ γ δ := by
  unfold b3_intersection
  rw [b6m_crossings_map f hf hinj γ δ]
  apply finsum_mem_congr rfl
  intro p hp
  exact congrArg (fun s : SignType ↦ (s : ℤ))
    (b6m_sign_velocity_map f hf hdf γ δ p.1 p.2 hp.2.2)

theorem b6m_period_push_intersection (f : C → D)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hinj : Function.Injective f)
    (hdf : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q)
    (R : LinearMap.BilinForm ℤ (b3_periodLattice ℂ D)) (hR : b3_IsIntersectionForm ℂ R)
    (x y : b3_periodLattice ℂ C) :
    R (b3A_push f hf x) (b3A_push f hf y) = Q x y := by
  let g := (b3A_push f hf).toIntLinearMap
  let Q' : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C) := (R.compl₂ g).comp g
  have hQ' : b3_IsIntersectionForm ℂ Q' := by
    intro γ δ htr
    change R (b3A_push f hf (b3_latticePeriod ℂ C γ))
      (b3A_push f hf (b3_latticePeriod ℂ C δ)) = b3_intersection ℂ γ δ
    rw [b3A_push_isPushforward f hf γ (b3A_mapLoop f hf γ) rfl,
      b3A_push_isPushforward f hf δ (b3A_mapLoop f hf δ) rfl]
    exact (hR _ _ (b6m_transverse_map f hf hinj hdf γ δ htr)).trans
      (b6m_intersection_map f hf hinj hdf γ δ)
  have h := b3Rest_intersectionForm_unique (E := ℂ) (C := C) (by simp) Q' Q hQ' hQ
  exact congrArg (fun B : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C) ↦ B x y) h

variable [T2Space C] [CompactSpace C] [ConnectedSpace C]

set_option backward.isDefEq.respectTransparency false in
theorem b6m_period_push_naturality (e : C ≃ₜ D)
    (he : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e)
    (P : b6m_H1 C →ₗ[ℤ] b3_periodLattice ℂ C)
    (hP : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ)
    (S : b6m_H1 D →ₗ[ℤ] b3_periodLattice ℂ D)
    (hS : ∀ δ : b3_SmoothLoop ℂ D, S (b6m_loopClass D δ) = b3_latticePeriod ℂ D δ)
    (x : b6m_H1 C) : b3A_push e he (P x) = S (b6m_H1Equiv e x) := by
  have h : (b3A_push e he).toIntLinearMap.comp P =
      S.comp (b6m_H1Equiv e).toLinearMap := by
    apply b6m_homology_linearMap_ext C
    intro γ
    change b3A_push e he (P (b6m_loopClass C γ)) = S (b6m_H1Equiv e (b6m_loopClass C γ))
    rw [hP, b6m_H1Equiv_loopClass e γ (b3A_mapLoop e he γ) (fun _ ↦ rfl), hS]
    exact b3A_push_isPushforward e he γ (b3A_mapLoop e he γ) rfl
  exact LinearMap.congr_fun h x

theorem b6m_intersection_biholomorphic (e : C ≃ₜ D)
    (he : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e)
    (hi : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω e.symm)
    (P : b6m_H1 C →ₗ[ℤ] b3_periodLattice ℂ C)
    (hP : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ)
    (S : b6m_H1 D →ₗ[ℤ] b3_periodLattice ℂ D)
    (hS : ∀ δ : b3_SmoothLoop ℂ D, S (b6m_loopClass D δ) = b3_latticePeriod ℂ D δ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q)
    (R : LinearMap.BilinForm ℤ (b3_periodLattice ℂ D)) (hR : b3_IsIntersectionForm ℂ R)
    (x y : b6m_H1 C) :
    R (S (b6m_H1Equiv e x)) (S (b6m_H1Equiv e y)) = Q (P x) (P y) := by
  rw [← b6m_period_push_naturality e he P hP S hS x,
    ← b6m_period_push_naturality e he P hP S hS y]
  exact b6m_period_push_intersection e he e.injective
    (b6m_mfderiv_biholomorphic_injective e he hi) Q hQ R hR _ _

theorem b6m_intersection_same_filling [CompactSpace D] [ConnectedSpace D]
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (f : C → X) (k : D → X)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k) (hnc : ∃ p q, f p ≠ f q)
    (e : C ≃ₜ D) (he : ∀ p, k (e p) = f p)
    (P : b6m_H1 C →ₗ[ℤ] b3_periodLattice ℂ C)
    (hP : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ)
    (S : b6m_H1 D →ₗ[ℤ] b3_periodLattice ℂ D)
    (hS : ∀ δ : b3_SmoothLoop ℂ D, S (b6m_loopClass D δ) = b3_latticePeriod ℂ D δ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q)
    (R : LinearMap.BilinForm ℤ (b3_periodLattice ℂ D)) (hR : b3_IsIntersectionForm ℂ R)
    (x y : b6m_H1 C) :
    R (S (b6m_H1Equiv e x)) (S (b6m_H1Equiv e y)) = Q (P x) (P y) := by
  obtain ⟨p, q, hpq⟩ := hnc
  have hnk : ∃ u v, k u ≠ k v := ⟨e p, e q, by simpa only [he] using hpq⟩
  have hforward := b6m_contMDiff_of_injective_comp e e.continuous e.injective
    f k hf hk hnk he
  have hreverse := b6m_contMDiff_of_injective_comp e.symm e.symm.continuous e.symm.injective
    k f hk hf ⟨p, q, hpq⟩ (fun z ↦ by simpa using (he (e.symm z)).symm)
  exact b6m_intersection_biholomorphic e hforward hreverse P hP S hS Q hQ R hR x y

end Maps

end HodgeLean.Foundations.Program
