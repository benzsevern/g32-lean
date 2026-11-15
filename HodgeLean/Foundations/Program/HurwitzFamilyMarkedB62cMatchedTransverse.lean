import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cPolygonReparam
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRealLoops

noncomputable section

namespace HodgeLean.Foundations.Program

open Manifold Filter Topology Set Metric
open scoped Manifold ContDiff

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6m_matched_transverse_polygon {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (γ : b3_SmoothLoop ℂ C) (L : b3Rest_Poly ℂ C)
    (hfin : ∀ j z, z ∈ segment ℝ (L.A j) (L.B j) →
      f ((chartAt ℂ (L.x j)).symm z) ≠ OnePoint.infty)
    (hkd : ∀ j z, z ∈ segment ℝ (L.A j) (L.B j) →
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k (e ((chartAt ℂ (L.x j)).symm z)) ≠ 0)
    (hV : ∀ j s, γ.1 s ≠ L.w j)
    (hS : ∀ (j : ℤ) (s l : ℝ), l ∈ Ioo (0 : ℝ) 1 →
      γ.1 s ∈ (chartAt ℂ (L.x j)).source →
      chartAt ℂ (L.x j) (γ.1 s) = L.A j + l • (L.B j - L.A j) →
      ∀ a b : ℝ, a • fderiv ℝ (chartAt ℂ (L.x j) ∘ γ.1) s 1 +
        b • (L.B j - L.A j) = 0 → a = 0 ∧ b = 0)
    (hreg : ∀ j l, l ∈ Icc (0 : ℝ) 1 → ∀ s,
      γ.1 s = (chartAt ℂ (L.x j)).symm (L.A j + l • (L.B j - L.A j)) →
      ∀ i, b4cov_chart0 (f ((chartAt ℂ (L.x j)).symm
          (L.A j + l • (L.B j - L.A j)))) ≠ b i ∧
        dist (b4cov_chart0 (f ((chartAt ℂ (L.x j)).symm
          (L.A j + l • (L.B j - L.A j))))) (b i) ≠ b6t_radius b) :
    ∃ R : b3_SmoothLoop ℂ C, ∃ T : b3_SmoothLoop ℂ D,
      (∀ s, T.1 s = e (R.1 s)) ∧ b3_Transverse ℂ γ R ∧
      b3_period ℂ C R = b3_period ℂ C L.smoothLoop ∧
      ∀ s, ∃ j l, l ∈ Icc (0 : ℝ) 1 ∧
        R.1 s = (chartAt ℂ (L.x j)).symm (L.A j + l • (L.B j - L.A j)) := by
  obtain ⟨σ, hper, hσ⟩ := b6m_polygon_matched_parameters b t hb f k hf hk e he L hfin hkd
  let paths : ℤ → ℝ → C := fun j s ↦
    (chartAt ℂ (L.x j)).symm (L.A j + σ j s • (L.B j - L.A j))
  have hgood j : b3A_IsGoodPath (E := ℂ) (paths j) (L.w j) (L.w (j + 1)) :=
    (hσ j).2.2.2.2.1
  have hgoodt j : b3A_IsGoodPath (E := ℂ) (e ∘ paths j) (e (L.w j)) (e (L.w (j + 1))) :=
    (hσ j).2.2.2.2.2.1
  have hA (j : ℤ) : L.A (j + L.N) = L.A j := by
    simp only [b3Rest_Poly.A, L.x_add, L.w_add]
  have hB (j : ℤ) : L.B (j + L.N) = L.B j := by
    simp only [b3Rest_Poly.B, L.x_add]
    rw [show j + L.N + 1 = (j + 1) + L.N by ring, L.w_add]
  have hpaths (j : ℤ) : paths (j + L.N) = paths j := by
    simp only [paths, L.x_add, hA, hB, hper]
  obtain ⟨R, T, hR, hT⟩ := b6m_glue_matched_paths e L.N L.w paths hpaths hgood hgoodt
  refine ⟨R, T, hT, ?_, b6m_period_eq_reparam_polygon L R σ
    (fun j ↦ (hσ j).2.1) hgood hR, ?_⟩
  · apply b6m_reparam_polygon_transverse L γ R σ (fun j ↦ (hσ j).1)
      (fun j ↦ (hσ j).2.1) (fun j ↦ (hσ j).2.2.1) hR hV hS
    intro s u hsu
    set j := ⌊(L.N : ℝ) * u⌋
    set v := Int.fract ((L.N : ℝ) * u)
    have hcross : γ.1 s = (chartAt ℂ (L.x j)).symm (L.A j + σ j v • (L.B j - L.A j)) :=
      hsu.trans (hR u)
    have h0 : σ j v ≠ 0 := by
      intro h
      apply hV j s
      rw [hcross, h, zero_smul, add_zero]
      exact (chartAt ℂ (L.x j)).left_inv (L.mem_w j).1
    have h1 : σ j v ≠ 1 := by
      intro h
      apply hV (j + 1) s
      rw [hcross, h, one_smul, add_sub_cancel]
      exact (chartAt ℂ (L.x j)).left_inv (L.mem_w' j).1
    have hr := (hσ j).2.1 v
    exact (hσ j).2.2.2.2.2.2 v
      ⟨lt_of_le_of_ne hr.1 (Ne.symm h0), lt_of_le_of_ne hr.2 h1⟩
      (hreg j (σ j v) hr s hcross)
  · intro s
    exact ⟨⌊(L.N : ℝ) * s⌋, σ ⌊(L.N : ℝ) * s⌋ (Int.fract ((L.N : ℝ) * s)),
      (hσ _).2.1 _, hR s⟩

attribute [local instance] b3Forms_isManifold_real in
theorem b6m_regular_matched_transverse_representatives {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart) (ht : t ∈ b6t_polydisc b)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hfn : ∃ x y, f x ≠ f y) (hkn : ∃ x y, k x ≠ k y)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (Γ Δ : b3_SmoothLoop ℂ C) :
    ∃ P : b3_SmoothLoop ℂ C, ∃ Q : b3_SmoothLoop ℂ D,
    ∃ R : b3_SmoothLoop ℂ C, ∃ T : b3_SmoothLoop ℂ D,
      (∀ s, Q.1 s = e (P.1 s)) ∧ (∀ s, T.1 s = e (R.1 s)) ∧
      b3_period ℂ C P = b3_period ℂ C Γ ∧ b3_period ℂ C R = b3_period ℂ C Δ ∧
      b3_Transverse ℂ P R ∧
      ∀ s u, P.1 s = R.1 u → MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (P.1 s) ∧
        ∀ v w : ℂ, SignType.sign (b3_orient ℂ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (P.1 s) v)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (P.1 s) w)) = SignType.sign (b3_orient ℂ v w) := by
  classical
  obtain ⟨P, Q, hQ, hP, hbad⟩ := b6m_exists_matched_smoothLoop b t hb f k hf hk hfn hkn e he Γ
  let F : Set C := range P.1 \ {x | ∃ z : ℂ, (z : OnePoint ℂ) = f x ∧
    ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b}
  let A : Set C := {x | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x = 0}
  let B : Set D := {y | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k y = 0}
  let S : Set C := F ∪ A ∪ e ⁻¹' B ∪ f ⁻¹' {OnePoint.infty}
  have hA : A.Finite := b4cov_critical_finite (by simp) f hf hfn
  have hB : B.Finite := b4cov_critical_finite (by simp) k hk hkn
  have hS : S.Finite := ((hbad.union hA).union (Set.Finite.preimage e.injective.injOn hB)).union
    (b4cov_fiber_finite (by simp) f hf hfn OnePoint.infty)
  obtain ⟨N, hN, x, r, hx, hr, hball, hmem⟩ :=
    b3Rest_exists_chartCover (E := ℂ) Δ.1 Δ.2.2.continuous Δ.2.1
  let K : b3Rest_Cover ℂ Δ.1 := ⟨N, hN, x, r, hx, hr, hball, hmem⟩
  obtain ⟨L, hF, hV, hdir, havoid⟩ := b6m_exists_polygon_data_off_finite P Δ.2.1 K S hS
  have hpoint (j : ℤ) (z : ℂ) (hz : z ∈ segment ℝ (L.A j) (L.B j)) :
      (chartAt ℂ (L.x j)).symm z ∉ S := by
    rw [segment_eq_image'] at hz
    obtain ⟨l, hl, rfl⟩ := hz
    exact havoid j l hl
  have hregular (y : C) (hy : y ∈ range P.1) (hn : y ∉ S) :
      ∃ z : ℂ, (z : OnePoint ℂ) = f y ∧ ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b := by
    by_contra h
    exact hn (Or.inl (Or.inl (Or.inl ⟨hy, h⟩)))
  obtain ⟨R, T, hT, htr, hR, hRp⟩ := b6m_matched_transverse_polygon b t hb f k hf hk e he P L
    (fun j z hz h ↦ hpoint j z hz (Or.inr h))
    (fun j z hz h ↦ hpoint j z hz (Or.inl (Or.inr h))) hV hdir (by
      intro j l hl s hcross
      obtain ⟨z, hz, hzr⟩ := hregular _ ⟨s, hcross⟩ (havoid j l hl)
      rw [← hz, b4cov_chart0_coe]
      exact hzr)
  have hL : b3_period ℂ C L.smoothLoop = b3_period ℂ C Δ := by
    funext θ
    have him : b3Forms_d (b3Forms_imForm θ) = 0 := by
      rw [b3Forms_imForm_eq]
      exact b3Forms_d_reForm (by simp : Module.finrank ℂ ℂ = 1) _
    rw [b3Forms_period_eq, b3Forms_period_eq]
    show (b3Forms_lineIntegral (b3Forms_reForm θ) L.loop 0 1 : ℂ) +
      Complex.I * (b3Forms_lineIntegral (b3Forms_imForm θ) L.loop 0 1 : ℂ) = _
    rw [b3Rest_Poly.lineIntegral_loop hF Δ.2.2 Δ.2.1 (b3Forms_isSmooth_reForm θ)
      (b3Forms_d_reForm (by simp) θ),
      b3Rest_Poly.lineIntegral_loop hF Δ.2.2 Δ.2.1 (b3Forms_isSmooth_imForm θ) him]
  refine ⟨P, Q, R, T, hQ, hT, hP, hR.trans hL, htr, ?_⟩
  intro s u hsu
  obtain ⟨j, l, hl, hu⟩ := hRp u
  have hn : P.1 s ∉ S := by rw [hsu, hu]; exact havoid j l hl
  obtain ⟨z, hz, hzr⟩ := hregular _ ⟨s, rfl⟩ hn
  exact b6m_filling_comparison_regular b t hb ht f k hf hk e he (P.1 s) z hz.symm hzr
    (fun h ↦ hn (Or.inl (Or.inl (Or.inr h)))) (fun h ↦ hn (Or.inl (Or.inr h)))

theorem b6m_filling_pairing_transport {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart) (ht : t ∈ b6t_polydisc b)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hfn : ∃ x y, f x ≠ f y) (hkn : ∃ x y, k x ≠ k y)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (P : b6m_H1 C →ₗ[ℤ] b3_periodLattice ℂ C)
    (hP : ∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ)
    (S : b6m_H1 D →ₗ[ℤ] b3_periodLattice ℂ D)
    (hS : ∀ δ : b3_SmoothLoop ℂ D, S (b6m_loopClass D δ) = b3_latticePeriod ℂ D δ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q)
    (R : LinearMap.BilinForm ℤ (b3_periodLattice ℂ D)) (hR : b3_IsIntersectionForm ℂ R)
    (x y : b6m_H1 C) :
    R (S (b6m_H1Equiv e x)) (S (b6m_H1Equiv e y)) = Q (P x) (P y) := by
  obtain ⟨U, hU⟩ := b6m_period_transport_exists C D e P hP S hS
  let V := S.comp (b6m_H1Equiv e).toLinearMap
  have hforms : R.compl₁₂ V V = Q.compl₁₂ P P := by
    apply b6m_homology_bilin_ext C
    intro Γ Δ
    change R (S (b6m_H1Equiv e (b6m_loopClass C Γ)))
      (S (b6m_H1Equiv e (b6m_loopClass C Δ))) =
      Q (P (b6m_loopClass C Γ)) (P (b6m_loopClass C Δ))
    obtain ⟨γ, γ', δ, δ', hγ, hδ, hpγ, hpδ, htr, hreg⟩ :=
      b6m_regular_matched_transverse_representatives b t hb ht f k hf hk hfn hkn e he Γ Δ
    have hΓ : P (b6m_loopClass C Γ) = P (b6m_loopClass C γ) := by
      rw [hP, hP]
      exact Subtype.ext hpγ.symm
    have hΔ : P (b6m_loopClass C Δ) = P (b6m_loopClass C δ) := by
      rw [hP, hP]
      exact Subtype.ext hpδ.symm
    have heΓ : S (b6m_H1Equiv e (b6m_loopClass C Γ)) =
        S (b6m_H1Equiv e (b6m_loopClass C γ)) := by rw [← hU, ← hU, hΓ]
    have heΔ : S (b6m_H1Equiv e (b6m_loopClass C Δ)) =
        S (b6m_H1Equiv e (b6m_loopClass C δ)) := by rw [← hU, ← hU, hΔ]
    rw [heΓ, heΔ, hΓ, hΔ]
    exact b6m_pairing_matched_real e γ δ γ' δ' (fun s ↦ (hγ s).symm)
      (fun s ↦ (hδ s).symm) (fun s t h ↦ (hreg s t h).1)
      (fun s t h ↦ (hreg s t h).2) htr P hP S hS Q hQ R hR
  exact congrArg (fun B : LinearMap.BilinForm ℤ (b6m_H1 C) ↦ B x y) hforms

theorem b6m_intersection_transport_of_torsionFree
    (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc b)
    (C D : Type) [TopologicalSpace C] [TopologicalSpace D]
    [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D]
    [Module.IsTorsionFree ℤ (b6m_H1 C)] [Module.IsTorsionFree ℤ (b6m_H1 D)]
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k) (hs : Function.Surjective f)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ : b3_IsIntersectionForm ℂ Q)
    (R : LinearMap.BilinForm ℤ (b3_periodLattice ℂ D)) (hR : b3_IsIntersectionForm ℂ R) :
    ∃ (P : b6m_H1 C ≃ₗ[ℤ] b3_periodLattice ℂ C)
      (S : b6m_H1 D ≃ₗ[ℤ] b3_periodLattice ℂ D),
      (∀ γ : b3_SmoothLoop ℂ C, P (b6m_loopClass C γ) = b3_latticePeriod ℂ C γ) ∧
      (∀ γ : b3_SmoothLoop ℂ D, S (b6m_loopClass D γ) = b3_latticePeriod ℂ D γ) ∧
      ∀ x y : b6m_H1 C,
        R (S (b6m_H1Equiv e x)) (S (b6m_H1Equiv e y)) = Q (P x) (P y) := by
  obtain ⟨p, hp⟩ := hs ((0 : ℂ) : OnePoint ℂ)
  obtain ⟨q, hq⟩ := hs ((1 : ℂ) : OnePoint ℂ)
  have hpq : f p ≠ f q := by
    rw [hp, hq]
    exact fun h ↦ zero_ne_one (OnePoint.coe_injective h)
  obtain ⟨E, hE⟩ := b6t_homeomorph b hb t ht
  have hkpq : k (e p) ≠ k (e q) := by
    rw [he, he, ← hE, ← hE]
    exact fun h ↦ hpq (E.injective h)
  obtain ⟨P, hP⟩ := b6m_period_comparison_of_torsionFree C
  obtain ⟨S, hS⟩ := b6m_period_comparison_of_torsionFree D
  exact ⟨P, S, hP, hS, b6m_filling_pairing_transport b t hb ht f k hf hk
    ⟨p, q, hpq⟩ ⟨e p, e q, hkpq⟩ e he P.toLinearMap hP S.toLinearMap hS Q hQ R hR⟩

end HodgeLean.Foundations.Program
