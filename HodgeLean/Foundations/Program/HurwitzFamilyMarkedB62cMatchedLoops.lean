import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLoopPaths

noncomputable section

namespace HodgeLean.Foundations.Program

open Manifold Filter Topology Set Metric
open scoped Manifold ContDiff

attribute [local instance] b3Forms_isManifold_real

theorem b6m_lineIntegral_eq_polygon {C : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    (L : b3Rest_Poly ℂ C) (p : ℝ → C)
    (hp : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 p)
    (hat : ∀ j : ℤ, p (j / L.N) = L.w j)
    (hmem : ∀ j : ℤ, ∀ s ∈ Icc ((j : ℝ) / L.N) ((j + 1) / L.N),
      p s ∈ (chartAt ℂ (L.x j)).source ∧
      chartAt ℂ (L.x j) (p s) ∈ ball (chartAt ℂ (L.x j) (L.x j)) (L.r j))
    {α : C → ℂ [⋀^Fin 1]→L[ℝ] ℝ} (hα : b3Forms_IsSmooth α) (hdα : b3Forms_d α = 0) :
    b3Forms_lineIntegral α p 0 1 = b3Forms_lineIntegral α L.loop 0 1 := by
  have hN : (0 : ℝ) < L.N := Nat.cast_pos.mpr L.pos
  have hlocal (j : ℤ) : b3Forms_lineIntegral α p ((j : ℝ) / L.N) ((j + 1) / L.N) =
      b3Forms_lineIntegral α L.loop ((j : ℝ) / L.N) ((j + 1) / L.N) := by
    obtain ⟨h, hh⟩ := b3Forms_exists_local_primitive hα hdα (L.x j) (convex_ball _ _)
      isOpen_ball (L.ball_sub j)
    have hle : (j : ℝ) / L.N ≤ (j + 1) / L.N := by gcongr; linarith
    have ep := b3Forms_lineIntegral_eq_of_primitive hα hh hp
      (fun s hs ↦ hmem j s (by rwa [uIcc_of_le hle] at hs))
    have eq := b3Forms_lineIntegral_eq_of_primitive hα hh L.loop_contMDiff
      (fun s hs ↦ L.loop_mem j (by rwa [uIcc_of_le hle] at hs))
    have hp1 : p ((j + 1) / L.N) = L.w (j + 1) := by
      simpa only [Int.cast_add, Int.cast_one] using hat (j + 1)
    have hL1 : L.loop ((j + 1) / L.N) = L.w (j + 1) := by
      simpa only [Int.cast_add, Int.cast_one] using L.loop_at (j + 1)
    rw [ep, eq, hat, L.loop_at, hp1, hL1]
  have hsum (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ) :
      ∑ i ∈ Finset.range L.N, b3Forms_lineIntegral α γ ((i : ℝ) / L.N) ((i + 1) / L.N) =
        b3Forms_lineIntegral α γ 0 1 := by
    have H := intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ ↦ (i : ℝ) / L.N)
      (n := L.N) (f := fun s ↦ α (γ s) (fun _ ↦ b3Forms_velocity γ s))
      (μ := MeasureTheory.volume)
      (fun i _ ↦ b3Forms_intervalIntegrable_lineIntegrand hα hγ _ _)
    simp only [Nat.cast_zero, zero_div, div_self hN.ne', Nat.cast_add, Nat.cast_one] at H
    exact H
  rw [← hsum p hp, ← hsum L.loop L.loop_contMDiff]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Int.cast_natCast] using hlocal (i : ℤ)

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6m_exists_matched_smoothLoop {C D : Type}
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace ℂ C] [ChartedSpace ℂ D]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [IsManifold 𝓘(ℂ, ℂ) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D]
    (b t : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (f : C → OnePoint ℂ) (k : D → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hk : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω k)
    (hfn : ∃ x y, f x ≠ f y) (hkn : ∃ x y, k x ≠ k y)
    (e : C ≃ₜ D) (he : ∀ x, k (e x) = b6t_sphere b t (f x))
    (Γ : b3_SmoothLoop ℂ C) :
    ∃ P : b3_SmoothLoop ℂ C, ∃ Q : b3_SmoothLoop ℂ D,
      (∀ s, Q.1 s = e (P.1 s)) ∧ b3_period ℂ C P = b3_period ℂ C Γ ∧
      (Set.range P.1 \ {x | ∃ z : ℂ, (z : OnePoint ℂ) = f x ∧
        ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b}).Finite := by
  obtain ⟨N, hN, x, r, hx, hr, hball, hmem⟩ :=
    b3Rest_exists_chartCover (E := ℂ) Γ.1 Γ.2.2.continuous Γ.2.1
  let K : b3Rest_Cover ℂ Γ.1 := ⟨N, hN, x, r, hx, hr, hball, hmem⟩
  obtain ⟨L, hLf, γ, hγper, hγ⟩ :=
    b6m_exists_matched_polygon_paths b t hb f k hf hk hfn hkn e he Γ.2.1 K
  obtain ⟨P, Q, hP, hQ⟩ := b6m_glue_matched_paths e L.N L.w γ hγper
    (fun j ↦ (hγ j).1) (fun j ↦ (hγ j).2.1)
  obtain ⟨hat, hPm⟩ := b6m_glued_path_chart_control L γ (fun j ↦ (hγ j).1)
    (fun j ↦ (hγ j).2.2.1) P.1 hP
  have hLI {α : C → ℂ [⋀^Fin 1]→L[ℝ] ℝ}
      (hα : b3Forms_IsSmooth α) (hdα : b3Forms_d α = 0) :
      b3Forms_lineIntegral α P.1 0 1 = b3Forms_lineIntegral α Γ.1 0 1 :=
    (b6m_lineIntegral_eq_polygon L P.1 P.2.2 hat hPm hα hdα).trans
      (b3Rest_Poly.lineIntegral_loop hLf Γ.2.2 Γ.2.1 hα hdα)
  refine ⟨P, Q, hQ, ?_, b6m_periodic_gluing_exceptional_finite L.N L.pos γ hγper _
    (fun j ↦ (hγ j).2.2.2) P.1 hP⟩
  funext θ
  have him : b3Forms_d (b3Forms_imForm θ) = 0 := by
    rw [b3Forms_imForm_eq]
    exact b3Forms_d_reForm (by simp : Module.finrank ℂ ℂ = 1) _
  rw [b3Forms_period_eq, b3Forms_period_eq]
  rw [hLI (b3Forms_isSmooth_reForm θ) (b3Forms_d_reForm (by simp) θ),
    hLI (b3Forms_isSmooth_imForm θ) him]

theorem b6m_exists_regular_matched_smoothLoop {C D : Type}
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
    (Γ : b3_SmoothLoop ℂ C) :
    ∃ P : b3_SmoothLoop ℂ C, ∃ Q : b3_SmoothLoop ℂ D, ∃ S : Set C, S.Finite ∧
      (∀ s, Q.1 s = e (P.1 s)) ∧ b3_period ℂ C P = b3_period ℂ C Γ ∧
      ∀ x ∈ Set.range P.1 \ S, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x ∧
        ∀ v w : ℂ, SignType.sign (b3_orient ℂ (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x v)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x w)) = SignType.sign (b3_orient ℂ v w) := by
  classical
  obtain ⟨P, Q, hQ, hP, hbad⟩ := b6m_exists_matched_smoothLoop b t hb f k hf hk hfn hkn e he Γ
  let F : Set C := Set.range P.1 \ {x | ∃ z : ℂ, (z : OnePoint ℂ) = f x ∧
    ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b}
  let A : Set C := {x | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x = 0}
  let B : Set D := {y | mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k y = 0}
  have hA : A.Finite := b4cov_critical_finite (by simp) f hf hfn
  have hB : B.Finite := b4cov_critical_finite (by simp) k hk hkn
  refine ⟨P, Q, F ∪ A ∪ e ⁻¹' B,
    (hbad.union hA).union (Set.Finite.preimage e.injective.injOn hB), hQ, hP, ?_⟩
  intro x hx
  have hreg : ∃ z : ℂ, (z : OnePoint ℂ) = f x ∧
      ∀ i, z ≠ b i ∧ dist z (b i) ≠ b6t_radius b := by
    by_contra h
    exact hx.2 (Or.inl (Or.inl ⟨hx.1, h⟩))
  obtain ⟨z, hz, hzr⟩ := hreg
  exact b6m_filling_comparison_regular b t hb ht f k hf hk e he x z hz.symm hzr
    (fun h ↦ hx.2 (Or.inl (Or.inr h))) (fun h ↦ hx.2 (Or.inr h))

end HodgeLean.Foundations.Program
