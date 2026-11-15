module

public import HodgeLean.Foundations.Mathlib.FredholmAnalyticSchur
public import HodgeLean.Foundations.Mathlib.FredholmAnalyticMatrix

/-! # Analytic kernel frames for constant-dimension analytic Fredholm families -/

@[expose] public noncomputable section

open Set Filter Topology Module

namespace HodgeLean.Foundations

/-- The Schur reduction `b63r_schur_core` at `T t₀` turns the kernels of `T t` into the kernels of
an analytic matrix family of constant rank, to which `b63r_matrix_frame_core` applies. -/
theorem b63r_frame_core {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {k d : ℕ} (W : Set (Fin k → ℂ)) (hW : IsOpen W) (T : (Fin k → ℂ) → E →L[ℂ] F)
    (hT : AnalyticOnNhd ℂ T W) (t₀ : Fin k → ℂ) (ht₀ : t₀ ∈ W) (hF : (T t₀).IsFredholm)
    (hd : ∀ t ∈ W, finrank ℂ ((T t).ker) = d) :
    ∃ W' : Set (Fin k → ℂ), IsOpen W' ∧ t₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ e : Fin d → (Fin k → ℂ) → E, (∀ i, AnalyticOnNhd ℂ (e i) W') ∧
        ∀ t ∈ W', LinearIndependent ℂ (fun i ↦ e i t) ∧
          Submodule.span ℂ (Set.range fun i ↦ e i t) = (T t).ker := by
  obtain ⟨𝒰, h𝒰, hT₀, M, L, hM, hL, -, hML⟩ := b63r_schur_core (T t₀) hF
  generalize hq : finrank ℂ (T t₀).ker = q at M L
  generalize finrank ℂ (F ⧸ (T t₀).range) = p at M
  set W₁ := W ∩ T ⁻¹' 𝒰 with hW₁
  have hW₁o : IsOpen W₁ := hT.continuousOn.isOpen_inter_preimage hW h𝒰
  have hMT : AnalyticOnNhd ℂ (fun t ↦ M (T t)) W₁ := fun t ht ↦ (hM _ ht.2).comp (hT t ht.1)
  have hLT : AnalyticOnNhd ℂ (fun t ↦ L (T t)) W₁ := fun t ht ↦ (hL _ ht.2).comp (hT t ht.1)
  let N : (Fin k → ℂ) → Matrix (Fin p) (Fin q) ℂ :=
    fun t ↦ LinearMap.toMatrix' (M (T t)).toLinearMap
  have hNlin : ∀ t, (N t).mulVecLin = (M (T t)).toLinearMap := fun t ↦ by
    rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  have hN : ∀ i j, AnalyticOnNhd ℂ (fun t ↦ N t i j) W₁ := by
    intro i j t ht
    have hc : AnalyticAt ℂ (fun A : (Fin q → ℂ) →L[ℂ] (Fin p → ℂ) ↦ A (Pi.single j 1) i)
        (M (T t)) := by
      have := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin p ↦ ℂ) i).comp
        (ContinuousLinearMap.apply ℂ (Fin p → ℂ) (Pi.single j 1))).analyticAt (M (T t))
      exact this
    have h2 := AnalyticAt.comp (f := fun t ↦ M (T t)) hc (hMT t ht)
    simp only [N, LinearMap.toMatrix'_apply]
    exact h2
  -- the kernel of `M (T t)` has dimension `d`
  have hker : ∀ t ∈ W₁, finrank ℂ (LinearMap.ker (N t).mulVecLin) = d := by
    intro t ht
    rw [hNlin, ← hd t ht.1, ← (hML _ ht.2).2]
    exact (LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective _ (hML _ ht.2).1 (LinearMap.ker (M (T t)).toLinearMap)))
  have hrank : ∀ t ∈ W₁, (N t).rank = q - d := by
    intro t ht
    have := LinearMap.finrank_range_add_finrank_ker (N t).mulVecLin
    rw [hker t ht, Module.finrank_fin_fun] at this
    rw [Matrix.rank]
    omega
  have hdq : d ≤ q := by
    have := LinearMap.finrank_range_add_finrank_ker (N t₀).mulVecLin
    rw [hker t₀ ⟨ht₀, hT₀⟩, Module.finrank_fin_fun] at this
    omega
  obtain ⟨W', hW'o, ht₀', hW'W₁, v, hv, hvt⟩ :=
    b63r_matrix_frame_core W₁ hW₁o N hN hrank t₀ ⟨ht₀, hT₀⟩
  have hcard : q - (q - d) = d := Nat.sub_sub_self hdq
  refine ⟨W', hW'o, ht₀', hW'W₁.trans inter_subset_left,
    fun i t ↦ L (T t) (v (Fin.cast hcard.symm i) t), fun i t ht ↦ ?_, fun t ht ↦ ?_⟩
  · exact ((ContinuousLinearMap.apply ℂ E).analyticAt_bilinear _).comp₂
      (hv _ t ht) (hLT t (hW'W₁ ht))
  · obtain ⟨hli, hsp⟩ := hvt t ht
    have ht₁ := hW'W₁ ht
    refine ⟨?_, ?_⟩
    · have := (hli.map' (L (T t)).toLinearMap
        (LinearMap.ker_eq_bot.mpr (hML _ ht₁.2).1)).comp _ (Fin.cast_injective hcard.symm)
      exact this
    · have hr : (Set.range fun i ↦ L (T t) (v (Fin.cast hcard.symm i) t)) =
          (L (T t)).toLinearMap '' Set.range fun i ↦ v i t := by
        rw [← Set.range_comp]
        exact (finCongr hcard.symm).surjective.range_comp (fun i ↦ L (T t) (v i t))
      rw [hr, ← Submodule.map_span, hsp, hNlin, (hML _ ht₁.2).2]

end HodgeLean.Foundations
