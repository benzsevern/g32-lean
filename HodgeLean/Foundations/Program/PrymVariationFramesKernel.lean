import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b63e_generalized_inverse {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (f : E →ₗ[ℂ] F) :
    ∃ g : F →ₗ[ℂ] E, f.comp (g.comp f) = f := by
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩))
  obtain ⟨g, hg⟩ := s.exists_extend
  refine ⟨g, ?_⟩
  ext x
  have h := LinearMap.congr_fun hs (f.rangeRestrict x)
  have h' := LinearMap.congr_fun hg (f.rangeRestrict x)
  change g (f x) = s (f.rangeRestrict x) at h'
  change f (g (f x)) = f x
  rw [h']
  exact congrArg Subtype.val h

theorem b63e_perturbation_kernel {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ E]
    (f₀ f : E →ₗ[ℂ] F) (g : F →ₗ[ℂ] E)
    (hg : f₀.comp (g.comp f₀) = f₀) (A : E ≃ₗ[ℂ] E)
    (hA : ∀ x, A x = x + g (f x - f₀ x))
    (hr : Module.finrank ℂ (LinearMap.range f) = Module.finrank ℂ (LinearMap.range f₀)) :
    (LinearMap.ker f).map A.toLinearMap = LinearMap.ker f₀ := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x, hx, rfl⟩
    change f₀ (A x) = 0
    rw [hA, LinearMap.mem_ker.mp hx, zero_sub, map_neg, map_add, map_neg]
    have h := LinearMap.congr_fun hg x
    change f₀ (g (f₀ x)) = f₀ x at h
    rw [h, add_neg_cancel]
  · rw [A.finrank_map_eq]
    have h₀ := f₀.finrank_range_add_finrank_ker
    have h := f.finrank_range_add_finrank_ker
    omega

set_option backward.isDefEq.respectTransparency false in
theorem b63e_kernel_frame {k m n r : ℕ} (W : Set (Fin k → ℂ)) (hW : IsOpen W)
    (M : (Fin k → ℂ) → Matrix (Fin m) (Fin n) ℂ)
    (hM : ∀ i j, AnalyticOnNhd ℂ (fun u ↦ M u i j) W)
    (hr : ∀ u ∈ W, (M u).rank = r) (u₀ : Fin k → ℂ) (hu₀ : u₀ ∈ W) :
    ∃ W' : Set (Fin k → ℂ), IsOpen W' ∧ u₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ c : Fin (n - r) → (Fin k → ℂ) → (Fin n → ℂ),
        (∀ i, AnalyticOnNhd ℂ (c i) W') ∧
        ∀ u ∈ W', LinearIndependent ℂ (fun i ↦ c i u) ∧
          Submodule.span ℂ (Set.range fun i ↦ c i u) = LinearMap.ker (M u).mulVecLin := by
  classical
  let E := Fin n → ℂ
  let f₀ := (M u₀).mulVecLin
  obtain ⟨g, hg⟩ := b63e_generalized_inverse f₀
  let T : (Fin m → Fin n → ℂ) →ₗ[ℂ] (E →L[ℂ] E) :=
    { toFun := fun N ↦ (g.comp (Matrix.mulVecLin N)).toContinuousLinearMap
      map_add' := by intros; ext x; simp
      map_smul' := by intros; ext x; simp }
  let A : (Fin k → ℂ) → (E →L[ℂ] E) := fun u ↦ 1 + T (M u - M u₀)
  have hA : AnalyticOnNhd ℂ A W := by
    intro u hu
    have hmat : AnalyticAt ℂ (fun v i j ↦ M v i j) u := .pi fun i ↦ .pi fun j ↦ hM i j u hu
    have hsub : AnalyticAt ℂ (fun v i j ↦ M v i j - M u₀ i j) u := hmat.sub analyticAt_const
    let Tc : (Fin m → Fin n → ℂ) →L[ℂ] (E →L[ℂ] E) := T.toContinuousLinearMap
    exact analyticAt_const.add ((Tc.analyticAt _).comp hsub)
  have hA₀ : A u₀ = 1 := by simp [A]
  have hne : {u | u ∈ W ∧ IsUnit (A u)} ∈ nhds u₀ :=
    Filter.inter_mem (hW.mem_nhds hu₀)
      ((hA u₀ hu₀).continuousAt (by simpa [hA₀] using
        (Units.isOpen.mem_nhds (isUnit_one : IsUnit (1 : E →L[ℂ] E)))))
  obtain ⟨W', hsub, hW', hu'⟩ := mem_nhds_iff.mp hne
  have hd : Module.finrank ℂ (LinearMap.ker f₀) = n - r := by
    have h := f₀.finrank_range_add_finrank_ker
    have hr₀ := hr u₀ hu₀
    change Module.finrank ℂ (LinearMap.range f₀) = r at hr₀
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    omega
  let B := Module.finBasisOfFinrankEq ℂ (LinearMap.ker f₀) hd
  let c := fun (i : Fin (n - r)) u ↦ Ring.inverse (A u) (B i).val
  refine ⟨W', hW', hu', fun u hu ↦ (hsub hu).1, c, ?_, ?_⟩
  · intro i u hu
    have hi : AnalyticAt ℂ (fun u ↦ Ring.inverse (A u)) u :=
      (analyticOnNhd_inverse (𝕜 := ℂ) (A := E →L[ℂ] E) (A u) (hsub hu).2).comp (hA u (hsub hu).1)
    exact (ContinuousLinearMap.apply ℂ E (B i).val).analyticAt _ |>.comp hi
  · intro u hu
    let e := (ContinuousLinearEquiv.ofUnit (hsub hu).2.unit).toLinearEquiv
    have he : ∀ x, e x = x + g ((M u).mulVecLin x - f₀ x) := by
      intro x
      change ((hsub hu).2.unit.val) x = _
      rw [IsUnit.unit_spec]
      change x + g ((M u - M u₀).mulVecLin x) = _
      rw [show (M u - M u₀).mulVecLin x = (M u).mulVecLin x - f₀ x by
        simpa only [f₀, Matrix.mulVecLin_apply] using Matrix.sub_mulVec (M u) (M u₀) x]
    have hk := b63e_perturbation_kernel f₀ (M u).mulVecLin g hg e he
      ((hr u (hsub hu).1).trans (hr u₀ hu₀).symm)
    have hc : ∀ i, c i u = e.symm (B i).val := by
      intro i
      change Ring.inverse (A u) (B i).val = _
      rw [Ring.inverse_of_isUnit (hsub hu).2]
      rfl
    have hB : LinearIndependent ℂ (fun i ↦ (B i).val) :=
      B.linearIndependent.map' (LinearMap.ker f₀).subtype (Submodule.ker_subtype _)
    have hs : Submodule.span ℂ (Set.range fun i ↦ (B i).val) = LinearMap.ker f₀ := by
      change Submodule.span ℂ (Set.range ((LinearMap.ker f₀).subtype ∘ B)) = _
      rw [Set.range_comp, ← Submodule.map_span, B.span_eq, Submodule.map_top,
        Submodule.range_subtype]
    simp_rw [hc]
    refine ⟨hB.map' e.symm.toLinearMap (LinearMap.ker_eq_bot.mpr e.symm.injective), ?_⟩
    change Submodule.span ℂ (Set.range (e.symm.toLinearMap ∘ (fun i ↦ (B i).val))) = _
    rw [Set.range_comp, ← Submodule.map_span, hs, ← hk]
    rw [← Submodule.map_comp]
    simp

set_option backward.isDefEq.respectTransparency false in
theorem b63e_kernel_frame_of_nullity {k m n g : ℕ} (W : Set (Fin k → ℂ)) (hW : IsOpen W)
    (M : (Fin k → ℂ) → Matrix (Fin m) (Fin n) ℂ)
    (hM : ∀ i j, AnalyticOnNhd ℂ (fun u ↦ M u i j) W)
    (hg : ∀ u ∈ W, Module.finrank ℂ (LinearMap.ker (M u).mulVecLin) = g)
    (u₀ : Fin k → ℂ) (hu₀ : u₀ ∈ W) :
    ∃ W' : Set (Fin k → ℂ), IsOpen W' ∧ u₀ ∈ W' ∧ W' ⊆ W ∧
      ∃ c : Fin g → (Fin k → ℂ) → (Fin n → ℂ),
        (∀ i, AnalyticOnNhd ℂ (c i) W') ∧
        ∀ u ∈ W', LinearIndependent ℂ (fun i ↦ c i u) ∧
          Submodule.span ℂ (Set.range fun i ↦ c i u) = LinearMap.ker (M u).mulVecLin := by
  have hr u (hu : u ∈ W) : (M u).rank = n - g := by
    have h := (M u).mulVecLin.finrank_range_add_finrank_ker
    rw [hg u hu, Module.finrank_fin_fun] at h
    change (M u).rank + g = n at h
    omega
  have hd : n - (n - g) = g := by
    have h := (M u₀).mulVecLin.finrank_range_add_finrank_ker
    rw [hg u₀ hu₀, Module.finrank_fin_fun] at h
    omega
  have h := b63e_kernel_frame W hW M hM hr u₀ hu₀
  rw [hd] at h
  exact h

end HodgeLean.Foundations.Program
