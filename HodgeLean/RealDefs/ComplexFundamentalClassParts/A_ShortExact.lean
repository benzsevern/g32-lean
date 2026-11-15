import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Cokernel rows of monomorphisms of short exact sequences

In an abelian category, let `L₁ ⟶ L₂ ⟶ L₃` be maps of short complexes whose three columns are
short exact. If `L₁` and `L₂` are short exact, so is `L₃`. This is the snake lemma with zero
kernel row.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HodgeLean.RealDefs

variable {C : Type*} [Category C] [Abelian C]

/-- The cokernel row of a degreewise-monomorphic map of short exact sequences is short exact. -/
theorem shortExact_of_shortExact_columns {L₁ L₂ L₃ : ShortComplex C}
    (v₁₂ : L₁ ⟶ L₂) (v₂₃ : L₂ ⟶ L₃) (w : v₁₂ ≫ v₂₃ = 0)
    (h₁ : L₁.ShortExact) (h₂ : L₂.ShortExact)
    (c₁ : (ShortComplex.mk v₁₂.τ₁ v₂₃.τ₁
      (by rw [← ShortComplex.comp_τ₁, w, ShortComplex.zero_τ₁])).ShortExact)
    (c₂ : (ShortComplex.mk v₁₂.τ₂ v₂₃.τ₂
      (by rw [← ShortComplex.comp_τ₂, w, ShortComplex.zero_τ₂])).ShortExact)
    (c₃ : (ShortComplex.mk v₁₂.τ₃ v₂₃.τ₃
      (by rw [← ShortComplex.comp_τ₃, w, ShortComplex.zero_τ₃])).ShortExact) :
    L₃.ShortExact := by
  have := h₁.epi_g
  have := h₂.mono_f
  have := h₂.epi_g
  have := c₁.epi_g
  have := c₂.epi_g
  have := c₃.epi_g
  have : Mono v₁₂.τ₃ := c₃.mono_f
  let S : ShortComplex.SnakeInput C :=
    { L₀ := kernel v₁₂
      L₁ := L₁
      L₂ := L₂
      L₃ := L₃
      v₀₁ := kernel.ι v₁₂
      v₁₂ := v₁₂
      v₂₃ := v₂₃
      w₀₂ := kernel.condition v₁₂
      w₁₃ := w
      h₀ := kernelIsKernel v₁₂
      h₃ := by
        apply ShortComplex.isColimitOfIsColimitπ
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm c₁.exact.gIsCokernel
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm c₂.exact.gIsCokernel
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm c₃.exact.gIsCokernel
      L₁_exact := h₁.exact
      epi_L₁_g := h₁.epi_g
      L₂_exact := h₂.exact
      mono_L₂_f := h₂.mono_f }
  have h0 : S.v₀₁.τ₃ = 0 := (cancel_mono v₁₂.τ₃).1 (by
    rw [zero_comp, ← ShortComplex.comp_τ₃]
    exact congrArg ShortComplex.Hom.τ₃ S.w₀₂)
  have : Mono S.v₀₁.τ₃ := ShortComplex.SnakeInput.mono_v₀₁_τ₃ S
  have hz : IsZero S.L₀.X₃ := IsZero.of_mono_eq_zero _ h0
  have hm : Mono S.L₂'.g := S.L₂'_exact.mono_g (hz.eq_of_src S.δ 0)
  have : Epi S.L₂.g := h₂.epi_g
  exact
    { exact := S.L₃_exact
      mono_f := hm
      epi_g := S.epi_L₃_g }

/-- The biproduct of two short exact sequences is short exact. -/
theorem biprod_shortExact {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact) :
    (ShortComplex.mk (biprod.map S.f T.f) (biprod.map S.g T.g)
      (by ext <;> simp)).ShortExact := by
  have := hS.mono_f
  have := hT.mono_f
  have := hS.epi_g
  have := hT.epi_g
  refine { exact := ?_, mono_f := by dsimp; infer_instance, epi_g := by dsimp; infer_instance }
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro W x₂ hx₂
  dsimp at x₂ hx₂
  have h1 : (x₂ ≫ biprod.fst) ≫ S.g = 0 := by
    have := hx₂ =≫ biprod.fst
    simpa using this
  obtain ⟨W', π, hπ, y, hy⟩ := hS.exact.exact_up_to_refinements (x₂ ≫ biprod.fst) h1
  have h2 : (π ≫ x₂ ≫ biprod.snd) ≫ T.g = 0 := by
    have := hx₂ =≫ biprod.snd
    simp only [Category.assoc, biprod.map_snd, zero_comp] at this
    simp [this]
  obtain ⟨W'', π', hπ', z, hz⟩ := hT.exact.exact_up_to_refinements (π ≫ x₂ ≫ biprod.snd) h2
  refine ⟨W'', π' ≫ π, epi_comp _ _, biprod.lift (π' ≫ y) z, ?_⟩
  dsimp
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc]
    rw [← hy]
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc]
    rw [← hz]

end HodgeLean.RealDefs
