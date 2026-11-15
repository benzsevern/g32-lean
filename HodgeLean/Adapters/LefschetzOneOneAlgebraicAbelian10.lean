import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian10Proofs

/-! # Reduced factors and equation-adapted regular charts

Implications from reduced analytic germs and regular-zero data. These are intermediate
segments; analytic purity and component-class gluing require further work.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Adapters

/-- No irreducible factor of a reduced equation divides all its directional derivatives.
Source: Gunning--Rossi, Analytic Functions of Several Complex Variables, Chapter II.B,
unique factorization of convergent power series; the product rule and
`bh9_irreducible_derivative_aux`. -/
theorem bh10_reduced_factor_derivative (n : ℕ) (p : Fin n → ℂ)
    (f g : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hred : Squarefree (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p))
    (hi : IsIrreducibleAt g p)
    (hdiv : ∃ h : (Fin n → ℂ) → ℂ, AnalyticAt ℂ h p ∧
      f =ᶠ[𝓝 p] (fun z ↦ g z * h z)) :
    ∃ v : Fin n → ℂ, ¬ ∃ h : (Fin n → ℂ) → ℂ,
      AnalyticAt ℂ h p ∧
      (fun z ↦ fderiv ℂ f z v) =ᶠ[𝓝 p] (fun z ↦ g z * h z) :=
  bh10_reduced_factor_derivative_aux n p f g hf hg hred hi hdiv

/-- A regular zero admits a holomorphic coordinate chart whose last coordinate is the equation.
Source: Gunning--Rossi, Chapter I.B, the holomorphic implicit function theorem. -/
theorem bh10_equation_chart (n : ℕ) (p : Fin (n + 1) → ℂ)
    (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticAt ℂ f p)
    (hp : f p = 0) (hd : fderiv ℂ f p ≠ 0) :
    ∃ e : OpenPartialHomeomorph (Fin (n + 1) → ℂ)
        ((Fin n → ℂ) × (Fin 1 → ℂ)),
      p ∈ e.source ∧ AnalyticOnNhd ℂ e e.source ∧
      AnalyticOnNhd ℂ e.symm e.target ∧
      ∀ y ∈ e.source, (e y).2 0 = f y :=
  bh10_equation_chart_aux n p f hf hp hd

open HodgeLean.Foundations.AnalyticDivisorAlgebraic18

example : ∃ v : Fin 2 → ℂ, ¬ ∃ h : (Fin 2 → ℂ) → ℂ,
    AnalyticAt ℂ h 0 ∧
    (fun z ↦ fderiv ℂ gaga18_axis z v) =ᶠ[𝓝 0]
      (fun z ↦ gaga18_axis z * h z) := by
  have hf := gaga18_concrete_data.1
  have hu : AnalyticAt ℂ gaga18_unit 0 := by
    unfold gaga18_unit
    exact analyticAt_const.add ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticAt 0)
  have hug := hu.mul hf
  exact bh10_reduced_factor_derivative 2 0 gaga18_axis gaga18_axis hf hf
    (gaga18_reduced_unit_data hf hug).1 gaga18_concrete_data.2.1
    ⟨fun _ ↦ 1, analyticAt_const, Filter.Eventually.of_forall (by simp)⟩

example : ∃ v : Fin 2 → ℂ, ¬ ∃ h : (Fin 2 → ℂ) → ℂ,
    AnalyticAt ℂ h 0 ∧
    (fun z ↦ fderiv ℂ (fun w ↦ gaga18_unit w * gaga18_axis w) z v) =ᶠ[𝓝 0]
      (fun z ↦ gaga18_axis z * h z) := by
  have hf := gaga18_concrete_data.1
  have hu : AnalyticAt ℂ gaga18_unit 0 := by
    unfold gaga18_unit
    exact analyticAt_const.add
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticAt 0)
  exact bh10_reduced_factor_derivative 2 0 (fun z ↦ gaga18_unit z * gaga18_axis z)
    gaga18_axis (hu.mul hf) hf (gaga18_reduced_unit_data hf (hu.mul hf)).2
    gaga18_concrete_data.2.1
    ⟨gaga18_unit, hu, Filter.Eventually.of_forall (fun z ↦ mul_comm _ _)⟩

example : ∃ e : OpenPartialHomeomorph (Fin 1 → ℂ)
    ((Fin 0 → ℂ) × (Fin 1 → ℂ)),
    (0 : Fin 1 → ℂ) ∈ e.source ∧ AnalyticOnNhd ℂ e e.source ∧
    AnalyticOnNhd ℂ e.symm e.target ∧
    ∀ y ∈ e.source, (e y).2 0 = y 0 := by
  apply bh10_equation_chart 0 0 (fun z ↦ z 0) ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0) rfl
  intro h
  have h' := congrArg (fun L : (Fin 1 → ℂ) →L[ℂ] ℂ ↦ L (fun _ ↦ 1)) h
  change ((fderiv ℂ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0) 0) (fun _ ↦ 1)) = 0 at h'
  rw [ContinuousLinearMap.fderiv] at h'
  exact one_ne_zero h'

end HodgeLean.Adapters
