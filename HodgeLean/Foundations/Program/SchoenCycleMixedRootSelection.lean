import HodgeLean.Foundations.Program.SchoenCycleMonicRootSelection

/-! # Exact small roots of every retained collision block -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology MvPolynomial
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- Select exact roots in every specified collision block and transport them through the specified coordinate enumeration.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, §3. -/
def s2e_mixedCoefficientRootSelection {n b : ℕ} (m : Fin b → ℕ)
    (ι : (Σ a, Fin (m a)) ≃ Fin n) (v : Fin n → ℂ) : Fin n → ℂ := fun i =>
  s2e_monicCoefficientRootSelection (m (ι.symm i).1)
    (fun j => v (ι ⟨(ι.symm i).1, j⟩)) (ι.symm i).2

/-- The mixed exact root selection restricts to the specified root selection on each original block.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, §3. -/
theorem s2e_mixedCoefficientRootSelection_apply {n b : ℕ} (m : Fin b → ℕ)
    (ι : (Σ a, Fin (m a)) ≃ Fin n) (v : Fin n → ℂ) (a : Fin b) (j : Fin (m a)) :
    s2e_mixedCoefficientRootSelection m ι v (ι ⟨a, j⟩) =
      s2e_monicCoefficientRootSelection (m a) (fun l => v (ι ⟨a, l⟩)) j := by
  exact congrArg (fun t : Σ a, Fin (m a) =>
    s2e_monicCoefficientRootSelection (m t.1) (fun l => v (ι ⟨t.1, l⟩)) t.2)
    (ι.symm_apply_apply ⟨a, j⟩)

/-- Exact mixed root selections recover the prescribed signed coefficient in every original block.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, §3. -/
theorem s2e_mixedCoefficientRootSelection_coefficient {n b : ℕ} (m : Fin b → ℕ)
    (ι : (Σ a, Fin (m a)) ≃ Fin n) (v : Fin n → ℂ) (a : Fin b) (j : Fin (m a)) :
    (-1 : ℂ) ^ (m a - j.val) *
      MvPolynomial.aeval (fun i => s2e_mixedCoefficientRootSelection m ι v (ι ⟨a, i⟩))
        (MvPolynomial.esymm (Fin (m a)) ℂ (m a - j.val)) = v (ι ⟨a, j⟩) := by
  simpa only [s2e_mixedCoefficientRootSelection_apply] using
    s2e_monicCoefficientRootSelection_coefficient (m a) (fun l => v (ι ⟨a, l⟩)) j

/-- All exact mixed root coordinates tend simultaneously to their retained collision centres.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, §3. -/
theorem s2e_mixedCoefficientRootSelection_tendsto_zero {n b : ℕ} (m : Fin b → ℕ)
    (ι : (Σ a, Fin (m a)) ≃ Fin n) :
    Tendsto (s2e_mixedCoefficientRootSelection m ι) (𝓝 0) (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  obtain ⟨⟨a, j⟩, rfl⟩ := ι.surjective i
  have hc : Tendsto (fun v : Fin n → ℂ => fun l : Fin (m a) => v (ι ⟨a, l⟩))
      (𝓝 0) (𝓝 0) :=
    (continuous_pi (fun l => continuous_apply (ι ⟨a, l⟩))).tendsto 0
  have hr := (s2e_monicCoefficientRootSelection_tendsto_zero (m a)).comp hc
  have h := ((continuous_apply j : Continuous (fun z : Fin (m a) → ℂ => z j)).tendsto 0).comp hr
  simpa only [Function.comp_def, s2e_mixedCoefficientRootSelection_apply, Pi.zero_apply] using h

/-- Zero mixed coefficients select exactly the zero root vector, retaining every block enumeration.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, §3. -/
theorem s2e_mixedCoefficientRootSelection_zero {n b : ℕ} (m : Fin b → ℕ)
    (ι : (Σ a, Fin (m a)) ≃ Fin n) :
    s2e_mixedCoefficientRootSelection m ι 0 = 0 := by
  apply pure_le_nhds_iff.mp
  have h := (s2e_mixedCoefficientRootSelection_tendsto_zero m ι).mono_left
    (pure_le_nhds (0 : Fin n → ℂ))
  simpa only [Tendsto, Filter.map_pure] using h

/-- A map with the exact mixed coefficient germ has a local right inverse given by the selected exact mixed roots.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, §3. -/
theorem s2e_mixedCoefficientRootSelection_right_inverse {n b : ℕ} (m : Fin b → ℕ)
    (ι : (Σ a, Fin (m a)) ≃ Fin n) (F : (Fin n → ℂ) → (Fin n → ℂ))
    (hF : ∀ᶠ z : Fin n → ℂ in 𝓝 0, ∀ a (j : Fin (m a)),
      F z (ι ⟨a, j⟩) = (-1 : ℂ) ^ (m a - j.val) *
        aeval (fun i => z (ι ⟨a, i⟩)) (esymm (Fin (m a)) ℂ (m a - j.val))) :
    ∀ᶠ v : Fin n → ℂ in 𝓝 0, F (s2e_mixedCoefficientRootSelection m ι v) = v := by
  filter_upwards [(s2e_mixedCoefficientRootSelection_tendsto_zero m ι).eventually hF] with v hv
  funext i
  obtain ⟨⟨a, j⟩, rfl⟩ := ι.surjective i
  rw [hv a j, s2e_mixedCoefficientRootSelection_coefficient]

end HodgeLean.Foundations.Program
