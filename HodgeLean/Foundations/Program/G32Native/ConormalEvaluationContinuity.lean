import HodgeLean.Foundations.Program.G32Native.CanonicalConormalEvaluation

/-! # Continuity criteria for the retained evaluation topologies -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Bundle
namespace HodgeLean.Foundations.Program.G32Native

/-- Continuity into the dual-module total space can be tested on base opens and
local section evaluations. -/
theorem continuous_normalEvaluation_iff
    {Q : Over (Spec ↧ℂ)} (M : Q.left.Modules) (k : ℕ)
    {T : Type*} [TopologicalSpace T]
    (f : T → TotalSpace (Fin k → ℂ) (normalFibreOfModule M)) :
    @Continuous _ _ _ (normalEvaluationTopology M k) f ↔
      Continuous (fun t => (f t).proj) ∧
      ∀ (U : Q.left.Opens)
        (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
          (Scheme.Modules.pullback U.ι).obj M)
        (O : Set ℂ), IsOpen O →
        IsOpen {t | ∃ hx : (f t).proj ∈ Point.overOpen U,
          (f t).2 (moduleSectionValue M U s (f t).proj hx) ∈ O} := by
  letI := normalEvaluationTopology M k
  rw [continuous_generateFrom_iff]
  constructor
  · intro h
    constructor
    · apply continuous_def.mpr
      intro O hO
      exact h _ (Or.inl ⟨O, hO, rfl⟩)
    · intro U s O hO
      exact h _ (Or.inr ⟨U, s, O, hO, rfl⟩)
  · rintro ⟨hb, hs⟩ A (⟨O, hO, rfl⟩ | ⟨U, s, O, hO, rfl⟩)
    · exact hb.isOpen_preimage O hO
    · exact hs U s O hO

/-- Coefficient continuity is exactly continuity of the base and every fixed
homogeneous evaluation. -/
theorem continuous_coefficientTotal_iff (G : CanonicalAbelGeometry)
    {T : Type*} [TopologicalSpace T]
    (f : T → TotalSpace (Fin G.k → ℂ)
      (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator)) :
    @Continuous _ _ _ (coefficientTotalTopology G) f ↔
      Continuous (fun t => (f t).proj) ∧
      ∀ a : Fin (G.k + 1) → ℂ, Continuous (fun t => (f t).2.1 a) := by
  unfold coefficientTotalTopology
  rw [continuous_induced_rng]
  change Continuous (fun t => ((f t).proj, fun a : Fin (G.k + 1) → ℂ =>
    (f t).2.1 a)) ↔ _
  rw [continuous_prodMk, continuous_pi_iff]

/-- Only the ordered coordinate evaluations are needed to test coefficient
continuity; all other homogeneous evaluations are their finite linear combinations. -/
theorem continuous_coefficientTotal_coordinates_iff (G : CanonicalAbelGeometry)
    {T : Type*} [TopologicalSpace T]
    (f : T → TotalSpace (Fin G.k → ℂ)
      (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator)) :
    @Continuous _ _ _ (coefficientTotalTopology G) f ↔
      Continuous (fun t => (f t).proj) ∧
      ∀ i : Fin (G.k + 1), Continuous (fun t => (f t).2.1 (Pi.single i 1)) := by
  rw [continuous_coefficientTotal_iff]
  constructor
  · rintro ⟨hb, he⟩
    exact ⟨hb, fun i => he (Pi.single i 1)⟩
  · rintro ⟨hb, he⟩
    refine ⟨hb, fun a => ?_⟩
    have ha : a = ∑ i : Fin (G.k + 1), a i • Pi.single i (1 : ℂ) := by
      ext j
      simp [Pi.smul_apply, Pi.single_apply]
    have hf : (fun t => (f t).2.1 a) =
        (fun t => ∑ i : Fin (G.k + 1), a i * (f t).2.1 (Pi.single i 1)) := by
      funext t
      conv_lhs => rw [ha]
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [hf]
    exact continuous_finset_sum _ (fun i _ => continuous_const.mul (he i))

/-- Projection to the original point is continuous for the local-section topology. -/
theorem continuous_normalEvaluation_proj
    {Q : Over (Spec ↧ℂ)} (M : Q.left.Modules) (k : ℕ) :
    @Continuous (TotalSpace (Fin k → ℂ) (normalFibreOfModule M)) (ComplexPoint Q)
      (normalEvaluationTopology M k) inferInstance TotalSpace.proj := by
  letI := normalEvaluationTopology M k
  apply continuous_def.mpr
  intro O hO
  exact isOpen_generateFrom_of_mem (Or.inl ⟨O, hO, rfl⟩)

#print axioms continuous_normalEvaluation_iff
#print axioms continuous_coefficientTotal_iff
#print axioms continuous_normalEvaluation_proj
#print axioms continuous_coefficientTotal_coordinates_iff
end HodgeLean.Foundations.Program.G32Native
