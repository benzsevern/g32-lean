import HodgeLean.Foundations.Program.G32Native.ConormalEvaluationContinuity

/-! # Local evaluation maps for the actual dual-module topology -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- Evaluation against an actual local section is continuous on its base open. -/
theorem continuous_normalLocalEvaluation
    {Q : Over (Spec ↧ℂ)} (M : Q.left.Modules) (k : ℕ)
    (U : Q.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj M) :
    letI := normalEvaluationTopology M k
    Continuous (fun z : {v : TotalSpace (Fin k → ℂ) (normalFibreOfModule M) |
      v.proj ∈ Point.overOpen U} => z.1.2 (moduleSectionValue M U s z.1.proj z.2)) := by
  letI := normalEvaluationTopology M k
  apply continuous_def.mpr
  intro O hO
  have hgen : IsOpen {v : TotalSpace (Fin k → ℂ) (normalFibreOfModule M) |
      ∃ hx : v.proj ∈ Point.overOpen U,
        v.2 (moduleSectionValue M U s v.proj hx) ∈ O} :=
    isOpen_generateFrom_of_mem (Or.inr ⟨U, s, O, hO, rfl⟩)
  have heq : (fun z : {v : TotalSpace (Fin k → ℂ) (normalFibreOfModule M) |
      v.proj ∈ Point.overOpen U} => z.1.2 (moduleSectionValue M U s z.1.proj z.2)) ⁻¹' O =
      Subtype.val ⁻¹' {v : TotalSpace (Fin k → ℂ) (normalFibreOfModule M) |
        ∃ hx : v.proj ∈ Point.overOpen U,
          v.2 (moduleSectionValue M U s v.proj hx) ∈ O} := by
    ext z
    exact ⟨fun hz => ⟨z.2, hz⟩, fun ⟨_, hz⟩ => hz⟩
  rw [heq]
  exact hgen.preimage continuous_subtype_val

#print axioms continuous_normalLocalEvaluation

/-- A continuous base map and continuous local evaluations give a continuous
map into the dual-module total space. -/
theorem continuous_normalEvaluation_of_localEvaluations
    {Q : Over (Spec ↧ℂ)} (M : Q.left.Modules) (k : ℕ)
    {T : Type*} [TopologicalSpace T]
    (f : T → TotalSpace (Fin k → ℂ) (normalFibreOfModule M))
    (hb : Continuous (fun t => (f t).proj))
    (he : ∀ (U : Q.left.Opens)
      (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
        (Scheme.Modules.pullback U.ι).obj M),
      Continuous (fun t : {t : T | (f t).proj ∈ Point.overOpen U} =>
        (f t.1).2 (moduleSectionValue M U s (f t.1).proj t.2))) :
    @Continuous _ _ _ (normalEvaluationTopology M k) f := by
  apply (continuous_normalEvaluation_iff M k f).mpr
  refine ⟨hb, ?_⟩
  intro U s O hO
  have hU : IsOpen {t : T | (f t).proj ∈ Point.overOpen U} :=
    (Point.isOpen_overOpen U).preimage hb
  have hE := hU.isOpenMap_subtype_val _ ((he U s).isOpen_preimage O hO)
  have hset : Subtype.val ''
      ((fun t : {t : T | (f t).proj ∈ Point.overOpen U} =>
        (f t.1).2 (moduleSectionValue M U s (f t.1).proj t.2)) ⁻¹' O) =
      {t | ∃ hx : (f t).proj ∈ Point.overOpen U,
        (f t).2 (moduleSectionValue M U s (f t).proj hx) ∈ O} := by
    ext t
    constructor
    · rintro ⟨⟨u, hu⟩, hv, rfl⟩
      exact ⟨hu, hv⟩
    · rintro ⟨ht, hv⟩
      exact ⟨⟨t, ht⟩, hv, rfl⟩
  rwa [hset] at hE

#print axioms continuous_normalEvaluation_of_localEvaluations

end HodgeLean.Foundations.Program.G32Native
