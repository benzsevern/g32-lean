import HodgeLean.Foundations.BundleThom.AnalyticNormalDefs

/-! # Continuity for algebraic evaluation coordinates

These maps use the specified topology before any bundle atlas is selected.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle
namespace HodgeLean.Foundations.BundleThom

variable {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V) (k : ℕ)
private local instance : TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

theorem i1_normalProjection_continuous : Continuous (TotalSpace.proj :
    TotalSpace (Fin k → ℂ) (i1_normalFibre j) → ComplexPoint Q) := by
  apply continuous_def.mpr
  intro O hO
  exact isOpen_generateFrom_of_mem (Or.inl ⟨O, hO, rfl⟩)

theorem i1_normalZeroSection_continuous :
    Continuous (zeroSection (Fin k → ℂ) (i1_normalFibre j)) := by
  apply continuous_generateFrom_iff.mpr
  intro A hA
  rcases hA with ⟨O, hO, rfl⟩ | ⟨U, s, O, hO, rfl⟩
  · exact hO
  · by_cases hzero : (0 : ℂ) ∈ O
    · have heq : (zeroSection (Fin k → ℂ) (i1_normalFibre j)) ⁻¹'
          {v | ∃ hx : v.proj ∈ Point.overOpen U,
            v.2 (i1_conormalSectionValue j U s v.proj hx) ∈ O} = Point.overOpen U := by
        ext x
        constructor
        · rintro ⟨hx, _⟩
          exact hx
        · intro hx
          exact ⟨hx, hzero⟩
      rw [heq]
      exact Point.isOpen_overOpen U
    · have heq : (zeroSection (Fin k → ℂ) (i1_normalFibre j)) ⁻¹'
          {v | ∃ hx : v.proj ∈ Point.overOpen U,
            v.2 (i1_conormalSectionValue j U s v.proj hx) ∈ O} = ∅ := by
        ext x
        constructor
        · rintro ⟨hx, hv⟩
          exact hzero hv
        · exact False.elim
      rw [heq]
      exact isOpen_empty

theorem i1_normalLocalEvaluation_continuous (U : Q.left.Opens)
    (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j)) :
    Continuous (fun z : {v : TotalSpace (Fin k → ℂ) (i1_normalFibre j) |
        v.proj ∈ Point.overOpen U} =>
      z.1.2 (i1_conormalSectionValue j U s z.1.proj z.2)) := by
  apply continuous_def.mpr
  intro O hO
  have h : IsOpen {v : TotalSpace (Fin k → ℂ) (i1_normalFibre j) |
      ∃ hx : v.proj ∈ Point.overOpen U,
        v.2 (i1_conormalSectionValue j U s v.proj hx) ∈ O} :=
    isOpen_generateFrom_of_mem (Or.inr ⟨U, s, O, hO, rfl⟩)
  have heq : (fun z : {v : TotalSpace (Fin k → ℂ) (i1_normalFibre j) |
        v.proj ∈ Point.overOpen U} =>
      z.1.2 (i1_conormalSectionValue j U s z.1.proj z.2)) ⁻¹' O =
      Subtype.val ⁻¹' {v : TotalSpace (Fin k → ℂ) (i1_normalFibre j) |
        ∃ hx : v.proj ∈ Point.overOpen U,
          v.2 (i1_conormalSectionValue j U s v.proj hx) ∈ O} := by
    ext z
    exact ⟨fun hz => ⟨z.2, hz⟩, fun ⟨_, hz⟩ => hz⟩
  rw [heq]
  exact h.preimage continuous_subtype_val

theorem i1_normalFibreInclusion_continuous (x : ComplexPoint Q) :
    @Continuous (i1_normalFibre j x)
      (TotalSpace (Fin k → ℂ) (i1_normalFibre j))
      (i1_normalFibreTopology j x) (i1_normalTotalTopology j k)
      (fun f => ⟨x, f⟩) := by
  letI := i1_normalFibreTopology j x
  apply continuous_generateFrom_iff.mpr
  intro A hA
  rcases hA with ⟨O, hO, rfl⟩ | ⟨U, s, O, hO, rfl⟩
  · exact hO.preimage continuous_const
  · by_cases hx : x ∈ Point.overOpen U
    · have heq : (fun f : i1_normalFibre j x =>
          (⟨x, f⟩ : TotalSpace (Fin k → ℂ) (i1_normalFibre j))) ⁻¹'
          {v | ∃ hv : v.proj ∈ Point.overOpen U,
            v.2 (i1_conormalSectionValue j U s v.proj hv) ∈ O} =
          (fun f : i1_normalFibre j x => f (i1_conormalSectionValue j U s x hx)) ⁻¹' O := by
        ext f
        exact ⟨fun ⟨_, hf⟩ => hf, fun hf => ⟨hx, hf⟩⟩
      rw [heq]
      exact hO.preimage ((continuous_apply _).comp continuous_induced_dom)
    · have heq : (fun f : i1_normalFibre j x =>
          (⟨x, f⟩ : TotalSpace (Fin k → ℂ) (i1_normalFibre j))) ⁻¹'
          {v | ∃ hv : v.proj ∈ Point.overOpen U,
            v.2 (i1_conormalSectionValue j U s v.proj hv) ∈ O} = ∅ := by
        ext f
        exact ⟨fun ⟨hv, _⟩ => hx hv, False.elim⟩
      rw [heq]
      exact isOpen_empty

theorem i1_normalZeroSection_isEmbedding :
    Topology.IsEmbedding (zeroSection (Fin k → ℂ) (i1_normalFibre j)) := by
  exact Function.LeftInverse.isEmbedding
    (f := (TotalSpace.proj : TotalSpace (Fin k → ℂ) (i1_normalFibre j) → ComplexPoint Q))
    (g := zeroSection (Fin k → ℂ) (i1_normalFibre j))
    (fun _ => rfl) (i1_normalProjection_continuous j k)
    (i1_normalZeroSection_continuous j k)

/-- Base continuity and continuity of each local evaluation suffice for a total-space map.
Source: Hartshorne, Algebraic Geometry, II.5, local coordinates for analytification. -/
theorem i1_normalTotal_continuous_of_evaluations {A : Type*} [TopologicalSpace A]
    (f : A → TotalSpace (Fin k → ℂ) (i1_normalFibre j))
    (hbase : Continuous (fun a => (f a).proj))
    (heval : ∀ (U : Q.left.Opens)
      (s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
        (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j)),
      Continuous (fun a : {a : A | (f a).proj ∈ Point.overOpen U} =>
        (f a.1).2 (i1_conormalSectionValue j U s (f a.1).proj a.2))) :
    Continuous f := by
  apply continuous_generateFrom_iff.mpr
  intro S hS
  rcases hS with ⟨O, hO, rfl⟩ | ⟨U, s, O, hO, rfl⟩
  · exact hO.preimage hbase
  · have hdomain : IsOpen {a : A | (f a).proj ∈ Point.overOpen U} :=
      (Point.isOpen_overOpen U).preimage hbase
    have heq : f ⁻¹' {v | ∃ hx : v.proj ∈ Point.overOpen U,
          v.2 (i1_conormalSectionValue j U s v.proj hx) ∈ O} =
        Subtype.val '' ((fun a : {a : A | (f a).proj ∈ Point.overOpen U} =>
          (f a.1).2 (i1_conormalSectionValue j U s (f a.1).proj a.2)) ⁻¹' O) := by
      ext a
      constructor
      · rintro ⟨ha, hv⟩
        exact ⟨⟨a, ha⟩, hv, rfl⟩
      · rintro ⟨⟨a, ha⟩, hv, rfl⟩
        exact ⟨ha, hv⟩
    rw [heq]
    exact hdomain.isOpenMap_subtype_val _ (hO.preimage (heval U s))

end HodgeLean.Foundations.BundleThom
