import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The dense complement used by the union conormal map -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program.G32Native

/-- Noncontainment in a second component gives a dense open subset of the first. -/
lemma union_component_complement_dense
    {V T₁ T₂ : Scheme} [IsIntegral T₁]
    (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V) [IsClosedImmersion t₂]
    (hnot : ¬ Set.range t₁ ⊆ Set.range t₂) :
    Dense (t₁ ⁻¹' (Set.range t₂)ᶜ) := by
  apply IsOpen.dense
  · exact t₂.isClosedEmbedding.isClosed_range.isOpen_compl.preimage t₁.continuous
  · obtain ⟨v, hv, hv₂⟩ := Set.not_subset.mp hnot
    obtain ⟨x, rfl⟩ := hv
    exact ⟨x, hv₂⟩

/-- The generic point of the first component avoids the second component. -/
lemma union_genericPoint_not_mem_second
    {V T₁ T₂ : Scheme} [IsIntegral T₁]
    (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V) [IsClosedImmersion t₂]
    (hnot : ¬ Set.range t₁ ⊆ Set.range t₂) :
    t₁ (genericPoint T₁) ∉ Set.range t₂ := by
  obtain ⟨v, hv, hv₂⟩ := Set.not_subset.mp hnot
  obtain ⟨x, rfl⟩ := hv
  exact (genericPoint_specializes x).mem_open
    (t₂.isClosedEmbedding.isClosed_range.isOpen_compl.preimage t₁.continuous) hv₂

/-- Noncontainment persists on every nonempty open of the integral component. -/
lemma union_component_noncontainment_on_open
    {V T₁ T₂ : Scheme} [IsIntegral T₁]
    (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V) [IsClosedImmersion t₂]
    (hnot : ¬ Set.range t₁ ⊆ Set.range t₂)
    (U : T₁.Opens) [Nonempty U] :
    ¬ Set.range (U.ι ≫ t₁) ⊆ Set.range t₂ := by
  intro h
  apply union_genericPoint_not_mem_second t₁ t₂ hnot
  have hx := h (Set.mem_range_self (f := (U.ι ≫ t₁)) (genericPoint U.toScheme))
  simpa only [Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion U.ι] using hx

/-- Noncontainment persists when both components are restricted to an ambient open. -/
lemma union_component_noncontainment_restrict
    {V T₁ T₂ : Scheme} [IsIntegral T₁]
    (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V) [IsClosedImmersion t₂]
    (hnot : ¬ Set.range t₁ ⊆ Set.range t₂)
    (U : V.Opens) [Nonempty (t₁ ⁻¹ᵁ U)] :
    ¬ Set.range (t₁ ∣_ U) ⊆ Set.range (t₂ ∣_ U) := by
  intro hc
  apply union_component_noncontainment_on_open t₁ t₂ hnot (t₁ ⁻¹ᵁ U)
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hc (Set.mem_range_self (f := (t₁ ∣_ U)) x)
  refine ⟨y.val, ?_⟩
  have he := congrArg (fun z : U => z.val) hy
  simpa only [morphismRestrict_base_coe, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using he

#print axioms union_component_complement_dense
#print axioms union_genericPoint_not_mem_second
#print axioms union_component_noncontainment_on_open
end HodgeLean.Foundations.Program.G32Native
