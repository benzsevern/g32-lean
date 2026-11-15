import HodgeLean.Adapters.NormalConeB4aClassRestriction
import HodgeLean.RealDefs.DegreeZero
import HodgeLean.Foundations.Program.CompensationAssemblyComponentPoint
import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentNormalization
import HodgeLean.Adapters.NormalConeB4aClassMultiplicity
import HodgeLean.Foundations.Program.CompensationAssemblySpan2Local

/-! # Detecting normalized supported classes in a holomorphic normal chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero

/-- A normalized class with nonzero local multiplicity is nonzero in its actual supported group. -/
theorem normalized_class_ne_zero_of_chart
    {Z : Scheme.{0}} (q : Z ⟶ Spec ↧ℂ) [LocallyOfFiniteType q]
    [QuasiCompact q] [IsSeparated q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * c))
    (hβ : a3b4_IsCycleClass q γ c β) (r : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q))
      ((Fin r → ℂ) × (Fin c → ℂ)))
    (hS : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport q γ ↔ (e y).2 = 0)
    (x : ComplexPoint (Over.mk q)) (hx : x ∈ e.source)
    (hxS : x ∈ a3b4_cycleSupport q γ) (he : a3b4_IsHolChart q e)
    (hm : a3b4_multiplicity q γ x ≠ 0) : β ≠ 0 := by
  intro hzero
  obtain ⟨W, hW, hWo, hxW, hnorm⟩ := hβ r e hS x hx hxS he
  rw [hzero, map_zero] at hnorm
  have hne := chartNormalProjectionCoclass_ne_zero (Fin r → ℂ) c e
    (a3b4_cycleSupport q γ) hS hWo hW hxW ((hS x hx).mp hxS)
  exact (smul_ne_zero hm hne) hnorm.symm

#print axioms normalized_class_ne_zero_of_chart
/-- A normalized class supported on one prime of the specified codimension is nonzero. -/
theorem normalized_single_prime_class_ne_zero
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (p : X.left) (k : ℕ)
    (hγ : γ.support = {p}) (hp : Order.coheight p = k)
    (β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an X.hom) (a3b4_cycleSupport X.hom γ)ᶜ) (2 * k))
    (hβ : a3b4_IsCycleClass X.hom γ k β) : β ≠ 0 := by
  classical
  obtain ⟨Z, q, rfl⟩ := Over.mk_surjective X
  let X : Over (Spec ↧ℂ) := Over.mk q
  obtain ⟨z, -, haS, haB⟩ := cq_component_regular_complex_point_on_open X p ⊤ (by
    obtain ⟨t⟩ := (inferInstance : Nonempty (a2r_component X p).left)
    exact ⟨t, trivial⟩)
  generalize Point.map (Over.homMk (cycleComponentι X.left p) rfl) z = a at haS haB
  have hsmooth : a ∈ cycleComponentSmoothSupportAmbientOpen X p := by
    intro hs
    apply haB
    rw [cq_componentBoundary_singleton]
    exact hs
  obtain ⟨e, he, hae, hhol, -⟩ :=
    s4_q3_component_class_holomorphic_chart X k p hp a hsmooth haS
  have hs : a3b4_cycleSupport X.hom γ = cycleComponentSupport X p := by
    change Point.underlying ⁻¹' (⋃ ξ ∈ γ.support, closure {ξ}) = _
    rw [hγ, Set.biUnion_singleton]
    rfl
  have hmem : p ∈ γ.support := by rw [hγ]; exact Set.mem_singleton p
  have hother : ∀ t ∈ γ.support, t ≠ p → a.underlying ∉ closure ({t} : Set X.left) := by
    intro t ht htp
    rw [hγ] at ht
    exact (htp (Set.mem_singleton_iff.mp ht)).elim
  apply normalized_class_ne_zero_of_chart X.hom γ k β hβ (dim X.left - k) e
    (fun y hy => (Set.ext_iff.mp hs y).trans (he y hy)) a hae (by rw [hs]; exact haS) hhol
  rw [a3b4a_classMultiplicity_eq_component X.hom γ p hmem a haS hother]
  exact Function.mem_support.mp hmem

#print axioms normalized_single_prime_class_ne_zero
/-- Every supported class on a single prime is a rational multiple of its normalized class. -/
theorem normalized_single_prime_class_spans
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (p : X.left) (k : ℕ)
    (hγ : γ.support = {p}) (hp : Order.coheight p = k)
    (β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an X.hom) (a3b4_cycleSupport X.hom γ)ᶜ) (2 * k))
    (hβ : a3b4_IsCycleClass X.hom γ k β)
    (v : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an X.hom) (a3b4_cycleSupport X.hom γ)ᶜ) (2 * k)) :
    ∃ r : ℚ, v = r • β := by
  have hne := normalized_single_prime_class_ne_zero X γ p k hγ hp β hβ
  have hs : a3b4_cycleSupport X.hom γ = cycleComponentSupport X p := by
    change Point.underlying ⁻¹' (⋃ ξ ∈ γ.support, closure {ξ}) = _
    rw [hγ, Set.biUnion_singleton]
    rfl
  clear hβ
  revert β v
  rw [hs]
  intro β v hne
  obtain ⟨a, ha⟩ := cq_span_relative_multiple X p k hp β
  obtain ⟨b, hb⟩ := cq_span_relative_multiple X p k hp v
  have ha0 : a ≠ 0 := by
    intro hzero
    apply hne
    rw [ha, hzero, zero_smul]
  refine ⟨b / a, ?_⟩
  rw [ha, hb, smul_smul, div_mul_cancel₀ b ha0]

#print axioms normalized_single_prime_class_spans
end HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero
