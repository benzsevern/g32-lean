import HodgeLean.Foundations.QuotientDuality.ProperCycleSingletonClass
import HodgeLean.Foundations.QuotientDuality.ProperCycleZeroDimension

/-! # Intrinsic zero-dimensional extension on the actual complex scheme -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual integral projective complex scheme of dimension zero has a unique intrinsic normalized top class, spanning its original ordinary homology.
Source: Hilbert's Nullstellensatz; Hatcher, Algebraic Topology, sections 2.1 and 3.3.
HC no distance; AV milestone no distance. -/
lemma properCycle_zero_dimensional_intrinsic_extension
    (V : Over (Spec ↧ℂ)) [IsIntegral V.left] [IsProjective V.hom]
    (hdim : topologicalKrullDim V.left = (0 : ℕ)) :
    ∃! c : Homology ℚ (a3b4_an V.hom) 0,
      (∀ (e : OpenPartialHomeomorph (ComplexPoint V) (Fin 0 → ℂ)),
        (∀ i, (f4_analytification V).IsHolFun (fun z : e.source => e z i)) →
        ∀ (x : ComplexPoint V) (hx : x ∈ e.source),
          localOrientation (a3b4_an V.hom) 0 c x = localClassOfChart 0 e x hx) ∧
      Function.Bijective (LinearMap.toSpanSingleton ℚ (Homology ℚ (a3b4_an V.hom) 0) c) := by
  have hd : TopologicalSpace.dim V.left = 0 := by
    unfold TopologicalSpace.dim
    rw [hdim]
    rfl
  letI : Subsingleton (ComplexPoint V) := properCycle_zero_dimension_complex_subsingleton V hd
  letI : Subsingleton (a3b4_an V.hom) := properCycle_zero_dimension_complex_subsingleton V hd
  letI : Unique (a3b4_an V.hom) :=
    { default := Classical.choice (properCycle_zero_dimension_complex_nonempty V hd)
      uniq := fun _ => Subsingleton.elim _ _ }
  obtain ⟨c, hc, hu⟩ := properCycle_singleton_complex_class (a3b4_an V.hom)
  refine ⟨c, ⟨fun e _ => hc.1 e, hc.2⟩, ?_⟩
  intro b hb
  apply hu b
  exact ⟨fun e x hx => hb.1 e (fun i => Fin.elim0 i) x hx, hb.2⟩

end HodgeLean.Foundations.QuotientDuality
