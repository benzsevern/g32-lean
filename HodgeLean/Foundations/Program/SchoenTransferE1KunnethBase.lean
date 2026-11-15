import HodgeLean.Foundations.Program.SchoenTransferE1CurveAction

/-! The empty-power base of the ordered curve-power comparison. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped DirectSum BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

/-- The empty ordered power has the scalar comparison in degree zero and
zero source and target in positive degrees.
Source: Hatcher, Algebraic Topology, §3.2, the unit in the Künneth formula. -/
theorem s4_e1_kunneth_empty
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral (g3_power Y 0).left] [Smooth (g3_power Y 0).hom]
    [IsProjective (g3_power Y 0).hom] (n : ℕ) :
    Function.Bijective (s4_e1_kunneth Y 0 n) := by
  classical
  by_cases hn : n = 0
  · subst n
    let I := {d : Fin 0 → ℕ // ∑ i, d i = 0}
    letI : Unique I :=
      { default := ⟨Fin.elim0, Fin.sum_univ_zero _⟩
        uniq := fun d => Subtype.ext (Subsingleton.elim _ _) }
    let f : (⨁ _ : I, ℚ) →ₗ[ℚ] HQ (g3_power Y 0) 0 :=
      DirectSum.toModule ℚ I _ (fun _ =>
        LinearMap.toSpanSingleton ℚ (HQ (g3_power Y 0) 0) (cupUnit (g3_power Y 0)))
    change Function.Bijective f
    have he : f = (cupProductOf_zeroEquiv (g3_power Y 0)).toLinearMap.comp
        (DirectSum.lid ℚ ℚ I).toLinearMap := by
      apply DirectSum.linearMap_ext ℚ
      intro d
      apply LinearMap.ext
      intro q
      have hd : d = default := Subsingleton.elim _ _
      subst d
      simp only [f, LinearMap.comp_apply, DirectSum.toModule_lof,
        LinearMap.toSpanSingleton_apply, LinearEquiv.coe_toLinearMap,
        DirectSum.lid_apply, DirectSum.lof_apply, cupProductOf_zeroEquiv_apply]
    rw [he]
    exact (cupProductOf_zeroEquiv (g3_power Y 0)).bijective.comp
      (DirectSum.lid ℚ ℚ I).bijective
  · letI : IsEmpty {d : Fin 0 → ℕ // ∑ i, d i = n} :=
      ⟨fun d => hn (by simpa only [Fin.sum_univ_zero] using d.property.symm)⟩
    letI : SmoothOfRelativeDimension 0 (g3_power Y 0).hom := by
      change SmoothOfRelativeDimension 0 (𝟙 (Spec ↧ℂ))
      infer_instance
    letI := j5d_subsingleton_HQ_of_lt (g3_power Y 0) 0 (Nat.pos_of_ne_zero hn)
    constructor
    · exact Function.injective_of_subsingleton _
    · intro x
      exact ⟨0, Subsingleton.elim _ _⟩

#print axioms s4_e1_kunneth_empty
end HodgeLean.Foundations.Program
