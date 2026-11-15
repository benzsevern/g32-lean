import HodgeLean.Foundations.Program.G32Native.PELPeriodGenerationSteps

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations

/-- Containing every complex-group conjugate of one period matrix suffices
for containment of the rank-three PEL group.
Source: Borel, Linear Algebraic Groups, second edition, §§2.2, 7.6;
Abdulali, Annals 155 (2002), §§3.2–3.3. -/
theorem pel_contains_of_period_conjugates (R : PELSplitReference)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 12) ℂ))
    (hH : @IsClosed _ (g1_zariski ℂ 12) (H : Set _))
    (z : PELSplitComponent R)
    (hconj : ∀ g ∈ g1_identityComponent (pelReferenceComplexIsometryGroup R),
      g⁻¹ * pelPeriodMatrix R z.val * g ∈ H) :
    g1_identityComponent (pelReferenceComplexIsometryGroup R) ⊆ (H : Set _) := by
  letI := g1_zariski ℂ 12
  let C := g1_identityComponentSubgroup (pelReferenceComplexIsometryGroup R)
  let K : Subgroup (Matrix.GeneralLinearGroup (Fin 12) ℂ) :=
    { carrier := {x | ∀ g ∈ C, g⁻¹ * x * g ∈ H}
      one_mem' := by intro g hg; simpa using H.one_mem
      mul_mem' := by
        intro x y hx hy g hg
        simpa only [mul_assoc, mul_inv_cancel_left] using H.mul_mem (hx g hg) (hy g hg)
      inv_mem' := by
        intro x hx g hg
        simpa only [mul_inv_rev, inv_inv, mul_assoc] using H.inv_mem (hx g hg) }
  have hK : IsClosed (K : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ)) := by
    have he : (K : Set _) = ⋂ g ∈ C,
        {x : Matrix.GeneralLinearGroup (Fin 12) ℂ | g⁻¹ * x * g ∈ H} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rfl
    rw [he]
    exact isClosed_biInter fun g hg => hH.preimage
      ((g2h_continuous_mul_right g).comp (g1_continuous_mul_left g⁻¹))
  have hn : ∀ g ∈ g1_identityComponent (pelReferenceComplexIsometryGroup R),
      ∀ x ∈ K, g⁻¹ * x * g ∈ K := by
    intro g hg x hx d hd
    have hh := hx (g * d) (C.mul_mem hg hd)
    simpa only [mul_inv_rev, mul_assoc] using hh
  have hx : pelPeriodMatrix R z.val ∈ K := hconj
  obtain ⟨hxC, hnoncentral⟩ := pel_period_noncentral_aux R z
  have hb := pel_connected_isometry_normal_subgroup_aux R K hK hn
    (pelPeriodMatrix R z.val) hx hxC hnoncentral
  intro x hx
  change x ∈ H
  have hh : (1 : Matrix.GeneralLinearGroup (Fin 12) ℂ)⁻¹ * x * 1 ∈ H :=
    (hb hx) 1 C.one_mem
  simpa only [inv_one, one_mul, mul_one] using hh

#print axioms pel_contains_of_period_conjugates
end HodgeLean.Foundations.Program.GeneralTypeIII
