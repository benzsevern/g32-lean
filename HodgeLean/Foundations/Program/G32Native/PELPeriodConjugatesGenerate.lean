import HodgeLean.Foundations.Program.G32Native.PELPeriodConjugacyGeneration

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations

/-- Containing all conjugates of one retained period matrix suffices to
contain the connected quaternionic isometry group. -/
theorem pel_period_conjugates_generate (R : PELSplitReference)
    (z : PELSplitComponent R)
    (G : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ)) (hG : g2_IsRatAlgSubgroup G)
    (hc : ∀ g ∈ g1_identityComponent (pelReferenceComplexIsometryGroup R),
      g⁻¹ * pelPeriodMatrix R z.val * g ∈ G) :
    g1_identityComponent (pelReferenceComplexIsometryGroup R) ⊆ G := by
  letI := g1_zariski ℂ 12
  let K : Subgroup (Matrix.GeneralLinearGroup (Fin 12) ℂ) :=
    { carrier := G
      one_mem' := hG.2.1
      mul_mem' := fun hx hy => hG.2.2.1 _ hx _ hy
      inv_mem' := fun hx => hG.2.2.2 _ hx }
  exact pel_contains_of_period_conjugates R K
    (closure_subset_iff_isClosed.mp
      (pelComplexClosure_subset_ratGroup G G hG (Set.Subset.refl G))) z hc

#print axioms pel_period_conjugates_generate
end HodgeLean.Foundations.Program.GeneralTypeIII
