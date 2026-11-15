import HodgeLean.Foundations.Program.G32Native.PELSplitDomain
import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular

noncomputable section
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open Topology

/-- Positive definite real matrices form a locally closed set in matrix space. -/
theorem matrix_posDef_isLocallyClosed {n : Type*} [Fintype n] [DecidableEq n] :
    IsLocallyClosed {A : Matrix n n ℝ | A.PosDef} := by
  have he : {A : Matrix n n ℝ | A.PosDef} =
      {A | A.PosSemidef} ∩ {A | A.det ≠ 0} := by
    ext A
    exact ⟨fun h => ⟨h.posSemidef, h.posSemidef.posDef_iff_det_ne_zero.mp h⟩,
      fun h => h.1.posDef_iff_det_ne_zero.mpr h.2⟩
  rw [he]
  exact Matrix.posSemidef_is_closed.isLocallyClosed.inter
    (isOpen_compl_singleton.preimage continuous_id.matrix_det).isLocallyClosed

/-- The coordinate map retains the ordinary matrix topology and distinguishes points. -/
theorem pel_domain_isEmbedding (R : PELSplitReference) :
    IsEmbedding (PELSplitDomain.J (R := R)) := by
  refine ⟨⟨rfl⟩, ?_⟩
  intro a b h
  cases a
  cases b
  cases h
  rfl

/-- The image of the period domain is locally closed in real matrix space. -/
theorem pel_domain_range_isLocallyClosed (R : PELSplitReference) :
    IsLocallyClosed (Set.range (PELSplitDomain.J (R := R))) := by
  let Ω := R.form.map (algebraMap ℚ ℝ)
  have he : Set.range (PELSplitDomain.J (R := R)) =
      {J : Matrix (Fin 12) (Fin 12) ℝ | J * J = -1} ∩
      {J | J.transpose * Ω * J = Ω} ∩
      {J | ∀ d, J * (R.operator d).map (algebraMap ℚ ℝ) =
        (R.operator d).map (algebraMap ℚ ℝ) * J} ∩
      {J | (Ω * J).PosDef} := by
    ext J
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨⟨z.square, z.isometry⟩, z.commute⟩, z.positive⟩
    · rintro ⟨⟨⟨hs, hi⟩, hc⟩, hp⟩
      exact ⟨⟨J, hs, hi, hp, hc⟩, rfl⟩
  rw [he]
  have hs : IsClosed {J : Matrix (Fin 12) (Fin 12) ℝ | J * J = -1} :=
    isClosed_eq (continuous_id.mul continuous_id) continuous_const
  have hi : IsClosed {J : Matrix (Fin 12) (Fin 12) ℝ | J.transpose * Ω * J = Ω} :=
    isClosed_eq ((continuous_id.matrix_transpose.mul continuous_const).mul continuous_id)
      continuous_const
  have hc : IsClosed {J : Matrix (Fin 12) (Fin 12) ℝ | ∀ d,
      J * (R.operator d).map (algebraMap ℚ ℝ) =
        (R.operator d).map (algebraMap ℚ ℝ) * J} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro d
    exact isClosed_eq (continuous_id.mul continuous_const)
      (continuous_const.mul continuous_id)
  exact ((hs.inter hi).inter hc).isLocallyClosed.inter
    (matrix_posDef_isLocallyClosed.preimage (continuous_const.mul continuous_id))

instance (R : PELSplitReference) : T2Space (PELSplitDomain R) :=
  (pel_domain_isEmbedding R).t2Space

instance (R : PELSplitReference) : LocallyCompactSpace (PELSplitDomain R) :=
  by
  letI : LocallyCompactSpace (Matrix (Fin 12) (Fin 12) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 12 → Fin 12 → ℝ))
  exact (pel_domain_isEmbedding R).isInducing.locallyCompactSpace
    (pel_domain_range_isLocallyClosed R)

instance (R : PELSplitReference) : LocallyCompactSpace (PELSplitComponent R) :=
  isClosed_connectedComponent.locallyCompactSpace

instance (R : PELSplitReference) : BaireSpace (PELSplitComponent R) := inferInstance

#print axioms matrix_posDef_isLocallyClosed
#print axioms pel_domain_range_isLocallyClosed
end HodgeLean.Foundations.Program.GeneralTypeIII
