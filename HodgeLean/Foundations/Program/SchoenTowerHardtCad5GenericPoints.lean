import HodgeLean.Foundations.Program.SchoenTowerHardtCad5AlgebraicFibers
import Mathlib.SetTheory.Cardinal.Subfield
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.Topology.Algebra.Module.Cardinality

/-! Real points outside the algebraic elements of countable coefficient fields. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_countable_algebraic (K : Type*) [CommRing K] [IsDomain K]
    [Countable K] [Algebra K ℝ] [Module.IsTorsionFree K ℝ] :
    {x : ℝ | IsAlgebraic K x}.Countable := by
  letI : Countable (ℕ →₀ K) := (Finsupp.graph_injective ℕ K).countable
  letI : Countable (Polynomial K) := (Polynomial.toFinsuppIso K).injective.countable
  have hc : (⋃ p : Polynomial K, {x : ℝ | x ∈ p.aroots ℝ}).Countable :=
    Set.countable_iUnion (fun p => (Multiset.finite_toSet (p.aroots ℝ)).countable)
  apply hc.mono
  rintro x ⟨p, hp, hz⟩
  exact Set.mem_iUnion.mpr ⟨p, Polynomial.mem_aroots.mpr ⟨hp, hz⟩⟩

theorem s2v_hardt_cad5_dense_transcendental (K : Subfield ℝ) [Countable K] :
    Dense {x : ℝ | Transcendental K x} :=
  (s2v_hardt_cad5_countable_algebraic K).dense_compl ℝ

theorem s2v_hardt_cad5_countable_coefficient_field (s : Set ℝ) (hs : s.Countable) :
    Countable (Subfield.closure s) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  exact (Subfield.cardinalMk_closure_le_max s).trans
    (max_le hs.le_aleph0 le_rfl)

end HodgeLean.Foundations.Program
