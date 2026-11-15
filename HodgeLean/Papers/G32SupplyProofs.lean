import HodgeLean.Papers.G32SupplyDefs

namespace HodgeLean.Papers

theorem g32s_fifty_one_admissible_aux :
    g32WitnessTable.length = 51 ∧
    (∀ r ∈ g32WitnessTable, 0 < r.h ∧ Even r.h ∧ IsSimpleExps r.m (expandExps r.exps)) := by
  refine ⟨by decide, ?_⟩
  intro r hr
  exact ⟨(papers_g32_table_h_pos_even r hr).1,
    (papers_g32_table_h_pos_even r hr).2, papers_g32_table_simple r hr⟩

end HodgeLean.Papers
