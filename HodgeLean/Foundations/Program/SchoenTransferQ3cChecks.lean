import HodgeLean.Foundations.Program.SchoenTransferQuotientLinear
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CohomologyZero

/-! Nonzero absolute pullback and a retained span detect altered final equations.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program
private abbrev P := Over.mk (𝟙 (Spec (CommRingCat.of ℂ)))
private instance : Unique (ComplexPoint P) where
  default := 𝟙 P
  uniq y := Over.mkIdTerminal.hom_ext y (𝟙 P)
private abbrev u := cohomologyUnitZero ℚ (TopCat.of (ComplexPoint P))

/-- The specified absolute pullback cannot be rescaled by two.
Source: Hatcher, Algebraic Topology, §3.1; cohomologyUnitZero_ne_zero. -/
theorem s4_q3c_absolute_pullback_falsification :
    s4_singularPullback (𝟙 P) 0 u ≠ (2 : ℚ) • u := by
  rw [s4_singularPullback_id, LinearMap.id_apply]
  intro h
  have hh : ((2 : ℚ) - 1) • u = 0 := by
    rw [sub_smul, one_smul, ← h, sub_self]
  have hu : u = 0 := (smul_eq_zero.mp hh).resolve_left (by norm_num)
  exact cohomologyUnitZero_ne_zero ℚ _ hu

example := s4_q3c_absolute_pullback_falsification

/-- The retained basis span contains a nonzero actual pullback, so replacing it by zero fails.
Source: Fulton, Intersection Theory, second edition, §19.1, linearity. -/
theorem s4_q3c_quotient_cycles_falsification :
    Submodule.span ℚ (Set.range (fun _ : Fin 1 => s4_singularPullback (𝟙 P) 0 u)) ≠ ⊥ := by
  intro h
  have hu : s4_singularPullback (𝟙 P) 0 u ∈
      Submodule.span ℚ (Set.range (fun _ : Fin 1 => s4_singularPullback (𝟙 P) 0 u)) :=
    Submodule.subset_span ⟨0, rfl⟩
  rw [h, Submodule.mem_bot, s4_singularPullback_id, LinearMap.id_apply] at hu
  exact cohomologyUnitZero_ne_zero ℚ _ hu

example := s4_q3c_quotient_cycles_falsification
#print axioms s4_q3c_absolute_pullback_falsification
#print axioms s4_q3c_quotient_cycles_falsification
end HodgeLean.Foundations.Program
