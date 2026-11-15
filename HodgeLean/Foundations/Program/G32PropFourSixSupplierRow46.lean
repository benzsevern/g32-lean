import HodgeLean.Foundations.Program.G32PropFourSixPacked0031
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow46Decode
import HodgeLean.Foundations.Program.G32PropFourSixPacked0026
import HodgeLean.Foundations.Program.G32PropFourSixPacked0026
import HodgeLean.Foundations.Program.G32PropFourSixPacked0027
import HodgeLean.Foundations.Program.G32PropFourSixPacked0027
import HodgeLean.Foundations.Program.G32PropFourSixPacked0027
import HodgeLean.Foundations.Program.G32PropFourSixPacked0027
import HodgeLean.Foundations.Program.G32PropFourSixPacked0028
import HodgeLean.Foundations.Program.G32PropFourSixPacked0028
import HodgeLean.Foundations.Program.G32PropFourSixPacked0028
import HodgeLean.Foundations.Program.G32PropFourSixPacked0028
import HodgeLean.Foundations.Program.G32PropFourSixPacked0028
import HodgeLean.Foundations.Program.G32PropFourSixPacked0028
import HodgeLean.Foundations.Program.G32PropFourSixPacked0029
import HodgeLean.Foundations.Program.G32PropFourSixPacked0029
import HodgeLean.Foundations.Program.G32PropFourSixPacked0029
import HodgeLean.Foundations.Program.G32PropFourSixPacked0029
import HodgeLean.Foundations.Program.G32PropFourSixPacked0029
import HodgeLean.Foundations.Program.G32PropFourSixPacked0030
import HodgeLean.Foundations.Program.G32PropFourSixPacked0030
import HodgeLean.Foundations.Program.G32PropFourSixPacked0030
import HodgeLean.Foundations.Program.G32PropFourSixPacked0030
import HodgeLean.Foundations.Program.G32PropFourSixPacked0031
import HodgeLean.Foundations.Program.G32PropFourSixPacked0031
import HodgeLean.Foundations.Program.G32PropFourSixPacked0031
import HodgeLean.Foundations.Program.G32PropFourSixPacked0031
import HodgeLean.Foundations.Program.G32PropFourSixPacked0025
import HodgeLean.Foundations.Program.G32PropFourSixPacked0025
import HodgeLean.Foundations.Program.G32PropFourSixPacked0025
import HodgeLean.Foundations.Program.G32PropFourSixPacked0025
import HodgeLean.Foundations.Program.G32PropFourSixPacked0026
import HodgeLean.Foundations.Program.G32PropFourSixPacked0026
import HodgeLean.Foundations.Program.G32PropFourSixPacked0026
import HodgeLean.Foundations.Program.G32PropFourSixPacked0026
import HodgeLean.Foundations.Program.G32PropFourSixPacked0026
import HodgeLean.Foundations.Program.G32PropFourSixPacked0027
import HodgeLean.Foundations.Program.G32PropFourSixPacked0027
import HodgeLean.Foundations.Program.G32PropFourSixPacked0027
import HodgeLean.Foundations.Program.G32PropFourSixPacked0027
import HodgeLean.Foundations.Program.G32PropFourSixPacked0028
import HodgeLean.Foundations.Program.G32PropFourSixPacked0028
import HodgeLean.Foundations.Program.G32PropFourSixPacked0028
import HodgeLean.Foundations.Program.G32PropFourSixPacked0028
import HodgeLean.Foundations.Program.G32PropFourSixPacked0028
import HodgeLean.Foundations.Program.G32PropFourSixPacked0028
import HodgeLean.Foundations.Program.G32PropFourSixPacked0029
import HodgeLean.Foundations.Program.G32PropFourSixPacked0029
import HodgeLean.Foundations.Program.G32PropFourSixPacked0029
import HodgeLean.Foundations.Program.G32PropFourSixPacked0029
import HodgeLean.Foundations.Program.G32PropFourSixPacked0029
import HodgeLean.Foundations.Program.G32PropFourSixPacked0030
import HodgeLean.Foundations.Program.G32PropFourSixPacked0030
import HodgeLean.Foundations.Program.G32PropFourSixPacked0030
import HodgeLean.Foundations.Program.G32PropFourSixPacked0030
import HodgeLean.Foundations.Program.G32PropFourSixPacked0031
import HodgeLean.Foundations.Program.G32PropFourSixPacked0031
import HodgeLean.Foundations.Program.G32PropFourSixPacked0031
import HodgeLean.Foundations.Program.G32PropFourSixPacked0031
import HodgeLean.Foundations.Program.G32PropFourSixPacked0025
import HodgeLean.Foundations.Program.G32PropFourSixPacked0025
import HodgeLean.Foundations.Program.G32PropFourSixPacked0025
import HodgeLean.Foundations.Program.G32PropFourSixPacked0025
import HodgeLean.Foundations.Program.G32PropFourSixPacked0026
import HodgeLean.Foundations.Program.G32PropFourSixPacked0026
import HodgeLean.Foundations.Program.G32PropFourSixPacked0026
import HodgeLean.Foundations.Program.G32PropFourSixPacked0171
import HodgeLean.Foundations.Program.G32PropFourSixPacked0171
import HodgeLean.Foundations.Program.G32PropFourSixPacked0171
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow46CharacterBlock00
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCheck
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row46_groupTransition :
    g32p_transitionCheck g32p_row46_groupNodes g32p_row46_groupMatrices
      g32p_row46_groupNext = true := by
  apply decide_eq_true
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row46_transitionBlock_000
  · exact g32p_row46_transitionBlock_001
  · exact g32p_row46_transitionBlock_002
  · exact g32p_row46_transitionBlock_003
  · exact g32p_row46_transitionBlock_004
  · exact g32p_row46_transitionBlock_005
  · exact g32p_row46_transitionBlock_006
  · exact g32p_row46_transitionBlock_007
  · exact g32p_row46_transitionBlock_008
  · exact g32p_row46_transitionBlock_009
  · exact g32p_row46_transitionBlock_010
  · exact g32p_row46_transitionBlock_011
  · exact g32p_row46_transitionBlock_012
  · exact g32p_row46_transitionBlock_013
  · exact g32p_row46_transitionBlock_014
  · exact g32p_row46_transitionBlock_015
  · exact g32p_row46_transitionBlock_016
  · exact g32p_row46_transitionBlock_017
  · exact g32p_row46_transitionBlock_018
  · exact g32p_row46_transitionBlock_019
  · exact g32p_row46_transitionBlock_020
  · exact g32p_row46_transitionBlock_021
  · exact g32p_row46_transitionBlock_022
  · exact g32p_row46_transitionBlock_023
  · exact g32p_row46_transitionBlock_024
  · exact g32p_row46_transitionBlock_025
  · exact g32p_row46_transitionBlock_026

theorem g32p_row46_groupStep (i : Fin 432) (s : Fin 4) :
    HurwitzPrymRex_mmul (g32p_row46_groupNodes i) (g32p_row46_groupMatrices s) =
      g32p_row46_groupNodes (g32p_row46_groupNext i s) := by
  exact g32p_transition_integral_sound _ _ _ g32p_row46_groupTransition i s

theorem g32p_row46_matrixDecode_leftInverse : ∀ i : Fin 432,
    g32p_row46_matrixDecode (g32p_matrixFingerprint (g32p_row46_groupNodes i)) = i := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row46_decodeBlock_000
  · exact g32p_row46_decodeBlock_001
  · exact g32p_row46_decodeBlock_002
  · exact g32p_row46_decodeBlock_003
  · exact g32p_row46_decodeBlock_004
  · exact g32p_row46_decodeBlock_005
  · exact g32p_row46_decodeBlock_006
  · exact g32p_row46_decodeBlock_007
  · exact g32p_row46_decodeBlock_008
  · exact g32p_row46_decodeBlock_009
  · exact g32p_row46_decodeBlock_010
  · exact g32p_row46_decodeBlock_011
  · exact g32p_row46_decodeBlock_012
  · exact g32p_row46_decodeBlock_013
  · exact g32p_row46_decodeBlock_014
  · exact g32p_row46_decodeBlock_015
  · exact g32p_row46_decodeBlock_016
  · exact g32p_row46_decodeBlock_017
  · exact g32p_row46_decodeBlock_018
  · exact g32p_row46_decodeBlock_019
  · exact g32p_row46_decodeBlock_020
  · exact g32p_row46_decodeBlock_021
  · exact g32p_row46_decodeBlock_022
  · exact g32p_row46_decodeBlock_023
  · exact g32p_row46_decodeBlock_024
  · exact g32p_row46_decodeBlock_025
  · exact g32p_row46_decodeBlock_026

theorem g32p_row46_groupInjective : Function.Injective g32p_row46_groupNodes :=
  g32p_matrix_injective_of_decoder _ _ g32p_row46_matrixDecode_leftInverse

theorem g32p_row46_groupParent_lt : ∀ i : Fin 432, i ≠ 0 →
    (g32p_row46_groupParent i).val < i.val := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row46_parentLtBlock_000
  · exact g32p_row46_parentLtBlock_001
  · exact g32p_row46_parentLtBlock_002
  · exact g32p_row46_parentLtBlock_003
  · exact g32p_row46_parentLtBlock_004
  · exact g32p_row46_parentLtBlock_005
  · exact g32p_row46_parentLtBlock_006
  · exact g32p_row46_parentLtBlock_007
  · exact g32p_row46_parentLtBlock_008
  · exact g32p_row46_parentLtBlock_009
  · exact g32p_row46_parentLtBlock_010
  · exact g32p_row46_parentLtBlock_011
  · exact g32p_row46_parentLtBlock_012
  · exact g32p_row46_parentLtBlock_013
  · exact g32p_row46_parentLtBlock_014
  · exact g32p_row46_parentLtBlock_015
  · exact g32p_row46_parentLtBlock_016
  · exact g32p_row46_parentLtBlock_017
  · exact g32p_row46_parentLtBlock_018
  · exact g32p_row46_parentLtBlock_019
  · exact g32p_row46_parentLtBlock_020
  · exact g32p_row46_parentLtBlock_021
  · exact g32p_row46_parentLtBlock_022
  · exact g32p_row46_parentLtBlock_023
  · exact g32p_row46_parentLtBlock_024
  · exact g32p_row46_parentLtBlock_025
  · exact g32p_row46_parentLtBlock_026

theorem g32p_row46_groupParent_step : ∀ i : Fin 432, i ≠ 0 →
    g32p_row46_groupNext (g32p_row46_groupParent i) (g32p_row46_groupLabel i) = i := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row46_parentStepBlock_000
  · exact g32p_row46_parentStepBlock_001
  · exact g32p_row46_parentStepBlock_002
  · exact g32p_row46_parentStepBlock_003
  · exact g32p_row46_parentStepBlock_004
  · exact g32p_row46_parentStepBlock_005
  · exact g32p_row46_parentStepBlock_006
  · exact g32p_row46_parentStepBlock_007
  · exact g32p_row46_parentStepBlock_008
  · exact g32p_row46_parentStepBlock_009
  · exact g32p_row46_parentStepBlock_010
  · exact g32p_row46_parentStepBlock_011
  · exact g32p_row46_parentStepBlock_012
  · exact g32p_row46_parentStepBlock_013
  · exact g32p_row46_parentStepBlock_014
  · exact g32p_row46_parentStepBlock_015
  · exact g32p_row46_parentStepBlock_016
  · exact g32p_row46_parentStepBlock_017
  · exact g32p_row46_parentStepBlock_018
  · exact g32p_row46_parentStepBlock_019
  · exact g32p_row46_parentStepBlock_020
  · exact g32p_row46_parentStepBlock_021
  · exact g32p_row46_parentStepBlock_022
  · exact g32p_row46_parentStepBlock_023
  · exact g32p_row46_parentStepBlock_024
  · exact g32p_row46_parentStepBlock_025
  · exact g32p_row46_parentStepBlock_026

theorem g32p_row46_groupEnumeration :
    ∃ e : Fin 432 ≃ Subgroup.closure (Set.range g32p_row46_groupGenerators),
      ∀ i, b4b_toMatrix (e i : g32p_G) =
        HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
          (g32p_row46_groupNodes i)) := by
  apply g32p_matrixPathEnumeration b4b_toMatrix Subtype.val_injective
    (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
    (by rw [HurwitzPrymRex_evM_mone, map_one])
    (by intro a b; rw [HurwitzPrymRex_evM_mmul g32h_omega_sq_add, map_mul])
    (HurwitzPrymRex_g32conj_injective.comp
      (HurwitzPrymRex_evM_injective g32h_omega_sq_add))
    g32p_row46_groupGenerators g32p_row46_groupMatrices g32p_row46_groupGenerator_map
    g32p_row46_groupNodes 0 g32p_row46_groupParent g32p_row46_groupLabel Fin.val
    g32p_row46_groupNext g32p_row46_groupInjective (by decide)
    g32p_row46_groupParent_lt
  · intro i hi
    have hs := g32p_row46_groupStep
      (g32p_row46_groupParent i) (g32p_row46_groupLabel i)
    rw [g32p_row46_groupParent_step i hi] at hs
    exact hs.symm
  · exact g32p_row46_groupStep

theorem g32p_row46_groupOrder :
    Nat.card (Subgroup.closure (Set.range g32p_row46_groupGenerators)) = 432 := by
  obtain ⟨e, _⟩ := g32p_row46_groupEnumeration
  simpa only [Nat.card_fin] using (Nat.card_congr e).symm

def g32p_row46_groupEquiv : Fin 432 ≃ Subgroup.closure (Set.range g32p_row46_groupGenerators) :=
  Classical.choose g32p_row46_groupEnumeration

theorem g32p_row46_groupEquiv_map (i : Fin 432) :
    b4b_toMatrix (g32p_row46_groupEquiv i : g32p_G) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row46_groupNodes i)) :=
  Classical.choose_spec g32p_row46_groupEnumeration i

theorem g32p_row46_groupEquiv_one : g32p_row46_groupEquiv 0 = 1 := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row46_groupEquiv 0 : g32p_G) = b4b_toMatrix 1
  rw [g32p_row46_groupEquiv_map, map_one,
    show g32p_row46_groupNodes 0 = HurwitzPrymRex_mone by decide,
    HurwitzPrymRex_evM_mone, map_one]

theorem g32p_row46_groupEquiv_step (i : Fin 432) (s : Fin 4) :
    g32p_row46_groupEquiv (g32p_row46_groupNext i s) =
      g32p_row46_groupEquiv i *
        ⟨g32p_row46_groupGenerators s, Subgroup.subset_closure (Set.mem_range_self s)⟩ := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row46_groupEquiv (g32p_row46_groupNext i s) : g32p_G) =
    b4b_toMatrix ((g32p_row46_groupEquiv i : g32p_G) * g32p_row46_groupGenerators s)
  rw [map_mul, g32p_row46_groupEquiv_map, g32p_row46_groupEquiv_map,
    g32p_row46_groupGenerator_map, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  exact congrArg (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
    (g32p_row46_groupStep i s).symm

theorem g32p_row46_characterTransition : ∀ i : Fin 432, ∀ s : Fin 4,
    g32p_row46_characterValues (g32p_row46_groupNext i s) =
      g32p_row46_characterValues i * g32p_row46_characterValues (g32p_row46_groupNext 0 s) := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row46_characterBlock_000
  · exact g32p_row46_characterBlock_001
  · exact g32p_row46_characterBlock_002
  · exact g32p_row46_characterBlock_003
  · exact g32p_row46_characterBlock_004
  · exact g32p_row46_characterBlock_005
  · exact g32p_row46_characterBlock_006
  · exact g32p_row46_characterBlock_007
  · exact g32p_row46_characterBlock_008
  · exact g32p_row46_characterBlock_009
  · exact g32p_row46_characterBlock_010
  · exact g32p_row46_characterBlock_011
  · exact g32p_row46_characterBlock_012
  · exact g32p_row46_characterBlock_013
  · exact g32p_row46_characterBlock_014
  · exact g32p_row46_characterBlock_015
  · exact g32p_row46_characterBlock_016
  · exact g32p_row46_characterBlock_017
  · exact g32p_row46_characterBlock_018
  · exact g32p_row46_characterBlock_019
  · exact g32p_row46_characterBlock_020
  · exact g32p_row46_characterBlock_021
  · exact g32p_row46_characterBlock_022
  · exact g32p_row46_characterBlock_023
  · exact g32p_row46_characterBlock_024
  · exact g32p_row46_characterBlock_025
  · exact g32p_row46_characterBlock_026

theorem g32p_row46_characterSurjective : Function.Surjective g32p_row46_characterValues := by
  decide +kernel

def g32p_row46_finiteSupplier : g32p_Supplier :=
  g32p_supplierOfFiniteTransitions (by decide) g32p_row46_groupGenerators
    g32p_row46_groupEquiv 0 g32p_row46_groupEquiv_one
    g32p_row46_groupNext g32p_row46_groupEquiv_step g32p_row46_characterValues
    (by rfl) g32p_row46_characterTransition g32p_row46_characterSurjective

theorem g32p_row46_finiteSupplier_order : Nat.card g32p_row46_finiteSupplier.H = 432 :=
  g32p_row46_groupOrder

theorem g32p_row46_finiteSupplier_value (i : Fin 432) :
    g32p_row46_finiteSupplier.χ (g32p_row46_groupEquiv i) = g32p_row46_characterValues i :=
  g32p_supplierOfFiniteTransitions_value ..

end HodgeLean.Foundations.Program
