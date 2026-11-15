import HodgeLean.Foundations.Program.G32PropFourSixPacked0027
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow09Decode
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
import HodgeLean.Foundations.Program.G32PropFourSixPacked0068
import HodgeLean.Foundations.Program.G32PropFourSixPacked0068
import HodgeLean.Foundations.Program.G32PropFourSixPacked0068
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow09CharacterBlock00
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

theorem g32p_row09_groupTransition :
    g32p_transitionCheck g32p_row09_groupNodes g32p_row09_groupMatrices
      g32p_row09_groupNext = true := by
  apply decide_eq_true
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row09_transitionBlock_000
  · exact g32p_row09_transitionBlock_001
  · exact g32p_row09_transitionBlock_002
  · exact g32p_row09_transitionBlock_003
  · exact g32p_row09_transitionBlock_004
  · exact g32p_row09_transitionBlock_005
  · exact g32p_row09_transitionBlock_006
  · exact g32p_row09_transitionBlock_007
  · exact g32p_row09_transitionBlock_008
  · exact g32p_row09_transitionBlock_009
  · exact g32p_row09_transitionBlock_010
  · exact g32p_row09_transitionBlock_011
  · exact g32p_row09_transitionBlock_012
  · exact g32p_row09_transitionBlock_013
  · exact g32p_row09_transitionBlock_014
  · exact g32p_row09_transitionBlock_015
  · exact g32p_row09_transitionBlock_016
  · exact g32p_row09_transitionBlock_017
  · exact g32p_row09_transitionBlock_018
  · exact g32p_row09_transitionBlock_019
  · exact g32p_row09_transitionBlock_020
  · exact g32p_row09_transitionBlock_021
  · exact g32p_row09_transitionBlock_022
  · exact g32p_row09_transitionBlock_023
  · exact g32p_row09_transitionBlock_024
  · exact g32p_row09_transitionBlock_025
  · exact g32p_row09_transitionBlock_026
  · exact g32p_row09_transitionBlock_027
  · exact g32p_row09_transitionBlock_028
  · exact g32p_row09_transitionBlock_029
  · exact g32p_row09_transitionBlock_030

theorem g32p_row09_groupStep (i : Fin 486) (s : Fin 3) :
    HurwitzPrymRex_mmul (g32p_row09_groupNodes i) (g32p_row09_groupMatrices s) =
      g32p_row09_groupNodes (g32p_row09_groupNext i s) := by
  exact g32p_transition_integral_sound _ _ _ g32p_row09_groupTransition i s

theorem g32p_row09_matrixDecode_leftInverse : ∀ i : Fin 486,
    g32p_row09_matrixDecode (g32p_matrixFingerprint (g32p_row09_groupNodes i)) = i := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row09_decodeBlock_000
  · exact g32p_row09_decodeBlock_001
  · exact g32p_row09_decodeBlock_002
  · exact g32p_row09_decodeBlock_003
  · exact g32p_row09_decodeBlock_004
  · exact g32p_row09_decodeBlock_005
  · exact g32p_row09_decodeBlock_006
  · exact g32p_row09_decodeBlock_007
  · exact g32p_row09_decodeBlock_008
  · exact g32p_row09_decodeBlock_009
  · exact g32p_row09_decodeBlock_010
  · exact g32p_row09_decodeBlock_011
  · exact g32p_row09_decodeBlock_012
  · exact g32p_row09_decodeBlock_013
  · exact g32p_row09_decodeBlock_014
  · exact g32p_row09_decodeBlock_015
  · exact g32p_row09_decodeBlock_016
  · exact g32p_row09_decodeBlock_017
  · exact g32p_row09_decodeBlock_018
  · exact g32p_row09_decodeBlock_019
  · exact g32p_row09_decodeBlock_020
  · exact g32p_row09_decodeBlock_021
  · exact g32p_row09_decodeBlock_022
  · exact g32p_row09_decodeBlock_023
  · exact g32p_row09_decodeBlock_024
  · exact g32p_row09_decodeBlock_025
  · exact g32p_row09_decodeBlock_026
  · exact g32p_row09_decodeBlock_027
  · exact g32p_row09_decodeBlock_028
  · exact g32p_row09_decodeBlock_029
  · exact g32p_row09_decodeBlock_030

theorem g32p_row09_groupInjective : Function.Injective g32p_row09_groupNodes :=
  g32p_matrix_injective_of_decoder _ _ g32p_row09_matrixDecode_leftInverse

theorem g32p_row09_groupParent_lt : ∀ i : Fin 486, i ≠ 0 →
    (g32p_row09_groupParent i).val < i.val := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row09_parentLtBlock_000
  · exact g32p_row09_parentLtBlock_001
  · exact g32p_row09_parentLtBlock_002
  · exact g32p_row09_parentLtBlock_003
  · exact g32p_row09_parentLtBlock_004
  · exact g32p_row09_parentLtBlock_005
  · exact g32p_row09_parentLtBlock_006
  · exact g32p_row09_parentLtBlock_007
  · exact g32p_row09_parentLtBlock_008
  · exact g32p_row09_parentLtBlock_009
  · exact g32p_row09_parentLtBlock_010
  · exact g32p_row09_parentLtBlock_011
  · exact g32p_row09_parentLtBlock_012
  · exact g32p_row09_parentLtBlock_013
  · exact g32p_row09_parentLtBlock_014
  · exact g32p_row09_parentLtBlock_015
  · exact g32p_row09_parentLtBlock_016
  · exact g32p_row09_parentLtBlock_017
  · exact g32p_row09_parentLtBlock_018
  · exact g32p_row09_parentLtBlock_019
  · exact g32p_row09_parentLtBlock_020
  · exact g32p_row09_parentLtBlock_021
  · exact g32p_row09_parentLtBlock_022
  · exact g32p_row09_parentLtBlock_023
  · exact g32p_row09_parentLtBlock_024
  · exact g32p_row09_parentLtBlock_025
  · exact g32p_row09_parentLtBlock_026
  · exact g32p_row09_parentLtBlock_027
  · exact g32p_row09_parentLtBlock_028
  · exact g32p_row09_parentLtBlock_029
  · exact g32p_row09_parentLtBlock_030

theorem g32p_row09_groupParent_step : ∀ i : Fin 486, i ≠ 0 →
    g32p_row09_groupNext (g32p_row09_groupParent i) (g32p_row09_groupLabel i) = i := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row09_parentStepBlock_000
  · exact g32p_row09_parentStepBlock_001
  · exact g32p_row09_parentStepBlock_002
  · exact g32p_row09_parentStepBlock_003
  · exact g32p_row09_parentStepBlock_004
  · exact g32p_row09_parentStepBlock_005
  · exact g32p_row09_parentStepBlock_006
  · exact g32p_row09_parentStepBlock_007
  · exact g32p_row09_parentStepBlock_008
  · exact g32p_row09_parentStepBlock_009
  · exact g32p_row09_parentStepBlock_010
  · exact g32p_row09_parentStepBlock_011
  · exact g32p_row09_parentStepBlock_012
  · exact g32p_row09_parentStepBlock_013
  · exact g32p_row09_parentStepBlock_014
  · exact g32p_row09_parentStepBlock_015
  · exact g32p_row09_parentStepBlock_016
  · exact g32p_row09_parentStepBlock_017
  · exact g32p_row09_parentStepBlock_018
  · exact g32p_row09_parentStepBlock_019
  · exact g32p_row09_parentStepBlock_020
  · exact g32p_row09_parentStepBlock_021
  · exact g32p_row09_parentStepBlock_022
  · exact g32p_row09_parentStepBlock_023
  · exact g32p_row09_parentStepBlock_024
  · exact g32p_row09_parentStepBlock_025
  · exact g32p_row09_parentStepBlock_026
  · exact g32p_row09_parentStepBlock_027
  · exact g32p_row09_parentStepBlock_028
  · exact g32p_row09_parentStepBlock_029
  · exact g32p_row09_parentStepBlock_030

theorem g32p_row09_groupEnumeration :
    ∃ e : Fin 486 ≃ Subgroup.closure (Set.range g32p_row09_groupGenerators),
      ∀ i, b4b_toMatrix (e i : g32p_G) =
        HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
          (g32p_row09_groupNodes i)) := by
  apply g32p_matrixPathEnumeration b4b_toMatrix Subtype.val_injective
    (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
    (by rw [HurwitzPrymRex_evM_mone, map_one])
    (by intro a b; rw [HurwitzPrymRex_evM_mmul g32h_omega_sq_add, map_mul])
    (HurwitzPrymRex_g32conj_injective.comp
      (HurwitzPrymRex_evM_injective g32h_omega_sq_add))
    g32p_row09_groupGenerators g32p_row09_groupMatrices g32p_row09_groupGenerator_map
    g32p_row09_groupNodes 0 g32p_row09_groupParent g32p_row09_groupLabel Fin.val
    g32p_row09_groupNext g32p_row09_groupInjective (by decide)
    g32p_row09_groupParent_lt
  · intro i hi
    have hs := g32p_row09_groupStep
      (g32p_row09_groupParent i) (g32p_row09_groupLabel i)
    rw [g32p_row09_groupParent_step i hi] at hs
    exact hs.symm
  · exact g32p_row09_groupStep

theorem g32p_row09_groupOrder :
    Nat.card (Subgroup.closure (Set.range g32p_row09_groupGenerators)) = 486 := by
  obtain ⟨e, _⟩ := g32p_row09_groupEnumeration
  simpa only [Nat.card_fin] using (Nat.card_congr e).symm

def g32p_row09_groupEquiv : Fin 486 ≃ Subgroup.closure (Set.range g32p_row09_groupGenerators) :=
  Classical.choose g32p_row09_groupEnumeration

theorem g32p_row09_groupEquiv_map (i : Fin 486) :
    b4b_toMatrix (g32p_row09_groupEquiv i : g32p_G) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row09_groupNodes i)) :=
  Classical.choose_spec g32p_row09_groupEnumeration i

theorem g32p_row09_groupEquiv_one : g32p_row09_groupEquiv 0 = 1 := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row09_groupEquiv 0 : g32p_G) = b4b_toMatrix 1
  rw [g32p_row09_groupEquiv_map, map_one,
    show g32p_row09_groupNodes 0 = HurwitzPrymRex_mone by decide,
    HurwitzPrymRex_evM_mone, map_one]

theorem g32p_row09_groupEquiv_step (i : Fin 486) (s : Fin 3) :
    g32p_row09_groupEquiv (g32p_row09_groupNext i s) =
      g32p_row09_groupEquiv i *
        ⟨g32p_row09_groupGenerators s, Subgroup.subset_closure (Set.mem_range_self s)⟩ := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row09_groupEquiv (g32p_row09_groupNext i s) : g32p_G) =
    b4b_toMatrix ((g32p_row09_groupEquiv i : g32p_G) * g32p_row09_groupGenerators s)
  rw [map_mul, g32p_row09_groupEquiv_map, g32p_row09_groupEquiv_map,
    g32p_row09_groupGenerator_map, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  exact congrArg (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
    (g32p_row09_groupStep i s).symm

theorem g32p_row09_characterTransition : ∀ i : Fin 486, ∀ s : Fin 3,
    g32p_row09_characterValues (g32p_row09_groupNext i s) =
      g32p_row09_characterValues i * g32p_row09_characterValues (g32p_row09_groupNext 0 s) := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row09_characterBlock_000
  · exact g32p_row09_characterBlock_001
  · exact g32p_row09_characterBlock_002
  · exact g32p_row09_characterBlock_003
  · exact g32p_row09_characterBlock_004
  · exact g32p_row09_characterBlock_005
  · exact g32p_row09_characterBlock_006
  · exact g32p_row09_characterBlock_007
  · exact g32p_row09_characterBlock_008
  · exact g32p_row09_characterBlock_009
  · exact g32p_row09_characterBlock_010
  · exact g32p_row09_characterBlock_011
  · exact g32p_row09_characterBlock_012
  · exact g32p_row09_characterBlock_013
  · exact g32p_row09_characterBlock_014
  · exact g32p_row09_characterBlock_015
  · exact g32p_row09_characterBlock_016
  · exact g32p_row09_characterBlock_017
  · exact g32p_row09_characterBlock_018
  · exact g32p_row09_characterBlock_019
  · exact g32p_row09_characterBlock_020
  · exact g32p_row09_characterBlock_021
  · exact g32p_row09_characterBlock_022
  · exact g32p_row09_characterBlock_023
  · exact g32p_row09_characterBlock_024
  · exact g32p_row09_characterBlock_025
  · exact g32p_row09_characterBlock_026
  · exact g32p_row09_characterBlock_027
  · exact g32p_row09_characterBlock_028
  · exact g32p_row09_characterBlock_029
  · exact g32p_row09_characterBlock_030

theorem g32p_row09_characterSurjective : Function.Surjective g32p_row09_characterValues := by
  decide +kernel

def g32p_row09_finiteSupplier : g32p_Supplier :=
  g32p_supplierOfFiniteTransitions (by decide) g32p_row09_groupGenerators
    g32p_row09_groupEquiv 0 g32p_row09_groupEquiv_one
    g32p_row09_groupNext g32p_row09_groupEquiv_step g32p_row09_characterValues
    (by rfl) g32p_row09_characterTransition g32p_row09_characterSurjective

theorem g32p_row09_finiteSupplier_order : Nat.card g32p_row09_finiteSupplier.H = 486 :=
  g32p_row09_groupOrder

theorem g32p_row09_finiteSupplier_value (i : Fin 486) :
    g32p_row09_finiteSupplier.χ (g32p_row09_groupEquiv i) = g32p_row09_characterValues i :=
  g32p_supplierOfFiniteTransitions_value ..

end HodgeLean.Foundations.Program
