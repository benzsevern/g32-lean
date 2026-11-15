import HodgeLean.Foundations.Program.G32PropFourSixPacked0030
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow36Decode
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
import HodgeLean.Foundations.Program.G32PropFourSixPacked0150
import HodgeLean.Foundations.Program.G32PropFourSixPacked0150
import HodgeLean.Foundations.Program.G32PropFourSixPacked0150
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow36CharacterBlock00
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

theorem g32p_row36_groupTransition :
    g32p_transitionCheck g32p_row36_groupNodes g32p_row36_groupMatrices
      g32p_row36_groupNext = true := by
  apply decide_eq_true
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row36_transitionBlock_000
  · exact g32p_row36_transitionBlock_001
  · exact g32p_row36_transitionBlock_002
  · exact g32p_row36_transitionBlock_003
  · exact g32p_row36_transitionBlock_004
  · exact g32p_row36_transitionBlock_005
  · exact g32p_row36_transitionBlock_006
  · exact g32p_row36_transitionBlock_007
  · exact g32p_row36_transitionBlock_008
  · exact g32p_row36_transitionBlock_009
  · exact g32p_row36_transitionBlock_010
  · exact g32p_row36_transitionBlock_011
  · exact g32p_row36_transitionBlock_012
  · exact g32p_row36_transitionBlock_013
  · exact g32p_row36_transitionBlock_014
  · exact g32p_row36_transitionBlock_015
  · exact g32p_row36_transitionBlock_016
  · exact g32p_row36_transitionBlock_017
  · exact g32p_row36_transitionBlock_018
  · exact g32p_row36_transitionBlock_019
  · exact g32p_row36_transitionBlock_020
  · exact g32p_row36_transitionBlock_021
  · exact g32p_row36_transitionBlock_022
  · exact g32p_row36_transitionBlock_023

theorem g32p_row36_groupStep (i : Fin 384) (s : Fin 3) :
    HurwitzPrymRex_mmul (g32p_row36_groupNodes i) (g32p_row36_groupMatrices s) =
      g32p_row36_groupNodes (g32p_row36_groupNext i s) := by
  exact g32p_transition_integral_sound _ _ _ g32p_row36_groupTransition i s

theorem g32p_row36_matrixDecode_leftInverse : ∀ i : Fin 384,
    g32p_row36_matrixDecode (g32p_matrixFingerprint (g32p_row36_groupNodes i)) = i := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row36_decodeBlock_000
  · exact g32p_row36_decodeBlock_001
  · exact g32p_row36_decodeBlock_002
  · exact g32p_row36_decodeBlock_003
  · exact g32p_row36_decodeBlock_004
  · exact g32p_row36_decodeBlock_005
  · exact g32p_row36_decodeBlock_006
  · exact g32p_row36_decodeBlock_007
  · exact g32p_row36_decodeBlock_008
  · exact g32p_row36_decodeBlock_009
  · exact g32p_row36_decodeBlock_010
  · exact g32p_row36_decodeBlock_011
  · exact g32p_row36_decodeBlock_012
  · exact g32p_row36_decodeBlock_013
  · exact g32p_row36_decodeBlock_014
  · exact g32p_row36_decodeBlock_015
  · exact g32p_row36_decodeBlock_016
  · exact g32p_row36_decodeBlock_017
  · exact g32p_row36_decodeBlock_018
  · exact g32p_row36_decodeBlock_019
  · exact g32p_row36_decodeBlock_020
  · exact g32p_row36_decodeBlock_021
  · exact g32p_row36_decodeBlock_022
  · exact g32p_row36_decodeBlock_023

theorem g32p_row36_groupInjective : Function.Injective g32p_row36_groupNodes :=
  g32p_matrix_injective_of_decoder _ _ g32p_row36_matrixDecode_leftInverse

theorem g32p_row36_groupParent_lt : ∀ i : Fin 384, i ≠ 0 →
    (g32p_row36_groupParent i).val < i.val := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row36_parentLtBlock_000
  · exact g32p_row36_parentLtBlock_001
  · exact g32p_row36_parentLtBlock_002
  · exact g32p_row36_parentLtBlock_003
  · exact g32p_row36_parentLtBlock_004
  · exact g32p_row36_parentLtBlock_005
  · exact g32p_row36_parentLtBlock_006
  · exact g32p_row36_parentLtBlock_007
  · exact g32p_row36_parentLtBlock_008
  · exact g32p_row36_parentLtBlock_009
  · exact g32p_row36_parentLtBlock_010
  · exact g32p_row36_parentLtBlock_011
  · exact g32p_row36_parentLtBlock_012
  · exact g32p_row36_parentLtBlock_013
  · exact g32p_row36_parentLtBlock_014
  · exact g32p_row36_parentLtBlock_015
  · exact g32p_row36_parentLtBlock_016
  · exact g32p_row36_parentLtBlock_017
  · exact g32p_row36_parentLtBlock_018
  · exact g32p_row36_parentLtBlock_019
  · exact g32p_row36_parentLtBlock_020
  · exact g32p_row36_parentLtBlock_021
  · exact g32p_row36_parentLtBlock_022
  · exact g32p_row36_parentLtBlock_023

theorem g32p_row36_groupParent_step : ∀ i : Fin 384, i ≠ 0 →
    g32p_row36_groupNext (g32p_row36_groupParent i) (g32p_row36_groupLabel i) = i := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row36_parentStepBlock_000
  · exact g32p_row36_parentStepBlock_001
  · exact g32p_row36_parentStepBlock_002
  · exact g32p_row36_parentStepBlock_003
  · exact g32p_row36_parentStepBlock_004
  · exact g32p_row36_parentStepBlock_005
  · exact g32p_row36_parentStepBlock_006
  · exact g32p_row36_parentStepBlock_007
  · exact g32p_row36_parentStepBlock_008
  · exact g32p_row36_parentStepBlock_009
  · exact g32p_row36_parentStepBlock_010
  · exact g32p_row36_parentStepBlock_011
  · exact g32p_row36_parentStepBlock_012
  · exact g32p_row36_parentStepBlock_013
  · exact g32p_row36_parentStepBlock_014
  · exact g32p_row36_parentStepBlock_015
  · exact g32p_row36_parentStepBlock_016
  · exact g32p_row36_parentStepBlock_017
  · exact g32p_row36_parentStepBlock_018
  · exact g32p_row36_parentStepBlock_019
  · exact g32p_row36_parentStepBlock_020
  · exact g32p_row36_parentStepBlock_021
  · exact g32p_row36_parentStepBlock_022
  · exact g32p_row36_parentStepBlock_023

theorem g32p_row36_groupEnumeration :
    ∃ e : Fin 384 ≃ Subgroup.closure (Set.range g32p_row36_groupGenerators),
      ∀ i, b4b_toMatrix (e i : g32p_G) =
        HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
          (g32p_row36_groupNodes i)) := by
  apply g32p_matrixPathEnumeration b4b_toMatrix Subtype.val_injective
    (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
    (by rw [HurwitzPrymRex_evM_mone, map_one])
    (by intro a b; rw [HurwitzPrymRex_evM_mmul g32h_omega_sq_add, map_mul])
    (HurwitzPrymRex_g32conj_injective.comp
      (HurwitzPrymRex_evM_injective g32h_omega_sq_add))
    g32p_row36_groupGenerators g32p_row36_groupMatrices g32p_row36_groupGenerator_map
    g32p_row36_groupNodes 0 g32p_row36_groupParent g32p_row36_groupLabel Fin.val
    g32p_row36_groupNext g32p_row36_groupInjective (by decide)
    g32p_row36_groupParent_lt
  · intro i hi
    have hs := g32p_row36_groupStep
      (g32p_row36_groupParent i) (g32p_row36_groupLabel i)
    rw [g32p_row36_groupParent_step i hi] at hs
    exact hs.symm
  · exact g32p_row36_groupStep

theorem g32p_row36_groupOrder :
    Nat.card (Subgroup.closure (Set.range g32p_row36_groupGenerators)) = 384 := by
  obtain ⟨e, _⟩ := g32p_row36_groupEnumeration
  simpa only [Nat.card_fin] using (Nat.card_congr e).symm

def g32p_row36_groupEquiv : Fin 384 ≃ Subgroup.closure (Set.range g32p_row36_groupGenerators) :=
  Classical.choose g32p_row36_groupEnumeration

theorem g32p_row36_groupEquiv_map (i : Fin 384) :
    b4b_toMatrix (g32p_row36_groupEquiv i : g32p_G) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row36_groupNodes i)) :=
  Classical.choose_spec g32p_row36_groupEnumeration i

theorem g32p_row36_groupEquiv_one : g32p_row36_groupEquiv 0 = 1 := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row36_groupEquiv 0 : g32p_G) = b4b_toMatrix 1
  rw [g32p_row36_groupEquiv_map, map_one,
    show g32p_row36_groupNodes 0 = HurwitzPrymRex_mone by decide,
    HurwitzPrymRex_evM_mone, map_one]

theorem g32p_row36_groupEquiv_step (i : Fin 384) (s : Fin 3) :
    g32p_row36_groupEquiv (g32p_row36_groupNext i s) =
      g32p_row36_groupEquiv i *
        ⟨g32p_row36_groupGenerators s, Subgroup.subset_closure (Set.mem_range_self s)⟩ := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row36_groupEquiv (g32p_row36_groupNext i s) : g32p_G) =
    b4b_toMatrix ((g32p_row36_groupEquiv i : g32p_G) * g32p_row36_groupGenerators s)
  rw [map_mul, g32p_row36_groupEquiv_map, g32p_row36_groupEquiv_map,
    g32p_row36_groupGenerator_map, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  exact congrArg (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
    (g32p_row36_groupStep i s).symm

theorem g32p_row36_characterTransition : ∀ i : Fin 384, ∀ s : Fin 3,
    g32p_row36_characterValues (g32p_row36_groupNext i s) =
      g32p_row36_characterValues i * g32p_row36_characterValues (g32p_row36_groupNext 0 s) := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row36_characterBlock_000
  · exact g32p_row36_characterBlock_001
  · exact g32p_row36_characterBlock_002
  · exact g32p_row36_characterBlock_003
  · exact g32p_row36_characterBlock_004
  · exact g32p_row36_characterBlock_005
  · exact g32p_row36_characterBlock_006
  · exact g32p_row36_characterBlock_007
  · exact g32p_row36_characterBlock_008
  · exact g32p_row36_characterBlock_009
  · exact g32p_row36_characterBlock_010
  · exact g32p_row36_characterBlock_011
  · exact g32p_row36_characterBlock_012
  · exact g32p_row36_characterBlock_013
  · exact g32p_row36_characterBlock_014
  · exact g32p_row36_characterBlock_015
  · exact g32p_row36_characterBlock_016
  · exact g32p_row36_characterBlock_017
  · exact g32p_row36_characterBlock_018
  · exact g32p_row36_characterBlock_019
  · exact g32p_row36_characterBlock_020
  · exact g32p_row36_characterBlock_021
  · exact g32p_row36_characterBlock_022
  · exact g32p_row36_characterBlock_023

theorem g32p_row36_characterSurjective : Function.Surjective g32p_row36_characterValues := by
  decide +kernel

def g32p_row36_finiteSupplier : g32p_Supplier :=
  g32p_supplierOfFiniteTransitions (by decide) g32p_row36_groupGenerators
    g32p_row36_groupEquiv 0 g32p_row36_groupEquiv_one
    g32p_row36_groupNext g32p_row36_groupEquiv_step g32p_row36_characterValues
    (by rfl) g32p_row36_characterTransition g32p_row36_characterSurjective

theorem g32p_row36_finiteSupplier_order : Nat.card g32p_row36_finiteSupplier.H = 384 :=
  g32p_row36_groupOrder

theorem g32p_row36_finiteSupplier_value (i : Fin 384) :
    g32p_row36_finiteSupplier.χ (g32p_row36_groupEquiv i) = g32p_row36_characterValues i :=
  g32p_supplierOfFiniteTransitions_value ..

end HodgeLean.Foundations.Program
