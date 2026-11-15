import HodgeLean.Foundations.Program.G32PropFourSixPacked0028
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow30Decode
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
import HodgeLean.Foundations.Program.G32PropFourSixPacked0130
import HodgeLean.Foundations.Program.G32PropFourSixPacked0130
import HodgeLean.Foundations.Program.G32PropFourSixPacked0130
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow30CharacterBlock00
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

theorem g32p_row30_groupTransition :
    g32p_transitionCheck g32p_row30_groupNodes g32p_row30_groupMatrices
      g32p_row30_groupNext = true := by
  apply decide_eq_true
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row30_transitionBlock_000
  · exact g32p_row30_transitionBlock_001
  · exact g32p_row30_transitionBlock_002
  · exact g32p_row30_transitionBlock_003
  · exact g32p_row30_transitionBlock_004
  · exact g32p_row30_transitionBlock_005
  · exact g32p_row30_transitionBlock_006
  · exact g32p_row30_transitionBlock_007
  · exact g32p_row30_transitionBlock_008
  · exact g32p_row30_transitionBlock_009
  · exact g32p_row30_transitionBlock_010
  · exact g32p_row30_transitionBlock_011
  · exact g32p_row30_transitionBlock_012
  · exact g32p_row30_transitionBlock_013
  · exact g32p_row30_transitionBlock_014
  · exact g32p_row30_transitionBlock_015
  · exact g32p_row30_transitionBlock_016
  · exact g32p_row30_transitionBlock_017
  · exact g32p_row30_transitionBlock_018
  · exact g32p_row30_transitionBlock_019
  · exact g32p_row30_transitionBlock_020

theorem g32p_row30_groupStep (i : Fin 324) (s : Fin 5) :
    HurwitzPrymRex_mmul (g32p_row30_groupNodes i) (g32p_row30_groupMatrices s) =
      g32p_row30_groupNodes (g32p_row30_groupNext i s) := by
  exact g32p_transition_integral_sound _ _ _ g32p_row30_groupTransition i s

theorem g32p_row30_matrixDecode_leftInverse : ∀ i : Fin 324,
    g32p_row30_matrixDecode (g32p_matrixFingerprint (g32p_row30_groupNodes i)) = i := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row30_decodeBlock_000
  · exact g32p_row30_decodeBlock_001
  · exact g32p_row30_decodeBlock_002
  · exact g32p_row30_decodeBlock_003
  · exact g32p_row30_decodeBlock_004
  · exact g32p_row30_decodeBlock_005
  · exact g32p_row30_decodeBlock_006
  · exact g32p_row30_decodeBlock_007
  · exact g32p_row30_decodeBlock_008
  · exact g32p_row30_decodeBlock_009
  · exact g32p_row30_decodeBlock_010
  · exact g32p_row30_decodeBlock_011
  · exact g32p_row30_decodeBlock_012
  · exact g32p_row30_decodeBlock_013
  · exact g32p_row30_decodeBlock_014
  · exact g32p_row30_decodeBlock_015
  · exact g32p_row30_decodeBlock_016
  · exact g32p_row30_decodeBlock_017
  · exact g32p_row30_decodeBlock_018
  · exact g32p_row30_decodeBlock_019
  · exact g32p_row30_decodeBlock_020

theorem g32p_row30_groupInjective : Function.Injective g32p_row30_groupNodes :=
  g32p_matrix_injective_of_decoder _ _ g32p_row30_matrixDecode_leftInverse

theorem g32p_row30_groupParent_lt : ∀ i : Fin 324, i ≠ 0 →
    (g32p_row30_groupParent i).val < i.val := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row30_parentLtBlock_000
  · exact g32p_row30_parentLtBlock_001
  · exact g32p_row30_parentLtBlock_002
  · exact g32p_row30_parentLtBlock_003
  · exact g32p_row30_parentLtBlock_004
  · exact g32p_row30_parentLtBlock_005
  · exact g32p_row30_parentLtBlock_006
  · exact g32p_row30_parentLtBlock_007
  · exact g32p_row30_parentLtBlock_008
  · exact g32p_row30_parentLtBlock_009
  · exact g32p_row30_parentLtBlock_010
  · exact g32p_row30_parentLtBlock_011
  · exact g32p_row30_parentLtBlock_012
  · exact g32p_row30_parentLtBlock_013
  · exact g32p_row30_parentLtBlock_014
  · exact g32p_row30_parentLtBlock_015
  · exact g32p_row30_parentLtBlock_016
  · exact g32p_row30_parentLtBlock_017
  · exact g32p_row30_parentLtBlock_018
  · exact g32p_row30_parentLtBlock_019
  · exact g32p_row30_parentLtBlock_020

theorem g32p_row30_groupParent_step : ∀ i : Fin 324, i ≠ 0 →
    g32p_row30_groupNext (g32p_row30_groupParent i) (g32p_row30_groupLabel i) = i := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row30_parentStepBlock_000
  · exact g32p_row30_parentStepBlock_001
  · exact g32p_row30_parentStepBlock_002
  · exact g32p_row30_parentStepBlock_003
  · exact g32p_row30_parentStepBlock_004
  · exact g32p_row30_parentStepBlock_005
  · exact g32p_row30_parentStepBlock_006
  · exact g32p_row30_parentStepBlock_007
  · exact g32p_row30_parentStepBlock_008
  · exact g32p_row30_parentStepBlock_009
  · exact g32p_row30_parentStepBlock_010
  · exact g32p_row30_parentStepBlock_011
  · exact g32p_row30_parentStepBlock_012
  · exact g32p_row30_parentStepBlock_013
  · exact g32p_row30_parentStepBlock_014
  · exact g32p_row30_parentStepBlock_015
  · exact g32p_row30_parentStepBlock_016
  · exact g32p_row30_parentStepBlock_017
  · exact g32p_row30_parentStepBlock_018
  · exact g32p_row30_parentStepBlock_019
  · exact g32p_row30_parentStepBlock_020

theorem g32p_row30_groupEnumeration :
    ∃ e : Fin 324 ≃ Subgroup.closure (Set.range g32p_row30_groupGenerators),
      ∀ i, b4b_toMatrix (e i : g32p_G) =
        HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
          (g32p_row30_groupNodes i)) := by
  apply g32p_matrixPathEnumeration b4b_toMatrix Subtype.val_injective
    (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
    (by rw [HurwitzPrymRex_evM_mone, map_one])
    (by intro a b; rw [HurwitzPrymRex_evM_mmul g32h_omega_sq_add, map_mul])
    (HurwitzPrymRex_g32conj_injective.comp
      (HurwitzPrymRex_evM_injective g32h_omega_sq_add))
    g32p_row30_groupGenerators g32p_row30_groupMatrices g32p_row30_groupGenerator_map
    g32p_row30_groupNodes 0 g32p_row30_groupParent g32p_row30_groupLabel Fin.val
    g32p_row30_groupNext g32p_row30_groupInjective (by decide)
    g32p_row30_groupParent_lt
  · intro i hi
    have hs := g32p_row30_groupStep
      (g32p_row30_groupParent i) (g32p_row30_groupLabel i)
    rw [g32p_row30_groupParent_step i hi] at hs
    exact hs.symm
  · exact g32p_row30_groupStep

theorem g32p_row30_groupOrder :
    Nat.card (Subgroup.closure (Set.range g32p_row30_groupGenerators)) = 324 := by
  obtain ⟨e, _⟩ := g32p_row30_groupEnumeration
  simpa only [Nat.card_fin] using (Nat.card_congr e).symm

def g32p_row30_groupEquiv : Fin 324 ≃ Subgroup.closure (Set.range g32p_row30_groupGenerators) :=
  Classical.choose g32p_row30_groupEnumeration

theorem g32p_row30_groupEquiv_map (i : Fin 324) :
    b4b_toMatrix (g32p_row30_groupEquiv i : g32p_G) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row30_groupNodes i)) :=
  Classical.choose_spec g32p_row30_groupEnumeration i

theorem g32p_row30_groupEquiv_one : g32p_row30_groupEquiv 0 = 1 := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row30_groupEquiv 0 : g32p_G) = b4b_toMatrix 1
  rw [g32p_row30_groupEquiv_map, map_one,
    show g32p_row30_groupNodes 0 = HurwitzPrymRex_mone by decide,
    HurwitzPrymRex_evM_mone, map_one]

theorem g32p_row30_groupEquiv_step (i : Fin 324) (s : Fin 5) :
    g32p_row30_groupEquiv (g32p_row30_groupNext i s) =
      g32p_row30_groupEquiv i *
        ⟨g32p_row30_groupGenerators s, Subgroup.subset_closure (Set.mem_range_self s)⟩ := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row30_groupEquiv (g32p_row30_groupNext i s) : g32p_G) =
    b4b_toMatrix ((g32p_row30_groupEquiv i : g32p_G) * g32p_row30_groupGenerators s)
  rw [map_mul, g32p_row30_groupEquiv_map, g32p_row30_groupEquiv_map,
    g32p_row30_groupGenerator_map, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  exact congrArg (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
    (g32p_row30_groupStep i s).symm

theorem g32p_row30_characterTransition : ∀ i : Fin 324, ∀ s : Fin 5,
    g32p_row30_characterValues (g32p_row30_groupNext i s) =
      g32p_row30_characterValues i * g32p_row30_characterValues (g32p_row30_groupNext 0 s) := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row30_characterBlock_000
  · exact g32p_row30_characterBlock_001
  · exact g32p_row30_characterBlock_002
  · exact g32p_row30_characterBlock_003
  · exact g32p_row30_characterBlock_004
  · exact g32p_row30_characterBlock_005
  · exact g32p_row30_characterBlock_006
  · exact g32p_row30_characterBlock_007
  · exact g32p_row30_characterBlock_008
  · exact g32p_row30_characterBlock_009
  · exact g32p_row30_characterBlock_010
  · exact g32p_row30_characterBlock_011
  · exact g32p_row30_characterBlock_012
  · exact g32p_row30_characterBlock_013
  · exact g32p_row30_characterBlock_014
  · exact g32p_row30_characterBlock_015
  · exact g32p_row30_characterBlock_016
  · exact g32p_row30_characterBlock_017
  · exact g32p_row30_characterBlock_018
  · exact g32p_row30_characterBlock_019
  · exact g32p_row30_characterBlock_020

theorem g32p_row30_characterSurjective : Function.Surjective g32p_row30_characterValues := by
  decide +kernel

def g32p_row30_finiteSupplier : g32p_Supplier :=
  g32p_supplierOfFiniteTransitions (by decide) g32p_row30_groupGenerators
    g32p_row30_groupEquiv 0 g32p_row30_groupEquiv_one
    g32p_row30_groupNext g32p_row30_groupEquiv_step g32p_row30_characterValues
    (by rfl) g32p_row30_characterTransition g32p_row30_characterSurjective

theorem g32p_row30_finiteSupplier_order : Nat.card g32p_row30_finiteSupplier.H = 324 :=
  g32p_row30_groupOrder

theorem g32p_row30_finiteSupplier_value (i : Fin 324) :
    g32p_row30_finiteSupplier.χ (g32p_row30_groupEquiv i) = g32p_row30_characterValues i :=
  g32p_supplierOfFiniteTransitions_value ..

end HodgeLean.Foundations.Program
