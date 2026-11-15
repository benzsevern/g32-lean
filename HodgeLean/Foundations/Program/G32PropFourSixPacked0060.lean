import HodgeLean.Foundations.Program.G32PropFourSixPacked0057
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow07Decode
import HodgeLean.Foundations.Program.G32PropFourSixPacked0059
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCheck
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row07_groupParent_lt : ∀ i : Fin 1944, i ≠ 0 →
    (g32p_row07_groupParent i).val < i.val := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row07_parentLtBlock_000
  · exact g32p_row07_parentLtBlock_001
  · exact g32p_row07_parentLtBlock_002
  · exact g32p_row07_parentLtBlock_003
  · exact g32p_row07_parentLtBlock_004
  · exact g32p_row07_parentLtBlock_005
  · exact g32p_row07_parentLtBlock_006
  · exact g32p_row07_parentLtBlock_007
  · exact g32p_row07_parentLtBlock_008
  · exact g32p_row07_parentLtBlock_009
  · exact g32p_row07_parentLtBlock_010
  · exact g32p_row07_parentLtBlock_011
  · exact g32p_row07_parentLtBlock_012
  · exact g32p_row07_parentLtBlock_013
  · exact g32p_row07_parentLtBlock_014
  · exact g32p_row07_parentLtBlock_015
  · exact g32p_row07_parentLtBlock_016
  · exact g32p_row07_parentLtBlock_017
  · exact g32p_row07_parentLtBlock_018
  · exact g32p_row07_parentLtBlock_019
  · exact g32p_row07_parentLtBlock_020
  · exact g32p_row07_parentLtBlock_021
  · exact g32p_row07_parentLtBlock_022
  · exact g32p_row07_parentLtBlock_023
  · exact g32p_row07_parentLtBlock_024
  · exact g32p_row07_parentLtBlock_025
  · exact g32p_row07_parentLtBlock_026
  · exact g32p_row07_parentLtBlock_027
  · exact g32p_row07_parentLtBlock_028
  · exact g32p_row07_parentLtBlock_029
  · exact g32p_row07_parentLtBlock_030
  · exact g32p_row07_parentLtBlock_031
  · exact g32p_row07_parentLtBlock_032
  · exact g32p_row07_parentLtBlock_033
  · exact g32p_row07_parentLtBlock_034
  · exact g32p_row07_parentLtBlock_035
  · exact g32p_row07_parentLtBlock_036
  · exact g32p_row07_parentLtBlock_037
  · exact g32p_row07_parentLtBlock_038
  · exact g32p_row07_parentLtBlock_039
  · exact g32p_row07_parentLtBlock_040
  · exact g32p_row07_parentLtBlock_041
  · exact g32p_row07_parentLtBlock_042
  · exact g32p_row07_parentLtBlock_043
  · exact g32p_row07_parentLtBlock_044
  · exact g32p_row07_parentLtBlock_045
  · exact g32p_row07_parentLtBlock_046
  · exact g32p_row07_parentLtBlock_047
  · exact g32p_row07_parentLtBlock_048
  · exact g32p_row07_parentLtBlock_049
  · exact g32p_row07_parentLtBlock_050
  · exact g32p_row07_parentLtBlock_051
  · exact g32p_row07_parentLtBlock_052
  · exact g32p_row07_parentLtBlock_053
  · exact g32p_row07_parentLtBlock_054
  · exact g32p_row07_parentLtBlock_055
  · exact g32p_row07_parentLtBlock_056
  · exact g32p_row07_parentLtBlock_057
  · exact g32p_row07_parentLtBlock_058
  · exact g32p_row07_parentLtBlock_059
  · exact g32p_row07_parentLtBlock_060
  · exact g32p_row07_parentLtBlock_061
  · exact g32p_row07_parentLtBlock_062
  · exact g32p_row07_parentLtBlock_063
  · exact g32p_row07_parentLtBlock_064
  · exact g32p_row07_parentLtBlock_065
  · exact g32p_row07_parentLtBlock_066
  · exact g32p_row07_parentLtBlock_067
  · exact g32p_row07_parentLtBlock_068
  · exact g32p_row07_parentLtBlock_069
  · exact g32p_row07_parentLtBlock_070
  · exact g32p_row07_parentLtBlock_071
  · exact g32p_row07_parentLtBlock_072
  · exact g32p_row07_parentLtBlock_073
  · exact g32p_row07_parentLtBlock_074
  · exact g32p_row07_parentLtBlock_075
  · exact g32p_row07_parentLtBlock_076
  · exact g32p_row07_parentLtBlock_077
  · exact g32p_row07_parentLtBlock_078
  · exact g32p_row07_parentLtBlock_079
  · exact g32p_row07_parentLtBlock_080
  · exact g32p_row07_parentLtBlock_081
  · exact g32p_row07_parentLtBlock_082
  · exact g32p_row07_parentLtBlock_083
  · exact g32p_row07_parentLtBlock_084
  · exact g32p_row07_parentLtBlock_085
  · exact g32p_row07_parentLtBlock_086
  · exact g32p_row07_parentLtBlock_087
  · exact g32p_row07_parentLtBlock_088
  · exact g32p_row07_parentLtBlock_089
  · exact g32p_row07_parentLtBlock_090
  · exact g32p_row07_parentLtBlock_091
  · exact g32p_row07_parentLtBlock_092
  · exact g32p_row07_parentLtBlock_093
  · exact g32p_row07_parentLtBlock_094
  · exact g32p_row07_parentLtBlock_095
  · exact g32p_row07_parentLtBlock_096
  · exact g32p_row07_parentLtBlock_097
  · exact g32p_row07_parentLtBlock_098
  · exact g32p_row07_parentLtBlock_099
  · exact g32p_row07_parentLtBlock_100
  · exact g32p_row07_parentLtBlock_101
  · exact g32p_row07_parentLtBlock_102
  · exact g32p_row07_parentLtBlock_103
  · exact g32p_row07_parentLtBlock_104
  · exact g32p_row07_parentLtBlock_105
  · exact g32p_row07_parentLtBlock_106
  · exact g32p_row07_parentLtBlock_107
  · exact g32p_row07_parentLtBlock_108
  · exact g32p_row07_parentLtBlock_109
  · exact g32p_row07_parentLtBlock_110
  · exact g32p_row07_parentLtBlock_111
  · exact g32p_row07_parentLtBlock_112
  · exact g32p_row07_parentLtBlock_113
  · exact g32p_row07_parentLtBlock_114
  · exact g32p_row07_parentLtBlock_115
  · exact g32p_row07_parentLtBlock_116
  · exact g32p_row07_parentLtBlock_117
  · exact g32p_row07_parentLtBlock_118
  · exact g32p_row07_parentLtBlock_119
  · exact g32p_row07_parentLtBlock_120
  · exact g32p_row07_parentLtBlock_121

theorem g32p_row07_groupParent_step : ∀ i : Fin 1944, i ≠ 0 →
    g32p_row07_groupNext (g32p_row07_groupParent i) (g32p_row07_groupLabel i) = i := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row07_parentStepBlock_000
  · exact g32p_row07_parentStepBlock_001
  · exact g32p_row07_parentStepBlock_002
  · exact g32p_row07_parentStepBlock_003
  · exact g32p_row07_parentStepBlock_004
  · exact g32p_row07_parentStepBlock_005
  · exact g32p_row07_parentStepBlock_006
  · exact g32p_row07_parentStepBlock_007
  · exact g32p_row07_parentStepBlock_008
  · exact g32p_row07_parentStepBlock_009
  · exact g32p_row07_parentStepBlock_010
  · exact g32p_row07_parentStepBlock_011
  · exact g32p_row07_parentStepBlock_012
  · exact g32p_row07_parentStepBlock_013
  · exact g32p_row07_parentStepBlock_014
  · exact g32p_row07_parentStepBlock_015
  · exact g32p_row07_parentStepBlock_016
  · exact g32p_row07_parentStepBlock_017
  · exact g32p_row07_parentStepBlock_018
  · exact g32p_row07_parentStepBlock_019
  · exact g32p_row07_parentStepBlock_020
  · exact g32p_row07_parentStepBlock_021
  · exact g32p_row07_parentStepBlock_022
  · exact g32p_row07_parentStepBlock_023
  · exact g32p_row07_parentStepBlock_024
  · exact g32p_row07_parentStepBlock_025
  · exact g32p_row07_parentStepBlock_026
  · exact g32p_row07_parentStepBlock_027
  · exact g32p_row07_parentStepBlock_028
  · exact g32p_row07_parentStepBlock_029
  · exact g32p_row07_parentStepBlock_030
  · exact g32p_row07_parentStepBlock_031
  · exact g32p_row07_parentStepBlock_032
  · exact g32p_row07_parentStepBlock_033
  · exact g32p_row07_parentStepBlock_034
  · exact g32p_row07_parentStepBlock_035
  · exact g32p_row07_parentStepBlock_036
  · exact g32p_row07_parentStepBlock_037
  · exact g32p_row07_parentStepBlock_038
  · exact g32p_row07_parentStepBlock_039
  · exact g32p_row07_parentStepBlock_040
  · exact g32p_row07_parentStepBlock_041
  · exact g32p_row07_parentStepBlock_042
  · exact g32p_row07_parentStepBlock_043
  · exact g32p_row07_parentStepBlock_044
  · exact g32p_row07_parentStepBlock_045
  · exact g32p_row07_parentStepBlock_046
  · exact g32p_row07_parentStepBlock_047
  · exact g32p_row07_parentStepBlock_048
  · exact g32p_row07_parentStepBlock_049
  · exact g32p_row07_parentStepBlock_050
  · exact g32p_row07_parentStepBlock_051
  · exact g32p_row07_parentStepBlock_052
  · exact g32p_row07_parentStepBlock_053
  · exact g32p_row07_parentStepBlock_054
  · exact g32p_row07_parentStepBlock_055
  · exact g32p_row07_parentStepBlock_056
  · exact g32p_row07_parentStepBlock_057
  · exact g32p_row07_parentStepBlock_058
  · exact g32p_row07_parentStepBlock_059
  · exact g32p_row07_parentStepBlock_060
  · exact g32p_row07_parentStepBlock_061
  · exact g32p_row07_parentStepBlock_062
  · exact g32p_row07_parentStepBlock_063
  · exact g32p_row07_parentStepBlock_064
  · exact g32p_row07_parentStepBlock_065
  · exact g32p_row07_parentStepBlock_066
  · exact g32p_row07_parentStepBlock_067
  · exact g32p_row07_parentStepBlock_068
  · exact g32p_row07_parentStepBlock_069
  · exact g32p_row07_parentStepBlock_070
  · exact g32p_row07_parentStepBlock_071
  · exact g32p_row07_parentStepBlock_072
  · exact g32p_row07_parentStepBlock_073
  · exact g32p_row07_parentStepBlock_074
  · exact g32p_row07_parentStepBlock_075
  · exact g32p_row07_parentStepBlock_076
  · exact g32p_row07_parentStepBlock_077
  · exact g32p_row07_parentStepBlock_078
  · exact g32p_row07_parentStepBlock_079
  · exact g32p_row07_parentStepBlock_080
  · exact g32p_row07_parentStepBlock_081
  · exact g32p_row07_parentStepBlock_082
  · exact g32p_row07_parentStepBlock_083
  · exact g32p_row07_parentStepBlock_084
  · exact g32p_row07_parentStepBlock_085
  · exact g32p_row07_parentStepBlock_086
  · exact g32p_row07_parentStepBlock_087
  · exact g32p_row07_parentStepBlock_088
  · exact g32p_row07_parentStepBlock_089
  · exact g32p_row07_parentStepBlock_090
  · exact g32p_row07_parentStepBlock_091
  · exact g32p_row07_parentStepBlock_092
  · exact g32p_row07_parentStepBlock_093
  · exact g32p_row07_parentStepBlock_094
  · exact g32p_row07_parentStepBlock_095
  · exact g32p_row07_parentStepBlock_096
  · exact g32p_row07_parentStepBlock_097
  · exact g32p_row07_parentStepBlock_098
  · exact g32p_row07_parentStepBlock_099
  · exact g32p_row07_parentStepBlock_100
  · exact g32p_row07_parentStepBlock_101
  · exact g32p_row07_parentStepBlock_102
  · exact g32p_row07_parentStepBlock_103
  · exact g32p_row07_parentStepBlock_104
  · exact g32p_row07_parentStepBlock_105
  · exact g32p_row07_parentStepBlock_106
  · exact g32p_row07_parentStepBlock_107
  · exact g32p_row07_parentStepBlock_108
  · exact g32p_row07_parentStepBlock_109
  · exact g32p_row07_parentStepBlock_110
  · exact g32p_row07_parentStepBlock_111
  · exact g32p_row07_parentStepBlock_112
  · exact g32p_row07_parentStepBlock_113
  · exact g32p_row07_parentStepBlock_114
  · exact g32p_row07_parentStepBlock_115
  · exact g32p_row07_parentStepBlock_116
  · exact g32p_row07_parentStepBlock_117
  · exact g32p_row07_parentStepBlock_118
  · exact g32p_row07_parentStepBlock_119
  · exact g32p_row07_parentStepBlock_120
  · exact g32p_row07_parentStepBlock_121


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row07_groupEnumeration :
    ∃ e : Fin 1944 ≃ Subgroup.closure (Set.range g32p_row07_groupGenerators),
      ∀ i, b4b_toMatrix (e i : g32p_G) =
        HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
          (g32p_row07_groupNodes i)) := by
  apply g32p_matrixPathEnumeration b4b_toMatrix Subtype.val_injective
    (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
    (by rw [HurwitzPrymRex_evM_mone, map_one])
    (by intro a b; rw [HurwitzPrymRex_evM_mmul g32h_omega_sq_add, map_mul])
    (HurwitzPrymRex_g32conj_injective.comp
      (HurwitzPrymRex_evM_injective g32h_omega_sq_add))
    g32p_row07_groupGenerators g32p_row07_groupMatrices g32p_row07_groupGenerator_map
    g32p_row07_groupNodes 0 g32p_row07_groupParent g32p_row07_groupLabel Fin.val
    g32p_row07_groupNext g32p_row07_groupInjective (by decide)
    g32p_row07_groupParent_lt
  · intro i hi
    have hs := g32p_row07_groupStep
      (g32p_row07_groupParent i) (g32p_row07_groupLabel i)
    rw [g32p_row07_groupParent_step i hi] at hs
    exact hs.symm
  · exact g32p_row07_groupStep

theorem g32p_row07_groupOrder :
    Nat.card (Subgroup.closure (Set.range g32p_row07_groupGenerators)) = 1944 := by
  obtain ⟨e, _⟩ := g32p_row07_groupEnumeration
  simpa only [Nat.card_fin] using (Nat.card_congr e).symm

def g32p_row07_groupEquiv : Fin 1944 ≃ Subgroup.closure (Set.range g32p_row07_groupGenerators) :=
  Classical.choose g32p_row07_groupEnumeration

theorem g32p_row07_groupEquiv_map (i : Fin 1944) :
    b4b_toMatrix (g32p_row07_groupEquiv i : g32p_G) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row07_groupNodes i)) :=
  Classical.choose_spec g32p_row07_groupEnumeration i

theorem g32p_row07_groupEquiv_one : g32p_row07_groupEquiv 0 = 1 := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row07_groupEquiv 0 : g32p_G) = b4b_toMatrix 1
  rw [g32p_row07_groupEquiv_map, map_one,
    show g32p_row07_groupNodes 0 = HurwitzPrymRex_mone by decide,
    HurwitzPrymRex_evM_mone, map_one]

theorem g32p_row07_groupEquiv_step (i : Fin 1944) (s : Fin 4) :
    g32p_row07_groupEquiv (g32p_row07_groupNext i s) =
      g32p_row07_groupEquiv i *
        ⟨g32p_row07_groupGenerators s, Subgroup.subset_closure (Set.mem_range_self s)⟩ := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row07_groupEquiv (g32p_row07_groupNext i s) : g32p_G) =
    b4b_toMatrix ((g32p_row07_groupEquiv i : g32p_G) * g32p_row07_groupGenerators s)
  rw [map_mul, g32p_row07_groupEquiv_map, g32p_row07_groupEquiv_map,
    g32p_row07_groupGenerator_map, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  exact congrArg (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
    (g32p_row07_groupStep i s).symm


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row07_characterTransition : ∀ i : Fin 1944, ∀ s : Fin 4,
    g32p_row07_characterValues (g32p_row07_groupNext i s) =
      g32p_row07_characterValues i * g32p_row07_characterValues (g32p_row07_groupNext 0 s) := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row07_characterBlock_000
  · exact g32p_row07_characterBlock_001
  · exact g32p_row07_characterBlock_002
  · exact g32p_row07_characterBlock_003
  · exact g32p_row07_characterBlock_004
  · exact g32p_row07_characterBlock_005
  · exact g32p_row07_characterBlock_006
  · exact g32p_row07_characterBlock_007
  · exact g32p_row07_characterBlock_008
  · exact g32p_row07_characterBlock_009
  · exact g32p_row07_characterBlock_010
  · exact g32p_row07_characterBlock_011
  · exact g32p_row07_characterBlock_012
  · exact g32p_row07_characterBlock_013
  · exact g32p_row07_characterBlock_014
  · exact g32p_row07_characterBlock_015
  · exact g32p_row07_characterBlock_016
  · exact g32p_row07_characterBlock_017
  · exact g32p_row07_characterBlock_018
  · exact g32p_row07_characterBlock_019
  · exact g32p_row07_characterBlock_020
  · exact g32p_row07_characterBlock_021
  · exact g32p_row07_characterBlock_022
  · exact g32p_row07_characterBlock_023
  · exact g32p_row07_characterBlock_024
  · exact g32p_row07_characterBlock_025
  · exact g32p_row07_characterBlock_026
  · exact g32p_row07_characterBlock_027
  · exact g32p_row07_characterBlock_028
  · exact g32p_row07_characterBlock_029
  · exact g32p_row07_characterBlock_030
  · exact g32p_row07_characterBlock_031
  · exact g32p_row07_characterBlock_032
  · exact g32p_row07_characterBlock_033
  · exact g32p_row07_characterBlock_034
  · exact g32p_row07_characterBlock_035
  · exact g32p_row07_characterBlock_036
  · exact g32p_row07_characterBlock_037
  · exact g32p_row07_characterBlock_038
  · exact g32p_row07_characterBlock_039
  · exact g32p_row07_characterBlock_040
  · exact g32p_row07_characterBlock_041
  · exact g32p_row07_characterBlock_042
  · exact g32p_row07_characterBlock_043
  · exact g32p_row07_characterBlock_044
  · exact g32p_row07_characterBlock_045
  · exact g32p_row07_characterBlock_046
  · exact g32p_row07_characterBlock_047
  · exact g32p_row07_characterBlock_048
  · exact g32p_row07_characterBlock_049
  · exact g32p_row07_characterBlock_050
  · exact g32p_row07_characterBlock_051
  · exact g32p_row07_characterBlock_052
  · exact g32p_row07_characterBlock_053
  · exact g32p_row07_characterBlock_054
  · exact g32p_row07_characterBlock_055
  · exact g32p_row07_characterBlock_056
  · exact g32p_row07_characterBlock_057
  · exact g32p_row07_characterBlock_058
  · exact g32p_row07_characterBlock_059
  · exact g32p_row07_characterBlock_060
  · exact g32p_row07_characterBlock_061
  · exact g32p_row07_characterBlock_062
  · exact g32p_row07_characterBlock_063
  · exact g32p_row07_characterBlock_064
  · exact g32p_row07_characterBlock_065
  · exact g32p_row07_characterBlock_066
  · exact g32p_row07_characterBlock_067
  · exact g32p_row07_characterBlock_068
  · exact g32p_row07_characterBlock_069
  · exact g32p_row07_characterBlock_070
  · exact g32p_row07_characterBlock_071
  · exact g32p_row07_characterBlock_072
  · exact g32p_row07_characterBlock_073
  · exact g32p_row07_characterBlock_074
  · exact g32p_row07_characterBlock_075
  · exact g32p_row07_characterBlock_076
  · exact g32p_row07_characterBlock_077
  · exact g32p_row07_characterBlock_078
  · exact g32p_row07_characterBlock_079
  · exact g32p_row07_characterBlock_080
  · exact g32p_row07_characterBlock_081
  · exact g32p_row07_characterBlock_082
  · exact g32p_row07_characterBlock_083
  · exact g32p_row07_characterBlock_084
  · exact g32p_row07_characterBlock_085
  · exact g32p_row07_characterBlock_086
  · exact g32p_row07_characterBlock_087
  · exact g32p_row07_characterBlock_088
  · exact g32p_row07_characterBlock_089
  · exact g32p_row07_characterBlock_090
  · exact g32p_row07_characterBlock_091
  · exact g32p_row07_characterBlock_092
  · exact g32p_row07_characterBlock_093
  · exact g32p_row07_characterBlock_094
  · exact g32p_row07_characterBlock_095
  · exact g32p_row07_characterBlock_096
  · exact g32p_row07_characterBlock_097
  · exact g32p_row07_characterBlock_098
  · exact g32p_row07_characterBlock_099
  · exact g32p_row07_characterBlock_100
  · exact g32p_row07_characterBlock_101
  · exact g32p_row07_characterBlock_102
  · exact g32p_row07_characterBlock_103
  · exact g32p_row07_characterBlock_104
  · exact g32p_row07_characterBlock_105
  · exact g32p_row07_characterBlock_106
  · exact g32p_row07_characterBlock_107
  · exact g32p_row07_characterBlock_108
  · exact g32p_row07_characterBlock_109
  · exact g32p_row07_characterBlock_110
  · exact g32p_row07_characterBlock_111
  · exact g32p_row07_characterBlock_112
  · exact g32p_row07_characterBlock_113
  · exact g32p_row07_characterBlock_114
  · exact g32p_row07_characterBlock_115
  · exact g32p_row07_characterBlock_116
  · exact g32p_row07_characterBlock_117
  · exact g32p_row07_characterBlock_118
  · exact g32p_row07_characterBlock_119
  · exact g32p_row07_characterBlock_120
  · exact g32p_row07_characterBlock_121

theorem g32p_row07_characterSurjective : Function.Surjective g32p_row07_characterValues := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end
