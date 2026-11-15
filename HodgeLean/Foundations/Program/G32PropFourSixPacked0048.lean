import HodgeLean.Foundations.Program.G32PropFourSixPacked0045
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow04Decode
import HodgeLean.Foundations.Program.G32PropFourSixPacked0047
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCheck
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_groupEnumeration :
    ∃ e : Fin 1728 ≃ Subgroup.closure (Set.range g32p_row04_groupGenerators),
      ∀ i, b4b_toMatrix (e i : g32p_G) =
        HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
          (g32p_row04_groupNodes i)) := by
  apply g32p_matrixPathEnumeration b4b_toMatrix Subtype.val_injective
    (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
    (by rw [HurwitzPrymRex_evM_mone, map_one])
    (by intro a b; rw [HurwitzPrymRex_evM_mmul g32h_omega_sq_add, map_mul])
    (HurwitzPrymRex_g32conj_injective.comp
      (HurwitzPrymRex_evM_injective g32h_omega_sq_add))
    g32p_row04_groupGenerators g32p_row04_groupMatrices g32p_row04_groupGenerator_map
    g32p_row04_groupNodes 0 g32p_row04_groupParent g32p_row04_groupLabel Fin.val
    g32p_row04_groupNext g32p_row04_groupInjective (by decide)
    g32p_row04_groupParent_lt
  · intro i hi
    have hs := g32p_row04_groupStep
      (g32p_row04_groupParent i) (g32p_row04_groupLabel i)
    rw [g32p_row04_groupParent_step i hi] at hs
    exact hs.symm
  · exact g32p_row04_groupStep

theorem g32p_row04_groupOrder :
    Nat.card (Subgroup.closure (Set.range g32p_row04_groupGenerators)) = 1728 := by
  obtain ⟨e, _⟩ := g32p_row04_groupEnumeration
  simpa only [Nat.card_fin] using (Nat.card_congr e).symm

def g32p_row04_groupEquiv : Fin 1728 ≃ Subgroup.closure (Set.range g32p_row04_groupGenerators) :=
  Classical.choose g32p_row04_groupEnumeration

theorem g32p_row04_groupEquiv_map (i : Fin 1728) :
    b4b_toMatrix (g32p_row04_groupEquiv i : g32p_G) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row04_groupNodes i)) :=
  Classical.choose_spec g32p_row04_groupEnumeration i

theorem g32p_row04_groupEquiv_one : g32p_row04_groupEquiv 0 = 1 := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row04_groupEquiv 0 : g32p_G) = b4b_toMatrix 1
  rw [g32p_row04_groupEquiv_map, map_one,
    show g32p_row04_groupNodes 0 = HurwitzPrymRex_mone by decide,
    HurwitzPrymRex_evM_mone, map_one]

theorem g32p_row04_groupEquiv_step (i : Fin 1728) (s : Fin 3) :
    g32p_row04_groupEquiv (g32p_row04_groupNext i s) =
      g32p_row04_groupEquiv i *
        ⟨g32p_row04_groupGenerators s, Subgroup.subset_closure (Set.mem_range_self s)⟩ := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row04_groupEquiv (g32p_row04_groupNext i s) : g32p_G) =
    b4b_toMatrix ((g32p_row04_groupEquiv i : g32p_G) * g32p_row04_groupGenerators s)
  rw [map_mul, g32p_row04_groupEquiv_map, g32p_row04_groupEquiv_map,
    g32p_row04_groupGenerator_map, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  exact congrArg (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
    (g32p_row04_groupStep i s).symm


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_characterTransition : ∀ i : Fin 1728, ∀ s : Fin 3,
    g32p_row04_characterValues (g32p_row04_groupNext i s) =
      g32p_row04_characterValues i * g32p_row04_characterValues (g32p_row04_groupNext 0 s) := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row04_characterBlock_000
  · exact g32p_row04_characterBlock_001
  · exact g32p_row04_characterBlock_002
  · exact g32p_row04_characterBlock_003
  · exact g32p_row04_characterBlock_004
  · exact g32p_row04_characterBlock_005
  · exact g32p_row04_characterBlock_006
  · exact g32p_row04_characterBlock_007
  · exact g32p_row04_characterBlock_008
  · exact g32p_row04_characterBlock_009
  · exact g32p_row04_characterBlock_010
  · exact g32p_row04_characterBlock_011
  · exact g32p_row04_characterBlock_012
  · exact g32p_row04_characterBlock_013
  · exact g32p_row04_characterBlock_014
  · exact g32p_row04_characterBlock_015
  · exact g32p_row04_characterBlock_016
  · exact g32p_row04_characterBlock_017
  · exact g32p_row04_characterBlock_018
  · exact g32p_row04_characterBlock_019
  · exact g32p_row04_characterBlock_020
  · exact g32p_row04_characterBlock_021
  · exact g32p_row04_characterBlock_022
  · exact g32p_row04_characterBlock_023
  · exact g32p_row04_characterBlock_024
  · exact g32p_row04_characterBlock_025
  · exact g32p_row04_characterBlock_026
  · exact g32p_row04_characterBlock_027
  · exact g32p_row04_characterBlock_028
  · exact g32p_row04_characterBlock_029
  · exact g32p_row04_characterBlock_030
  · exact g32p_row04_characterBlock_031
  · exact g32p_row04_characterBlock_032
  · exact g32p_row04_characterBlock_033
  · exact g32p_row04_characterBlock_034
  · exact g32p_row04_characterBlock_035
  · exact g32p_row04_characterBlock_036
  · exact g32p_row04_characterBlock_037
  · exact g32p_row04_characterBlock_038
  · exact g32p_row04_characterBlock_039
  · exact g32p_row04_characterBlock_040
  · exact g32p_row04_characterBlock_041
  · exact g32p_row04_characterBlock_042
  · exact g32p_row04_characterBlock_043
  · exact g32p_row04_characterBlock_044
  · exact g32p_row04_characterBlock_045
  · exact g32p_row04_characterBlock_046
  · exact g32p_row04_characterBlock_047
  · exact g32p_row04_characterBlock_048
  · exact g32p_row04_characterBlock_049
  · exact g32p_row04_characterBlock_050
  · exact g32p_row04_characterBlock_051
  · exact g32p_row04_characterBlock_052
  · exact g32p_row04_characterBlock_053
  · exact g32p_row04_characterBlock_054
  · exact g32p_row04_characterBlock_055
  · exact g32p_row04_characterBlock_056
  · exact g32p_row04_characterBlock_057
  · exact g32p_row04_characterBlock_058
  · exact g32p_row04_characterBlock_059
  · exact g32p_row04_characterBlock_060
  · exact g32p_row04_characterBlock_061
  · exact g32p_row04_characterBlock_062
  · exact g32p_row04_characterBlock_063
  · exact g32p_row04_characterBlock_064
  · exact g32p_row04_characterBlock_065
  · exact g32p_row04_characterBlock_066
  · exact g32p_row04_characterBlock_067
  · exact g32p_row04_characterBlock_068
  · exact g32p_row04_characterBlock_069
  · exact g32p_row04_characterBlock_070
  · exact g32p_row04_characterBlock_071
  · exact g32p_row04_characterBlock_072
  · exact g32p_row04_characterBlock_073
  · exact g32p_row04_characterBlock_074
  · exact g32p_row04_characterBlock_075
  · exact g32p_row04_characterBlock_076
  · exact g32p_row04_characterBlock_077
  · exact g32p_row04_characterBlock_078
  · exact g32p_row04_characterBlock_079
  · exact g32p_row04_characterBlock_080
  · exact g32p_row04_characterBlock_081
  · exact g32p_row04_characterBlock_082
  · exact g32p_row04_characterBlock_083
  · exact g32p_row04_characterBlock_084
  · exact g32p_row04_characterBlock_085
  · exact g32p_row04_characterBlock_086
  · exact g32p_row04_characterBlock_087
  · exact g32p_row04_characterBlock_088
  · exact g32p_row04_characterBlock_089
  · exact g32p_row04_characterBlock_090
  · exact g32p_row04_characterBlock_091
  · exact g32p_row04_characterBlock_092
  · exact g32p_row04_characterBlock_093
  · exact g32p_row04_characterBlock_094
  · exact g32p_row04_characterBlock_095
  · exact g32p_row04_characterBlock_096
  · exact g32p_row04_characterBlock_097
  · exact g32p_row04_characterBlock_098
  · exact g32p_row04_characterBlock_099
  · exact g32p_row04_characterBlock_100
  · exact g32p_row04_characterBlock_101
  · exact g32p_row04_characterBlock_102
  · exact g32p_row04_characterBlock_103
  · exact g32p_row04_characterBlock_104
  · exact g32p_row04_characterBlock_105
  · exact g32p_row04_characterBlock_106
  · exact g32p_row04_characterBlock_107

theorem g32p_row04_characterSurjective : Function.Surjective g32p_row04_characterValues := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end
