import HodgeLean.Foundations.Program.G32PropFourSixPacked0634
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness05CosetData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0647
import HodgeLean.Foundations.Program.G32PropFourSixPacked0648
import HodgeLean.Foundations.Program.G32PropFourSixCharacters

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row05_cosetBranchMatrix0 : g32p_row05_cosetBranchMatrices 0 = g32p_cosetIntegralBranches 0 := by
  decide +kernel

theorem g32p_row05_cosetPartition0 : (g32p_row05_cosetCycles0).flatten.Perm (List.range 320) := by
  decide +kernel

theorem g32p_row05_cosetRootLabels0 : ∀ j : Fin 128, g32p_row05_cosetLabels0 (g32p_row05_cosetRoots0 j) = j := by
  decide +kernel

theorem g32p_row05_cosetNextLabels0 : ∀ i : Fin 320, g32p_row05_cosetLabels0 (g32p_row05_cosetBranchNext 0 i) = g32p_row05_cosetLabels0 i := by
  decide +kernel

theorem g32p_row05_cosetReach0 : ∀ i : Fin 320, (g32p_row05_cosetBranchNext 0)^[g32p_row05_cosetDistances0 i] (g32p_row05_cosetRoots0 (g32p_row05_cosetLabels0 i)) = i := by
  decide +kernel

theorem g32p_row05_cosetPeriods0 : ∀ j : Fin 128, 0 < g32p_row05_cosetLengths0 j ∧ (g32p_row05_cosetBranchNext 0)^[g32p_row05_cosetLengths0 j] (g32p_row05_cosetRoots0 j) = g32p_row05_cosetRoots0 j ∧ ∀ t : Fin (g32p_row05_cosetLengths0 j), 0 < t.val → (g32p_row05_cosetBranchNext 0)^[t.val] (g32p_row05_cosetRoots0 j) ≠ g32p_row05_cosetRoots0 j := by
  decide +kernel

theorem g32p_row05_cosetCycleSteps0 : ∀ cycle ∈ g32p_row05_cosetCycles0,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row05_cosetBranchNext 0 ⟨i % 320, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

theorem g32p_row05_cosetInverse0 : ∀ i : Fin 320,
    ((g32p_row05_cosetBranchNext 0)^[2]) (g32p_row05_cosetBranchNext 0 i) = i ∧
    g32p_row05_cosetBranchNext 0 (((g32p_row05_cosetBranchNext 0)^[2]) i) = i := by
  decide +kernel

theorem g32p_row05_cosetPermutation0 : Function.Bijective (g32p_row05_cosetBranchNext 0) := by
  have hl : Function.LeftInverse ((g32p_row05_cosetBranchNext 0)^[2]) (g32p_row05_cosetBranchNext 0) :=
    fun i => (g32p_row05_cosetInverse0 i).1
  have hr : Function.RightInverse ((g32p_row05_cosetBranchNext 0)^[2]) (g32p_row05_cosetBranchNext 0) :=
    fun i => (g32p_row05_cosetInverse0 i).2
  exact ⟨hl.injective, hr.surjective⟩


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row05_cosetBranchMatrix1 : g32p_row05_cosetBranchMatrices 1 = g32p_cosetIntegralBranches 1 := by
  decide +kernel

theorem g32p_row05_cosetPartition1 : (g32p_row05_cosetCycles1).flatten.Perm (List.range 320) := by
  decide +kernel

theorem g32p_row05_cosetRootLabels1 : ∀ j : Fin 128, g32p_row05_cosetLabels1 (g32p_row05_cosetRoots1 j) = j := by
  decide +kernel

theorem g32p_row05_cosetNextLabels1 : ∀ i : Fin 320, g32p_row05_cosetLabels1 (g32p_row05_cosetBranchNext 1 i) = g32p_row05_cosetLabels1 i := by
  decide +kernel

theorem g32p_row05_cosetReach1 : ∀ i : Fin 320, (g32p_row05_cosetBranchNext 1)^[g32p_row05_cosetDistances1 i] (g32p_row05_cosetRoots1 (g32p_row05_cosetLabels1 i)) = i := by
  decide +kernel

theorem g32p_row05_cosetPeriods1 : ∀ j : Fin 128, 0 < g32p_row05_cosetLengths1 j ∧ (g32p_row05_cosetBranchNext 1)^[g32p_row05_cosetLengths1 j] (g32p_row05_cosetRoots1 j) = g32p_row05_cosetRoots1 j ∧ ∀ t : Fin (g32p_row05_cosetLengths1 j), 0 < t.val → (g32p_row05_cosetBranchNext 1)^[t.val] (g32p_row05_cosetRoots1 j) ≠ g32p_row05_cosetRoots1 j := by
  decide +kernel

theorem g32p_row05_cosetCycleSteps1 : ∀ cycle ∈ g32p_row05_cosetCycles1,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row05_cosetBranchNext 1 ⟨i % 320, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

theorem g32p_row05_cosetInverse1 : ∀ i : Fin 320,
    ((g32p_row05_cosetBranchNext 1)^[2]) (g32p_row05_cosetBranchNext 1 i) = i ∧
    g32p_row05_cosetBranchNext 1 (((g32p_row05_cosetBranchNext 1)^[2]) i) = i := by
  decide +kernel

theorem g32p_row05_cosetPermutation1 : Function.Bijective (g32p_row05_cosetBranchNext 1) := by
  have hl : Function.LeftInverse ((g32p_row05_cosetBranchNext 1)^[2]) (g32p_row05_cosetBranchNext 1) :=
    fun i => (g32p_row05_cosetInverse1 i).1
  have hr : Function.RightInverse ((g32p_row05_cosetBranchNext 1)^[2]) (g32p_row05_cosetBranchNext 1) :=
    fun i => (g32p_row05_cosetInverse1 i).2
  exact ⟨hl.injective, hr.surjective⟩


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row05_cosetBranchMatrix2 : g32p_row05_cosetBranchMatrices 2 = g32p_cosetIntegralBranches 2 := by
  decide +kernel

theorem g32p_row05_cosetPartition2 : (g32p_row05_cosetCycles2).flatten.Perm (List.range 320) := by
  decide +kernel

theorem g32p_row05_cosetRootLabels2 : ∀ j : Fin 176, g32p_row05_cosetLabels2 (g32p_row05_cosetRoots2 j) = j := by
  decide +kernel

theorem g32p_row05_cosetNextLabels2 : ∀ i : Fin 320, g32p_row05_cosetLabels2 (g32p_row05_cosetBranchNext 2 i) = g32p_row05_cosetLabels2 i := by
  decide +kernel

theorem g32p_row05_cosetReach2 : ∀ i : Fin 320, (g32p_row05_cosetBranchNext 2)^[g32p_row05_cosetDistances2 i] (g32p_row05_cosetRoots2 (g32p_row05_cosetLabels2 i)) = i := by
  decide +kernel

theorem g32p_row05_cosetPeriods2 : ∀ j : Fin 176, 0 < g32p_row05_cosetLengths2 j ∧ (g32p_row05_cosetBranchNext 2)^[g32p_row05_cosetLengths2 j] (g32p_row05_cosetRoots2 j) = g32p_row05_cosetRoots2 j ∧ ∀ t : Fin (g32p_row05_cosetLengths2 j), 0 < t.val → (g32p_row05_cosetBranchNext 2)^[t.val] (g32p_row05_cosetRoots2 j) ≠ g32p_row05_cosetRoots2 j := by
  decide +kernel

theorem g32p_row05_cosetCycleSteps2 : ∀ cycle ∈ g32p_row05_cosetCycles2,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row05_cosetBranchNext 2 ⟨i % 320, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

theorem g32p_row05_cosetInverse2 : ∀ i : Fin 320,
    ((g32p_row05_cosetBranchNext 2)^[1]) (g32p_row05_cosetBranchNext 2 i) = i ∧
    g32p_row05_cosetBranchNext 2 (((g32p_row05_cosetBranchNext 2)^[1]) i) = i := by
  decide +kernel

theorem g32p_row05_cosetPermutation2 : Function.Bijective (g32p_row05_cosetBranchNext 2) := by
  have hl : Function.LeftInverse ((g32p_row05_cosetBranchNext 2)^[1]) (g32p_row05_cosetBranchNext 2) :=
    fun i => (g32p_row05_cosetInverse2 i).1
  have hr : Function.RightInverse ((g32p_row05_cosetBranchNext 2)^[1]) (g32p_row05_cosetBranchNext 2) :=
    fun i => (g32p_row05_cosetInverse2 i).2
  exact ⟨hl.injective, hr.surjective⟩


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row05_cosetEquiv : Fin 320 ≃ (g32p_G ⧸ g32p_row05_finiteSupplier.H) :=
  Equiv.ofBijective _ g32p_row05_cosetEnumeration

theorem g32p_row05_cosetBranchMap (b : Fin 3) :
    b4b_toMatrix (g32p_cosetBranches b) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row05_cosetBranchMatrices b)) := by
  have he : g32p_row05_cosetBranchMatrices b = g32p_cosetIntegralBranches b := by
    fin_cases b
    · exact g32p_row05_cosetBranchMatrix0
    · exact g32p_row05_cosetBranchMatrix1
    · exact g32p_row05_cosetBranchMatrix2
  rw [he]
  exact g32p_cosetBranches_map b

theorem g32p_row05_cosetBranchCheck (b : Fin 3) (i : Fin 320) :
    HurwitzPrymRex_mmul (g32p_row05_cosetBranchMatrices b) (g32p_row05_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row05_cosetRepresentatives (g32p_row05_cosetBranchNext b i))
        (g32p_row05_groupNodes (g32p_row05_cosetBranchFactor b i)) := by
  fin_cases i
  · exact g32p_row05_cosetBranchStep_0000 b
  · exact g32p_row05_cosetBranchStep_0001 b
  · exact g32p_row05_cosetBranchStep_0002 b
  · exact g32p_row05_cosetBranchStep_0003 b
  · exact g32p_row05_cosetBranchStep_0004 b
  · exact g32p_row05_cosetBranchStep_0005 b
  · exact g32p_row05_cosetBranchStep_0006 b
  · exact g32p_row05_cosetBranchStep_0007 b
  · exact g32p_row05_cosetBranchStep_0008 b
  · exact g32p_row05_cosetBranchStep_0009 b
  · exact g32p_row05_cosetBranchStep_0010 b
  · exact g32p_row05_cosetBranchStep_0011 b
  · exact g32p_row05_cosetBranchStep_0012 b
  · exact g32p_row05_cosetBranchStep_0013 b
  · exact g32p_row05_cosetBranchStep_0014 b
  · exact g32p_row05_cosetBranchStep_0015 b
  · exact g32p_row05_cosetBranchStep_0016 b
  · exact g32p_row05_cosetBranchStep_0017 b
  · exact g32p_row05_cosetBranchStep_0018 b
  · exact g32p_row05_cosetBranchStep_0019 b
  · exact g32p_row05_cosetBranchStep_0020 b
  · exact g32p_row05_cosetBranchStep_0021 b
  · exact g32p_row05_cosetBranchStep_0022 b
  · exact g32p_row05_cosetBranchStep_0023 b
  · exact g32p_row05_cosetBranchStep_0024 b
  · exact g32p_row05_cosetBranchStep_0025 b
  · exact g32p_row05_cosetBranchStep_0026 b
  · exact g32p_row05_cosetBranchStep_0027 b
  · exact g32p_row05_cosetBranchStep_0028 b
  · exact g32p_row05_cosetBranchStep_0029 b
  · exact g32p_row05_cosetBranchStep_0030 b
  · exact g32p_row05_cosetBranchStep_0031 b
  · exact g32p_row05_cosetBranchStep_0032 b
  · exact g32p_row05_cosetBranchStep_0033 b
  · exact g32p_row05_cosetBranchStep_0034 b
  · exact g32p_row05_cosetBranchStep_0035 b
  · exact g32p_row05_cosetBranchStep_0036 b
  · exact g32p_row05_cosetBranchStep_0037 b
  · exact g32p_row05_cosetBranchStep_0038 b
  · exact g32p_row05_cosetBranchStep_0039 b
  · exact g32p_row05_cosetBranchStep_0040 b
  · exact g32p_row05_cosetBranchStep_0041 b
  · exact g32p_row05_cosetBranchStep_0042 b
  · exact g32p_row05_cosetBranchStep_0043 b
  · exact g32p_row05_cosetBranchStep_0044 b
  · exact g32p_row05_cosetBranchStep_0045 b
  · exact g32p_row05_cosetBranchStep_0046 b
  · exact g32p_row05_cosetBranchStep_0047 b
  · exact g32p_row05_cosetBranchStep_0048 b
  · exact g32p_row05_cosetBranchStep_0049 b
  · exact g32p_row05_cosetBranchStep_0050 b
  · exact g32p_row05_cosetBranchStep_0051 b
  · exact g32p_row05_cosetBranchStep_0052 b
  · exact g32p_row05_cosetBranchStep_0053 b
  · exact g32p_row05_cosetBranchStep_0054 b
  · exact g32p_row05_cosetBranchStep_0055 b
  · exact g32p_row05_cosetBranchStep_0056 b
  · exact g32p_row05_cosetBranchStep_0057 b
  · exact g32p_row05_cosetBranchStep_0058 b
  · exact g32p_row05_cosetBranchStep_0059 b
  · exact g32p_row05_cosetBranchStep_0060 b
  · exact g32p_row05_cosetBranchStep_0061 b
  · exact g32p_row05_cosetBranchStep_0062 b
  · exact g32p_row05_cosetBranchStep_0063 b
  · exact g32p_row05_cosetBranchStep_0064 b
  · exact g32p_row05_cosetBranchStep_0065 b
  · exact g32p_row05_cosetBranchStep_0066 b
  · exact g32p_row05_cosetBranchStep_0067 b
  · exact g32p_row05_cosetBranchStep_0068 b
  · exact g32p_row05_cosetBranchStep_0069 b
  · exact g32p_row05_cosetBranchStep_0070 b
  · exact g32p_row05_cosetBranchStep_0071 b
  · exact g32p_row05_cosetBranchStep_0072 b
  · exact g32p_row05_cosetBranchStep_0073 b
  · exact g32p_row05_cosetBranchStep_0074 b
  · exact g32p_row05_cosetBranchStep_0075 b
  · exact g32p_row05_cosetBranchStep_0076 b
  · exact g32p_row05_cosetBranchStep_0077 b
  · exact g32p_row05_cosetBranchStep_0078 b
  · exact g32p_row05_cosetBranchStep_0079 b
  · exact g32p_row05_cosetBranchStep_0080 b
  · exact g32p_row05_cosetBranchStep_0081 b
  · exact g32p_row05_cosetBranchStep_0082 b
  · exact g32p_row05_cosetBranchStep_0083 b
  · exact g32p_row05_cosetBranchStep_0084 b
  · exact g32p_row05_cosetBranchStep_0085 b
  · exact g32p_row05_cosetBranchStep_0086 b
  · exact g32p_row05_cosetBranchStep_0087 b
  · exact g32p_row05_cosetBranchStep_0088 b
  · exact g32p_row05_cosetBranchStep_0089 b
  · exact g32p_row05_cosetBranchStep_0090 b
  · exact g32p_row05_cosetBranchStep_0091 b
  · exact g32p_row05_cosetBranchStep_0092 b
  · exact g32p_row05_cosetBranchStep_0093 b
  · exact g32p_row05_cosetBranchStep_0094 b
  · exact g32p_row05_cosetBranchStep_0095 b
  · exact g32p_row05_cosetBranchStep_0096 b
  · exact g32p_row05_cosetBranchStep_0097 b
  · exact g32p_row05_cosetBranchStep_0098 b
  · exact g32p_row05_cosetBranchStep_0099 b
  · exact g32p_row05_cosetBranchStep_0100 b
  · exact g32p_row05_cosetBranchStep_0101 b
  · exact g32p_row05_cosetBranchStep_0102 b
  · exact g32p_row05_cosetBranchStep_0103 b
  · exact g32p_row05_cosetBranchStep_0104 b
  · exact g32p_row05_cosetBranchStep_0105 b
  · exact g32p_row05_cosetBranchStep_0106 b
  · exact g32p_row05_cosetBranchStep_0107 b
  · exact g32p_row05_cosetBranchStep_0108 b
  · exact g32p_row05_cosetBranchStep_0109 b
  · exact g32p_row05_cosetBranchStep_0110 b
  · exact g32p_row05_cosetBranchStep_0111 b
  · exact g32p_row05_cosetBranchStep_0112 b
  · exact g32p_row05_cosetBranchStep_0113 b
  · exact g32p_row05_cosetBranchStep_0114 b
  · exact g32p_row05_cosetBranchStep_0115 b
  · exact g32p_row05_cosetBranchStep_0116 b
  · exact g32p_row05_cosetBranchStep_0117 b
  · exact g32p_row05_cosetBranchStep_0118 b
  · exact g32p_row05_cosetBranchStep_0119 b
  · exact g32p_row05_cosetBranchStep_0120 b
  · exact g32p_row05_cosetBranchStep_0121 b
  · exact g32p_row05_cosetBranchStep_0122 b
  · exact g32p_row05_cosetBranchStep_0123 b
  · exact g32p_row05_cosetBranchStep_0124 b
  · exact g32p_row05_cosetBranchStep_0125 b
  · exact g32p_row05_cosetBranchStep_0126 b
  · exact g32p_row05_cosetBranchStep_0127 b
  · exact g32p_row05_cosetBranchStep_0128 b
  · exact g32p_row05_cosetBranchStep_0129 b
  · exact g32p_row05_cosetBranchStep_0130 b
  · exact g32p_row05_cosetBranchStep_0131 b
  · exact g32p_row05_cosetBranchStep_0132 b
  · exact g32p_row05_cosetBranchStep_0133 b
  · exact g32p_row05_cosetBranchStep_0134 b
  · exact g32p_row05_cosetBranchStep_0135 b
  · exact g32p_row05_cosetBranchStep_0136 b
  · exact g32p_row05_cosetBranchStep_0137 b
  · exact g32p_row05_cosetBranchStep_0138 b
  · exact g32p_row05_cosetBranchStep_0139 b
  · exact g32p_row05_cosetBranchStep_0140 b
  · exact g32p_row05_cosetBranchStep_0141 b
  · exact g32p_row05_cosetBranchStep_0142 b
  · exact g32p_row05_cosetBranchStep_0143 b
  · exact g32p_row05_cosetBranchStep_0144 b
  · exact g32p_row05_cosetBranchStep_0145 b
  · exact g32p_row05_cosetBranchStep_0146 b
  · exact g32p_row05_cosetBranchStep_0147 b
  · exact g32p_row05_cosetBranchStep_0148 b
  · exact g32p_row05_cosetBranchStep_0149 b
  · exact g32p_row05_cosetBranchStep_0150 b
  · exact g32p_row05_cosetBranchStep_0151 b
  · exact g32p_row05_cosetBranchStep_0152 b
  · exact g32p_row05_cosetBranchStep_0153 b
  · exact g32p_row05_cosetBranchStep_0154 b
  · exact g32p_row05_cosetBranchStep_0155 b
  · exact g32p_row05_cosetBranchStep_0156 b
  · exact g32p_row05_cosetBranchStep_0157 b
  · exact g32p_row05_cosetBranchStep_0158 b
  · exact g32p_row05_cosetBranchStep_0159 b
  · exact g32p_row05_cosetBranchStep_0160 b
  · exact g32p_row05_cosetBranchStep_0161 b
  · exact g32p_row05_cosetBranchStep_0162 b
  · exact g32p_row05_cosetBranchStep_0163 b
  · exact g32p_row05_cosetBranchStep_0164 b
  · exact g32p_row05_cosetBranchStep_0165 b
  · exact g32p_row05_cosetBranchStep_0166 b
  · exact g32p_row05_cosetBranchStep_0167 b
  · exact g32p_row05_cosetBranchStep_0168 b
  · exact g32p_row05_cosetBranchStep_0169 b
  · exact g32p_row05_cosetBranchStep_0170 b
  · exact g32p_row05_cosetBranchStep_0171 b
  · exact g32p_row05_cosetBranchStep_0172 b
  · exact g32p_row05_cosetBranchStep_0173 b
  · exact g32p_row05_cosetBranchStep_0174 b
  · exact g32p_row05_cosetBranchStep_0175 b
  · exact g32p_row05_cosetBranchStep_0176 b
  · exact g32p_row05_cosetBranchStep_0177 b
  · exact g32p_row05_cosetBranchStep_0178 b
  · exact g32p_row05_cosetBranchStep_0179 b
  · exact g32p_row05_cosetBranchStep_0180 b
  · exact g32p_row05_cosetBranchStep_0181 b
  · exact g32p_row05_cosetBranchStep_0182 b
  · exact g32p_row05_cosetBranchStep_0183 b
  · exact g32p_row05_cosetBranchStep_0184 b
  · exact g32p_row05_cosetBranchStep_0185 b
  · exact g32p_row05_cosetBranchStep_0186 b
  · exact g32p_row05_cosetBranchStep_0187 b
  · exact g32p_row05_cosetBranchStep_0188 b
  · exact g32p_row05_cosetBranchStep_0189 b
  · exact g32p_row05_cosetBranchStep_0190 b
  · exact g32p_row05_cosetBranchStep_0191 b
  · exact g32p_row05_cosetBranchStep_0192 b
  · exact g32p_row05_cosetBranchStep_0193 b
  · exact g32p_row05_cosetBranchStep_0194 b
  · exact g32p_row05_cosetBranchStep_0195 b
  · exact g32p_row05_cosetBranchStep_0196 b
  · exact g32p_row05_cosetBranchStep_0197 b
  · exact g32p_row05_cosetBranchStep_0198 b
  · exact g32p_row05_cosetBranchStep_0199 b
  · exact g32p_row05_cosetBranchStep_0200 b
  · exact g32p_row05_cosetBranchStep_0201 b
  · exact g32p_row05_cosetBranchStep_0202 b
  · exact g32p_row05_cosetBranchStep_0203 b
  · exact g32p_row05_cosetBranchStep_0204 b
  · exact g32p_row05_cosetBranchStep_0205 b
  · exact g32p_row05_cosetBranchStep_0206 b
  · exact g32p_row05_cosetBranchStep_0207 b
  · exact g32p_row05_cosetBranchStep_0208 b
  · exact g32p_row05_cosetBranchStep_0209 b
  · exact g32p_row05_cosetBranchStep_0210 b
  · exact g32p_row05_cosetBranchStep_0211 b
  · exact g32p_row05_cosetBranchStep_0212 b
  · exact g32p_row05_cosetBranchStep_0213 b
  · exact g32p_row05_cosetBranchStep_0214 b
  · exact g32p_row05_cosetBranchStep_0215 b
  · exact g32p_row05_cosetBranchStep_0216 b
  · exact g32p_row05_cosetBranchStep_0217 b
  · exact g32p_row05_cosetBranchStep_0218 b
  · exact g32p_row05_cosetBranchStep_0219 b
  · exact g32p_row05_cosetBranchStep_0220 b
  · exact g32p_row05_cosetBranchStep_0221 b
  · exact g32p_row05_cosetBranchStep_0222 b
  · exact g32p_row05_cosetBranchStep_0223 b
  · exact g32p_row05_cosetBranchStep_0224 b
  · exact g32p_row05_cosetBranchStep_0225 b
  · exact g32p_row05_cosetBranchStep_0226 b
  · exact g32p_row05_cosetBranchStep_0227 b
  · exact g32p_row05_cosetBranchStep_0228 b
  · exact g32p_row05_cosetBranchStep_0229 b
  · exact g32p_row05_cosetBranchStep_0230 b
  · exact g32p_row05_cosetBranchStep_0231 b
  · exact g32p_row05_cosetBranchStep_0232 b
  · exact g32p_row05_cosetBranchStep_0233 b
  · exact g32p_row05_cosetBranchStep_0234 b
  · exact g32p_row05_cosetBranchStep_0235 b
  · exact g32p_row05_cosetBranchStep_0236 b
  · exact g32p_row05_cosetBranchStep_0237 b
  · exact g32p_row05_cosetBranchStep_0238 b
  · exact g32p_row05_cosetBranchStep_0239 b
  · exact g32p_row05_cosetBranchStep_0240 b
  · exact g32p_row05_cosetBranchStep_0241 b
  · exact g32p_row05_cosetBranchStep_0242 b
  · exact g32p_row05_cosetBranchStep_0243 b
  · exact g32p_row05_cosetBranchStep_0244 b
  · exact g32p_row05_cosetBranchStep_0245 b
  · exact g32p_row05_cosetBranchStep_0246 b
  · exact g32p_row05_cosetBranchStep_0247 b
  · exact g32p_row05_cosetBranchStep_0248 b
  · exact g32p_row05_cosetBranchStep_0249 b
  · exact g32p_row05_cosetBranchStep_0250 b
  · exact g32p_row05_cosetBranchStep_0251 b
  · exact g32p_row05_cosetBranchStep_0252 b
  · exact g32p_row05_cosetBranchStep_0253 b
  · exact g32p_row05_cosetBranchStep_0254 b
  · exact g32p_row05_cosetBranchStep_0255 b
  · exact g32p_row05_cosetBranchStep_0256 b
  · exact g32p_row05_cosetBranchStep_0257 b
  · exact g32p_row05_cosetBranchStep_0258 b
  · exact g32p_row05_cosetBranchStep_0259 b
  · exact g32p_row05_cosetBranchStep_0260 b
  · exact g32p_row05_cosetBranchStep_0261 b
  · exact g32p_row05_cosetBranchStep_0262 b
  · exact g32p_row05_cosetBranchStep_0263 b
  · exact g32p_row05_cosetBranchStep_0264 b
  · exact g32p_row05_cosetBranchStep_0265 b
  · exact g32p_row05_cosetBranchStep_0266 b
  · exact g32p_row05_cosetBranchStep_0267 b
  · exact g32p_row05_cosetBranchStep_0268 b
  · exact g32p_row05_cosetBranchStep_0269 b
  · exact g32p_row05_cosetBranchStep_0270 b
  · exact g32p_row05_cosetBranchStep_0271 b
  · exact g32p_row05_cosetBranchStep_0272 b
  · exact g32p_row05_cosetBranchStep_0273 b
  · exact g32p_row05_cosetBranchStep_0274 b
  · exact g32p_row05_cosetBranchStep_0275 b
  · exact g32p_row05_cosetBranchStep_0276 b
  · exact g32p_row05_cosetBranchStep_0277 b
  · exact g32p_row05_cosetBranchStep_0278 b
  · exact g32p_row05_cosetBranchStep_0279 b
  · exact g32p_row05_cosetBranchStep_0280 b
  · exact g32p_row05_cosetBranchStep_0281 b
  · exact g32p_row05_cosetBranchStep_0282 b
  · exact g32p_row05_cosetBranchStep_0283 b
  · exact g32p_row05_cosetBranchStep_0284 b
  · exact g32p_row05_cosetBranchStep_0285 b
  · exact g32p_row05_cosetBranchStep_0286 b
  · exact g32p_row05_cosetBranchStep_0287 b
  · exact g32p_row05_cosetBranchStep_0288 b
  · exact g32p_row05_cosetBranchStep_0289 b
  · exact g32p_row05_cosetBranchStep_0290 b
  · exact g32p_row05_cosetBranchStep_0291 b
  · exact g32p_row05_cosetBranchStep_0292 b
  · exact g32p_row05_cosetBranchStep_0293 b
  · exact g32p_row05_cosetBranchStep_0294 b
  · exact g32p_row05_cosetBranchStep_0295 b
  · exact g32p_row05_cosetBranchStep_0296 b
  · exact g32p_row05_cosetBranchStep_0297 b
  · exact g32p_row05_cosetBranchStep_0298 b
  · exact g32p_row05_cosetBranchStep_0299 b
  · exact g32p_row05_cosetBranchStep_0300 b
  · exact g32p_row05_cosetBranchStep_0301 b
  · exact g32p_row05_cosetBranchStep_0302 b
  · exact g32p_row05_cosetBranchStep_0303 b
  · exact g32p_row05_cosetBranchStep_0304 b
  · exact g32p_row05_cosetBranchStep_0305 b
  · exact g32p_row05_cosetBranchStep_0306 b
  · exact g32p_row05_cosetBranchStep_0307 b
  · exact g32p_row05_cosetBranchStep_0308 b
  · exact g32p_row05_cosetBranchStep_0309 b
  · exact g32p_row05_cosetBranchStep_0310 b
  · exact g32p_row05_cosetBranchStep_0311 b
  · exact g32p_row05_cosetBranchStep_0312 b
  · exact g32p_row05_cosetBranchStep_0313 b
  · exact g32p_row05_cosetBranchStep_0314 b
  · exact g32p_row05_cosetBranchStep_0315 b
  · exact g32p_row05_cosetBranchStep_0316 b
  · exact g32p_row05_cosetBranchStep_0317 b
  · exact g32p_row05_cosetBranchStep_0318 b
  · exact g32p_row05_cosetBranchStep_0319 b

theorem g32p_row05_cosetActualBranchStep (b : Fin 3) (i : Fin 320) :
    g32p_cosetBranches b * g32p_row05_cosetActualRepresentatives i =
      g32p_row05_cosetActualRepresentatives (g32p_row05_cosetBranchNext b i) *
        (g32p_row05_groupEquiv (g32p_row05_cosetBranchFactor b i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_cosetBranches b * g32p_row05_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row05_cosetActualRepresentatives (g32p_row05_cosetBranchNext b i) *
      (g32p_row05_groupEquiv (g32p_row05_cosetBranchFactor b i) : g32p_G))
  rw [map_mul, map_mul, g32p_row05_cosetBranchMap, g32p_row05_cosetActualRepresentatives_map,
    g32p_row05_cosetActualRepresentatives_map, g32p_row05_groupEquiv_map,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add, g32p_row05_cosetBranchCheck]

theorem g32p_row05_cosetQuotientStep (b : Fin 3) (i : Fin 320) :
    g32p_row05_cosetEquiv (g32p_row05_cosetBranchNext b i) = g32p_cosetBranches b • g32p_row05_cosetEquiv i := by
  change (QuotientGroup.mk (g32p_row05_cosetActualRepresentatives (g32p_row05_cosetBranchNext b i)) : g32p_G ⧸ g32p_row05_finiteSupplier.H) =
    g32p_cosetBranches b • (QuotientGroup.mk (g32p_row05_cosetActualRepresentatives i) : g32p_G ⧸ g32p_row05_finiteSupplier.H)
  rw [MulAction.Quotient.smul_coe, smul_eq_mul]
  apply QuotientGroup.eq.mpr
  rw [g32p_row05_cosetActualBranchStep, ← mul_assoc, inv_mul_cancel, one_mul]
  exact (g32p_row05_groupEquiv (g32p_row05_cosetBranchFactor b i)).property

def g32p_row05_cosetOrbitEquiv0 : Fin 128 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 0)) (g32p_G ⧸ g32p_row05_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 0) g32p_row05_cosetEquiv
    (g32p_row05_cosetBranchNext 0) (g32p_row05_cosetQuotientStep 0) g32p_row05_cosetLabels0 g32p_row05_cosetRoots0
    g32p_row05_cosetDistances0 g32p_row05_cosetRootLabels0 g32p_row05_cosetNextLabels0 g32p_row05_cosetReach0)

theorem g32p_row05_cosetPeriod0 (j : Fin 128) :
    Function.minimalPeriod ((g32p_cosetBranches 0) • ·) (g32p_row05_cosetEquiv (g32p_row05_cosetRoots0 j)) = g32p_row05_cosetLengths0 j := by
  apply g32p_period_of_cycle g32p_row05_cosetEquiv (g32p_row05_cosetBranchNext 0) ((g32p_cosetBranches 0) • ·)
    (g32p_row05_cosetQuotientStep 0) _ _ (g32p_row05_cosetPeriods0 j).1 (g32p_row05_cosetPeriods0 j).2.1
  intro t ht hlt
  exact (g32p_row05_cosetPeriods0 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row05_cosetActualMonodromy0 (j : Fin 128) :
    (g32p_cosetBranches 0) ^ g32p_row05_cosetLengths0 j * g32p_row05_cosetActualRepresentatives (g32p_row05_cosetRoots0 j) =
      g32p_row05_cosetActualRepresentatives (g32p_row05_cosetRoots0 j) *
        (g32p_row05_groupEquiv (g32p_row05_cosetMonodromies0 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row05_cosetBranchMatrices 0)
    (g32p_row05_cosetRepresentatives (g32p_row05_cosetRoots0 j))
    (g32p_row05_groupNodes (g32p_row05_cosetMonodromies0 j))
    (g32p_row05_cosetLengths0 j) (g32p_row05_cosetBranchMap 0)
    (g32p_row05_cosetActualRepresentatives_map _) (g32p_row05_groupEquiv_map _)
  fin_cases j
  · exact g32p_row05_cosetMonodromy_0_0000.1
  · exact g32p_row05_cosetMonodromy_0_0001.1
  · exact g32p_row05_cosetMonodromy_0_0002.1
  · exact g32p_row05_cosetMonodromy_0_0003.1
  · exact g32p_row05_cosetMonodromy_0_0004.1
  · exact g32p_row05_cosetMonodromy_0_0005.1
  · exact g32p_row05_cosetMonodromy_0_0006.1
  · exact g32p_row05_cosetMonodromy_0_0007.1
  · exact g32p_row05_cosetMonodromy_0_0008.1
  · exact g32p_row05_cosetMonodromy_0_0009.1
  · exact g32p_row05_cosetMonodromy_0_0010.1
  · exact g32p_row05_cosetMonodromy_0_0011.1
  · exact g32p_row05_cosetMonodromy_0_0012.1
  · exact g32p_row05_cosetMonodromy_0_0013.1
  · exact g32p_row05_cosetMonodromy_0_0014.1
  · exact g32p_row05_cosetMonodromy_0_0015.1
  · exact g32p_row05_cosetMonodromy_0_0016.1
  · exact g32p_row05_cosetMonodromy_0_0017.1
  · exact g32p_row05_cosetMonodromy_0_0018.1
  · exact g32p_row05_cosetMonodromy_0_0019.1
  · exact g32p_row05_cosetMonodromy_0_0020.1
  · exact g32p_row05_cosetMonodromy_0_0021.1
  · exact g32p_row05_cosetMonodromy_0_0022.1
  · exact g32p_row05_cosetMonodromy_0_0023.1
  · exact g32p_row05_cosetMonodromy_0_0024.1
  · exact g32p_row05_cosetMonodromy_0_0025.1
  · exact g32p_row05_cosetMonodromy_0_0026.1
  · exact g32p_row05_cosetMonodromy_0_0027.1
  · exact g32p_row05_cosetMonodromy_0_0028.1
  · exact g32p_row05_cosetMonodromy_0_0029.1
  · exact g32p_row05_cosetMonodromy_0_0030.1
  · exact g32p_row05_cosetMonodromy_0_0031.1
  · exact g32p_row05_cosetMonodromy_0_0032.1
  · exact g32p_row05_cosetMonodromy_0_0033.1
  · exact g32p_row05_cosetMonodromy_0_0034.1
  · exact g32p_row05_cosetMonodromy_0_0035.1
  · exact g32p_row05_cosetMonodromy_0_0036.1
  · exact g32p_row05_cosetMonodromy_0_0037.1
  · exact g32p_row05_cosetMonodromy_0_0038.1
  · exact g32p_row05_cosetMonodromy_0_0039.1
  · exact g32p_row05_cosetMonodromy_0_0040.1
  · exact g32p_row05_cosetMonodromy_0_0041.1
  · exact g32p_row05_cosetMonodromy_0_0042.1
  · exact g32p_row05_cosetMonodromy_0_0043.1
  · exact g32p_row05_cosetMonodromy_0_0044.1
  · exact g32p_row05_cosetMonodromy_0_0045.1
  · exact g32p_row05_cosetMonodromy_0_0046.1
  · exact g32p_row05_cosetMonodromy_0_0047.1
  · exact g32p_row05_cosetMonodromy_0_0048.1
  · exact g32p_row05_cosetMonodromy_0_0049.1
  · exact g32p_row05_cosetMonodromy_0_0050.1
  · exact g32p_row05_cosetMonodromy_0_0051.1
  · exact g32p_row05_cosetMonodromy_0_0052.1
  · exact g32p_row05_cosetMonodromy_0_0053.1
  · exact g32p_row05_cosetMonodromy_0_0054.1
  · exact g32p_row05_cosetMonodromy_0_0055.1
  · exact g32p_row05_cosetMonodromy_0_0056.1
  · exact g32p_row05_cosetMonodromy_0_0057.1
  · exact g32p_row05_cosetMonodromy_0_0058.1
  · exact g32p_row05_cosetMonodromy_0_0059.1
  · exact g32p_row05_cosetMonodromy_0_0060.1
  · exact g32p_row05_cosetMonodromy_0_0061.1
  · exact g32p_row05_cosetMonodromy_0_0062.1
  · exact g32p_row05_cosetMonodromy_0_0063.1
  · exact g32p_row05_cosetMonodromy_0_0064.1
  · exact g32p_row05_cosetMonodromy_0_0065.1
  · exact g32p_row05_cosetMonodromy_0_0066.1
  · exact g32p_row05_cosetMonodromy_0_0067.1
  · exact g32p_row05_cosetMonodromy_0_0068.1
  · exact g32p_row05_cosetMonodromy_0_0069.1
  · exact g32p_row05_cosetMonodromy_0_0070.1
  · exact g32p_row05_cosetMonodromy_0_0071.1
  · exact g32p_row05_cosetMonodromy_0_0072.1
  · exact g32p_row05_cosetMonodromy_0_0073.1
  · exact g32p_row05_cosetMonodromy_0_0074.1
  · exact g32p_row05_cosetMonodromy_0_0075.1
  · exact g32p_row05_cosetMonodromy_0_0076.1
  · exact g32p_row05_cosetMonodromy_0_0077.1
  · exact g32p_row05_cosetMonodromy_0_0078.1
  · exact g32p_row05_cosetMonodromy_0_0079.1
  · exact g32p_row05_cosetMonodromy_0_0080.1
  · exact g32p_row05_cosetMonodromy_0_0081.1
  · exact g32p_row05_cosetMonodromy_0_0082.1
  · exact g32p_row05_cosetMonodromy_0_0083.1
  · exact g32p_row05_cosetMonodromy_0_0084.1
  · exact g32p_row05_cosetMonodromy_0_0085.1
  · exact g32p_row05_cosetMonodromy_0_0086.1
  · exact g32p_row05_cosetMonodromy_0_0087.1
  · exact g32p_row05_cosetMonodromy_0_0088.1
  · exact g32p_row05_cosetMonodromy_0_0089.1
  · exact g32p_row05_cosetMonodromy_0_0090.1
  · exact g32p_row05_cosetMonodromy_0_0091.1
  · exact g32p_row05_cosetMonodromy_0_0092.1
  · exact g32p_row05_cosetMonodromy_0_0093.1
  · exact g32p_row05_cosetMonodromy_0_0094.1
  · exact g32p_row05_cosetMonodromy_0_0095.1
  · exact g32p_row05_cosetMonodromy_0_0096.1
  · exact g32p_row05_cosetMonodromy_0_0097.1
  · exact g32p_row05_cosetMonodromy_0_0098.1
  · exact g32p_row05_cosetMonodromy_0_0099.1
  · exact g32p_row05_cosetMonodromy_0_0100.1
  · exact g32p_row05_cosetMonodromy_0_0101.1
  · exact g32p_row05_cosetMonodromy_0_0102.1
  · exact g32p_row05_cosetMonodromy_0_0103.1
  · exact g32p_row05_cosetMonodromy_0_0104.1
  · exact g32p_row05_cosetMonodromy_0_0105.1
  · exact g32p_row05_cosetMonodromy_0_0106.1
  · exact g32p_row05_cosetMonodromy_0_0107.1
  · exact g32p_row05_cosetMonodromy_0_0108.1
  · exact g32p_row05_cosetMonodromy_0_0109.1
  · exact g32p_row05_cosetMonodromy_0_0110.1
  · exact g32p_row05_cosetMonodromy_0_0111.1
  · exact g32p_row05_cosetMonodromy_0_0112.1
  · exact g32p_row05_cosetMonodromy_0_0113.1
  · exact g32p_row05_cosetMonodromy_0_0114.1
  · exact g32p_row05_cosetMonodromy_0_0115.1
  · exact g32p_row05_cosetMonodromy_0_0116.1
  · exact g32p_row05_cosetMonodromy_0_0117.1
  · exact g32p_row05_cosetMonodromy_0_0118.1
  · exact g32p_row05_cosetMonodromy_0_0119.1
  · exact g32p_row05_cosetMonodromy_0_0120.1
  · exact g32p_row05_cosetMonodromy_0_0121.1
  · exact g32p_row05_cosetMonodromy_0_0122.1
  · exact g32p_row05_cosetMonodromy_0_0123.1
  · exact g32p_row05_cosetMonodromy_0_0124.1
  · exact g32p_row05_cosetMonodromy_0_0125.1
  · exact g32p_row05_cosetMonodromy_0_0126.1
  · exact g32p_row05_cosetMonodromy_0_0127.1

theorem g32p_row05_cosetCharacter0 (j : Fin 128) :
    g32p_row05_finiteSupplier.χ (g32p_row05_groupEquiv (g32p_row05_cosetMonodromies0 j)) = g32p_row05_cosetExponents0 j := by
  rw [g32p_row05_finiteSupplier_value]
  fin_cases j
  · exact g32p_row05_cosetMonodromy_0_0000.2
  · exact g32p_row05_cosetMonodromy_0_0001.2
  · exact g32p_row05_cosetMonodromy_0_0002.2
  · exact g32p_row05_cosetMonodromy_0_0003.2
  · exact g32p_row05_cosetMonodromy_0_0004.2
  · exact g32p_row05_cosetMonodromy_0_0005.2
  · exact g32p_row05_cosetMonodromy_0_0006.2
  · exact g32p_row05_cosetMonodromy_0_0007.2
  · exact g32p_row05_cosetMonodromy_0_0008.2
  · exact g32p_row05_cosetMonodromy_0_0009.2
  · exact g32p_row05_cosetMonodromy_0_0010.2
  · exact g32p_row05_cosetMonodromy_0_0011.2
  · exact g32p_row05_cosetMonodromy_0_0012.2
  · exact g32p_row05_cosetMonodromy_0_0013.2
  · exact g32p_row05_cosetMonodromy_0_0014.2
  · exact g32p_row05_cosetMonodromy_0_0015.2
  · exact g32p_row05_cosetMonodromy_0_0016.2
  · exact g32p_row05_cosetMonodromy_0_0017.2
  · exact g32p_row05_cosetMonodromy_0_0018.2
  · exact g32p_row05_cosetMonodromy_0_0019.2
  · exact g32p_row05_cosetMonodromy_0_0020.2
  · exact g32p_row05_cosetMonodromy_0_0021.2
  · exact g32p_row05_cosetMonodromy_0_0022.2
  · exact g32p_row05_cosetMonodromy_0_0023.2
  · exact g32p_row05_cosetMonodromy_0_0024.2
  · exact g32p_row05_cosetMonodromy_0_0025.2
  · exact g32p_row05_cosetMonodromy_0_0026.2
  · exact g32p_row05_cosetMonodromy_0_0027.2
  · exact g32p_row05_cosetMonodromy_0_0028.2
  · exact g32p_row05_cosetMonodromy_0_0029.2
  · exact g32p_row05_cosetMonodromy_0_0030.2
  · exact g32p_row05_cosetMonodromy_0_0031.2
  · exact g32p_row05_cosetMonodromy_0_0032.2
  · exact g32p_row05_cosetMonodromy_0_0033.2
  · exact g32p_row05_cosetMonodromy_0_0034.2
  · exact g32p_row05_cosetMonodromy_0_0035.2
  · exact g32p_row05_cosetMonodromy_0_0036.2
  · exact g32p_row05_cosetMonodromy_0_0037.2
  · exact g32p_row05_cosetMonodromy_0_0038.2
  · exact g32p_row05_cosetMonodromy_0_0039.2
  · exact g32p_row05_cosetMonodromy_0_0040.2
  · exact g32p_row05_cosetMonodromy_0_0041.2
  · exact g32p_row05_cosetMonodromy_0_0042.2
  · exact g32p_row05_cosetMonodromy_0_0043.2
  · exact g32p_row05_cosetMonodromy_0_0044.2
  · exact g32p_row05_cosetMonodromy_0_0045.2
  · exact g32p_row05_cosetMonodromy_0_0046.2
  · exact g32p_row05_cosetMonodromy_0_0047.2
  · exact g32p_row05_cosetMonodromy_0_0048.2
  · exact g32p_row05_cosetMonodromy_0_0049.2
  · exact g32p_row05_cosetMonodromy_0_0050.2
  · exact g32p_row05_cosetMonodromy_0_0051.2
  · exact g32p_row05_cosetMonodromy_0_0052.2
  · exact g32p_row05_cosetMonodromy_0_0053.2
  · exact g32p_row05_cosetMonodromy_0_0054.2
  · exact g32p_row05_cosetMonodromy_0_0055.2
  · exact g32p_row05_cosetMonodromy_0_0056.2
  · exact g32p_row05_cosetMonodromy_0_0057.2
  · exact g32p_row05_cosetMonodromy_0_0058.2
  · exact g32p_row05_cosetMonodromy_0_0059.2
  · exact g32p_row05_cosetMonodromy_0_0060.2
  · exact g32p_row05_cosetMonodromy_0_0061.2
  · exact g32p_row05_cosetMonodromy_0_0062.2
  · exact g32p_row05_cosetMonodromy_0_0063.2
  · exact g32p_row05_cosetMonodromy_0_0064.2
  · exact g32p_row05_cosetMonodromy_0_0065.2
  · exact g32p_row05_cosetMonodromy_0_0066.2
  · exact g32p_row05_cosetMonodromy_0_0067.2
  · exact g32p_row05_cosetMonodromy_0_0068.2
  · exact g32p_row05_cosetMonodromy_0_0069.2
  · exact g32p_row05_cosetMonodromy_0_0070.2
  · exact g32p_row05_cosetMonodromy_0_0071.2
  · exact g32p_row05_cosetMonodromy_0_0072.2
  · exact g32p_row05_cosetMonodromy_0_0073.2
  · exact g32p_row05_cosetMonodromy_0_0074.2
  · exact g32p_row05_cosetMonodromy_0_0075.2
  · exact g32p_row05_cosetMonodromy_0_0076.2
  · exact g32p_row05_cosetMonodromy_0_0077.2
  · exact g32p_row05_cosetMonodromy_0_0078.2
  · exact g32p_row05_cosetMonodromy_0_0079.2
  · exact g32p_row05_cosetMonodromy_0_0080.2
  · exact g32p_row05_cosetMonodromy_0_0081.2
  · exact g32p_row05_cosetMonodromy_0_0082.2
  · exact g32p_row05_cosetMonodromy_0_0083.2
  · exact g32p_row05_cosetMonodromy_0_0084.2
  · exact g32p_row05_cosetMonodromy_0_0085.2
  · exact g32p_row05_cosetMonodromy_0_0086.2
  · exact g32p_row05_cosetMonodromy_0_0087.2
  · exact g32p_row05_cosetMonodromy_0_0088.2
  · exact g32p_row05_cosetMonodromy_0_0089.2
  · exact g32p_row05_cosetMonodromy_0_0090.2
  · exact g32p_row05_cosetMonodromy_0_0091.2
  · exact g32p_row05_cosetMonodromy_0_0092.2
  · exact g32p_row05_cosetMonodromy_0_0093.2
  · exact g32p_row05_cosetMonodromy_0_0094.2
  · exact g32p_row05_cosetMonodromy_0_0095.2
  · exact g32p_row05_cosetMonodromy_0_0096.2
  · exact g32p_row05_cosetMonodromy_0_0097.2
  · exact g32p_row05_cosetMonodromy_0_0098.2
  · exact g32p_row05_cosetMonodromy_0_0099.2
  · exact g32p_row05_cosetMonodromy_0_0100.2
  · exact g32p_row05_cosetMonodromy_0_0101.2
  · exact g32p_row05_cosetMonodromy_0_0102.2
  · exact g32p_row05_cosetMonodromy_0_0103.2
  · exact g32p_row05_cosetMonodromy_0_0104.2
  · exact g32p_row05_cosetMonodromy_0_0105.2
  · exact g32p_row05_cosetMonodromy_0_0106.2
  · exact g32p_row05_cosetMonodromy_0_0107.2
  · exact g32p_row05_cosetMonodromy_0_0108.2
  · exact g32p_row05_cosetMonodromy_0_0109.2
  · exact g32p_row05_cosetMonodromy_0_0110.2
  · exact g32p_row05_cosetMonodromy_0_0111.2
  · exact g32p_row05_cosetMonodromy_0_0112.2
  · exact g32p_row05_cosetMonodromy_0_0113.2
  · exact g32p_row05_cosetMonodromy_0_0114.2
  · exact g32p_row05_cosetMonodromy_0_0115.2
  · exact g32p_row05_cosetMonodromy_0_0116.2
  · exact g32p_row05_cosetMonodromy_0_0117.2
  · exact g32p_row05_cosetMonodromy_0_0118.2
  · exact g32p_row05_cosetMonodromy_0_0119.2
  · exact g32p_row05_cosetMonodromy_0_0120.2
  · exact g32p_row05_cosetMonodromy_0_0121.2
  · exact g32p_row05_cosetMonodromy_0_0122.2
  · exact g32p_row05_cosetMonodromy_0_0123.2
  · exact g32p_row05_cosetMonodromy_0_0124.2
  · exact g32p_row05_cosetMonodromy_0_0125.2
  · exact g32p_row05_cosetMonodromy_0_0126.2
  · exact g32p_row05_cosetMonodromy_0_0127.2

theorem g32p_row05_cosetBranchExponents0 :
    papersExps g32p_row05_finiteSupplier.H g32p_row05_finiteSupplier.χ (g32p_cosetBranches 0) =
      (Finset.univ.val.map (fun j : Fin 128 => Multiplicative.toAdd (g32p_row05_cosetExponents0 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row05_cosetOrbitEquiv0
    (fun j => g32p_row05_cosetActualRepresentatives (g32p_row05_cosetRoots0 j)) (fun _ => rfl) g32p_row05_cosetLengths0 g32p_row05_cosetPeriod0
    (fun j => g32p_row05_groupEquiv (g32p_row05_cosetMonodromies0 j)) g32p_row05_cosetActualMonodromy0]
  simp only [g32p_row05_cosetCharacter0]
  rfl

def g32p_row05_cosetOrbitEquiv1 : Fin 128 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 1)) (g32p_G ⧸ g32p_row05_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 1) g32p_row05_cosetEquiv
    (g32p_row05_cosetBranchNext 1) (g32p_row05_cosetQuotientStep 1) g32p_row05_cosetLabels1 g32p_row05_cosetRoots1
    g32p_row05_cosetDistances1 g32p_row05_cosetRootLabels1 g32p_row05_cosetNextLabels1 g32p_row05_cosetReach1)

theorem g32p_row05_cosetPeriod1 (j : Fin 128) :
    Function.minimalPeriod ((g32p_cosetBranches 1) • ·) (g32p_row05_cosetEquiv (g32p_row05_cosetRoots1 j)) = g32p_row05_cosetLengths1 j := by
  apply g32p_period_of_cycle g32p_row05_cosetEquiv (g32p_row05_cosetBranchNext 1) ((g32p_cosetBranches 1) • ·)
    (g32p_row05_cosetQuotientStep 1) _ _ (g32p_row05_cosetPeriods1 j).1 (g32p_row05_cosetPeriods1 j).2.1
  intro t ht hlt
  exact (g32p_row05_cosetPeriods1 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row05_cosetActualMonodromy1 (j : Fin 128) :
    (g32p_cosetBranches 1) ^ g32p_row05_cosetLengths1 j * g32p_row05_cosetActualRepresentatives (g32p_row05_cosetRoots1 j) =
      g32p_row05_cosetActualRepresentatives (g32p_row05_cosetRoots1 j) *
        (g32p_row05_groupEquiv (g32p_row05_cosetMonodromies1 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row05_cosetBranchMatrices 1)
    (g32p_row05_cosetRepresentatives (g32p_row05_cosetRoots1 j))
    (g32p_row05_groupNodes (g32p_row05_cosetMonodromies1 j))
    (g32p_row05_cosetLengths1 j) (g32p_row05_cosetBranchMap 1)
    (g32p_row05_cosetActualRepresentatives_map _) (g32p_row05_groupEquiv_map _)
  fin_cases j
  · exact g32p_row05_cosetMonodromy_1_0000.1
  · exact g32p_row05_cosetMonodromy_1_0001.1
  · exact g32p_row05_cosetMonodromy_1_0002.1
  · exact g32p_row05_cosetMonodromy_1_0003.1
  · exact g32p_row05_cosetMonodromy_1_0004.1
  · exact g32p_row05_cosetMonodromy_1_0005.1
  · exact g32p_row05_cosetMonodromy_1_0006.1
  · exact g32p_row05_cosetMonodromy_1_0007.1
  · exact g32p_row05_cosetMonodromy_1_0008.1
  · exact g32p_row05_cosetMonodromy_1_0009.1
  · exact g32p_row05_cosetMonodromy_1_0010.1
  · exact g32p_row05_cosetMonodromy_1_0011.1
  · exact g32p_row05_cosetMonodromy_1_0012.1
  · exact g32p_row05_cosetMonodromy_1_0013.1
  · exact g32p_row05_cosetMonodromy_1_0014.1
  · exact g32p_row05_cosetMonodromy_1_0015.1
  · exact g32p_row05_cosetMonodromy_1_0016.1
  · exact g32p_row05_cosetMonodromy_1_0017.1
  · exact g32p_row05_cosetMonodromy_1_0018.1
  · exact g32p_row05_cosetMonodromy_1_0019.1
  · exact g32p_row05_cosetMonodromy_1_0020.1
  · exact g32p_row05_cosetMonodromy_1_0021.1
  · exact g32p_row05_cosetMonodromy_1_0022.1
  · exact g32p_row05_cosetMonodromy_1_0023.1
  · exact g32p_row05_cosetMonodromy_1_0024.1
  · exact g32p_row05_cosetMonodromy_1_0025.1
  · exact g32p_row05_cosetMonodromy_1_0026.1
  · exact g32p_row05_cosetMonodromy_1_0027.1
  · exact g32p_row05_cosetMonodromy_1_0028.1
  · exact g32p_row05_cosetMonodromy_1_0029.1
  · exact g32p_row05_cosetMonodromy_1_0030.1
  · exact g32p_row05_cosetMonodromy_1_0031.1
  · exact g32p_row05_cosetMonodromy_1_0032.1
  · exact g32p_row05_cosetMonodromy_1_0033.1
  · exact g32p_row05_cosetMonodromy_1_0034.1
  · exact g32p_row05_cosetMonodromy_1_0035.1
  · exact g32p_row05_cosetMonodromy_1_0036.1
  · exact g32p_row05_cosetMonodromy_1_0037.1
  · exact g32p_row05_cosetMonodromy_1_0038.1
  · exact g32p_row05_cosetMonodromy_1_0039.1
  · exact g32p_row05_cosetMonodromy_1_0040.1
  · exact g32p_row05_cosetMonodromy_1_0041.1
  · exact g32p_row05_cosetMonodromy_1_0042.1
  · exact g32p_row05_cosetMonodromy_1_0043.1
  · exact g32p_row05_cosetMonodromy_1_0044.1
  · exact g32p_row05_cosetMonodromy_1_0045.1
  · exact g32p_row05_cosetMonodromy_1_0046.1
  · exact g32p_row05_cosetMonodromy_1_0047.1
  · exact g32p_row05_cosetMonodromy_1_0048.1
  · exact g32p_row05_cosetMonodromy_1_0049.1
  · exact g32p_row05_cosetMonodromy_1_0050.1
  · exact g32p_row05_cosetMonodromy_1_0051.1
  · exact g32p_row05_cosetMonodromy_1_0052.1
  · exact g32p_row05_cosetMonodromy_1_0053.1
  · exact g32p_row05_cosetMonodromy_1_0054.1
  · exact g32p_row05_cosetMonodromy_1_0055.1
  · exact g32p_row05_cosetMonodromy_1_0056.1
  · exact g32p_row05_cosetMonodromy_1_0057.1
  · exact g32p_row05_cosetMonodromy_1_0058.1
  · exact g32p_row05_cosetMonodromy_1_0059.1
  · exact g32p_row05_cosetMonodromy_1_0060.1
  · exact g32p_row05_cosetMonodromy_1_0061.1
  · exact g32p_row05_cosetMonodromy_1_0062.1
  · exact g32p_row05_cosetMonodromy_1_0063.1
  · exact g32p_row05_cosetMonodromy_1_0064.1
  · exact g32p_row05_cosetMonodromy_1_0065.1
  · exact g32p_row05_cosetMonodromy_1_0066.1
  · exact g32p_row05_cosetMonodromy_1_0067.1
  · exact g32p_row05_cosetMonodromy_1_0068.1
  · exact g32p_row05_cosetMonodromy_1_0069.1
  · exact g32p_row05_cosetMonodromy_1_0070.1
  · exact g32p_row05_cosetMonodromy_1_0071.1
  · exact g32p_row05_cosetMonodromy_1_0072.1
  · exact g32p_row05_cosetMonodromy_1_0073.1
  · exact g32p_row05_cosetMonodromy_1_0074.1
  · exact g32p_row05_cosetMonodromy_1_0075.1
  · exact g32p_row05_cosetMonodromy_1_0076.1
  · exact g32p_row05_cosetMonodromy_1_0077.1
  · exact g32p_row05_cosetMonodromy_1_0078.1
  · exact g32p_row05_cosetMonodromy_1_0079.1
  · exact g32p_row05_cosetMonodromy_1_0080.1
  · exact g32p_row05_cosetMonodromy_1_0081.1
  · exact g32p_row05_cosetMonodromy_1_0082.1
  · exact g32p_row05_cosetMonodromy_1_0083.1
  · exact g32p_row05_cosetMonodromy_1_0084.1
  · exact g32p_row05_cosetMonodromy_1_0085.1
  · exact g32p_row05_cosetMonodromy_1_0086.1
  · exact g32p_row05_cosetMonodromy_1_0087.1
  · exact g32p_row05_cosetMonodromy_1_0088.1
  · exact g32p_row05_cosetMonodromy_1_0089.1
  · exact g32p_row05_cosetMonodromy_1_0090.1
  · exact g32p_row05_cosetMonodromy_1_0091.1
  · exact g32p_row05_cosetMonodromy_1_0092.1
  · exact g32p_row05_cosetMonodromy_1_0093.1
  · exact g32p_row05_cosetMonodromy_1_0094.1
  · exact g32p_row05_cosetMonodromy_1_0095.1
  · exact g32p_row05_cosetMonodromy_1_0096.1
  · exact g32p_row05_cosetMonodromy_1_0097.1
  · exact g32p_row05_cosetMonodromy_1_0098.1
  · exact g32p_row05_cosetMonodromy_1_0099.1
  · exact g32p_row05_cosetMonodromy_1_0100.1
  · exact g32p_row05_cosetMonodromy_1_0101.1
  · exact g32p_row05_cosetMonodromy_1_0102.1
  · exact g32p_row05_cosetMonodromy_1_0103.1
  · exact g32p_row05_cosetMonodromy_1_0104.1
  · exact g32p_row05_cosetMonodromy_1_0105.1
  · exact g32p_row05_cosetMonodromy_1_0106.1
  · exact g32p_row05_cosetMonodromy_1_0107.1
  · exact g32p_row05_cosetMonodromy_1_0108.1
  · exact g32p_row05_cosetMonodromy_1_0109.1
  · exact g32p_row05_cosetMonodromy_1_0110.1
  · exact g32p_row05_cosetMonodromy_1_0111.1
  · exact g32p_row05_cosetMonodromy_1_0112.1
  · exact g32p_row05_cosetMonodromy_1_0113.1
  · exact g32p_row05_cosetMonodromy_1_0114.1
  · exact g32p_row05_cosetMonodromy_1_0115.1
  · exact g32p_row05_cosetMonodromy_1_0116.1
  · exact g32p_row05_cosetMonodromy_1_0117.1
  · exact g32p_row05_cosetMonodromy_1_0118.1
  · exact g32p_row05_cosetMonodromy_1_0119.1
  · exact g32p_row05_cosetMonodromy_1_0120.1
  · exact g32p_row05_cosetMonodromy_1_0121.1
  · exact g32p_row05_cosetMonodromy_1_0122.1
  · exact g32p_row05_cosetMonodromy_1_0123.1
  · exact g32p_row05_cosetMonodromy_1_0124.1
  · exact g32p_row05_cosetMonodromy_1_0125.1
  · exact g32p_row05_cosetMonodromy_1_0126.1
  · exact g32p_row05_cosetMonodromy_1_0127.1

theorem g32p_row05_cosetCharacter1 (j : Fin 128) :
    g32p_row05_finiteSupplier.χ (g32p_row05_groupEquiv (g32p_row05_cosetMonodromies1 j)) = g32p_row05_cosetExponents1 j := by
  rw [g32p_row05_finiteSupplier_value]
  fin_cases j
  · exact g32p_row05_cosetMonodromy_1_0000.2
  · exact g32p_row05_cosetMonodromy_1_0001.2
  · exact g32p_row05_cosetMonodromy_1_0002.2
  · exact g32p_row05_cosetMonodromy_1_0003.2
  · exact g32p_row05_cosetMonodromy_1_0004.2
  · exact g32p_row05_cosetMonodromy_1_0005.2
  · exact g32p_row05_cosetMonodromy_1_0006.2
  · exact g32p_row05_cosetMonodromy_1_0007.2
  · exact g32p_row05_cosetMonodromy_1_0008.2
  · exact g32p_row05_cosetMonodromy_1_0009.2
  · exact g32p_row05_cosetMonodromy_1_0010.2
  · exact g32p_row05_cosetMonodromy_1_0011.2
  · exact g32p_row05_cosetMonodromy_1_0012.2
  · exact g32p_row05_cosetMonodromy_1_0013.2
  · exact g32p_row05_cosetMonodromy_1_0014.2
  · exact g32p_row05_cosetMonodromy_1_0015.2
  · exact g32p_row05_cosetMonodromy_1_0016.2
  · exact g32p_row05_cosetMonodromy_1_0017.2
  · exact g32p_row05_cosetMonodromy_1_0018.2
  · exact g32p_row05_cosetMonodromy_1_0019.2
  · exact g32p_row05_cosetMonodromy_1_0020.2
  · exact g32p_row05_cosetMonodromy_1_0021.2
  · exact g32p_row05_cosetMonodromy_1_0022.2
  · exact g32p_row05_cosetMonodromy_1_0023.2
  · exact g32p_row05_cosetMonodromy_1_0024.2
  · exact g32p_row05_cosetMonodromy_1_0025.2
  · exact g32p_row05_cosetMonodromy_1_0026.2
  · exact g32p_row05_cosetMonodromy_1_0027.2
  · exact g32p_row05_cosetMonodromy_1_0028.2
  · exact g32p_row05_cosetMonodromy_1_0029.2
  · exact g32p_row05_cosetMonodromy_1_0030.2
  · exact g32p_row05_cosetMonodromy_1_0031.2
  · exact g32p_row05_cosetMonodromy_1_0032.2
  · exact g32p_row05_cosetMonodromy_1_0033.2
  · exact g32p_row05_cosetMonodromy_1_0034.2
  · exact g32p_row05_cosetMonodromy_1_0035.2
  · exact g32p_row05_cosetMonodromy_1_0036.2
  · exact g32p_row05_cosetMonodromy_1_0037.2
  · exact g32p_row05_cosetMonodromy_1_0038.2
  · exact g32p_row05_cosetMonodromy_1_0039.2
  · exact g32p_row05_cosetMonodromy_1_0040.2
  · exact g32p_row05_cosetMonodromy_1_0041.2
  · exact g32p_row05_cosetMonodromy_1_0042.2
  · exact g32p_row05_cosetMonodromy_1_0043.2
  · exact g32p_row05_cosetMonodromy_1_0044.2
  · exact g32p_row05_cosetMonodromy_1_0045.2
  · exact g32p_row05_cosetMonodromy_1_0046.2
  · exact g32p_row05_cosetMonodromy_1_0047.2
  · exact g32p_row05_cosetMonodromy_1_0048.2
  · exact g32p_row05_cosetMonodromy_1_0049.2
  · exact g32p_row05_cosetMonodromy_1_0050.2
  · exact g32p_row05_cosetMonodromy_1_0051.2
  · exact g32p_row05_cosetMonodromy_1_0052.2
  · exact g32p_row05_cosetMonodromy_1_0053.2
  · exact g32p_row05_cosetMonodromy_1_0054.2
  · exact g32p_row05_cosetMonodromy_1_0055.2
  · exact g32p_row05_cosetMonodromy_1_0056.2
  · exact g32p_row05_cosetMonodromy_1_0057.2
  · exact g32p_row05_cosetMonodromy_1_0058.2
  · exact g32p_row05_cosetMonodromy_1_0059.2
  · exact g32p_row05_cosetMonodromy_1_0060.2
  · exact g32p_row05_cosetMonodromy_1_0061.2
  · exact g32p_row05_cosetMonodromy_1_0062.2
  · exact g32p_row05_cosetMonodromy_1_0063.2
  · exact g32p_row05_cosetMonodromy_1_0064.2
  · exact g32p_row05_cosetMonodromy_1_0065.2
  · exact g32p_row05_cosetMonodromy_1_0066.2
  · exact g32p_row05_cosetMonodromy_1_0067.2
  · exact g32p_row05_cosetMonodromy_1_0068.2
  · exact g32p_row05_cosetMonodromy_1_0069.2
  · exact g32p_row05_cosetMonodromy_1_0070.2
  · exact g32p_row05_cosetMonodromy_1_0071.2
  · exact g32p_row05_cosetMonodromy_1_0072.2
  · exact g32p_row05_cosetMonodromy_1_0073.2
  · exact g32p_row05_cosetMonodromy_1_0074.2
  · exact g32p_row05_cosetMonodromy_1_0075.2
  · exact g32p_row05_cosetMonodromy_1_0076.2
  · exact g32p_row05_cosetMonodromy_1_0077.2
  · exact g32p_row05_cosetMonodromy_1_0078.2
  · exact g32p_row05_cosetMonodromy_1_0079.2
  · exact g32p_row05_cosetMonodromy_1_0080.2
  · exact g32p_row05_cosetMonodromy_1_0081.2
  · exact g32p_row05_cosetMonodromy_1_0082.2
  · exact g32p_row05_cosetMonodromy_1_0083.2
  · exact g32p_row05_cosetMonodromy_1_0084.2
  · exact g32p_row05_cosetMonodromy_1_0085.2
  · exact g32p_row05_cosetMonodromy_1_0086.2
  · exact g32p_row05_cosetMonodromy_1_0087.2
  · exact g32p_row05_cosetMonodromy_1_0088.2
  · exact g32p_row05_cosetMonodromy_1_0089.2
  · exact g32p_row05_cosetMonodromy_1_0090.2
  · exact g32p_row05_cosetMonodromy_1_0091.2
  · exact g32p_row05_cosetMonodromy_1_0092.2
  · exact g32p_row05_cosetMonodromy_1_0093.2
  · exact g32p_row05_cosetMonodromy_1_0094.2
  · exact g32p_row05_cosetMonodromy_1_0095.2
  · exact g32p_row05_cosetMonodromy_1_0096.2
  · exact g32p_row05_cosetMonodromy_1_0097.2
  · exact g32p_row05_cosetMonodromy_1_0098.2
  · exact g32p_row05_cosetMonodromy_1_0099.2
  · exact g32p_row05_cosetMonodromy_1_0100.2
  · exact g32p_row05_cosetMonodromy_1_0101.2
  · exact g32p_row05_cosetMonodromy_1_0102.2
  · exact g32p_row05_cosetMonodromy_1_0103.2
  · exact g32p_row05_cosetMonodromy_1_0104.2
  · exact g32p_row05_cosetMonodromy_1_0105.2
  · exact g32p_row05_cosetMonodromy_1_0106.2
  · exact g32p_row05_cosetMonodromy_1_0107.2
  · exact g32p_row05_cosetMonodromy_1_0108.2
  · exact g32p_row05_cosetMonodromy_1_0109.2
  · exact g32p_row05_cosetMonodromy_1_0110.2
  · exact g32p_row05_cosetMonodromy_1_0111.2
  · exact g32p_row05_cosetMonodromy_1_0112.2
  · exact g32p_row05_cosetMonodromy_1_0113.2
  · exact g32p_row05_cosetMonodromy_1_0114.2
  · exact g32p_row05_cosetMonodromy_1_0115.2
  · exact g32p_row05_cosetMonodromy_1_0116.2
  · exact g32p_row05_cosetMonodromy_1_0117.2
  · exact g32p_row05_cosetMonodromy_1_0118.2
  · exact g32p_row05_cosetMonodromy_1_0119.2
  · exact g32p_row05_cosetMonodromy_1_0120.2
  · exact g32p_row05_cosetMonodromy_1_0121.2
  · exact g32p_row05_cosetMonodromy_1_0122.2
  · exact g32p_row05_cosetMonodromy_1_0123.2
  · exact g32p_row05_cosetMonodromy_1_0124.2
  · exact g32p_row05_cosetMonodromy_1_0125.2
  · exact g32p_row05_cosetMonodromy_1_0126.2
  · exact g32p_row05_cosetMonodromy_1_0127.2

theorem g32p_row05_cosetBranchExponents1 :
    papersExps g32p_row05_finiteSupplier.H g32p_row05_finiteSupplier.χ (g32p_cosetBranches 1) =
      (Finset.univ.val.map (fun j : Fin 128 => Multiplicative.toAdd (g32p_row05_cosetExponents1 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row05_cosetOrbitEquiv1
    (fun j => g32p_row05_cosetActualRepresentatives (g32p_row05_cosetRoots1 j)) (fun _ => rfl) g32p_row05_cosetLengths1 g32p_row05_cosetPeriod1
    (fun j => g32p_row05_groupEquiv (g32p_row05_cosetMonodromies1 j)) g32p_row05_cosetActualMonodromy1]
  simp only [g32p_row05_cosetCharacter1]
  rfl

def g32p_row05_cosetOrbitEquiv2 : Fin 176 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 2)) (g32p_G ⧸ g32p_row05_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 2) g32p_row05_cosetEquiv
    (g32p_row05_cosetBranchNext 2) (g32p_row05_cosetQuotientStep 2) g32p_row05_cosetLabels2 g32p_row05_cosetRoots2
    g32p_row05_cosetDistances2 g32p_row05_cosetRootLabels2 g32p_row05_cosetNextLabels2 g32p_row05_cosetReach2)

theorem g32p_row05_cosetPeriod2 (j : Fin 176) :
    Function.minimalPeriod ((g32p_cosetBranches 2) • ·) (g32p_row05_cosetEquiv (g32p_row05_cosetRoots2 j)) = g32p_row05_cosetLengths2 j := by
  apply g32p_period_of_cycle g32p_row05_cosetEquiv (g32p_row05_cosetBranchNext 2) ((g32p_cosetBranches 2) • ·)
    (g32p_row05_cosetQuotientStep 2) _ _ (g32p_row05_cosetPeriods2 j).1 (g32p_row05_cosetPeriods2 j).2.1
  intro t ht hlt
  exact (g32p_row05_cosetPeriods2 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row05_cosetActualMonodromy2 (j : Fin 176) :
    (g32p_cosetBranches 2) ^ g32p_row05_cosetLengths2 j * g32p_row05_cosetActualRepresentatives (g32p_row05_cosetRoots2 j) =
      g32p_row05_cosetActualRepresentatives (g32p_row05_cosetRoots2 j) *
        (g32p_row05_groupEquiv (g32p_row05_cosetMonodromies2 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row05_cosetBranchMatrices 2)
    (g32p_row05_cosetRepresentatives (g32p_row05_cosetRoots2 j))
    (g32p_row05_groupNodes (g32p_row05_cosetMonodromies2 j))
    (g32p_row05_cosetLengths2 j) (g32p_row05_cosetBranchMap 2)
    (g32p_row05_cosetActualRepresentatives_map _) (g32p_row05_groupEquiv_map _)
  fin_cases j
  · exact g32p_row05_cosetMonodromy_2_0000.1
  · exact g32p_row05_cosetMonodromy_2_0001.1
  · exact g32p_row05_cosetMonodromy_2_0002.1
  · exact g32p_row05_cosetMonodromy_2_0003.1
  · exact g32p_row05_cosetMonodromy_2_0004.1
  · exact g32p_row05_cosetMonodromy_2_0005.1
  · exact g32p_row05_cosetMonodromy_2_0006.1
  · exact g32p_row05_cosetMonodromy_2_0007.1
  · exact g32p_row05_cosetMonodromy_2_0008.1
  · exact g32p_row05_cosetMonodromy_2_0009.1
  · exact g32p_row05_cosetMonodromy_2_0010.1
  · exact g32p_row05_cosetMonodromy_2_0011.1
  · exact g32p_row05_cosetMonodromy_2_0012.1
  · exact g32p_row05_cosetMonodromy_2_0013.1
  · exact g32p_row05_cosetMonodromy_2_0014.1
  · exact g32p_row05_cosetMonodromy_2_0015.1
  · exact g32p_row05_cosetMonodromy_2_0016.1
  · exact g32p_row05_cosetMonodromy_2_0017.1
  · exact g32p_row05_cosetMonodromy_2_0018.1
  · exact g32p_row05_cosetMonodromy_2_0019.1
  · exact g32p_row05_cosetMonodromy_2_0020.1
  · exact g32p_row05_cosetMonodromy_2_0021.1
  · exact g32p_row05_cosetMonodromy_2_0022.1
  · exact g32p_row05_cosetMonodromy_2_0023.1
  · exact g32p_row05_cosetMonodromy_2_0024.1
  · exact g32p_row05_cosetMonodromy_2_0025.1
  · exact g32p_row05_cosetMonodromy_2_0026.1
  · exact g32p_row05_cosetMonodromy_2_0027.1
  · exact g32p_row05_cosetMonodromy_2_0028.1
  · exact g32p_row05_cosetMonodromy_2_0029.1
  · exact g32p_row05_cosetMonodromy_2_0030.1
  · exact g32p_row05_cosetMonodromy_2_0031.1
  · exact g32p_row05_cosetMonodromy_2_0032.1
  · exact g32p_row05_cosetMonodromy_2_0033.1
  · exact g32p_row05_cosetMonodromy_2_0034.1
  · exact g32p_row05_cosetMonodromy_2_0035.1
  · exact g32p_row05_cosetMonodromy_2_0036.1
  · exact g32p_row05_cosetMonodromy_2_0037.1
  · exact g32p_row05_cosetMonodromy_2_0038.1
  · exact g32p_row05_cosetMonodromy_2_0039.1
  · exact g32p_row05_cosetMonodromy_2_0040.1
  · exact g32p_row05_cosetMonodromy_2_0041.1
  · exact g32p_row05_cosetMonodromy_2_0042.1
  · exact g32p_row05_cosetMonodromy_2_0043.1
  · exact g32p_row05_cosetMonodromy_2_0044.1
  · exact g32p_row05_cosetMonodromy_2_0045.1
  · exact g32p_row05_cosetMonodromy_2_0046.1
  · exact g32p_row05_cosetMonodromy_2_0047.1
  · exact g32p_row05_cosetMonodromy_2_0048.1
  · exact g32p_row05_cosetMonodromy_2_0049.1
  · exact g32p_row05_cosetMonodromy_2_0050.1
  · exact g32p_row05_cosetMonodromy_2_0051.1
  · exact g32p_row05_cosetMonodromy_2_0052.1
  · exact g32p_row05_cosetMonodromy_2_0053.1
  · exact g32p_row05_cosetMonodromy_2_0054.1
  · exact g32p_row05_cosetMonodromy_2_0055.1
  · exact g32p_row05_cosetMonodromy_2_0056.1
  · exact g32p_row05_cosetMonodromy_2_0057.1
  · exact g32p_row05_cosetMonodromy_2_0058.1
  · exact g32p_row05_cosetMonodromy_2_0059.1
  · exact g32p_row05_cosetMonodromy_2_0060.1
  · exact g32p_row05_cosetMonodromy_2_0061.1
  · exact g32p_row05_cosetMonodromy_2_0062.1
  · exact g32p_row05_cosetMonodromy_2_0063.1
  · exact g32p_row05_cosetMonodromy_2_0064.1
  · exact g32p_row05_cosetMonodromy_2_0065.1
  · exact g32p_row05_cosetMonodromy_2_0066.1
  · exact g32p_row05_cosetMonodromy_2_0067.1
  · exact g32p_row05_cosetMonodromy_2_0068.1
  · exact g32p_row05_cosetMonodromy_2_0069.1
  · exact g32p_row05_cosetMonodromy_2_0070.1
  · exact g32p_row05_cosetMonodromy_2_0071.1
  · exact g32p_row05_cosetMonodromy_2_0072.1
  · exact g32p_row05_cosetMonodromy_2_0073.1
  · exact g32p_row05_cosetMonodromy_2_0074.1
  · exact g32p_row05_cosetMonodromy_2_0075.1
  · exact g32p_row05_cosetMonodromy_2_0076.1
  · exact g32p_row05_cosetMonodromy_2_0077.1
  · exact g32p_row05_cosetMonodromy_2_0078.1
  · exact g32p_row05_cosetMonodromy_2_0079.1
  · exact g32p_row05_cosetMonodromy_2_0080.1
  · exact g32p_row05_cosetMonodromy_2_0081.1
  · exact g32p_row05_cosetMonodromy_2_0082.1
  · exact g32p_row05_cosetMonodromy_2_0083.1
  · exact g32p_row05_cosetMonodromy_2_0084.1
  · exact g32p_row05_cosetMonodromy_2_0085.1
  · exact g32p_row05_cosetMonodromy_2_0086.1
  · exact g32p_row05_cosetMonodromy_2_0087.1
  · exact g32p_row05_cosetMonodromy_2_0088.1
  · exact g32p_row05_cosetMonodromy_2_0089.1
  · exact g32p_row05_cosetMonodromy_2_0090.1
  · exact g32p_row05_cosetMonodromy_2_0091.1
  · exact g32p_row05_cosetMonodromy_2_0092.1
  · exact g32p_row05_cosetMonodromy_2_0093.1
  · exact g32p_row05_cosetMonodromy_2_0094.1
  · exact g32p_row05_cosetMonodromy_2_0095.1
  · exact g32p_row05_cosetMonodromy_2_0096.1
  · exact g32p_row05_cosetMonodromy_2_0097.1
  · exact g32p_row05_cosetMonodromy_2_0098.1
  · exact g32p_row05_cosetMonodromy_2_0099.1
  · exact g32p_row05_cosetMonodromy_2_0100.1
  · exact g32p_row05_cosetMonodromy_2_0101.1
  · exact g32p_row05_cosetMonodromy_2_0102.1
  · exact g32p_row05_cosetMonodromy_2_0103.1
  · exact g32p_row05_cosetMonodromy_2_0104.1
  · exact g32p_row05_cosetMonodromy_2_0105.1
  · exact g32p_row05_cosetMonodromy_2_0106.1
  · exact g32p_row05_cosetMonodromy_2_0107.1
  · exact g32p_row05_cosetMonodromy_2_0108.1
  · exact g32p_row05_cosetMonodromy_2_0109.1
  · exact g32p_row05_cosetMonodromy_2_0110.1
  · exact g32p_row05_cosetMonodromy_2_0111.1
  · exact g32p_row05_cosetMonodromy_2_0112.1
  · exact g32p_row05_cosetMonodromy_2_0113.1
  · exact g32p_row05_cosetMonodromy_2_0114.1
  · exact g32p_row05_cosetMonodromy_2_0115.1
  · exact g32p_row05_cosetMonodromy_2_0116.1
  · exact g32p_row05_cosetMonodromy_2_0117.1
  · exact g32p_row05_cosetMonodromy_2_0118.1
  · exact g32p_row05_cosetMonodromy_2_0119.1
  · exact g32p_row05_cosetMonodromy_2_0120.1
  · exact g32p_row05_cosetMonodromy_2_0121.1
  · exact g32p_row05_cosetMonodromy_2_0122.1
  · exact g32p_row05_cosetMonodromy_2_0123.1
  · exact g32p_row05_cosetMonodromy_2_0124.1
  · exact g32p_row05_cosetMonodromy_2_0125.1
  · exact g32p_row05_cosetMonodromy_2_0126.1
  · exact g32p_row05_cosetMonodromy_2_0127.1
  · exact g32p_row05_cosetMonodromy_2_0128.1
  · exact g32p_row05_cosetMonodromy_2_0129.1
  · exact g32p_row05_cosetMonodromy_2_0130.1
  · exact g32p_row05_cosetMonodromy_2_0131.1
  · exact g32p_row05_cosetMonodromy_2_0132.1
  · exact g32p_row05_cosetMonodromy_2_0133.1
  · exact g32p_row05_cosetMonodromy_2_0134.1
  · exact g32p_row05_cosetMonodromy_2_0135.1
  · exact g32p_row05_cosetMonodromy_2_0136.1
  · exact g32p_row05_cosetMonodromy_2_0137.1
  · exact g32p_row05_cosetMonodromy_2_0138.1
  · exact g32p_row05_cosetMonodromy_2_0139.1
  · exact g32p_row05_cosetMonodromy_2_0140.1
  · exact g32p_row05_cosetMonodromy_2_0141.1
  · exact g32p_row05_cosetMonodromy_2_0142.1
  · exact g32p_row05_cosetMonodromy_2_0143.1
  · exact g32p_row05_cosetMonodromy_2_0144.1
  · exact g32p_row05_cosetMonodromy_2_0145.1
  · exact g32p_row05_cosetMonodromy_2_0146.1
  · exact g32p_row05_cosetMonodromy_2_0147.1
  · exact g32p_row05_cosetMonodromy_2_0148.1
  · exact g32p_row05_cosetMonodromy_2_0149.1
  · exact g32p_row05_cosetMonodromy_2_0150.1
  · exact g32p_row05_cosetMonodromy_2_0151.1
  · exact g32p_row05_cosetMonodromy_2_0152.1
  · exact g32p_row05_cosetMonodromy_2_0153.1
  · exact g32p_row05_cosetMonodromy_2_0154.1
  · exact g32p_row05_cosetMonodromy_2_0155.1
  · exact g32p_row05_cosetMonodromy_2_0156.1
  · exact g32p_row05_cosetMonodromy_2_0157.1
  · exact g32p_row05_cosetMonodromy_2_0158.1
  · exact g32p_row05_cosetMonodromy_2_0159.1
  · exact g32p_row05_cosetMonodromy_2_0160.1
  · exact g32p_row05_cosetMonodromy_2_0161.1
  · exact g32p_row05_cosetMonodromy_2_0162.1
  · exact g32p_row05_cosetMonodromy_2_0163.1
  · exact g32p_row05_cosetMonodromy_2_0164.1
  · exact g32p_row05_cosetMonodromy_2_0165.1
  · exact g32p_row05_cosetMonodromy_2_0166.1
  · exact g32p_row05_cosetMonodromy_2_0167.1
  · exact g32p_row05_cosetMonodromy_2_0168.1
  · exact g32p_row05_cosetMonodromy_2_0169.1
  · exact g32p_row05_cosetMonodromy_2_0170.1
  · exact g32p_row05_cosetMonodromy_2_0171.1
  · exact g32p_row05_cosetMonodromy_2_0172.1
  · exact g32p_row05_cosetMonodromy_2_0173.1
  · exact g32p_row05_cosetMonodromy_2_0174.1
  · exact g32p_row05_cosetMonodromy_2_0175.1

theorem g32p_row05_cosetCharacter2 (j : Fin 176) :
    g32p_row05_finiteSupplier.χ (g32p_row05_groupEquiv (g32p_row05_cosetMonodromies2 j)) = g32p_row05_cosetExponents2 j := by
  rw [g32p_row05_finiteSupplier_value]
  fin_cases j
  · exact g32p_row05_cosetMonodromy_2_0000.2
  · exact g32p_row05_cosetMonodromy_2_0001.2
  · exact g32p_row05_cosetMonodromy_2_0002.2
  · exact g32p_row05_cosetMonodromy_2_0003.2
  · exact g32p_row05_cosetMonodromy_2_0004.2
  · exact g32p_row05_cosetMonodromy_2_0005.2
  · exact g32p_row05_cosetMonodromy_2_0006.2
  · exact g32p_row05_cosetMonodromy_2_0007.2
  · exact g32p_row05_cosetMonodromy_2_0008.2
  · exact g32p_row05_cosetMonodromy_2_0009.2
  · exact g32p_row05_cosetMonodromy_2_0010.2
  · exact g32p_row05_cosetMonodromy_2_0011.2
  · exact g32p_row05_cosetMonodromy_2_0012.2
  · exact g32p_row05_cosetMonodromy_2_0013.2
  · exact g32p_row05_cosetMonodromy_2_0014.2
  · exact g32p_row05_cosetMonodromy_2_0015.2
  · exact g32p_row05_cosetMonodromy_2_0016.2
  · exact g32p_row05_cosetMonodromy_2_0017.2
  · exact g32p_row05_cosetMonodromy_2_0018.2
  · exact g32p_row05_cosetMonodromy_2_0019.2
  · exact g32p_row05_cosetMonodromy_2_0020.2
  · exact g32p_row05_cosetMonodromy_2_0021.2
  · exact g32p_row05_cosetMonodromy_2_0022.2
  · exact g32p_row05_cosetMonodromy_2_0023.2
  · exact g32p_row05_cosetMonodromy_2_0024.2
  · exact g32p_row05_cosetMonodromy_2_0025.2
  · exact g32p_row05_cosetMonodromy_2_0026.2
  · exact g32p_row05_cosetMonodromy_2_0027.2
  · exact g32p_row05_cosetMonodromy_2_0028.2
  · exact g32p_row05_cosetMonodromy_2_0029.2
  · exact g32p_row05_cosetMonodromy_2_0030.2
  · exact g32p_row05_cosetMonodromy_2_0031.2
  · exact g32p_row05_cosetMonodromy_2_0032.2
  · exact g32p_row05_cosetMonodromy_2_0033.2
  · exact g32p_row05_cosetMonodromy_2_0034.2
  · exact g32p_row05_cosetMonodromy_2_0035.2
  · exact g32p_row05_cosetMonodromy_2_0036.2
  · exact g32p_row05_cosetMonodromy_2_0037.2
  · exact g32p_row05_cosetMonodromy_2_0038.2
  · exact g32p_row05_cosetMonodromy_2_0039.2
  · exact g32p_row05_cosetMonodromy_2_0040.2
  · exact g32p_row05_cosetMonodromy_2_0041.2
  · exact g32p_row05_cosetMonodromy_2_0042.2
  · exact g32p_row05_cosetMonodromy_2_0043.2
  · exact g32p_row05_cosetMonodromy_2_0044.2
  · exact g32p_row05_cosetMonodromy_2_0045.2
  · exact g32p_row05_cosetMonodromy_2_0046.2
  · exact g32p_row05_cosetMonodromy_2_0047.2
  · exact g32p_row05_cosetMonodromy_2_0048.2
  · exact g32p_row05_cosetMonodromy_2_0049.2
  · exact g32p_row05_cosetMonodromy_2_0050.2
  · exact g32p_row05_cosetMonodromy_2_0051.2
  · exact g32p_row05_cosetMonodromy_2_0052.2
  · exact g32p_row05_cosetMonodromy_2_0053.2
  · exact g32p_row05_cosetMonodromy_2_0054.2
  · exact g32p_row05_cosetMonodromy_2_0055.2
  · exact g32p_row05_cosetMonodromy_2_0056.2
  · exact g32p_row05_cosetMonodromy_2_0057.2
  · exact g32p_row05_cosetMonodromy_2_0058.2
  · exact g32p_row05_cosetMonodromy_2_0059.2
  · exact g32p_row05_cosetMonodromy_2_0060.2
  · exact g32p_row05_cosetMonodromy_2_0061.2
  · exact g32p_row05_cosetMonodromy_2_0062.2
  · exact g32p_row05_cosetMonodromy_2_0063.2
  · exact g32p_row05_cosetMonodromy_2_0064.2
  · exact g32p_row05_cosetMonodromy_2_0065.2
  · exact g32p_row05_cosetMonodromy_2_0066.2
  · exact g32p_row05_cosetMonodromy_2_0067.2
  · exact g32p_row05_cosetMonodromy_2_0068.2
  · exact g32p_row05_cosetMonodromy_2_0069.2
  · exact g32p_row05_cosetMonodromy_2_0070.2
  · exact g32p_row05_cosetMonodromy_2_0071.2
  · exact g32p_row05_cosetMonodromy_2_0072.2
  · exact g32p_row05_cosetMonodromy_2_0073.2
  · exact g32p_row05_cosetMonodromy_2_0074.2
  · exact g32p_row05_cosetMonodromy_2_0075.2
  · exact g32p_row05_cosetMonodromy_2_0076.2
  · exact g32p_row05_cosetMonodromy_2_0077.2
  · exact g32p_row05_cosetMonodromy_2_0078.2
  · exact g32p_row05_cosetMonodromy_2_0079.2
  · exact g32p_row05_cosetMonodromy_2_0080.2
  · exact g32p_row05_cosetMonodromy_2_0081.2
  · exact g32p_row05_cosetMonodromy_2_0082.2
  · exact g32p_row05_cosetMonodromy_2_0083.2
  · exact g32p_row05_cosetMonodromy_2_0084.2
  · exact g32p_row05_cosetMonodromy_2_0085.2
  · exact g32p_row05_cosetMonodromy_2_0086.2
  · exact g32p_row05_cosetMonodromy_2_0087.2
  · exact g32p_row05_cosetMonodromy_2_0088.2
  · exact g32p_row05_cosetMonodromy_2_0089.2
  · exact g32p_row05_cosetMonodromy_2_0090.2
  · exact g32p_row05_cosetMonodromy_2_0091.2
  · exact g32p_row05_cosetMonodromy_2_0092.2
  · exact g32p_row05_cosetMonodromy_2_0093.2
  · exact g32p_row05_cosetMonodromy_2_0094.2
  · exact g32p_row05_cosetMonodromy_2_0095.2
  · exact g32p_row05_cosetMonodromy_2_0096.2
  · exact g32p_row05_cosetMonodromy_2_0097.2
  · exact g32p_row05_cosetMonodromy_2_0098.2
  · exact g32p_row05_cosetMonodromy_2_0099.2
  · exact g32p_row05_cosetMonodromy_2_0100.2
  · exact g32p_row05_cosetMonodromy_2_0101.2
  · exact g32p_row05_cosetMonodromy_2_0102.2
  · exact g32p_row05_cosetMonodromy_2_0103.2
  · exact g32p_row05_cosetMonodromy_2_0104.2
  · exact g32p_row05_cosetMonodromy_2_0105.2
  · exact g32p_row05_cosetMonodromy_2_0106.2
  · exact g32p_row05_cosetMonodromy_2_0107.2
  · exact g32p_row05_cosetMonodromy_2_0108.2
  · exact g32p_row05_cosetMonodromy_2_0109.2
  · exact g32p_row05_cosetMonodromy_2_0110.2
  · exact g32p_row05_cosetMonodromy_2_0111.2
  · exact g32p_row05_cosetMonodromy_2_0112.2
  · exact g32p_row05_cosetMonodromy_2_0113.2
  · exact g32p_row05_cosetMonodromy_2_0114.2
  · exact g32p_row05_cosetMonodromy_2_0115.2
  · exact g32p_row05_cosetMonodromy_2_0116.2
  · exact g32p_row05_cosetMonodromy_2_0117.2
  · exact g32p_row05_cosetMonodromy_2_0118.2
  · exact g32p_row05_cosetMonodromy_2_0119.2
  · exact g32p_row05_cosetMonodromy_2_0120.2
  · exact g32p_row05_cosetMonodromy_2_0121.2
  · exact g32p_row05_cosetMonodromy_2_0122.2
  · exact g32p_row05_cosetMonodromy_2_0123.2
  · exact g32p_row05_cosetMonodromy_2_0124.2
  · exact g32p_row05_cosetMonodromy_2_0125.2
  · exact g32p_row05_cosetMonodromy_2_0126.2
  · exact g32p_row05_cosetMonodromy_2_0127.2
  · exact g32p_row05_cosetMonodromy_2_0128.2
  · exact g32p_row05_cosetMonodromy_2_0129.2
  · exact g32p_row05_cosetMonodromy_2_0130.2
  · exact g32p_row05_cosetMonodromy_2_0131.2
  · exact g32p_row05_cosetMonodromy_2_0132.2
  · exact g32p_row05_cosetMonodromy_2_0133.2
  · exact g32p_row05_cosetMonodromy_2_0134.2
  · exact g32p_row05_cosetMonodromy_2_0135.2
  · exact g32p_row05_cosetMonodromy_2_0136.2
  · exact g32p_row05_cosetMonodromy_2_0137.2
  · exact g32p_row05_cosetMonodromy_2_0138.2
  · exact g32p_row05_cosetMonodromy_2_0139.2
  · exact g32p_row05_cosetMonodromy_2_0140.2
  · exact g32p_row05_cosetMonodromy_2_0141.2
  · exact g32p_row05_cosetMonodromy_2_0142.2
  · exact g32p_row05_cosetMonodromy_2_0143.2
  · exact g32p_row05_cosetMonodromy_2_0144.2
  · exact g32p_row05_cosetMonodromy_2_0145.2
  · exact g32p_row05_cosetMonodromy_2_0146.2
  · exact g32p_row05_cosetMonodromy_2_0147.2
  · exact g32p_row05_cosetMonodromy_2_0148.2
  · exact g32p_row05_cosetMonodromy_2_0149.2
  · exact g32p_row05_cosetMonodromy_2_0150.2
  · exact g32p_row05_cosetMonodromy_2_0151.2
  · exact g32p_row05_cosetMonodromy_2_0152.2
  · exact g32p_row05_cosetMonodromy_2_0153.2
  · exact g32p_row05_cosetMonodromy_2_0154.2
  · exact g32p_row05_cosetMonodromy_2_0155.2
  · exact g32p_row05_cosetMonodromy_2_0156.2
  · exact g32p_row05_cosetMonodromy_2_0157.2
  · exact g32p_row05_cosetMonodromy_2_0158.2
  · exact g32p_row05_cosetMonodromy_2_0159.2
  · exact g32p_row05_cosetMonodromy_2_0160.2
  · exact g32p_row05_cosetMonodromy_2_0161.2
  · exact g32p_row05_cosetMonodromy_2_0162.2
  · exact g32p_row05_cosetMonodromy_2_0163.2
  · exact g32p_row05_cosetMonodromy_2_0164.2
  · exact g32p_row05_cosetMonodromy_2_0165.2
  · exact g32p_row05_cosetMonodromy_2_0166.2
  · exact g32p_row05_cosetMonodromy_2_0167.2
  · exact g32p_row05_cosetMonodromy_2_0168.2
  · exact g32p_row05_cosetMonodromy_2_0169.2
  · exact g32p_row05_cosetMonodromy_2_0170.2
  · exact g32p_row05_cosetMonodromy_2_0171.2
  · exact g32p_row05_cosetMonodromy_2_0172.2
  · exact g32p_row05_cosetMonodromy_2_0173.2
  · exact g32p_row05_cosetMonodromy_2_0174.2
  · exact g32p_row05_cosetMonodromy_2_0175.2

theorem g32p_row05_cosetBranchExponents2 :
    papersExps g32p_row05_finiteSupplier.H g32p_row05_finiteSupplier.χ (g32p_cosetBranches 2) =
      (Finset.univ.val.map (fun j : Fin 176 => Multiplicative.toAdd (g32p_row05_cosetExponents2 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row05_cosetOrbitEquiv2
    (fun j => g32p_row05_cosetActualRepresentatives (g32p_row05_cosetRoots2 j)) (fun _ => rfl) g32p_row05_cosetLengths2 g32p_row05_cosetPeriod2
    (fun j => g32p_row05_groupEquiv (g32p_row05_cosetMonodromies2 j)) g32p_row05_cosetActualMonodromy2]
  simp only [g32p_row05_cosetCharacter2]
  rfl

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_row05_exponents :
    (g32p_exponents g32p_row05_finiteSupplier).Perm (expandExps [(1, 144), (2, 144)]) := by
  have h0 : papersExps g32p_row05_finiteSupplier.H g32p_row05_finiteSupplier.χ (g32p_classDatum 0) = (([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (ZMod 3)) : Multiset (ZMod 3)) := by
    change papersExps g32p_row05_finiteSupplier.H g32p_row05_finiteSupplier.χ (g32p_cosetBranches 0) = _
    rw [g32p_row05_cosetBranchExponents0]
    change ((Finset.univ : Finset (Fin 128)).val.map
      (fun j => Multiplicative.toAdd (g32p_row05_cosetExponents0 j))).filter (· ≠ 0) = (([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (ZMod 3)) : Multiset (ZMod 3))
    decide +kernel
  have h1 : papersExps g32p_row05_finiteSupplier.H g32p_row05_finiteSupplier.χ (g32p_classDatum 6) = (([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 3)) : Multiset (ZMod 3)) := by
    change papersExps g32p_row05_finiteSupplier.H g32p_row05_finiteSupplier.χ (g32p_cosetBranches 1) = _
    rw [g32p_row05_cosetBranchExponents1]
    change ((Finset.univ : Finset (Fin 128)).val.map
      (fun j => Multiplicative.toAdd (g32p_row05_cosetExponents1 j))).filter (· ≠ 0) = (([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 3)) : Multiset (ZMod 3))
    decide +kernel
  have h2 : papersExps g32p_row05_finiteSupplier.H g32p_row05_finiteSupplier.χ (g32p_classDatum 12) = (([] : List (ZMod 3)) : Multiset (ZMod 3)) := by
    change papersExps g32p_row05_finiteSupplier.H g32p_row05_finiteSupplier.χ (g32p_cosetBranches 2) = _
    rw [g32p_row05_cosetBranchExponents2]
    change ((Finset.univ : Finset (Fin 176)).val.map
      (fun j => Multiplicative.toAdd (g32p_row05_cosetExponents2 j))).filter (· ≠ 0) = (([] : List (ZMod 3)) : Multiset (ZMod 3))
    decide +kernel
  have hs : papersExpsTuple g32p_row05_finiteSupplier.H g32p_row05_finiteSupplier.χ g32p_classList =
      6 • (([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (ZMod 3)) : Multiset (ZMod 3)) + 6 • (([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 3)) : Multiset (ZMod 3)) + (([] : List (ZMod 3)) : Multiset (ZMod 3)) := by
    have hc : g32p_classList = List.replicate 6 (g32p_classDatum 0) ++
        List.replicate 6 (g32p_classDatum 6) ++ [g32p_classDatum 12] := rfl
    simp only [papersExpsTuple, hc, List.map_append, List.map_replicate,
      List.map_cons, List.map_nil, List.sum_append, List.sum_replicate,
      List.sum_cons, List.sum_nil, List.sum_singleton, h0, h1, h2, add_zero]
    rfl
  apply Multiset.coe_eq_coe.mp
  change (((papersExpsTuple _ _ _).map ZMod.val).toList : Multiset ℕ) = _
  rw [Multiset.coe_toList, hs]
  change (6 • (([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (ZMod 3)) : Multiset (ZMod 3)) + 6 • (([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 3)) : Multiset (ZMod 3)) + (([] : List (ZMod 3)) : Multiset (ZMod 3))).map ZMod.val = ↑(expandExps [(1, 144), (2, 144)])
  decide +kernel

theorem g32p_row05_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 5 ∧ r.m = g32p_row05_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row05_finiteSupplier.H ∧
      (g32p_exponents g32p_row05_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨5, (-1), 486, 3, 905, 288, 2096, some 1, [(1, 144), (2, 144)], .S⟩, ?_, rfl, rfl, g32p_row05_finiteSupplier_order.symm, g32p_row05_exponents⟩
  decide

def g32p_row05_complexWitness : g32p_row05_finiteSupplier.H →* ℂˣ := g32p_complexCharacter g32p_row05_finiteSupplier

theorem g32p_row05_supplierWitness :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 5 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) := by
  exact ⟨g32p_row05_finiteSupplier, g32p_row05_complexWitness, g32p_complexCharacter_apply _,
    g32p_row05_finiteSupplier_table⟩

end HodgeLean.Foundations.Program

end
end
