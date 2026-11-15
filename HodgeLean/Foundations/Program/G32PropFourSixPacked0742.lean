import HodgeLean.Foundations.Program.G32PropFourSixPacked0721
import HodgeLean.Foundations.Program.G32PropFourSixPacked0741
import HodgeLean.Foundations.Program.G32PropFourSixPacked0722
import HodgeLean.Foundations.Program.G32PropFourSixPacked0723
import HodgeLean.Foundations.Program.G32PropFourSixPacked0724
import HodgeLean.Foundations.Program.G32PropFourSixPacked0725
import HodgeLean.Foundations.Program.G32PropFourSixPacked0726
import HodgeLean.Foundations.Program.G32PropFourSixPacked0727
import HodgeLean.Foundations.Program.G32PropFourSixPacked0728
import HodgeLean.Foundations.Program.G32PropFourSixPacked0729
import HodgeLean.Foundations.Program.G32PropFourSixPacked0730
import HodgeLean.Foundations.Program.G32PropFourSixPacked0731
import HodgeLean.Foundations.Program.G32PropFourSixPacked0732
import HodgeLean.Foundations.Program.G32PropFourSixPacked0733
import HodgeLean.Foundations.Program.G32PropFourSixPacked0734
import HodgeLean.Foundations.Program.G32PropFourSixPacked0735
import HodgeLean.Foundations.Program.G32PropFourSixPacked0736
import HodgeLean.Foundations.Program.G32PropFourSixPacked0737
import HodgeLean.Foundations.Program.G32PropFourSixPacked0738
import HodgeLean.Foundations.Program.G32PropFourSixPacked0739
import HodgeLean.Foundations.Program.G32PropFourSixPacked0740
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634
import HodgeLean.Foundations.Program.G32PropFourSixCharacters

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option maxRecDepth 2048

def g32p_row18_cosetEquiv : Fin 4320 ≃ (g32p_G ⧸ g32p_row18_finiteSupplier.H) :=
  Equiv.ofBijective _ g32p_row18_cosetEnumeration

theorem g32p_row18_cosetBranchMap (b : Fin 3) :
    b4b_toMatrix (g32p_cosetBranches b) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row18_cosetBranchMatrices b)) := by
  have he : g32p_row18_cosetBranchMatrices b = g32p_cosetIntegralBranches b := by
    fin_cases b
    · exact g32p_row18_cosetBranchMatrix0
    · exact g32p_row18_cosetBranchMatrix1
    · exact g32p_row18_cosetBranchMatrix2
  rw [he]
  exact g32p_cosetBranches_map b

theorem g32p_row18_cosetBranchCheck (b : Fin 3) (i : Fin 4320) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices b) (g32p_row18_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext b i))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor b i)) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row18_cosetBranchBlock_0000 b
  · exact g32p_row18_cosetBranchBlock_0001 b
  · exact g32p_row18_cosetBranchBlock_0002 b
  · exact g32p_row18_cosetBranchBlock_0003 b
  · exact g32p_row18_cosetBranchBlock_0004 b
  · exact g32p_row18_cosetBranchBlock_0005 b
  · exact g32p_row18_cosetBranchBlock_0006 b
  · exact g32p_row18_cosetBranchBlock_0007 b
  · exact g32p_row18_cosetBranchBlock_0008 b
  · exact g32p_row18_cosetBranchBlock_0009 b
  · exact g32p_row18_cosetBranchBlock_0010 b
  · exact g32p_row18_cosetBranchBlock_0011 b
  · exact g32p_row18_cosetBranchBlock_0012 b
  · exact g32p_row18_cosetBranchBlock_0013 b
  · exact g32p_row18_cosetBranchBlock_0014 b
  · exact g32p_row18_cosetBranchBlock_0015 b
  · exact g32p_row18_cosetBranchBlock_0016 b
  · exact g32p_row18_cosetBranchBlock_0017 b
  · exact g32p_row18_cosetBranchBlock_0018 b
  · exact g32p_row18_cosetBranchBlock_0019 b
  · exact g32p_row18_cosetBranchBlock_0020 b
  · exact g32p_row18_cosetBranchBlock_0021 b
  · exact g32p_row18_cosetBranchBlock_0022 b
  · exact g32p_row18_cosetBranchBlock_0023 b
  · exact g32p_row18_cosetBranchBlock_0024 b
  · exact g32p_row18_cosetBranchBlock_0025 b
  · exact g32p_row18_cosetBranchBlock_0026 b
  · exact g32p_row18_cosetBranchBlock_0027 b
  · exact g32p_row18_cosetBranchBlock_0028 b
  · exact g32p_row18_cosetBranchBlock_0029 b
  · exact g32p_row18_cosetBranchBlock_0030 b
  · exact g32p_row18_cosetBranchBlock_0031 b
  · exact g32p_row18_cosetBranchBlock_0032 b
  · exact g32p_row18_cosetBranchBlock_0033 b
  · exact g32p_row18_cosetBranchBlock_0034 b
  · exact g32p_row18_cosetBranchBlock_0035 b
  · exact g32p_row18_cosetBranchBlock_0036 b
  · exact g32p_row18_cosetBranchBlock_0037 b
  · exact g32p_row18_cosetBranchBlock_0038 b
  · exact g32p_row18_cosetBranchBlock_0039 b
  · exact g32p_row18_cosetBranchBlock_0040 b
  · exact g32p_row18_cosetBranchBlock_0041 b
  · exact g32p_row18_cosetBranchBlock_0042 b
  · exact g32p_row18_cosetBranchBlock_0043 b
  · exact g32p_row18_cosetBranchBlock_0044 b
  · exact g32p_row18_cosetBranchBlock_0045 b
  · exact g32p_row18_cosetBranchBlock_0046 b
  · exact g32p_row18_cosetBranchBlock_0047 b
  · exact g32p_row18_cosetBranchBlock_0048 b
  · exact g32p_row18_cosetBranchBlock_0049 b
  · exact g32p_row18_cosetBranchBlock_0050 b
  · exact g32p_row18_cosetBranchBlock_0051 b
  · exact g32p_row18_cosetBranchBlock_0052 b
  · exact g32p_row18_cosetBranchBlock_0053 b
  · exact g32p_row18_cosetBranchBlock_0054 b
  · exact g32p_row18_cosetBranchBlock_0055 b
  · exact g32p_row18_cosetBranchBlock_0056 b
  · exact g32p_row18_cosetBranchBlock_0057 b
  · exact g32p_row18_cosetBranchBlock_0058 b
  · exact g32p_row18_cosetBranchBlock_0059 b
  · exact g32p_row18_cosetBranchBlock_0060 b
  · exact g32p_row18_cosetBranchBlock_0061 b
  · exact g32p_row18_cosetBranchBlock_0062 b
  · exact g32p_row18_cosetBranchBlock_0063 b
  · exact g32p_row18_cosetBranchBlock_0064 b
  · exact g32p_row18_cosetBranchBlock_0065 b
  · exact g32p_row18_cosetBranchBlock_0066 b
  · exact g32p_row18_cosetBranchBlock_0067 b
  · exact g32p_row18_cosetBranchBlock_0068 b
  · exact g32p_row18_cosetBranchBlock_0069 b
  · exact g32p_row18_cosetBranchBlock_0070 b
  · exact g32p_row18_cosetBranchBlock_0071 b
  · exact g32p_row18_cosetBranchBlock_0072 b
  · exact g32p_row18_cosetBranchBlock_0073 b
  · exact g32p_row18_cosetBranchBlock_0074 b
  · exact g32p_row18_cosetBranchBlock_0075 b
  · exact g32p_row18_cosetBranchBlock_0076 b
  · exact g32p_row18_cosetBranchBlock_0077 b
  · exact g32p_row18_cosetBranchBlock_0078 b
  · exact g32p_row18_cosetBranchBlock_0079 b
  · exact g32p_row18_cosetBranchBlock_0080 b
  · exact g32p_row18_cosetBranchBlock_0081 b
  · exact g32p_row18_cosetBranchBlock_0082 b
  · exact g32p_row18_cosetBranchBlock_0083 b
  · exact g32p_row18_cosetBranchBlock_0084 b
  · exact g32p_row18_cosetBranchBlock_0085 b
  · exact g32p_row18_cosetBranchBlock_0086 b
  · exact g32p_row18_cosetBranchBlock_0087 b
  · exact g32p_row18_cosetBranchBlock_0088 b
  · exact g32p_row18_cosetBranchBlock_0089 b
  · exact g32p_row18_cosetBranchBlock_0090 b
  · exact g32p_row18_cosetBranchBlock_0091 b
  · exact g32p_row18_cosetBranchBlock_0092 b
  · exact g32p_row18_cosetBranchBlock_0093 b
  · exact g32p_row18_cosetBranchBlock_0094 b
  · exact g32p_row18_cosetBranchBlock_0095 b
  · exact g32p_row18_cosetBranchBlock_0096 b
  · exact g32p_row18_cosetBranchBlock_0097 b
  · exact g32p_row18_cosetBranchBlock_0098 b
  · exact g32p_row18_cosetBranchBlock_0099 b
  · exact g32p_row18_cosetBranchBlock_0100 b
  · exact g32p_row18_cosetBranchBlock_0101 b
  · exact g32p_row18_cosetBranchBlock_0102 b
  · exact g32p_row18_cosetBranchBlock_0103 b
  · exact g32p_row18_cosetBranchBlock_0104 b
  · exact g32p_row18_cosetBranchBlock_0105 b
  · exact g32p_row18_cosetBranchBlock_0106 b
  · exact g32p_row18_cosetBranchBlock_0107 b
  · exact g32p_row18_cosetBranchBlock_0108 b
  · exact g32p_row18_cosetBranchBlock_0109 b
  · exact g32p_row18_cosetBranchBlock_0110 b
  · exact g32p_row18_cosetBranchBlock_0111 b
  · exact g32p_row18_cosetBranchBlock_0112 b
  · exact g32p_row18_cosetBranchBlock_0113 b
  · exact g32p_row18_cosetBranchBlock_0114 b
  · exact g32p_row18_cosetBranchBlock_0115 b
  · exact g32p_row18_cosetBranchBlock_0116 b
  · exact g32p_row18_cosetBranchBlock_0117 b
  · exact g32p_row18_cosetBranchBlock_0118 b
  · exact g32p_row18_cosetBranchBlock_0119 b
  · exact g32p_row18_cosetBranchBlock_0120 b
  · exact g32p_row18_cosetBranchBlock_0121 b
  · exact g32p_row18_cosetBranchBlock_0122 b
  · exact g32p_row18_cosetBranchBlock_0123 b
  · exact g32p_row18_cosetBranchBlock_0124 b
  · exact g32p_row18_cosetBranchBlock_0125 b
  · exact g32p_row18_cosetBranchBlock_0126 b
  · exact g32p_row18_cosetBranchBlock_0127 b
  · exact g32p_row18_cosetBranchBlock_0128 b
  · exact g32p_row18_cosetBranchBlock_0129 b
  · exact g32p_row18_cosetBranchBlock_0130 b
  · exact g32p_row18_cosetBranchBlock_0131 b
  · exact g32p_row18_cosetBranchBlock_0132 b
  · exact g32p_row18_cosetBranchBlock_0133 b
  · exact g32p_row18_cosetBranchBlock_0134 b
  · exact g32p_row18_cosetBranchBlock_0135 b
  · exact g32p_row18_cosetBranchBlock_0136 b
  · exact g32p_row18_cosetBranchBlock_0137 b
  · exact g32p_row18_cosetBranchBlock_0138 b
  · exact g32p_row18_cosetBranchBlock_0139 b
  · exact g32p_row18_cosetBranchBlock_0140 b
  · exact g32p_row18_cosetBranchBlock_0141 b
  · exact g32p_row18_cosetBranchBlock_0142 b
  · exact g32p_row18_cosetBranchBlock_0143 b
  · exact g32p_row18_cosetBranchBlock_0144 b
  · exact g32p_row18_cosetBranchBlock_0145 b
  · exact g32p_row18_cosetBranchBlock_0146 b
  · exact g32p_row18_cosetBranchBlock_0147 b
  · exact g32p_row18_cosetBranchBlock_0148 b
  · exact g32p_row18_cosetBranchBlock_0149 b
  · exact g32p_row18_cosetBranchBlock_0150 b
  · exact g32p_row18_cosetBranchBlock_0151 b
  · exact g32p_row18_cosetBranchBlock_0152 b
  · exact g32p_row18_cosetBranchBlock_0153 b
  · exact g32p_row18_cosetBranchBlock_0154 b
  · exact g32p_row18_cosetBranchBlock_0155 b
  · exact g32p_row18_cosetBranchBlock_0156 b
  · exact g32p_row18_cosetBranchBlock_0157 b
  · exact g32p_row18_cosetBranchBlock_0158 b
  · exact g32p_row18_cosetBranchBlock_0159 b
  · exact g32p_row18_cosetBranchBlock_0160 b
  · exact g32p_row18_cosetBranchBlock_0161 b
  · exact g32p_row18_cosetBranchBlock_0162 b
  · exact g32p_row18_cosetBranchBlock_0163 b
  · exact g32p_row18_cosetBranchBlock_0164 b
  · exact g32p_row18_cosetBranchBlock_0165 b
  · exact g32p_row18_cosetBranchBlock_0166 b
  · exact g32p_row18_cosetBranchBlock_0167 b
  · exact g32p_row18_cosetBranchBlock_0168 b
  · exact g32p_row18_cosetBranchBlock_0169 b
  · exact g32p_row18_cosetBranchBlock_0170 b
  · exact g32p_row18_cosetBranchBlock_0171 b
  · exact g32p_row18_cosetBranchBlock_0172 b
  · exact g32p_row18_cosetBranchBlock_0173 b
  · exact g32p_row18_cosetBranchBlock_0174 b
  · exact g32p_row18_cosetBranchBlock_0175 b
  · exact g32p_row18_cosetBranchBlock_0176 b
  · exact g32p_row18_cosetBranchBlock_0177 b
  · exact g32p_row18_cosetBranchBlock_0178 b
  · exact g32p_row18_cosetBranchBlock_0179 b
  · exact g32p_row18_cosetBranchBlock_0180 b
  · exact g32p_row18_cosetBranchBlock_0181 b
  · exact g32p_row18_cosetBranchBlock_0182 b
  · exact g32p_row18_cosetBranchBlock_0183 b
  · exact g32p_row18_cosetBranchBlock_0184 b
  · exact g32p_row18_cosetBranchBlock_0185 b
  · exact g32p_row18_cosetBranchBlock_0186 b
  · exact g32p_row18_cosetBranchBlock_0187 b
  · exact g32p_row18_cosetBranchBlock_0188 b
  · exact g32p_row18_cosetBranchBlock_0189 b
  · exact g32p_row18_cosetBranchBlock_0190 b
  · exact g32p_row18_cosetBranchBlock_0191 b
  · exact g32p_row18_cosetBranchBlock_0192 b
  · exact g32p_row18_cosetBranchBlock_0193 b
  · exact g32p_row18_cosetBranchBlock_0194 b
  · exact g32p_row18_cosetBranchBlock_0195 b
  · exact g32p_row18_cosetBranchBlock_0196 b
  · exact g32p_row18_cosetBranchBlock_0197 b
  · exact g32p_row18_cosetBranchBlock_0198 b
  · exact g32p_row18_cosetBranchBlock_0199 b
  · exact g32p_row18_cosetBranchBlock_0200 b
  · exact g32p_row18_cosetBranchBlock_0201 b
  · exact g32p_row18_cosetBranchBlock_0202 b
  · exact g32p_row18_cosetBranchBlock_0203 b
  · exact g32p_row18_cosetBranchBlock_0204 b
  · exact g32p_row18_cosetBranchBlock_0205 b
  · exact g32p_row18_cosetBranchBlock_0206 b
  · exact g32p_row18_cosetBranchBlock_0207 b
  · exact g32p_row18_cosetBranchBlock_0208 b
  · exact g32p_row18_cosetBranchBlock_0209 b
  · exact g32p_row18_cosetBranchBlock_0210 b
  · exact g32p_row18_cosetBranchBlock_0211 b
  · exact g32p_row18_cosetBranchBlock_0212 b
  · exact g32p_row18_cosetBranchBlock_0213 b
  · exact g32p_row18_cosetBranchBlock_0214 b
  · exact g32p_row18_cosetBranchBlock_0215 b
  · exact g32p_row18_cosetBranchBlock_0216 b
  · exact g32p_row18_cosetBranchBlock_0217 b
  · exact g32p_row18_cosetBranchBlock_0218 b
  · exact g32p_row18_cosetBranchBlock_0219 b
  · exact g32p_row18_cosetBranchBlock_0220 b
  · exact g32p_row18_cosetBranchBlock_0221 b
  · exact g32p_row18_cosetBranchBlock_0222 b
  · exact g32p_row18_cosetBranchBlock_0223 b
  · exact g32p_row18_cosetBranchBlock_0224 b
  · exact g32p_row18_cosetBranchBlock_0225 b
  · exact g32p_row18_cosetBranchBlock_0226 b
  · exact g32p_row18_cosetBranchBlock_0227 b
  · exact g32p_row18_cosetBranchBlock_0228 b
  · exact g32p_row18_cosetBranchBlock_0229 b
  · exact g32p_row18_cosetBranchBlock_0230 b
  · exact g32p_row18_cosetBranchBlock_0231 b
  · exact g32p_row18_cosetBranchBlock_0232 b
  · exact g32p_row18_cosetBranchBlock_0233 b
  · exact g32p_row18_cosetBranchBlock_0234 b
  · exact g32p_row18_cosetBranchBlock_0235 b
  · exact g32p_row18_cosetBranchBlock_0236 b
  · exact g32p_row18_cosetBranchBlock_0237 b
  · exact g32p_row18_cosetBranchBlock_0238 b
  · exact g32p_row18_cosetBranchBlock_0239 b
  · exact g32p_row18_cosetBranchBlock_0240 b
  · exact g32p_row18_cosetBranchBlock_0241 b
  · exact g32p_row18_cosetBranchBlock_0242 b
  · exact g32p_row18_cosetBranchBlock_0243 b
  · exact g32p_row18_cosetBranchBlock_0244 b
  · exact g32p_row18_cosetBranchBlock_0245 b
  · exact g32p_row18_cosetBranchBlock_0246 b
  · exact g32p_row18_cosetBranchBlock_0247 b
  · exact g32p_row18_cosetBranchBlock_0248 b
  · exact g32p_row18_cosetBranchBlock_0249 b
  · exact g32p_row18_cosetBranchBlock_0250 b
  · exact g32p_row18_cosetBranchBlock_0251 b
  · exact g32p_row18_cosetBranchBlock_0252 b
  · exact g32p_row18_cosetBranchBlock_0253 b
  · exact g32p_row18_cosetBranchBlock_0254 b
  · exact g32p_row18_cosetBranchBlock_0255 b
  · exact g32p_row18_cosetBranchBlock_0256 b
  · exact g32p_row18_cosetBranchBlock_0257 b
  · exact g32p_row18_cosetBranchBlock_0258 b
  · exact g32p_row18_cosetBranchBlock_0259 b
  · exact g32p_row18_cosetBranchBlock_0260 b
  · exact g32p_row18_cosetBranchBlock_0261 b
  · exact g32p_row18_cosetBranchBlock_0262 b
  · exact g32p_row18_cosetBranchBlock_0263 b
  · exact g32p_row18_cosetBranchBlock_0264 b
  · exact g32p_row18_cosetBranchBlock_0265 b
  · exact g32p_row18_cosetBranchBlock_0266 b
  · exact g32p_row18_cosetBranchBlock_0267 b
  · exact g32p_row18_cosetBranchBlock_0268 b
  · exact g32p_row18_cosetBranchBlock_0269 b


theorem g32p_row18_cosetActualBranchStep (b : Fin 3) (i : Fin 4320) :
    g32p_cosetBranches b * g32p_row18_cosetActualRepresentatives i =
      g32p_row18_cosetActualRepresentatives (g32p_row18_cosetBranchNext b i) *
        (g32p_row18_groupEquiv (g32p_row18_cosetBranchFactor b i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_cosetBranches b * g32p_row18_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row18_cosetActualRepresentatives (g32p_row18_cosetBranchNext b i) *
      (g32p_row18_groupEquiv (g32p_row18_cosetBranchFactor b i) : g32p_G))
  rw [map_mul, map_mul, g32p_row18_cosetBranchMap, g32p_row18_cosetActualRepresentatives_map,
    g32p_row18_cosetActualRepresentatives_map, g32p_row18_groupEquiv_map,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add, g32p_row18_cosetBranchCheck]

theorem g32p_row18_cosetQuotientStep (b : Fin 3) (i : Fin 4320) :
    g32p_row18_cosetEquiv (g32p_row18_cosetBranchNext b i) = g32p_cosetBranches b • g32p_row18_cosetEquiv i := by
  change (QuotientGroup.mk (g32p_row18_cosetActualRepresentatives (g32p_row18_cosetBranchNext b i)) : g32p_G ⧸ g32p_row18_finiteSupplier.H) =
    g32p_cosetBranches b • (QuotientGroup.mk (g32p_row18_cosetActualRepresentatives i) : g32p_G ⧸ g32p_row18_finiteSupplier.H)
  rw [MulAction.Quotient.smul_coe, smul_eq_mul]
  apply QuotientGroup.eq.mpr
  rw [g32p_row18_cosetActualBranchStep, ← mul_assoc, inv_mul_cancel, one_mul]
  exact (g32p_row18_groupEquiv (g32p_row18_cosetBranchFactor b i)).property

def g32p_row18_cosetOrbitEquiv0 : Fin 1440 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 0)) (g32p_G ⧸ g32p_row18_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 0) g32p_row18_cosetEquiv
    (g32p_row18_cosetBranchNext 0) (g32p_row18_cosetQuotientStep 0) g32p_row18_cosetLabels0 g32p_row18_cosetRoots0
    g32p_row18_cosetDistances0 g32p_row18_cosetRootLabels0 g32p_row18_cosetNextLabels0 g32p_row18_cosetReach0)

theorem g32p_row18_cosetPeriod0 (j : Fin 1440) :
    Function.minimalPeriod ((g32p_cosetBranches 0) • ·) (g32p_row18_cosetEquiv (g32p_row18_cosetRoots0 j)) = g32p_row18_cosetLengths0 j := by
  apply g32p_period_of_cycle g32p_row18_cosetEquiv (g32p_row18_cosetBranchNext 0) ((g32p_cosetBranches 0) • ·)
    (g32p_row18_cosetQuotientStep 0) _ _ (g32p_row18_cosetPeriods0 j).1 (g32p_row18_cosetPeriods0 j).2.1
  intro t ht hlt
  exact (g32p_row18_cosetPeriods0 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row18_cosetMonodromyCheck0 (j : Fin 1440) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row18_cosetBranchMatrices 0) (g32p_row18_cosetLengths0 j))
      (g32p_row18_cosetRepresentatives (g32p_row18_cosetRoots0 j)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetRoots0 j))
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 j)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 j) = g32p_row18_cosetExponents0 j := by
  revert j
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row18_cosetMonodromyBlock0_0000
  · exact g32p_row18_cosetMonodromyBlock0_0001
  · exact g32p_row18_cosetMonodromyBlock0_0002
  · exact g32p_row18_cosetMonodromyBlock0_0003
  · exact g32p_row18_cosetMonodromyBlock0_0004
  · exact g32p_row18_cosetMonodromyBlock0_0005
  · exact g32p_row18_cosetMonodromyBlock0_0006
  · exact g32p_row18_cosetMonodromyBlock0_0007
  · exact g32p_row18_cosetMonodromyBlock0_0008
  · exact g32p_row18_cosetMonodromyBlock0_0009
  · exact g32p_row18_cosetMonodromyBlock0_0010
  · exact g32p_row18_cosetMonodromyBlock0_0011
  · exact g32p_row18_cosetMonodromyBlock0_0012
  · exact g32p_row18_cosetMonodromyBlock0_0013
  · exact g32p_row18_cosetMonodromyBlock0_0014
  · exact g32p_row18_cosetMonodromyBlock0_0015
  · exact g32p_row18_cosetMonodromyBlock0_0016
  · exact g32p_row18_cosetMonodromyBlock0_0017
  · exact g32p_row18_cosetMonodromyBlock0_0018
  · exact g32p_row18_cosetMonodromyBlock0_0019
  · exact g32p_row18_cosetMonodromyBlock0_0020
  · exact g32p_row18_cosetMonodromyBlock0_0021
  · exact g32p_row18_cosetMonodromyBlock0_0022
  · exact g32p_row18_cosetMonodromyBlock0_0023
  · exact g32p_row18_cosetMonodromyBlock0_0024
  · exact g32p_row18_cosetMonodromyBlock0_0025
  · exact g32p_row18_cosetMonodromyBlock0_0026
  · exact g32p_row18_cosetMonodromyBlock0_0027
  · exact g32p_row18_cosetMonodromyBlock0_0028
  · exact g32p_row18_cosetMonodromyBlock0_0029
  · exact g32p_row18_cosetMonodromyBlock0_0030
  · exact g32p_row18_cosetMonodromyBlock0_0031
  · exact g32p_row18_cosetMonodromyBlock0_0032
  · exact g32p_row18_cosetMonodromyBlock0_0033
  · exact g32p_row18_cosetMonodromyBlock0_0034
  · exact g32p_row18_cosetMonodromyBlock0_0035
  · exact g32p_row18_cosetMonodromyBlock0_0036
  · exact g32p_row18_cosetMonodromyBlock0_0037
  · exact g32p_row18_cosetMonodromyBlock0_0038
  · exact g32p_row18_cosetMonodromyBlock0_0039
  · exact g32p_row18_cosetMonodromyBlock0_0040
  · exact g32p_row18_cosetMonodromyBlock0_0041
  · exact g32p_row18_cosetMonodromyBlock0_0042
  · exact g32p_row18_cosetMonodromyBlock0_0043
  · exact g32p_row18_cosetMonodromyBlock0_0044
  · exact g32p_row18_cosetMonodromyBlock0_0045
  · exact g32p_row18_cosetMonodromyBlock0_0046
  · exact g32p_row18_cosetMonodromyBlock0_0047
  · exact g32p_row18_cosetMonodromyBlock0_0048
  · exact g32p_row18_cosetMonodromyBlock0_0049
  · exact g32p_row18_cosetMonodromyBlock0_0050
  · exact g32p_row18_cosetMonodromyBlock0_0051
  · exact g32p_row18_cosetMonodromyBlock0_0052
  · exact g32p_row18_cosetMonodromyBlock0_0053
  · exact g32p_row18_cosetMonodromyBlock0_0054
  · exact g32p_row18_cosetMonodromyBlock0_0055
  · exact g32p_row18_cosetMonodromyBlock0_0056
  · exact g32p_row18_cosetMonodromyBlock0_0057
  · exact g32p_row18_cosetMonodromyBlock0_0058
  · exact g32p_row18_cosetMonodromyBlock0_0059
  · exact g32p_row18_cosetMonodromyBlock0_0060
  · exact g32p_row18_cosetMonodromyBlock0_0061
  · exact g32p_row18_cosetMonodromyBlock0_0062
  · exact g32p_row18_cosetMonodromyBlock0_0063
  · exact g32p_row18_cosetMonodromyBlock0_0064
  · exact g32p_row18_cosetMonodromyBlock0_0065
  · exact g32p_row18_cosetMonodromyBlock0_0066
  · exact g32p_row18_cosetMonodromyBlock0_0067
  · exact g32p_row18_cosetMonodromyBlock0_0068
  · exact g32p_row18_cosetMonodromyBlock0_0069
  · exact g32p_row18_cosetMonodromyBlock0_0070
  · exact g32p_row18_cosetMonodromyBlock0_0071
  · exact g32p_row18_cosetMonodromyBlock0_0072
  · exact g32p_row18_cosetMonodromyBlock0_0073
  · exact g32p_row18_cosetMonodromyBlock0_0074
  · exact g32p_row18_cosetMonodromyBlock0_0075
  · exact g32p_row18_cosetMonodromyBlock0_0076
  · exact g32p_row18_cosetMonodromyBlock0_0077
  · exact g32p_row18_cosetMonodromyBlock0_0078
  · exact g32p_row18_cosetMonodromyBlock0_0079
  · exact g32p_row18_cosetMonodromyBlock0_0080
  · exact g32p_row18_cosetMonodromyBlock0_0081
  · exact g32p_row18_cosetMonodromyBlock0_0082
  · exact g32p_row18_cosetMonodromyBlock0_0083
  · exact g32p_row18_cosetMonodromyBlock0_0084
  · exact g32p_row18_cosetMonodromyBlock0_0085
  · exact g32p_row18_cosetMonodromyBlock0_0086
  · exact g32p_row18_cosetMonodromyBlock0_0087
  · exact g32p_row18_cosetMonodromyBlock0_0088
  · exact g32p_row18_cosetMonodromyBlock0_0089

theorem g32p_row18_cosetActualMonodromy0 (j : Fin 1440) :
    (g32p_cosetBranches 0) ^ g32p_row18_cosetLengths0 j * g32p_row18_cosetActualRepresentatives (g32p_row18_cosetRoots0 j) =
      g32p_row18_cosetActualRepresentatives (g32p_row18_cosetRoots0 j) *
        (g32p_row18_groupEquiv (g32p_row18_cosetMonodromies0 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row18_cosetBranchMatrices 0)
    (g32p_row18_cosetRepresentatives (g32p_row18_cosetRoots0 j))
    (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 j))
    (g32p_row18_cosetLengths0 j) (g32p_row18_cosetBranchMap 0)
    (g32p_row18_cosetActualRepresentatives_map _) (g32p_row18_groupEquiv_map _)
  exact (g32p_row18_cosetMonodromyCheck0 j).1

theorem g32p_row18_cosetCharacter0 (j : Fin 1440) :
    g32p_row18_finiteSupplier.χ (g32p_row18_groupEquiv (g32p_row18_cosetMonodromies0 j)) = g32p_row18_cosetExponents0 j := by
  rw [g32p_row18_finiteSupplier_value]
  exact (g32p_row18_cosetMonodromyCheck0 j).2

theorem g32p_row18_cosetBranchExponents0 :
    papersExps g32p_row18_finiteSupplier.H g32p_row18_finiteSupplier.χ (g32p_cosetBranches 0) =
      (Finset.univ.val.map (fun j : Fin 1440 => Multiplicative.toAdd (g32p_row18_cosetExponents0 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row18_cosetOrbitEquiv0
    (fun j => g32p_row18_cosetActualRepresentatives (g32p_row18_cosetRoots0 j)) (fun _ => rfl) g32p_row18_cosetLengths0 g32p_row18_cosetPeriod0
    (fun j => g32p_row18_groupEquiv (g32p_row18_cosetMonodromies0 j)) g32p_row18_cosetActualMonodromy0]
  simp only [g32p_row18_cosetCharacter0]
  rfl

def g32p_row18_cosetOrbitEquiv1 : Fin 1440 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 1)) (g32p_G ⧸ g32p_row18_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 1) g32p_row18_cosetEquiv
    (g32p_row18_cosetBranchNext 1) (g32p_row18_cosetQuotientStep 1) g32p_row18_cosetLabels1 g32p_row18_cosetRoots1
    g32p_row18_cosetDistances1 g32p_row18_cosetRootLabels1 g32p_row18_cosetNextLabels1 g32p_row18_cosetReach1)

theorem g32p_row18_cosetPeriod1 (j : Fin 1440) :
    Function.minimalPeriod ((g32p_cosetBranches 1) • ·) (g32p_row18_cosetEquiv (g32p_row18_cosetRoots1 j)) = g32p_row18_cosetLengths1 j := by
  apply g32p_period_of_cycle g32p_row18_cosetEquiv (g32p_row18_cosetBranchNext 1) ((g32p_cosetBranches 1) • ·)
    (g32p_row18_cosetQuotientStep 1) _ _ (g32p_row18_cosetPeriods1 j).1 (g32p_row18_cosetPeriods1 j).2.1
  intro t ht hlt
  exact (g32p_row18_cosetPeriods1 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row18_cosetMonodromyCheck1 (j : Fin 1440) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row18_cosetBranchMatrices 1) (g32p_row18_cosetLengths1 j))
      (g32p_row18_cosetRepresentatives (g32p_row18_cosetRoots1 j)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetRoots1 j))
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies1 j)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies1 j) = g32p_row18_cosetExponents1 j := by
  revert j
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row18_cosetMonodromyBlock1_0000
  · exact g32p_row18_cosetMonodromyBlock1_0001
  · exact g32p_row18_cosetMonodromyBlock1_0002
  · exact g32p_row18_cosetMonodromyBlock1_0003
  · exact g32p_row18_cosetMonodromyBlock1_0004
  · exact g32p_row18_cosetMonodromyBlock1_0005
  · exact g32p_row18_cosetMonodromyBlock1_0006
  · exact g32p_row18_cosetMonodromyBlock1_0007
  · exact g32p_row18_cosetMonodromyBlock1_0008
  · exact g32p_row18_cosetMonodromyBlock1_0009
  · exact g32p_row18_cosetMonodromyBlock1_0010
  · exact g32p_row18_cosetMonodromyBlock1_0011
  · exact g32p_row18_cosetMonodromyBlock1_0012
  · exact g32p_row18_cosetMonodromyBlock1_0013
  · exact g32p_row18_cosetMonodromyBlock1_0014
  · exact g32p_row18_cosetMonodromyBlock1_0015
  · exact g32p_row18_cosetMonodromyBlock1_0016
  · exact g32p_row18_cosetMonodromyBlock1_0017
  · exact g32p_row18_cosetMonodromyBlock1_0018
  · exact g32p_row18_cosetMonodromyBlock1_0019
  · exact g32p_row18_cosetMonodromyBlock1_0020
  · exact g32p_row18_cosetMonodromyBlock1_0021
  · exact g32p_row18_cosetMonodromyBlock1_0022
  · exact g32p_row18_cosetMonodromyBlock1_0023
  · exact g32p_row18_cosetMonodromyBlock1_0024
  · exact g32p_row18_cosetMonodromyBlock1_0025
  · exact g32p_row18_cosetMonodromyBlock1_0026
  · exact g32p_row18_cosetMonodromyBlock1_0027
  · exact g32p_row18_cosetMonodromyBlock1_0028
  · exact g32p_row18_cosetMonodromyBlock1_0029
  · exact g32p_row18_cosetMonodromyBlock1_0030
  · exact g32p_row18_cosetMonodromyBlock1_0031
  · exact g32p_row18_cosetMonodromyBlock1_0032
  · exact g32p_row18_cosetMonodromyBlock1_0033
  · exact g32p_row18_cosetMonodromyBlock1_0034
  · exact g32p_row18_cosetMonodromyBlock1_0035
  · exact g32p_row18_cosetMonodromyBlock1_0036
  · exact g32p_row18_cosetMonodromyBlock1_0037
  · exact g32p_row18_cosetMonodromyBlock1_0038
  · exact g32p_row18_cosetMonodromyBlock1_0039
  · exact g32p_row18_cosetMonodromyBlock1_0040
  · exact g32p_row18_cosetMonodromyBlock1_0041
  · exact g32p_row18_cosetMonodromyBlock1_0042
  · exact g32p_row18_cosetMonodromyBlock1_0043
  · exact g32p_row18_cosetMonodromyBlock1_0044
  · exact g32p_row18_cosetMonodromyBlock1_0045
  · exact g32p_row18_cosetMonodromyBlock1_0046
  · exact g32p_row18_cosetMonodromyBlock1_0047
  · exact g32p_row18_cosetMonodromyBlock1_0048
  · exact g32p_row18_cosetMonodromyBlock1_0049
  · exact g32p_row18_cosetMonodromyBlock1_0050
  · exact g32p_row18_cosetMonodromyBlock1_0051
  · exact g32p_row18_cosetMonodromyBlock1_0052
  · exact g32p_row18_cosetMonodromyBlock1_0053
  · exact g32p_row18_cosetMonodromyBlock1_0054
  · exact g32p_row18_cosetMonodromyBlock1_0055
  · exact g32p_row18_cosetMonodromyBlock1_0056
  · exact g32p_row18_cosetMonodromyBlock1_0057
  · exact g32p_row18_cosetMonodromyBlock1_0058
  · exact g32p_row18_cosetMonodromyBlock1_0059
  · exact g32p_row18_cosetMonodromyBlock1_0060
  · exact g32p_row18_cosetMonodromyBlock1_0061
  · exact g32p_row18_cosetMonodromyBlock1_0062
  · exact g32p_row18_cosetMonodromyBlock1_0063
  · exact g32p_row18_cosetMonodromyBlock1_0064
  · exact g32p_row18_cosetMonodromyBlock1_0065
  · exact g32p_row18_cosetMonodromyBlock1_0066
  · exact g32p_row18_cosetMonodromyBlock1_0067
  · exact g32p_row18_cosetMonodromyBlock1_0068
  · exact g32p_row18_cosetMonodromyBlock1_0069
  · exact g32p_row18_cosetMonodromyBlock1_0070
  · exact g32p_row18_cosetMonodromyBlock1_0071
  · exact g32p_row18_cosetMonodromyBlock1_0072
  · exact g32p_row18_cosetMonodromyBlock1_0073
  · exact g32p_row18_cosetMonodromyBlock1_0074
  · exact g32p_row18_cosetMonodromyBlock1_0075
  · exact g32p_row18_cosetMonodromyBlock1_0076
  · exact g32p_row18_cosetMonodromyBlock1_0077
  · exact g32p_row18_cosetMonodromyBlock1_0078
  · exact g32p_row18_cosetMonodromyBlock1_0079
  · exact g32p_row18_cosetMonodromyBlock1_0080
  · exact g32p_row18_cosetMonodromyBlock1_0081
  · exact g32p_row18_cosetMonodromyBlock1_0082
  · exact g32p_row18_cosetMonodromyBlock1_0083
  · exact g32p_row18_cosetMonodromyBlock1_0084
  · exact g32p_row18_cosetMonodromyBlock1_0085
  · exact g32p_row18_cosetMonodromyBlock1_0086
  · exact g32p_row18_cosetMonodromyBlock1_0087
  · exact g32p_row18_cosetMonodromyBlock1_0088
  · exact g32p_row18_cosetMonodromyBlock1_0089

theorem g32p_row18_cosetActualMonodromy1 (j : Fin 1440) :
    (g32p_cosetBranches 1) ^ g32p_row18_cosetLengths1 j * g32p_row18_cosetActualRepresentatives (g32p_row18_cosetRoots1 j) =
      g32p_row18_cosetActualRepresentatives (g32p_row18_cosetRoots1 j) *
        (g32p_row18_groupEquiv (g32p_row18_cosetMonodromies1 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row18_cosetBranchMatrices 1)
    (g32p_row18_cosetRepresentatives (g32p_row18_cosetRoots1 j))
    (g32p_row18_groupNodes (g32p_row18_cosetMonodromies1 j))
    (g32p_row18_cosetLengths1 j) (g32p_row18_cosetBranchMap 1)
    (g32p_row18_cosetActualRepresentatives_map _) (g32p_row18_groupEquiv_map _)
  exact (g32p_row18_cosetMonodromyCheck1 j).1

theorem g32p_row18_cosetCharacter1 (j : Fin 1440) :
    g32p_row18_finiteSupplier.χ (g32p_row18_groupEquiv (g32p_row18_cosetMonodromies1 j)) = g32p_row18_cosetExponents1 j := by
  rw [g32p_row18_finiteSupplier_value]
  exact (g32p_row18_cosetMonodromyCheck1 j).2

theorem g32p_row18_cosetBranchExponents1 :
    papersExps g32p_row18_finiteSupplier.H g32p_row18_finiteSupplier.χ (g32p_cosetBranches 1) =
      (Finset.univ.val.map (fun j : Fin 1440 => Multiplicative.toAdd (g32p_row18_cosetExponents1 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row18_cosetOrbitEquiv1
    (fun j => g32p_row18_cosetActualRepresentatives (g32p_row18_cosetRoots1 j)) (fun _ => rfl) g32p_row18_cosetLengths1 g32p_row18_cosetPeriod1
    (fun j => g32p_row18_groupEquiv (g32p_row18_cosetMonodromies1 j)) g32p_row18_cosetActualMonodromy1]
  simp only [g32p_row18_cosetCharacter1]
  rfl

def g32p_row18_cosetOrbitEquiv2 : Fin 2208 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 2)) (g32p_G ⧸ g32p_row18_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 2) g32p_row18_cosetEquiv
    (g32p_row18_cosetBranchNext 2) (g32p_row18_cosetQuotientStep 2) g32p_row18_cosetLabels2 g32p_row18_cosetRoots2
    g32p_row18_cosetDistances2 g32p_row18_cosetRootLabels2 g32p_row18_cosetNextLabels2 g32p_row18_cosetReach2)

theorem g32p_row18_cosetPeriod2 (j : Fin 2208) :
    Function.minimalPeriod ((g32p_cosetBranches 2) • ·) (g32p_row18_cosetEquiv (g32p_row18_cosetRoots2 j)) = g32p_row18_cosetLengths2 j := by
  apply g32p_period_of_cycle g32p_row18_cosetEquiv (g32p_row18_cosetBranchNext 2) ((g32p_cosetBranches 2) • ·)
    (g32p_row18_cosetQuotientStep 2) _ _ (g32p_row18_cosetPeriods2 j).1 (g32p_row18_cosetPeriods2 j).2.1
  intro t ht hlt
  exact (g32p_row18_cosetPeriods2 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row18_cosetMonodromyCheck2 (j : Fin 2208) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row18_cosetBranchMatrices 2) (g32p_row18_cosetLengths2 j))
      (g32p_row18_cosetRepresentatives (g32p_row18_cosetRoots2 j)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetRoots2 j))
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies2 j)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies2 j) = g32p_row18_cosetExponents2 j := by
  revert j
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row18_cosetMonodromyBlock2_0000
  · exact g32p_row18_cosetMonodromyBlock2_0001
  · exact g32p_row18_cosetMonodromyBlock2_0002
  · exact g32p_row18_cosetMonodromyBlock2_0003
  · exact g32p_row18_cosetMonodromyBlock2_0004
  · exact g32p_row18_cosetMonodromyBlock2_0005
  · exact g32p_row18_cosetMonodromyBlock2_0006
  · exact g32p_row18_cosetMonodromyBlock2_0007
  · exact g32p_row18_cosetMonodromyBlock2_0008
  · exact g32p_row18_cosetMonodromyBlock2_0009
  · exact g32p_row18_cosetMonodromyBlock2_0010
  · exact g32p_row18_cosetMonodromyBlock2_0011
  · exact g32p_row18_cosetMonodromyBlock2_0012
  · exact g32p_row18_cosetMonodromyBlock2_0013
  · exact g32p_row18_cosetMonodromyBlock2_0014
  · exact g32p_row18_cosetMonodromyBlock2_0015
  · exact g32p_row18_cosetMonodromyBlock2_0016
  · exact g32p_row18_cosetMonodromyBlock2_0017
  · exact g32p_row18_cosetMonodromyBlock2_0018
  · exact g32p_row18_cosetMonodromyBlock2_0019
  · exact g32p_row18_cosetMonodromyBlock2_0020
  · exact g32p_row18_cosetMonodromyBlock2_0021
  · exact g32p_row18_cosetMonodromyBlock2_0022
  · exact g32p_row18_cosetMonodromyBlock2_0023
  · exact g32p_row18_cosetMonodromyBlock2_0024
  · exact g32p_row18_cosetMonodromyBlock2_0025
  · exact g32p_row18_cosetMonodromyBlock2_0026
  · exact g32p_row18_cosetMonodromyBlock2_0027
  · exact g32p_row18_cosetMonodromyBlock2_0028
  · exact g32p_row18_cosetMonodromyBlock2_0029
  · exact g32p_row18_cosetMonodromyBlock2_0030
  · exact g32p_row18_cosetMonodromyBlock2_0031
  · exact g32p_row18_cosetMonodromyBlock2_0032
  · exact g32p_row18_cosetMonodromyBlock2_0033
  · exact g32p_row18_cosetMonodromyBlock2_0034
  · exact g32p_row18_cosetMonodromyBlock2_0035
  · exact g32p_row18_cosetMonodromyBlock2_0036
  · exact g32p_row18_cosetMonodromyBlock2_0037
  · exact g32p_row18_cosetMonodromyBlock2_0038
  · exact g32p_row18_cosetMonodromyBlock2_0039
  · exact g32p_row18_cosetMonodromyBlock2_0040
  · exact g32p_row18_cosetMonodromyBlock2_0041
  · exact g32p_row18_cosetMonodromyBlock2_0042
  · exact g32p_row18_cosetMonodromyBlock2_0043
  · exact g32p_row18_cosetMonodromyBlock2_0044
  · exact g32p_row18_cosetMonodromyBlock2_0045
  · exact g32p_row18_cosetMonodromyBlock2_0046
  · exact g32p_row18_cosetMonodromyBlock2_0047
  · exact g32p_row18_cosetMonodromyBlock2_0048
  · exact g32p_row18_cosetMonodromyBlock2_0049
  · exact g32p_row18_cosetMonodromyBlock2_0050
  · exact g32p_row18_cosetMonodromyBlock2_0051
  · exact g32p_row18_cosetMonodromyBlock2_0052
  · exact g32p_row18_cosetMonodromyBlock2_0053
  · exact g32p_row18_cosetMonodromyBlock2_0054
  · exact g32p_row18_cosetMonodromyBlock2_0055
  · exact g32p_row18_cosetMonodromyBlock2_0056
  · exact g32p_row18_cosetMonodromyBlock2_0057
  · exact g32p_row18_cosetMonodromyBlock2_0058
  · exact g32p_row18_cosetMonodromyBlock2_0059
  · exact g32p_row18_cosetMonodromyBlock2_0060
  · exact g32p_row18_cosetMonodromyBlock2_0061
  · exact g32p_row18_cosetMonodromyBlock2_0062
  · exact g32p_row18_cosetMonodromyBlock2_0063
  · exact g32p_row18_cosetMonodromyBlock2_0064
  · exact g32p_row18_cosetMonodromyBlock2_0065
  · exact g32p_row18_cosetMonodromyBlock2_0066
  · exact g32p_row18_cosetMonodromyBlock2_0067
  · exact g32p_row18_cosetMonodromyBlock2_0068
  · exact g32p_row18_cosetMonodromyBlock2_0069
  · exact g32p_row18_cosetMonodromyBlock2_0070
  · exact g32p_row18_cosetMonodromyBlock2_0071
  · exact g32p_row18_cosetMonodromyBlock2_0072
  · exact g32p_row18_cosetMonodromyBlock2_0073
  · exact g32p_row18_cosetMonodromyBlock2_0074
  · exact g32p_row18_cosetMonodromyBlock2_0075
  · exact g32p_row18_cosetMonodromyBlock2_0076
  · exact g32p_row18_cosetMonodromyBlock2_0077
  · exact g32p_row18_cosetMonodromyBlock2_0078
  · exact g32p_row18_cosetMonodromyBlock2_0079
  · exact g32p_row18_cosetMonodromyBlock2_0080
  · exact g32p_row18_cosetMonodromyBlock2_0081
  · exact g32p_row18_cosetMonodromyBlock2_0082
  · exact g32p_row18_cosetMonodromyBlock2_0083
  · exact g32p_row18_cosetMonodromyBlock2_0084
  · exact g32p_row18_cosetMonodromyBlock2_0085
  · exact g32p_row18_cosetMonodromyBlock2_0086
  · exact g32p_row18_cosetMonodromyBlock2_0087
  · exact g32p_row18_cosetMonodromyBlock2_0088
  · exact g32p_row18_cosetMonodromyBlock2_0089
  · exact g32p_row18_cosetMonodromyBlock2_0090
  · exact g32p_row18_cosetMonodromyBlock2_0091
  · exact g32p_row18_cosetMonodromyBlock2_0092
  · exact g32p_row18_cosetMonodromyBlock2_0093
  · exact g32p_row18_cosetMonodromyBlock2_0094
  · exact g32p_row18_cosetMonodromyBlock2_0095
  · exact g32p_row18_cosetMonodromyBlock2_0096
  · exact g32p_row18_cosetMonodromyBlock2_0097
  · exact g32p_row18_cosetMonodromyBlock2_0098
  · exact g32p_row18_cosetMonodromyBlock2_0099
  · exact g32p_row18_cosetMonodromyBlock2_0100
  · exact g32p_row18_cosetMonodromyBlock2_0101
  · exact g32p_row18_cosetMonodromyBlock2_0102
  · exact g32p_row18_cosetMonodromyBlock2_0103
  · exact g32p_row18_cosetMonodromyBlock2_0104
  · exact g32p_row18_cosetMonodromyBlock2_0105
  · exact g32p_row18_cosetMonodromyBlock2_0106
  · exact g32p_row18_cosetMonodromyBlock2_0107
  · exact g32p_row18_cosetMonodromyBlock2_0108
  · exact g32p_row18_cosetMonodromyBlock2_0109
  · exact g32p_row18_cosetMonodromyBlock2_0110
  · exact g32p_row18_cosetMonodromyBlock2_0111
  · exact g32p_row18_cosetMonodromyBlock2_0112
  · exact g32p_row18_cosetMonodromyBlock2_0113
  · exact g32p_row18_cosetMonodromyBlock2_0114
  · exact g32p_row18_cosetMonodromyBlock2_0115
  · exact g32p_row18_cosetMonodromyBlock2_0116
  · exact g32p_row18_cosetMonodromyBlock2_0117
  · exact g32p_row18_cosetMonodromyBlock2_0118
  · exact g32p_row18_cosetMonodromyBlock2_0119
  · exact g32p_row18_cosetMonodromyBlock2_0120
  · exact g32p_row18_cosetMonodromyBlock2_0121
  · exact g32p_row18_cosetMonodromyBlock2_0122
  · exact g32p_row18_cosetMonodromyBlock2_0123
  · exact g32p_row18_cosetMonodromyBlock2_0124
  · exact g32p_row18_cosetMonodromyBlock2_0125
  · exact g32p_row18_cosetMonodromyBlock2_0126
  · exact g32p_row18_cosetMonodromyBlock2_0127
  · exact g32p_row18_cosetMonodromyBlock2_0128
  · exact g32p_row18_cosetMonodromyBlock2_0129
  · exact g32p_row18_cosetMonodromyBlock2_0130
  · exact g32p_row18_cosetMonodromyBlock2_0131
  · exact g32p_row18_cosetMonodromyBlock2_0132
  · exact g32p_row18_cosetMonodromyBlock2_0133
  · exact g32p_row18_cosetMonodromyBlock2_0134
  · exact g32p_row18_cosetMonodromyBlock2_0135
  · exact g32p_row18_cosetMonodromyBlock2_0136
  · exact g32p_row18_cosetMonodromyBlock2_0137

theorem g32p_row18_cosetActualMonodromy2 (j : Fin 2208) :
    (g32p_cosetBranches 2) ^ g32p_row18_cosetLengths2 j * g32p_row18_cosetActualRepresentatives (g32p_row18_cosetRoots2 j) =
      g32p_row18_cosetActualRepresentatives (g32p_row18_cosetRoots2 j) *
        (g32p_row18_groupEquiv (g32p_row18_cosetMonodromies2 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row18_cosetBranchMatrices 2)
    (g32p_row18_cosetRepresentatives (g32p_row18_cosetRoots2 j))
    (g32p_row18_groupNodes (g32p_row18_cosetMonodromies2 j))
    (g32p_row18_cosetLengths2 j) (g32p_row18_cosetBranchMap 2)
    (g32p_row18_cosetActualRepresentatives_map _) (g32p_row18_groupEquiv_map _)
  exact (g32p_row18_cosetMonodromyCheck2 j).1

theorem g32p_row18_cosetCharacter2 (j : Fin 2208) :
    g32p_row18_finiteSupplier.χ (g32p_row18_groupEquiv (g32p_row18_cosetMonodromies2 j)) = g32p_row18_cosetExponents2 j := by
  rw [g32p_row18_finiteSupplier_value]
  exact (g32p_row18_cosetMonodromyCheck2 j).2

theorem g32p_row18_cosetBranchExponents2 :
    papersExps g32p_row18_finiteSupplier.H g32p_row18_finiteSupplier.χ (g32p_cosetBranches 2) =
      (Finset.univ.val.map (fun j : Fin 2208 => Multiplicative.toAdd (g32p_row18_cosetExponents2 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row18_cosetOrbitEquiv2
    (fun j => g32p_row18_cosetActualRepresentatives (g32p_row18_cosetRoots2 j)) (fun _ => rfl) g32p_row18_cosetLengths2 g32p_row18_cosetPeriod2
    (fun j => g32p_row18_groupEquiv (g32p_row18_cosetMonodromies2 j)) g32p_row18_cosetActualMonodromy2]
  simp only [g32p_row18_cosetCharacter2]
  rfl

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_exponents :
    (g32p_exponents g32p_row18_finiteSupplier).Perm (expandExps [(3, 96)]) := by
  have h0 : papersExps g32p_row18_finiteSupplier.H g32p_row18_finiteSupplier.χ (g32p_classDatum 0) = (([] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    change papersExps g32p_row18_finiteSupplier.H g32p_row18_finiteSupplier.χ (g32p_cosetBranches 0) = _
    rw [g32p_row18_cosetBranchExponents0]
    change ((Finset.univ : Finset (Fin 1440)).val.map
      (fun j => Multiplicative.toAdd (g32p_row18_cosetExponents0 j))).filter (· ≠ 0) = (([] : List (ZMod 6)) : Multiset (ZMod 6))
    decide +kernel
  have h1 : papersExps g32p_row18_finiteSupplier.H g32p_row18_finiteSupplier.χ (g32p_classDatum 6) = (([] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    change papersExps g32p_row18_finiteSupplier.H g32p_row18_finiteSupplier.χ (g32p_cosetBranches 1) = _
    rw [g32p_row18_cosetBranchExponents1]
    change ((Finset.univ : Finset (Fin 1440)).val.map
      (fun j => Multiplicative.toAdd (g32p_row18_cosetExponents1 j))).filter (· ≠ 0) = (([] : List (ZMod 6)) : Multiset (ZMod 6))
    decide +kernel
  have h2 : papersExps g32p_row18_finiteSupplier.H g32p_row18_finiteSupplier.χ (g32p_classDatum 12) = (([3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    change papersExps g32p_row18_finiteSupplier.H g32p_row18_finiteSupplier.χ (g32p_cosetBranches 2) = _
    rw [g32p_row18_cosetBranchExponents2]
    change ((Finset.univ : Finset (Fin 2208)).val.map
      (fun j => Multiplicative.toAdd (g32p_row18_cosetExponents2 j))).filter (· ≠ 0) = (([3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : List (ZMod 6)) : Multiset (ZMod 6))
    decide +kernel
  have hs : papersExpsTuple g32p_row18_finiteSupplier.H g32p_row18_finiteSupplier.χ g32p_classList =
      6 • (([] : List (ZMod 6)) : Multiset (ZMod 6)) + 6 • (([] : List (ZMod 6)) : Multiset (ZMod 6)) + (([3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    have hc : g32p_classList = List.replicate 6 (g32p_classDatum 0) ++
        List.replicate 6 (g32p_classDatum 6) ++ [g32p_classDatum 12] := rfl
    simp only [papersExpsTuple, hc, List.map_append, List.map_replicate,
      List.map_cons, List.map_nil, List.sum_append, List.sum_replicate,
      List.sum_cons, List.sum_nil, List.sum_singleton, h0, h1, h2, add_zero]
    rfl
  apply Multiset.coe_eq_coe.mp
  change (((papersExpsTuple _ _ _).map ZMod.val).toList : Multiset ℕ) = _
  rw [Multiset.coe_toList, hs]
  change (6 • (([] : List (ZMod 6)) : Multiset (ZMod 6)) + 6 • (([] : List (ZMod 6)) : Multiset (ZMod 6)) + (([3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : List (ZMod 6)) : Multiset (ZMod 6))).map ZMod.val = ↑(expandExps [(3, 96)])
  decide +kernel

theorem g32p_row18_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 18 ∧ r.m = g32p_row18_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row18_finiteSupplier.H ∧
      (g32p_exponents g32p_row18_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨18, (-1), 36, 6, 14017, 96, 28128, some 3, [(3, 96)], .S⟩, ?_, rfl, rfl, g32p_row18_finiteSupplier_order.symm, g32p_row18_exponents⟩
  decide

def g32p_row18_complexWitness : g32p_row18_finiteSupplier.H →* ℂˣ := g32p_complexCharacter g32p_row18_finiteSupplier

theorem g32p_row18_supplierWitness :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 18 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) := by
  exact ⟨g32p_row18_finiteSupplier, g32p_row18_complexWitness, g32p_complexCharacter_apply _,
    g32p_row18_finiteSupplier_table⟩

end HodgeLean.Foundations.Program

end
end
