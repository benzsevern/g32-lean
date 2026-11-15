import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0971
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness42CosetData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0629
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow42
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row42_cosetWord_0256 :
    g32p_archiveIntegralWord (g32p_row42_cosetWords 256) = g32p_row42_cosetRepresentatives 256 := by
  decide +kernel

theorem g32p_row42_cosetGeneratorStep_0256 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives 256) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s 256))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s 256)) := by
  decide +kernel

theorem g32p_row42_cosetBranchStep_0256 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices s) (g32p_row42_cosetRepresentatives 256) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetBranchNext s 256))
        (g32p_row26_groupNodes (g32p_row42_cosetBranchFactor s 256)) := by
  decide +kernel

theorem g32p_row42_cosetWord_0257 :
    g32p_archiveIntegralWord (g32p_row42_cosetWords 257) = g32p_row42_cosetRepresentatives 257 := by
  decide +kernel

theorem g32p_row42_cosetGeneratorStep_0257 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives 257) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s 257))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s 257)) := by
  decide +kernel

theorem g32p_row42_cosetBranchStep_0257 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices s) (g32p_row42_cosetRepresentatives 257) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetBranchNext s 257))
        (g32p_row26_groupNodes (g32p_row42_cosetBranchFactor s 257)) := by
  decide +kernel

theorem g32p_row42_cosetWord_0258 :
    g32p_archiveIntegralWord (g32p_row42_cosetWords 258) = g32p_row42_cosetRepresentatives 258 := by
  decide +kernel

theorem g32p_row42_cosetGeneratorStep_0258 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives 258) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s 258))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s 258)) := by
  decide +kernel

theorem g32p_row42_cosetBranchStep_0258 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices s) (g32p_row42_cosetRepresentatives 258) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetBranchNext s 258))
        (g32p_row26_groupNodes (g32p_row42_cosetBranchFactor s 258)) := by
  decide +kernel

theorem g32p_row42_cosetWord_0259 :
    g32p_archiveIntegralWord (g32p_row42_cosetWords 259) = g32p_row42_cosetRepresentatives 259 := by
  decide +kernel

theorem g32p_row42_cosetGeneratorStep_0259 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives 259) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s 259))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s 259)) := by
  decide +kernel

theorem g32p_row42_cosetBranchStep_0259 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices s) (g32p_row42_cosetRepresentatives 259) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetBranchNext s 259))
        (g32p_row26_groupNodes (g32p_row42_cosetBranchFactor s 259)) := by
  decide +kernel

theorem g32p_row42_cosetWord_0260 :
    g32p_archiveIntegralWord (g32p_row42_cosetWords 260) = g32p_row42_cosetRepresentatives 260 := by
  decide +kernel

theorem g32p_row42_cosetGeneratorStep_0260 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives 260) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s 260))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s 260)) := by
  decide +kernel

theorem g32p_row42_cosetBranchStep_0260 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices s) (g32p_row42_cosetRepresentatives 260) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetBranchNext s 260))
        (g32p_row26_groupNodes (g32p_row42_cosetBranchFactor s 260)) := by
  decide +kernel

theorem g32p_row42_cosetWord_0261 :
    g32p_archiveIntegralWord (g32p_row42_cosetWords 261) = g32p_row42_cosetRepresentatives 261 := by
  decide +kernel

theorem g32p_row42_cosetGeneratorStep_0261 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives 261) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s 261))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s 261)) := by
  decide +kernel

theorem g32p_row42_cosetBranchStep_0261 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices s) (g32p_row42_cosetRepresentatives 261) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetBranchNext s 261))
        (g32p_row26_groupNodes (g32p_row42_cosetBranchFactor s 261)) := by
  decide +kernel

theorem g32p_row42_cosetWord_0262 :
    g32p_archiveIntegralWord (g32p_row42_cosetWords 262) = g32p_row42_cosetRepresentatives 262 := by
  decide +kernel

theorem g32p_row42_cosetGeneratorStep_0262 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives 262) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s 262))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s 262)) := by
  decide +kernel

theorem g32p_row42_cosetBranchStep_0262 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices s) (g32p_row42_cosetRepresentatives 262) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetBranchNext s 262))
        (g32p_row26_groupNodes (g32p_row42_cosetBranchFactor s 262)) := by
  decide +kernel

theorem g32p_row42_cosetWord_0263 :
    g32p_archiveIntegralWord (g32p_row42_cosetWords 263) = g32p_row42_cosetRepresentatives 263 := by
  decide +kernel

theorem g32p_row42_cosetGeneratorStep_0263 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives 263) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s 263))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s 263)) := by
  decide +kernel

theorem g32p_row42_cosetBranchStep_0263 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices s) (g32p_row42_cosetRepresentatives 263) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetBranchNext s 263))
        (g32p_row26_groupNodes (g32p_row42_cosetBranchFactor s 263)) := by
  decide +kernel

theorem g32p_row42_cosetWord_0264 :
    g32p_archiveIntegralWord (g32p_row42_cosetWords 264) = g32p_row42_cosetRepresentatives 264 := by
  decide +kernel

theorem g32p_row42_cosetGeneratorStep_0264 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives 264) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s 264))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s 264)) := by
  decide +kernel

theorem g32p_row42_cosetBranchStep_0264 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices s) (g32p_row42_cosetRepresentatives 264) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetBranchNext s 264))
        (g32p_row26_groupNodes (g32p_row42_cosetBranchFactor s 264)) := by
  decide +kernel

theorem g32p_row42_cosetWord_0265 :
    g32p_archiveIntegralWord (g32p_row42_cosetWords 265) = g32p_row42_cosetRepresentatives 265 := by
  decide +kernel

theorem g32p_row42_cosetGeneratorStep_0265 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives 265) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s 265))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s 265)) := by
  decide +kernel

theorem g32p_row42_cosetBranchStep_0265 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices s) (g32p_row42_cosetRepresentatives 265) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetBranchNext s 265))
        (g32p_row26_groupNodes (g32p_row42_cosetBranchFactor s 265)) := by
  decide +kernel

theorem g32p_row42_cosetWord_0266 :
    g32p_archiveIntegralWord (g32p_row42_cosetWords 266) = g32p_row42_cosetRepresentatives 266 := by
  decide +kernel

theorem g32p_row42_cosetGeneratorStep_0266 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives 266) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s 266))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s 266)) := by
  decide +kernel

theorem g32p_row42_cosetBranchStep_0266 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices s) (g32p_row42_cosetRepresentatives 266) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetBranchNext s 266))
        (g32p_row26_groupNodes (g32p_row42_cosetBranchFactor s 266)) := by
  decide +kernel

theorem g32p_row42_cosetWord_0267 :
    g32p_archiveIntegralWord (g32p_row42_cosetWords 267) = g32p_row42_cosetRepresentatives 267 := by
  decide +kernel

theorem g32p_row42_cosetGeneratorStep_0267 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives 267) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s 267))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s 267)) := by
  decide +kernel

theorem g32p_row42_cosetBranchStep_0267 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices s) (g32p_row42_cosetRepresentatives 267) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetBranchNext s 267))
        (g32p_row26_groupNodes (g32p_row42_cosetBranchFactor s 267)) := by
  decide +kernel

theorem g32p_row42_cosetWord_0268 :
    g32p_archiveIntegralWord (g32p_row42_cosetWords 268) = g32p_row42_cosetRepresentatives 268 := by
  decide +kernel

theorem g32p_row42_cosetGeneratorStep_0268 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives 268) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s 268))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s 268)) := by
  decide +kernel

theorem g32p_row42_cosetBranchStep_0268 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices s) (g32p_row42_cosetRepresentatives 268) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetBranchNext s 268))
        (g32p_row26_groupNodes (g32p_row42_cosetBranchFactor s 268)) := by
  decide +kernel

theorem g32p_row42_cosetWord_0269 :
    g32p_archiveIntegralWord (g32p_row42_cosetWords 269) = g32p_row42_cosetRepresentatives 269 := by
  decide +kernel

theorem g32p_row42_cosetGeneratorStep_0269 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives 269) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s 269))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s 269)) := by
  decide +kernel

theorem g32p_row42_cosetBranchStep_0269 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices s) (g32p_row42_cosetRepresentatives 269) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetBranchNext s 269))
        (g32p_row26_groupNodes (g32p_row42_cosetBranchFactor s 269)) := by
  decide +kernel

theorem g32p_row42_cosetWordBlock_0016 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row42_cosetWords (g32p_finBlockIndex 270 16 r)) = g32p_row42_cosetRepresentatives (g32p_finBlockIndex 270 16 r) := by
  fin_cases r
  · exact g32p_row42_cosetWord_0256
  · exact g32p_row42_cosetWord_0257
  · exact g32p_row42_cosetWord_0258
  · exact g32p_row42_cosetWord_0259
  · exact g32p_row42_cosetWord_0260
  · exact g32p_row42_cosetWord_0261
  · exact g32p_row42_cosetWord_0262
  · exact g32p_row42_cosetWord_0263
  · exact g32p_row42_cosetWord_0264
  · exact g32p_row42_cosetWord_0265
  · exact g32p_row42_cosetWord_0266
  · exact g32p_row42_cosetWord_0267
  · exact g32p_row42_cosetWord_0268
  · exact g32p_row42_cosetWord_0269
  · exact g32p_row42_cosetWord_0000
  · exact g32p_row42_cosetWord_0001

theorem g32p_row42_cosetGeneratorBlock_0016 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives (g32p_finBlockIndex 270 16 r)) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s (g32p_finBlockIndex 270 16 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s (g32p_finBlockIndex 270 16 r))) := by
  fin_cases r
  · exact g32p_row42_cosetGeneratorStep_0256 s
  · exact g32p_row42_cosetGeneratorStep_0257 s
  · exact g32p_row42_cosetGeneratorStep_0258 s
  · exact g32p_row42_cosetGeneratorStep_0259 s
  · exact g32p_row42_cosetGeneratorStep_0260 s
  · exact g32p_row42_cosetGeneratorStep_0261 s
  · exact g32p_row42_cosetGeneratorStep_0262 s
  · exact g32p_row42_cosetGeneratorStep_0263 s
  · exact g32p_row42_cosetGeneratorStep_0264 s
  · exact g32p_row42_cosetGeneratorStep_0265 s
  · exact g32p_row42_cosetGeneratorStep_0266 s
  · exact g32p_row42_cosetGeneratorStep_0267 s
  · exact g32p_row42_cosetGeneratorStep_0268 s
  · exact g32p_row42_cosetGeneratorStep_0269 s
  · exact g32p_row42_cosetGeneratorStep_0000 s
  · exact g32p_row42_cosetGeneratorStep_0001 s

theorem g32p_row42_cosetBranchBlock_0016 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices s) (g32p_row42_cosetRepresentatives (g32p_finBlockIndex 270 16 r)) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetBranchNext s (g32p_finBlockIndex 270 16 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetBranchFactor s (g32p_finBlockIndex 270 16 r))) := by
  fin_cases r
  · exact g32p_row42_cosetBranchStep_0256 s
  · exact g32p_row42_cosetBranchStep_0257 s
  · exact g32p_row42_cosetBranchStep_0258 s
  · exact g32p_row42_cosetBranchStep_0259 s
  · exact g32p_row42_cosetBranchStep_0260 s
  · exact g32p_row42_cosetBranchStep_0261 s
  · exact g32p_row42_cosetBranchStep_0262 s
  · exact g32p_row42_cosetBranchStep_0263 s
  · exact g32p_row42_cosetBranchStep_0264 s
  · exact g32p_row42_cosetBranchStep_0265 s
  · exact g32p_row42_cosetBranchStep_0266 s
  · exact g32p_row42_cosetBranchStep_0267 s
  · exact g32p_row42_cosetBranchStep_0268 s
  · exact g32p_row42_cosetBranchStep_0269 s
  · exact g32p_row42_cosetBranchStep_0000 s
  · exact g32p_row42_cosetBranchStep_0001 s


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_row42_cosetWord (i : Fin 270) :
    g32p_archiveIntegralWord (g32p_row42_cosetWords i) = g32p_row42_cosetRepresentatives i := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row42_cosetWordBlock_0000
  · exact g32p_row42_cosetWordBlock_0001
  · exact g32p_row42_cosetWordBlock_0002
  · exact g32p_row42_cosetWordBlock_0003
  · exact g32p_row42_cosetWordBlock_0004
  · exact g32p_row42_cosetWordBlock_0005
  · exact g32p_row42_cosetWordBlock_0006
  · exact g32p_row42_cosetWordBlock_0007
  · exact g32p_row42_cosetWordBlock_0008
  · exact g32p_row42_cosetWordBlock_0009
  · exact g32p_row42_cosetWordBlock_0010
  · exact g32p_row42_cosetWordBlock_0011
  · exact g32p_row42_cosetWordBlock_0012
  · exact g32p_row42_cosetWordBlock_0013
  · exact g32p_row42_cosetWordBlock_0014
  · exact g32p_row42_cosetWordBlock_0015
  · exact g32p_row42_cosetWordBlock_0016


def g32p_row42_cosetActualRepresentatives (i : Fin 270) : g32p_G := g32p_archiveWord (g32p_row42_cosetWords i)

theorem g32p_row42_cosetActualRepresentatives_map (i : Fin 270) :
    b4b_toMatrix (g32p_row42_cosetActualRepresentatives i) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row42_cosetRepresentatives i)) := by
  rw [g32p_row42_cosetActualRepresentatives, g32p_archiveIntegralWord_map, g32p_row42_cosetWord]

theorem g32p_row42_cosetGeneratorStep (s : Fin 4) (i : Fin 270) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row42_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetGeneratorNext s i))
        (g32p_row26_groupNodes (g32p_row42_cosetGeneratorFactor s i)) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row42_cosetGeneratorBlock_0000 s
  · exact g32p_row42_cosetGeneratorBlock_0001 s
  · exact g32p_row42_cosetGeneratorBlock_0002 s
  · exact g32p_row42_cosetGeneratorBlock_0003 s
  · exact g32p_row42_cosetGeneratorBlock_0004 s
  · exact g32p_row42_cosetGeneratorBlock_0005 s
  · exact g32p_row42_cosetGeneratorBlock_0006 s
  · exact g32p_row42_cosetGeneratorBlock_0007 s
  · exact g32p_row42_cosetGeneratorBlock_0008 s
  · exact g32p_row42_cosetGeneratorBlock_0009 s
  · exact g32p_row42_cosetGeneratorBlock_0010 s
  · exact g32p_row42_cosetGeneratorBlock_0011 s
  · exact g32p_row42_cosetGeneratorBlock_0012 s
  · exact g32p_row42_cosetGeneratorBlock_0013 s
  · exact g32p_row42_cosetGeneratorBlock_0014 s
  · exact g32p_row42_cosetGeneratorBlock_0015 s
  · exact g32p_row42_cosetGeneratorBlock_0016 s


theorem g32p_row42_cosetActualStep (s : Fin 4) (i : Fin 270) :
    g32p_word (g32p_archiveWords s) * g32p_row42_cosetActualRepresentatives i =
      g32p_row42_cosetActualRepresentatives (g32p_row42_cosetGeneratorNext s i) *
        (g32p_row26_groupEquiv (g32p_row42_cosetGeneratorFactor s i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_word (g32p_archiveWords s) * g32p_row42_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row42_cosetActualRepresentatives (g32p_row42_cosetGeneratorNext s i) *
      (g32p_row26_groupEquiv (g32p_row42_cosetGeneratorFactor s i) : g32p_G))
  rw [map_mul, map_mul, g32p_row42_cosetActualRepresentatives_map,
    g32p_row42_cosetActualRepresentatives_map, g32p_row26_groupEquiv_map,
    g32p_integralWord_map, g32p_archiveWordIntegral,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    g32p_row42_cosetGeneratorStep]

theorem g32p_row42_cosetEnumeration :
    Function.Bijective (fun i => (QuotientGroup.mk (g32p_row42_cosetActualRepresentatives i) :
      g32p_G ⧸ g32p_row42_finiteSupplier.H)) := by
  apply g32p_coset_bijective
  · apply g32p_coset_surjective _ _ g32p_archive_generators_top _ 0 (by rfl)
      g32p_row42_cosetGeneratorNext
      (fun s i => g32p_row26_groupEquiv (g32p_row42_cosetGeneratorFactor s i))
    exact g32p_row42_cosetActualStep
  · rw [g32p_row42_finiteSupplier_order]
    have hg : Nat.card g32p_G = 155520 :=
      (Nat.card_coe_set_eq (g32h_G : Set (Matrix (Fin 4) (Fin 4) ℂ))).trans
        HurwitzPrymRex_g32_ncard
    rw [hg]


end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row42_cosetMonodromy_0_0000 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 0)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 0)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 0) = g32p_row42_cosetExponents0 0 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0001 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 1)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 1)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 1) = g32p_row42_cosetExponents0 1 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0002 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 2)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 2)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 2) = g32p_row42_cosetExponents0 2 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0003 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 3)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 3)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 3) = g32p_row42_cosetExponents0 3 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0004 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 4)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 4)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 4) = g32p_row42_cosetExponents0 4 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0005 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 5)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 5)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 5) = g32p_row42_cosetExponents0 5 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0006 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 6)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 6)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 6) = g32p_row42_cosetExponents0 6 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0007 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 7)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 7)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 7) = g32p_row42_cosetExponents0 7 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0008 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 8)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 8)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 8) = g32p_row42_cosetExponents0 8 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0009 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 9)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 9)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 9) = g32p_row42_cosetExponents0 9 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0010 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 10)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 10)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 10) = g32p_row42_cosetExponents0 10 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0011 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 11)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 11)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 11) = g32p_row42_cosetExponents0 11 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0012 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 12)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 12)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 12) = g32p_row42_cosetExponents0 12 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0013 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 13)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 13)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 13) = g32p_row42_cosetExponents0 13 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0014 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 14)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 14)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 14) = g32p_row42_cosetExponents0 14 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0015 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 15)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 15)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 15) = g32p_row42_cosetExponents0 15 := by
  decide +kernel

theorem g32p_row42_cosetMonodromyBlock0_0000 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row42_cosetBranchMatrices 0) (g32p_row42_cosetLengths0 (g32p_finBlockIndex 108 0 r)))
      (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots0 (g32p_finBlockIndex 108 0 r))) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots0 (g32p_finBlockIndex 108 0 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 (g32p_finBlockIndex 108 0 r))) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 (g32p_finBlockIndex 108 0 r)) = g32p_row42_cosetExponents0 (g32p_finBlockIndex 108 0 r) := by
  fin_cases r
  · exact g32p_row42_cosetMonodromy_0_0000
  · exact g32p_row42_cosetMonodromy_0_0001
  · exact g32p_row42_cosetMonodromy_0_0002
  · exact g32p_row42_cosetMonodromy_0_0003
  · exact g32p_row42_cosetMonodromy_0_0004
  · exact g32p_row42_cosetMonodromy_0_0005
  · exact g32p_row42_cosetMonodromy_0_0006
  · exact g32p_row42_cosetMonodromy_0_0007
  · exact g32p_row42_cosetMonodromy_0_0008
  · exact g32p_row42_cosetMonodromy_0_0009
  · exact g32p_row42_cosetMonodromy_0_0010
  · exact g32p_row42_cosetMonodromy_0_0011
  · exact g32p_row42_cosetMonodromy_0_0012
  · exact g32p_row42_cosetMonodromy_0_0013
  · exact g32p_row42_cosetMonodromy_0_0014
  · exact g32p_row42_cosetMonodromy_0_0015


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row42_cosetMonodromy_0_0016 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 16)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 16)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 16) = g32p_row42_cosetExponents0 16 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0017 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 17)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 17)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 17) = g32p_row42_cosetExponents0 17 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0018 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 18) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 18)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 18)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 18) = g32p_row42_cosetExponents0 18 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0019 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 19) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 19)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 19)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 19) = g32p_row42_cosetExponents0 19 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0020 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 22) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 22)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 20)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 20) = g32p_row42_cosetExponents0 20 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0021 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 23) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 23)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 21)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 21) = g32p_row42_cosetExponents0 21 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0022 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 24)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 22)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 22) = g32p_row42_cosetExponents0 22 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0023 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 25)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 23)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 23) = g32p_row42_cosetExponents0 23 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0024 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 26)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 24)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 24) = g32p_row42_cosetExponents0 24 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0025 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 27) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 27)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 25)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 25) = g32p_row42_cosetExponents0 25 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0026 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 28) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 28)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 26)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 26) = g32p_row42_cosetExponents0 26 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0027 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 29)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 27)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 27) = g32p_row42_cosetExponents0 27 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0028 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 30) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 30)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 28)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 28) = g32p_row42_cosetExponents0 28 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0029 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 31)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 29)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 29) = g32p_row42_cosetExponents0 29 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0030 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 32)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 30)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 30) = g32p_row42_cosetExponents0 30 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0031 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 33) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 33)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 31)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 31) = g32p_row42_cosetExponents0 31 := by
  decide +kernel

theorem g32p_row42_cosetMonodromyBlock0_0001 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row42_cosetBranchMatrices 0) (g32p_row42_cosetLengths0 (g32p_finBlockIndex 108 1 r)))
      (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots0 (g32p_finBlockIndex 108 1 r))) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots0 (g32p_finBlockIndex 108 1 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 (g32p_finBlockIndex 108 1 r))) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 (g32p_finBlockIndex 108 1 r)) = g32p_row42_cosetExponents0 (g32p_finBlockIndex 108 1 r) := by
  fin_cases r
  · exact g32p_row42_cosetMonodromy_0_0016
  · exact g32p_row42_cosetMonodromy_0_0017
  · exact g32p_row42_cosetMonodromy_0_0018
  · exact g32p_row42_cosetMonodromy_0_0019
  · exact g32p_row42_cosetMonodromy_0_0020
  · exact g32p_row42_cosetMonodromy_0_0021
  · exact g32p_row42_cosetMonodromy_0_0022
  · exact g32p_row42_cosetMonodromy_0_0023
  · exact g32p_row42_cosetMonodromy_0_0024
  · exact g32p_row42_cosetMonodromy_0_0025
  · exact g32p_row42_cosetMonodromy_0_0026
  · exact g32p_row42_cosetMonodromy_0_0027
  · exact g32p_row42_cosetMonodromy_0_0028
  · exact g32p_row42_cosetMonodromy_0_0029
  · exact g32p_row42_cosetMonodromy_0_0030
  · exact g32p_row42_cosetMonodromy_0_0031


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row42_cosetMonodromy_0_0032 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 34) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 34)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 32)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 32) = g32p_row42_cosetExponents0 32 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0033 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 35) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 35)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 33)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 33) = g32p_row42_cosetExponents0 33 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0034 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 36) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 36)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 34)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 34) = g32p_row42_cosetExponents0 34 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0035 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 37) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 37)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 35)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 35) = g32p_row42_cosetExponents0 35 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0036 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 40) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 40)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 36)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 36) = g32p_row42_cosetExponents0 36 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0037 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 41) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 41)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 37)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 37) = g32p_row42_cosetExponents0 37 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0038 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 42) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 42)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 38)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 38) = g32p_row42_cosetExponents0 38 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0039 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 43) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 43)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 39)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 39) = g32p_row42_cosetExponents0 39 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0040 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 44) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 44)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 40)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 40) = g32p_row42_cosetExponents0 40 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0041 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 45) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 45)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 41)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 41) = g32p_row42_cosetExponents0 41 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0042 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 46) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 46)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 42)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 42) = g32p_row42_cosetExponents0 42 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0043 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 47) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 47)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 43)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 43) = g32p_row42_cosetExponents0 43 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0044 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 48) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 48)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 44)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 44) = g32p_row42_cosetExponents0 44 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0045 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 49) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 49)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 45)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 45) = g32p_row42_cosetExponents0 45 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0046 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 56) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 56)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 46)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 46) = g32p_row42_cosetExponents0 46 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0047 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 61) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 61)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 47)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 47) = g32p_row42_cosetExponents0 47 := by
  decide +kernel

theorem g32p_row42_cosetMonodromyBlock0_0002 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row42_cosetBranchMatrices 0) (g32p_row42_cosetLengths0 (g32p_finBlockIndex 108 2 r)))
      (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots0 (g32p_finBlockIndex 108 2 r))) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots0 (g32p_finBlockIndex 108 2 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 (g32p_finBlockIndex 108 2 r))) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 (g32p_finBlockIndex 108 2 r)) = g32p_row42_cosetExponents0 (g32p_finBlockIndex 108 2 r) := by
  fin_cases r
  · exact g32p_row42_cosetMonodromy_0_0032
  · exact g32p_row42_cosetMonodromy_0_0033
  · exact g32p_row42_cosetMonodromy_0_0034
  · exact g32p_row42_cosetMonodromy_0_0035
  · exact g32p_row42_cosetMonodromy_0_0036
  · exact g32p_row42_cosetMonodromy_0_0037
  · exact g32p_row42_cosetMonodromy_0_0038
  · exact g32p_row42_cosetMonodromy_0_0039
  · exact g32p_row42_cosetMonodromy_0_0040
  · exact g32p_row42_cosetMonodromy_0_0041
  · exact g32p_row42_cosetMonodromy_0_0042
  · exact g32p_row42_cosetMonodromy_0_0043
  · exact g32p_row42_cosetMonodromy_0_0044
  · exact g32p_row42_cosetMonodromy_0_0045
  · exact g32p_row42_cosetMonodromy_0_0046
  · exact g32p_row42_cosetMonodromy_0_0047


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row42_cosetMonodromy_0_0048 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 62) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 62)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 48)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 48) = g32p_row42_cosetExponents0 48 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0049 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 63) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 63)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 49)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 49) = g32p_row42_cosetExponents0 49 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0050 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 64) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 64)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 50)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 50) = g32p_row42_cosetExponents0 50 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0051 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 65) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 65)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 51)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 51) = g32p_row42_cosetExponents0 51 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0052 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 66) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 66)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 52)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 52) = g32p_row42_cosetExponents0 52 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0053 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 67) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 67)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 53)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 53) = g32p_row42_cosetExponents0 53 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0054 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 68) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 68)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 54)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 54) = g32p_row42_cosetExponents0 54 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0055 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 70) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 70)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 55)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 55) = g32p_row42_cosetExponents0 55 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0056 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 72) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 72)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 56)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 56) = g32p_row42_cosetExponents0 56 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0057 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 75) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 75)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 57)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 57) = g32p_row42_cosetExponents0 57 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0058 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 76) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 76)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 58)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 58) = g32p_row42_cosetExponents0 58 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0059 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 77) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 77)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 59)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 59) = g32p_row42_cosetExponents0 59 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0060 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 79) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 79)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 60)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 60) = g32p_row42_cosetExponents0 60 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0061 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 80) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 80)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 61)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 61) = g32p_row42_cosetExponents0 61 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0062 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 83) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 83)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 62)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 62) = g32p_row42_cosetExponents0 62 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0063 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 85) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 85)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 63)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 63) = g32p_row42_cosetExponents0 63 := by
  decide +kernel

theorem g32p_row42_cosetMonodromyBlock0_0003 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row42_cosetBranchMatrices 0) (g32p_row42_cosetLengths0 (g32p_finBlockIndex 108 3 r)))
      (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots0 (g32p_finBlockIndex 108 3 r))) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots0 (g32p_finBlockIndex 108 3 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 (g32p_finBlockIndex 108 3 r))) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 (g32p_finBlockIndex 108 3 r)) = g32p_row42_cosetExponents0 (g32p_finBlockIndex 108 3 r) := by
  fin_cases r
  · exact g32p_row42_cosetMonodromy_0_0048
  · exact g32p_row42_cosetMonodromy_0_0049
  · exact g32p_row42_cosetMonodromy_0_0050
  · exact g32p_row42_cosetMonodromy_0_0051
  · exact g32p_row42_cosetMonodromy_0_0052
  · exact g32p_row42_cosetMonodromy_0_0053
  · exact g32p_row42_cosetMonodromy_0_0054
  · exact g32p_row42_cosetMonodromy_0_0055
  · exact g32p_row42_cosetMonodromy_0_0056
  · exact g32p_row42_cosetMonodromy_0_0057
  · exact g32p_row42_cosetMonodromy_0_0058
  · exact g32p_row42_cosetMonodromy_0_0059
  · exact g32p_row42_cosetMonodromy_0_0060
  · exact g32p_row42_cosetMonodromy_0_0061
  · exact g32p_row42_cosetMonodromy_0_0062
  · exact g32p_row42_cosetMonodromy_0_0063


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row42_cosetMonodromy_0_0064 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 88) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 88)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 64)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 64) = g32p_row42_cosetExponents0 64 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0065 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 89) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 89)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 65)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 65) = g32p_row42_cosetExponents0 65 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0066 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 91) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 91)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 66)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 66) = g32p_row42_cosetExponents0 66 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0067 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 92) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 92)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 67)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 67) = g32p_row42_cosetExponents0 67 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0068 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 94) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 94)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 68)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 68) = g32p_row42_cosetExponents0 68 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0069 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 95) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 95)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 69)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 69) = g32p_row42_cosetExponents0 69 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0070 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 96) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 96)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 70)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 70) = g32p_row42_cosetExponents0 70 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0071 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 100) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 100)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 71)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 71) = g32p_row42_cosetExponents0 71 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0072 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 102) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 102)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 72)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 72) = g32p_row42_cosetExponents0 72 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0073 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 103) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 103)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 73)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 73) = g32p_row42_cosetExponents0 73 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0074 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 104) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 104)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 74)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 74) = g32p_row42_cosetExponents0 74 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0075 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 105) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 105)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 75)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 75) = g32p_row42_cosetExponents0 75 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0076 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 109) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 109)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 76)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 76) = g32p_row42_cosetExponents0 76 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0077 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 110) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 110)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 77)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 77) = g32p_row42_cosetExponents0 77 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0078 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 112) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 112)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 78)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 78) = g32p_row42_cosetExponents0 78 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0079 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 116) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 116)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 79)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 79) = g32p_row42_cosetExponents0 79 := by
  decide +kernel

theorem g32p_row42_cosetMonodromyBlock0_0004 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row42_cosetBranchMatrices 0) (g32p_row42_cosetLengths0 (g32p_finBlockIndex 108 4 r)))
      (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots0 (g32p_finBlockIndex 108 4 r))) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots0 (g32p_finBlockIndex 108 4 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 (g32p_finBlockIndex 108 4 r))) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 (g32p_finBlockIndex 108 4 r)) = g32p_row42_cosetExponents0 (g32p_finBlockIndex 108 4 r) := by
  fin_cases r
  · exact g32p_row42_cosetMonodromy_0_0064
  · exact g32p_row42_cosetMonodromy_0_0065
  · exact g32p_row42_cosetMonodromy_0_0066
  · exact g32p_row42_cosetMonodromy_0_0067
  · exact g32p_row42_cosetMonodromy_0_0068
  · exact g32p_row42_cosetMonodromy_0_0069
  · exact g32p_row42_cosetMonodromy_0_0070
  · exact g32p_row42_cosetMonodromy_0_0071
  · exact g32p_row42_cosetMonodromy_0_0072
  · exact g32p_row42_cosetMonodromy_0_0073
  · exact g32p_row42_cosetMonodromy_0_0074
  · exact g32p_row42_cosetMonodromy_0_0075
  · exact g32p_row42_cosetMonodromy_0_0076
  · exact g32p_row42_cosetMonodromy_0_0077
  · exact g32p_row42_cosetMonodromy_0_0078
  · exact g32p_row42_cosetMonodromy_0_0079


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row42_cosetMonodromy_0_0080 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 120) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 120)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 80)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 80) = g32p_row42_cosetExponents0 80 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0081 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 123) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 123)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 81)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 81) = g32p_row42_cosetExponents0 81 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0082 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 125) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 125)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 82)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 82) = g32p_row42_cosetExponents0 82 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0083 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 127) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 127)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 83)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 83) = g32p_row42_cosetExponents0 83 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0084 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 134) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 134)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 84)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 84) = g32p_row42_cosetExponents0 84 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0085 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 135) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 135)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 85)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 85) = g32p_row42_cosetExponents0 85 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0086 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 136) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 136)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 86)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 86) = g32p_row42_cosetExponents0 86 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0087 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 139) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 139)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 87)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 87) = g32p_row42_cosetExponents0 87 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0088 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 142) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 142)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 88)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 88) = g32p_row42_cosetExponents0 88 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0089 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 146) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 146)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 89)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 89) = g32p_row42_cosetExponents0 89 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0090 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 155) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 155)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 90)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 90) = g32p_row42_cosetExponents0 90 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0091 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 157) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 157)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 91)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 91) = g32p_row42_cosetExponents0 91 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0092 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 158) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 158)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 92)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 92) = g32p_row42_cosetExponents0 92 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0093 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 159) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 159)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 93)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 93) = g32p_row42_cosetExponents0 93 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0094 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 162) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 162)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 94)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 94) = g32p_row42_cosetExponents0 94 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0095 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 163) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 163)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 95)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 95) = g32p_row42_cosetExponents0 95 := by
  decide +kernel

theorem g32p_row42_cosetMonodromyBlock0_0005 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row42_cosetBranchMatrices 0) (g32p_row42_cosetLengths0 (g32p_finBlockIndex 108 5 r)))
      (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots0 (g32p_finBlockIndex 108 5 r))) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots0 (g32p_finBlockIndex 108 5 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 (g32p_finBlockIndex 108 5 r))) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 (g32p_finBlockIndex 108 5 r)) = g32p_row42_cosetExponents0 (g32p_finBlockIndex 108 5 r) := by
  fin_cases r
  · exact g32p_row42_cosetMonodromy_0_0080
  · exact g32p_row42_cosetMonodromy_0_0081
  · exact g32p_row42_cosetMonodromy_0_0082
  · exact g32p_row42_cosetMonodromy_0_0083
  · exact g32p_row42_cosetMonodromy_0_0084
  · exact g32p_row42_cosetMonodromy_0_0085
  · exact g32p_row42_cosetMonodromy_0_0086
  · exact g32p_row42_cosetMonodromy_0_0087
  · exact g32p_row42_cosetMonodromy_0_0088
  · exact g32p_row42_cosetMonodromy_0_0089
  · exact g32p_row42_cosetMonodromy_0_0090
  · exact g32p_row42_cosetMonodromy_0_0091
  · exact g32p_row42_cosetMonodromy_0_0092
  · exact g32p_row42_cosetMonodromy_0_0093
  · exact g32p_row42_cosetMonodromy_0_0094
  · exact g32p_row42_cosetMonodromy_0_0095


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row42_cosetMonodromy_0_0096 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 165) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 165)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 96)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 96) = g32p_row42_cosetExponents0 96 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0097 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 169) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 169)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 97)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 97) = g32p_row42_cosetExponents0 97 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0098 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 177) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 177)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 98)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 98) = g32p_row42_cosetExponents0 98 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0099 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 182) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 182)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 99)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 99) = g32p_row42_cosetExponents0 99 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0100 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 183) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 183)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 100)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 100) = g32p_row42_cosetExponents0 100 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0101 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 188) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 188)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 101)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 101) = g32p_row42_cosetExponents0 101 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0102 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 190) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 190)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 102)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 102) = g32p_row42_cosetExponents0 102 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0103 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 215) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 215)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 103)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 103) = g32p_row42_cosetExponents0 103 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0104 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 221) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 221)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 104)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 104) = g32p_row42_cosetExponents0 104 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0105 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 228) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 228)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 105)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 105) = g32p_row42_cosetExponents0 105 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0106 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 237) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 237)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 106)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 106) = g32p_row42_cosetExponents0 106 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_0_0107 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 252) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 252)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 107)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 107) = g32p_row42_cosetExponents0 107 := by
  decide +kernel

theorem g32p_row42_cosetMonodromyBlock0_0006 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row42_cosetBranchMatrices 0) (g32p_row42_cosetLengths0 (g32p_finBlockIndex 108 6 r)))
      (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots0 (g32p_finBlockIndex 108 6 r))) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots0 (g32p_finBlockIndex 108 6 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies0 (g32p_finBlockIndex 108 6 r))) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies0 (g32p_finBlockIndex 108 6 r)) = g32p_row42_cosetExponents0 (g32p_finBlockIndex 108 6 r) := by
  fin_cases r
  · exact g32p_row42_cosetMonodromy_0_0096
  · exact g32p_row42_cosetMonodromy_0_0097
  · exact g32p_row42_cosetMonodromy_0_0098
  · exact g32p_row42_cosetMonodromy_0_0099
  · exact g32p_row42_cosetMonodromy_0_0100
  · exact g32p_row42_cosetMonodromy_0_0101
  · exact g32p_row42_cosetMonodromy_0_0102
  · exact g32p_row42_cosetMonodromy_0_0103
  · exact g32p_row42_cosetMonodromy_0_0104
  · exact g32p_row42_cosetMonodromy_0_0105
  · exact g32p_row42_cosetMonodromy_0_0106
  · exact g32p_row42_cosetMonodromy_0_0107
  · exact g32p_row42_cosetMonodromy_0_0000
  · exact g32p_row42_cosetMonodromy_0_0001
  · exact g32p_row42_cosetMonodromy_0_0002
  · exact g32p_row42_cosetMonodromy_0_0003


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row42_cosetMonodromy_1_0000 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 0)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 0)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 0) = g32p_row42_cosetExponents1 0 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0001 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 1)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 1)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 1) = g32p_row42_cosetExponents1 1 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0002 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 2)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 2)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 2) = g32p_row42_cosetExponents1 2 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0003 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 3)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 3)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 3) = g32p_row42_cosetExponents1 3 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0004 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 5)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 4)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 4) = g32p_row42_cosetExponents1 4 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0005 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 6)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 5)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 5) = g32p_row42_cosetExponents1 5 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0006 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 7)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 6)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 6) = g32p_row42_cosetExponents1 6 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0007 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 8)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 7)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 7) = g32p_row42_cosetExponents1 7 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0008 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 9)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 8)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 8) = g32p_row42_cosetExponents1 8 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0009 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 10)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 9)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 9) = g32p_row42_cosetExponents1 9 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0010 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 11)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 10)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 10) = g32p_row42_cosetExponents1 10 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0011 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 12)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 11)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 11) = g32p_row42_cosetExponents1 11 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0012 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 13)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 12)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 12) = g32p_row42_cosetExponents1 12 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0013 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 14)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 13)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 13) = g32p_row42_cosetExponents1 13 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0014 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 15)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 14)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 14) = g32p_row42_cosetExponents1 14 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0015 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 19) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 19)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 15)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 15) = g32p_row42_cosetExponents1 15 := by
  decide +kernel

theorem g32p_row42_cosetMonodromyBlock1_0000 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row42_cosetBranchMatrices 1) (g32p_row42_cosetLengths1 (g32p_finBlockIndex 108 0 r)))
      (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots1 (g32p_finBlockIndex 108 0 r))) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots1 (g32p_finBlockIndex 108 0 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 (g32p_finBlockIndex 108 0 r))) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 (g32p_finBlockIndex 108 0 r)) = g32p_row42_cosetExponents1 (g32p_finBlockIndex 108 0 r) := by
  fin_cases r
  · exact g32p_row42_cosetMonodromy_1_0000
  · exact g32p_row42_cosetMonodromy_1_0001
  · exact g32p_row42_cosetMonodromy_1_0002
  · exact g32p_row42_cosetMonodromy_1_0003
  · exact g32p_row42_cosetMonodromy_1_0004
  · exact g32p_row42_cosetMonodromy_1_0005
  · exact g32p_row42_cosetMonodromy_1_0006
  · exact g32p_row42_cosetMonodromy_1_0007
  · exact g32p_row42_cosetMonodromy_1_0008
  · exact g32p_row42_cosetMonodromy_1_0009
  · exact g32p_row42_cosetMonodromy_1_0010
  · exact g32p_row42_cosetMonodromy_1_0011
  · exact g32p_row42_cosetMonodromy_1_0012
  · exact g32p_row42_cosetMonodromy_1_0013
  · exact g32p_row42_cosetMonodromy_1_0014
  · exact g32p_row42_cosetMonodromy_1_0015


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row42_cosetMonodromy_1_0016 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 20) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 20)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 16)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 16) = g32p_row42_cosetExponents1 16 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0017 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 21)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 17)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 17) = g32p_row42_cosetExponents1 17 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0018 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 22) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 22)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 18)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 18) = g32p_row42_cosetExponents1 18 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0019 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 23) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 23)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 19)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 19) = g32p_row42_cosetExponents1 19 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0020 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 24)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 20)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 20) = g32p_row42_cosetExponents1 20 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0021 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 25)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 21)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 21) = g32p_row42_cosetExponents1 21 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0022 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 26)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 22)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 22) = g32p_row42_cosetExponents1 22 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0023 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 27) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 27)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 23)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 23) = g32p_row42_cosetExponents1 23 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0024 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 28) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 28)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 24)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 24) = g32p_row42_cosetExponents1 24 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0025 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 29)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 25)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 25) = g32p_row42_cosetExponents1 25 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0026 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 30) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 30)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 26)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 26) = g32p_row42_cosetExponents1 26 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0027 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 31)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 27)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 27) = g32p_row42_cosetExponents1 27 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0028 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 32)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 28)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 28) = g32p_row42_cosetExponents1 28 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0029 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 36) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 36)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 29)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 29) = g32p_row42_cosetExponents1 29 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0030 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 39) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 39)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 30)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 30) = g32p_row42_cosetExponents1 30 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0031 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 40) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 40)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 31)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 31) = g32p_row42_cosetExponents1 31 := by
  decide +kernel

theorem g32p_row42_cosetMonodromyBlock1_0001 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row42_cosetBranchMatrices 1) (g32p_row42_cosetLengths1 (g32p_finBlockIndex 108 1 r)))
      (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots1 (g32p_finBlockIndex 108 1 r))) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots1 (g32p_finBlockIndex 108 1 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 (g32p_finBlockIndex 108 1 r))) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 (g32p_finBlockIndex 108 1 r)) = g32p_row42_cosetExponents1 (g32p_finBlockIndex 108 1 r) := by
  fin_cases r
  · exact g32p_row42_cosetMonodromy_1_0016
  · exact g32p_row42_cosetMonodromy_1_0017
  · exact g32p_row42_cosetMonodromy_1_0018
  · exact g32p_row42_cosetMonodromy_1_0019
  · exact g32p_row42_cosetMonodromy_1_0020
  · exact g32p_row42_cosetMonodromy_1_0021
  · exact g32p_row42_cosetMonodromy_1_0022
  · exact g32p_row42_cosetMonodromy_1_0023
  · exact g32p_row42_cosetMonodromy_1_0024
  · exact g32p_row42_cosetMonodromy_1_0025
  · exact g32p_row42_cosetMonodromy_1_0026
  · exact g32p_row42_cosetMonodromy_1_0027
  · exact g32p_row42_cosetMonodromy_1_0028
  · exact g32p_row42_cosetMonodromy_1_0029
  · exact g32p_row42_cosetMonodromy_1_0030
  · exact g32p_row42_cosetMonodromy_1_0031


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row42_cosetMonodromy_1_0032 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 41) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 41)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 32)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 32) = g32p_row42_cosetExponents1 32 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0033 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 42) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 42)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 33)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 33) = g32p_row42_cosetExponents1 33 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0034 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 51) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 51)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 34)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 34) = g32p_row42_cosetExponents1 34 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0035 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 52) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 52)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 35)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 35) = g32p_row42_cosetExponents1 35 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0036 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 53) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 53)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 36)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 36) = g32p_row42_cosetExponents1 36 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0037 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 54) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 54)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 37)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 37) = g32p_row42_cosetExponents1 37 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0038 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 56) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 56)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 38)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 38) = g32p_row42_cosetExponents1 38 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0039 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 57) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 57)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 39)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 39) = g32p_row42_cosetExponents1 39 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0040 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 58) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 58)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 40)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 40) = g32p_row42_cosetExponents1 40 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0041 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 61) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 61)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 41)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 41) = g32p_row42_cosetExponents1 41 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0042 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 62) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 62)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 42)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 42) = g32p_row42_cosetExponents1 42 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0043 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 63) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 63)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 43)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 43) = g32p_row42_cosetExponents1 43 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0044 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 64) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 64)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 44)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 44) = g32p_row42_cosetExponents1 44 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0045 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 66) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 66)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 45)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 45) = g32p_row42_cosetExponents1 45 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0046 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 69) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 69)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 46)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 46) = g32p_row42_cosetExponents1 46 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0047 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 70) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 70)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 47)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 47) = g32p_row42_cosetExponents1 47 := by
  decide +kernel

theorem g32p_row42_cosetMonodromyBlock1_0002 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row42_cosetBranchMatrices 1) (g32p_row42_cosetLengths1 (g32p_finBlockIndex 108 2 r)))
      (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots1 (g32p_finBlockIndex 108 2 r))) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots1 (g32p_finBlockIndex 108 2 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 (g32p_finBlockIndex 108 2 r))) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 (g32p_finBlockIndex 108 2 r)) = g32p_row42_cosetExponents1 (g32p_finBlockIndex 108 2 r) := by
  fin_cases r
  · exact g32p_row42_cosetMonodromy_1_0032
  · exact g32p_row42_cosetMonodromy_1_0033
  · exact g32p_row42_cosetMonodromy_1_0034
  · exact g32p_row42_cosetMonodromy_1_0035
  · exact g32p_row42_cosetMonodromy_1_0036
  · exact g32p_row42_cosetMonodromy_1_0037
  · exact g32p_row42_cosetMonodromy_1_0038
  · exact g32p_row42_cosetMonodromy_1_0039
  · exact g32p_row42_cosetMonodromy_1_0040
  · exact g32p_row42_cosetMonodromy_1_0041
  · exact g32p_row42_cosetMonodromy_1_0042
  · exact g32p_row42_cosetMonodromy_1_0043
  · exact g32p_row42_cosetMonodromy_1_0044
  · exact g32p_row42_cosetMonodromy_1_0045
  · exact g32p_row42_cosetMonodromy_1_0046
  · exact g32p_row42_cosetMonodromy_1_0047


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row42_cosetMonodromy_1_0048 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 73) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 73)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 48)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 48) = g32p_row42_cosetExponents1 48 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0049 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 77) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 77)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 49)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 49) = g32p_row42_cosetExponents1 49 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0050 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 78) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 78)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 50)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 50) = g32p_row42_cosetExponents1 50 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0051 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 79) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 79)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 51)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 51) = g32p_row42_cosetExponents1 51 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0052 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 80) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 80)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 52)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 52) = g32p_row42_cosetExponents1 52 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0053 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 81) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 81)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 53)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 53) = g32p_row42_cosetExponents1 53 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0054 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 82) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 82)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 54)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 54) = g32p_row42_cosetExponents1 54 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0055 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 87) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 87)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 55)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 55) = g32p_row42_cosetExponents1 55 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0056 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 104) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 104)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 56)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 56) = g32p_row42_cosetExponents1 56 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0057 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 105) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 105)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 57)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 57) = g32p_row42_cosetExponents1 57 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0058 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 108) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 108)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 58)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 58) = g32p_row42_cosetExponents1 58 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0059 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 109) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 109)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 59)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 59) = g32p_row42_cosetExponents1 59 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0060 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 112) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 112)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 60)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 60) = g32p_row42_cosetExponents1 60 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0061 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 113) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 113)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 61)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 61) = g32p_row42_cosetExponents1 61 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0062 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 119) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 119)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 62)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 62) = g32p_row42_cosetExponents1 62 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0063 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 123) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 123)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 63)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 63) = g32p_row42_cosetExponents1 63 := by
  decide +kernel

theorem g32p_row42_cosetMonodromyBlock1_0003 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row42_cosetBranchMatrices 1) (g32p_row42_cosetLengths1 (g32p_finBlockIndex 108 3 r)))
      (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots1 (g32p_finBlockIndex 108 3 r))) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots1 (g32p_finBlockIndex 108 3 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 (g32p_finBlockIndex 108 3 r))) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 (g32p_finBlockIndex 108 3 r)) = g32p_row42_cosetExponents1 (g32p_finBlockIndex 108 3 r) := by
  fin_cases r
  · exact g32p_row42_cosetMonodromy_1_0048
  · exact g32p_row42_cosetMonodromy_1_0049
  · exact g32p_row42_cosetMonodromy_1_0050
  · exact g32p_row42_cosetMonodromy_1_0051
  · exact g32p_row42_cosetMonodromy_1_0052
  · exact g32p_row42_cosetMonodromy_1_0053
  · exact g32p_row42_cosetMonodromy_1_0054
  · exact g32p_row42_cosetMonodromy_1_0055
  · exact g32p_row42_cosetMonodromy_1_0056
  · exact g32p_row42_cosetMonodromy_1_0057
  · exact g32p_row42_cosetMonodromy_1_0058
  · exact g32p_row42_cosetMonodromy_1_0059
  · exact g32p_row42_cosetMonodromy_1_0060
  · exact g32p_row42_cosetMonodromy_1_0061
  · exact g32p_row42_cosetMonodromy_1_0062
  · exact g32p_row42_cosetMonodromy_1_0063


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row42_cosetMonodromy_1_0064 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 125) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 125)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 64)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 64) = g32p_row42_cosetExponents1 64 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0065 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 126) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 126)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 65)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 65) = g32p_row42_cosetExponents1 65 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0066 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 127) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 127)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 66)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 66) = g32p_row42_cosetExponents1 66 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0067 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 128) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 128)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 67)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 67) = g32p_row42_cosetExponents1 67 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0068 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 129) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 129)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 68)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 68) = g32p_row42_cosetExponents1 68 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0069 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 130) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 130)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 69)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 69) = g32p_row42_cosetExponents1 69 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0070 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 131) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 131)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 70)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 70) = g32p_row42_cosetExponents1 70 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0071 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 132) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 132)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 71)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 71) = g32p_row42_cosetExponents1 71 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0072 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 133) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 133)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 72)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 72) = g32p_row42_cosetExponents1 72 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0073 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 136) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 136)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 73)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 73) = g32p_row42_cosetExponents1 73 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0074 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 137) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 137)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 74)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 74) = g32p_row42_cosetExponents1 74 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0075 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 138) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 138)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 75)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 75) = g32p_row42_cosetExponents1 75 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0076 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 139) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 139)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 76)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 76) = g32p_row42_cosetExponents1 76 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0077 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 144) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 144)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 77)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 77) = g32p_row42_cosetExponents1 77 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0078 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 145) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 145)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 78)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 78) = g32p_row42_cosetExponents1 78 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0079 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 156) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 156)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 79)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 79) = g32p_row42_cosetExponents1 79 := by
  decide +kernel

theorem g32p_row42_cosetMonodromyBlock1_0004 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row42_cosetBranchMatrices 1) (g32p_row42_cosetLengths1 (g32p_finBlockIndex 108 4 r)))
      (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots1 (g32p_finBlockIndex 108 4 r))) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots1 (g32p_finBlockIndex 108 4 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 (g32p_finBlockIndex 108 4 r))) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 (g32p_finBlockIndex 108 4 r)) = g32p_row42_cosetExponents1 (g32p_finBlockIndex 108 4 r) := by
  fin_cases r
  · exact g32p_row42_cosetMonodromy_1_0064
  · exact g32p_row42_cosetMonodromy_1_0065
  · exact g32p_row42_cosetMonodromy_1_0066
  · exact g32p_row42_cosetMonodromy_1_0067
  · exact g32p_row42_cosetMonodromy_1_0068
  · exact g32p_row42_cosetMonodromy_1_0069
  · exact g32p_row42_cosetMonodromy_1_0070
  · exact g32p_row42_cosetMonodromy_1_0071
  · exact g32p_row42_cosetMonodromy_1_0072
  · exact g32p_row42_cosetMonodromy_1_0073
  · exact g32p_row42_cosetMonodromy_1_0074
  · exact g32p_row42_cosetMonodromy_1_0075
  · exact g32p_row42_cosetMonodromy_1_0076
  · exact g32p_row42_cosetMonodromy_1_0077
  · exact g32p_row42_cosetMonodromy_1_0078
  · exact g32p_row42_cosetMonodromy_1_0079


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row42_cosetMonodromy_1_0080 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 157) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 157)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 80)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 80) = g32p_row42_cosetExponents1 80 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0081 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 159) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 159)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 81)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 81) = g32p_row42_cosetExponents1 81 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0082 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 161) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 161)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 82)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 82) = g32p_row42_cosetExponents1 82 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0083 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 162) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 162)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 83)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 83) = g32p_row42_cosetExponents1 83 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0084 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 178) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 178)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 84)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 84) = g32p_row42_cosetExponents1 84 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0085 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 180) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 180)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 85)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 85) = g32p_row42_cosetExponents1 85 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0086 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 181) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 181)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 86)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 86) = g32p_row42_cosetExponents1 86 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0087 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 185) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 185)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 87)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 87) = g32p_row42_cosetExponents1 87 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0088 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 188) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 188)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 88)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 88) = g32p_row42_cosetExponents1 88 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0089 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 191) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 191)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 89)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 89) = g32p_row42_cosetExponents1 89 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0090 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 194) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 194)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 90)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 90) = g32p_row42_cosetExponents1 90 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0091 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 196) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 196)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 91)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 91) = g32p_row42_cosetExponents1 91 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0092 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 197) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 197)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 92)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 92) = g32p_row42_cosetExponents1 92 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0093 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 198) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 198)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 93)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 93) = g32p_row42_cosetExponents1 93 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0094 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 199) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 199)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 94)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 94) = g32p_row42_cosetExponents1 94 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0095 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 200) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 200)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 95)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 95) = g32p_row42_cosetExponents1 95 := by
  decide +kernel

theorem g32p_row42_cosetMonodromyBlock1_0005 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row42_cosetBranchMatrices 1) (g32p_row42_cosetLengths1 (g32p_finBlockIndex 108 5 r)))
      (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots1 (g32p_finBlockIndex 108 5 r))) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots1 (g32p_finBlockIndex 108 5 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 (g32p_finBlockIndex 108 5 r))) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 (g32p_finBlockIndex 108 5 r)) = g32p_row42_cosetExponents1 (g32p_finBlockIndex 108 5 r) := by
  fin_cases r
  · exact g32p_row42_cosetMonodromy_1_0080
  · exact g32p_row42_cosetMonodromy_1_0081
  · exact g32p_row42_cosetMonodromy_1_0082
  · exact g32p_row42_cosetMonodromy_1_0083
  · exact g32p_row42_cosetMonodromy_1_0084
  · exact g32p_row42_cosetMonodromy_1_0085
  · exact g32p_row42_cosetMonodromy_1_0086
  · exact g32p_row42_cosetMonodromy_1_0087
  · exact g32p_row42_cosetMonodromy_1_0088
  · exact g32p_row42_cosetMonodromy_1_0089
  · exact g32p_row42_cosetMonodromy_1_0090
  · exact g32p_row42_cosetMonodromy_1_0091
  · exact g32p_row42_cosetMonodromy_1_0092
  · exact g32p_row42_cosetMonodromy_1_0093
  · exact g32p_row42_cosetMonodromy_1_0094
  · exact g32p_row42_cosetMonodromy_1_0095


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row42_cosetMonodromy_1_0096 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 202) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 202)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 96)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 96) = g32p_row42_cosetExponents1 96 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0097 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 207) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 207)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 97)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 97) = g32p_row42_cosetExponents1 97 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0098 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 210) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 210)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 98)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 98) = g32p_row42_cosetExponents1 98 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0099 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 211) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 211)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 99)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 99) = g32p_row42_cosetExponents1 99 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0100 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 214) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 214)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 100)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 100) = g32p_row42_cosetExponents1 100 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0101 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 217) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 217)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 101)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 101) = g32p_row42_cosetExponents1 101 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0102 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row42_cosetRepresentatives 218) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 218)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 102)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 102) = g32p_row42_cosetExponents1 102 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0103 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 230) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 230)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 103)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 103) = g32p_row42_cosetExponents1 103 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0104 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 231) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 231)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 104)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 104) = g32p_row42_cosetExponents1 104 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0105 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 233) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 233)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 105)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 105) = g32p_row42_cosetExponents1 105 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0106 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 257) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 257)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 106)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 106) = g32p_row42_cosetExponents1 106 := by
  decide +kernel

theorem g32p_row42_cosetMonodromy_1_0107 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row42_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row42_cosetRepresentatives 268) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives 268)
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 107)) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 107) = g32p_row42_cosetExponents1 107 := by
  decide +kernel

theorem g32p_row42_cosetMonodromyBlock1_0006 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row42_cosetBranchMatrices 1) (g32p_row42_cosetLengths1 (g32p_finBlockIndex 108 6 r)))
      (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots1 (g32p_finBlockIndex 108 6 r))) =
      HurwitzPrymRex_mmul (g32p_row42_cosetRepresentatives (g32p_row42_cosetRoots1 (g32p_finBlockIndex 108 6 r)))
        (g32p_row26_groupNodes (g32p_row42_cosetMonodromies1 (g32p_finBlockIndex 108 6 r))) ∧
    g32p_row42_characterValues (g32p_row42_cosetMonodromies1 (g32p_finBlockIndex 108 6 r)) = g32p_row42_cosetExponents1 (g32p_finBlockIndex 108 6 r) := by
  fin_cases r
  · exact g32p_row42_cosetMonodromy_1_0096
  · exact g32p_row42_cosetMonodromy_1_0097
  · exact g32p_row42_cosetMonodromy_1_0098
  · exact g32p_row42_cosetMonodromy_1_0099
  · exact g32p_row42_cosetMonodromy_1_0100
  · exact g32p_row42_cosetMonodromy_1_0101
  · exact g32p_row42_cosetMonodromy_1_0102
  · exact g32p_row42_cosetMonodromy_1_0103
  · exact g32p_row42_cosetMonodromy_1_0104
  · exact g32p_row42_cosetMonodromy_1_0105
  · exact g32p_row42_cosetMonodromy_1_0106
  · exact g32p_row42_cosetMonodromy_1_0107
  · exact g32p_row42_cosetMonodromy_1_0000
  · exact g32p_row42_cosetMonodromy_1_0001
  · exact g32p_row42_cosetMonodromy_1_0002
  · exact g32p_row42_cosetMonodromy_1_0003


end HodgeLean.Foundations.Program

end
