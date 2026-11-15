import HodgeLean.Foundations.Program.HurwitzPrymRexG32Data

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-rex`: the G32 stabilizer-chain certificate (kernel checks)

Each fact below is a closed Boolean computation over `ℤ[ω]`, checked by the kernel.
HC no distance; AV milestone no distance.
-/

namespace HodgeLean.Foundations.Program

theorem HurwitzPrymRex_g32_step1 :
    HurwitzPrymRex_stepCheck HurwitzPrymRex_g32TOne [HurwitzPrymRex_g32TTwo, HurwitzPrymRex_g32TThree]
      HurwitzPrymRex_g32SOne HurwitzPrymRex_g32WOne = true := by decide +kernel

theorem HurwitzPrymRex_g32_step2 :
    HurwitzPrymRex_stepCheck HurwitzPrymRex_g32TTwo [HurwitzPrymRex_g32TThree]
      HurwitzPrymRex_g32STwo HurwitzPrymRex_g32WTwo = true := by decide +kernel

theorem HurwitzPrymRex_g32_step3 :
    HurwitzPrymRex_stepCheck HurwitzPrymRex_g32TThree []
      HurwitzPrymRex_g32SThree HurwitzPrymRex_g32WThree = true := by decide +kernel

theorem HurwitzPrymRex_g32_derivT1 :
    HurwitzPrymRex_derivCheck HurwitzPrymRex_g32SOne HurwitzPrymRex_g32TOne
      HurwitzPrymRex_g32TWOne = true := by decide +kernel

theorem HurwitzPrymRex_g32_derivT2 :
    HurwitzPrymRex_derivCheck HurwitzPrymRex_g32STwo HurwitzPrymRex_g32TTwo
      HurwitzPrymRex_g32TWTwo = true := by decide +kernel

theorem HurwitzPrymRex_g32_derivT3 :
    HurwitzPrymRex_derivCheck HurwitzPrymRex_g32SThree HurwitzPrymRex_g32TThree
      HurwitzPrymRex_g32TWThree = true := by decide +kernel

theorem HurwitzPrymRex_g32_derivD1 :
    HurwitzPrymRex_derivCheck HurwitzPrymRex_g32SOne HurwitzPrymRex_g32DOne
      HurwitzPrymRex_g32DWOne = true := by decide +kernel

theorem HurwitzPrymRex_g32_derivD2 :
    HurwitzPrymRex_derivCheck HurwitzPrymRex_g32STwo HurwitzPrymRex_g32DTwo
      HurwitzPrymRex_g32DWTwo = true := by decide +kernel

theorem HurwitzPrymRex_g32_sub2 :
    HurwitzPrymRex_g32STwo.all (fun s ↦ HurwitzPrymRex_g32DOne.any (HurwitzPrymRex_mbeq s)) =
      true := by decide +kernel

theorem HurwitzPrymRex_g32_sub3 :
    HurwitzPrymRex_g32SThree.all (fun s ↦ HurwitzPrymRex_g32DTwo.any (HurwitzPrymRex_mbeq s)) =
      true := by decide +kernel

theorem HurwitzPrymRex_g32_fix2 : HurwitzPrymRex_fixCheck 2 HurwitzPrymRex_g32STwo = true := by
  decide +kernel

theorem HurwitzPrymRex_g32_fix3 : HurwitzPrymRex_fixCheck 3 HurwitzPrymRex_g32SThree = true := by
  decide +kernel

theorem HurwitzPrymRex_g32_nodup1 :
    (HurwitzPrymRex_g32TOne.map (HurwitzPrymRex_colKey 2)).Nodup := by decide +kernel

theorem HurwitzPrymRex_g32_nodup2 :
    (HurwitzPrymRex_g32TTwo.map (HurwitzPrymRex_colKey 3)).Nodup := by decide +kernel

theorem HurwitzPrymRex_g32_nodup3 :
    (HurwitzPrymRex_g32TThree.map (HurwitzPrymRex_colKey 0)).Nodup := by decide +kernel

theorem HurwitzPrymRex_g32_inv :
    HurwitzPrymRex_invCheck HurwitzPrymRex_g32SOne HurwitzPrymRex_g32SOneInv = true := by
  decide +kernel

theorem HurwitzPrymRex_g32_lengths : HurwitzPrymRex_g32TOne.length = 240 ∧
    HurwitzPrymRex_g32TTwo.length = 72 ∧ HurwitzPrymRex_g32TThree.length = 9 := by
  decide +kernel

end HodgeLean.Foundations.Program
