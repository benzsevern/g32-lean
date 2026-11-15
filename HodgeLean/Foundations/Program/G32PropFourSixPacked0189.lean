import HodgeLean.Foundations.Program.G32PropFourSixRootPointData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_check_000 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_000 =
      (![g32p_rootMatrix_001, g32p_rootMatrix_002, g32p_rootMatrix_000, g32p_rootMatrix_003]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_001 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_001 =
      (![g32p_rootMatrix_004, g32p_rootMatrix_005, g32p_rootMatrix_001, g32p_rootMatrix_006]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_002 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_002 =
      (![g32p_rootMatrix_007, g32p_rootMatrix_008, g32p_rootMatrix_009, g32p_rootMatrix_010]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_003 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_003 =
      (![g32p_rootMatrix_011, g32p_rootMatrix_010, g32p_rootMatrix_012, g32p_rootMatrix_013]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_004 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_004 =
      (![g32p_rootMatrix_000, g32p_rootMatrix_014, g32p_rootMatrix_004, g32p_rootMatrix_015]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_005 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_005 =
      (![g32p_rootMatrix_016, g32p_rootMatrix_017, g32p_rootMatrix_018, g32p_rootMatrix_019]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_006 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_006 =
      (![g32p_rootMatrix_020, g32p_rootMatrix_019, g32p_rootMatrix_021, g32p_rootMatrix_022]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_007 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_007 =
      (![g32p_rootMatrix_023, g32p_rootMatrix_016, g32p_rootMatrix_024, g32p_rootMatrix_007]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_008 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_008 =
      (![g32p_rootMatrix_025, g32p_rootMatrix_000, g32p_rootMatrix_026, g32p_rootMatrix_027]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_009 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_009 =
      (![g32p_rootMatrix_024, g32p_rootMatrix_009, g32p_rootMatrix_028, g32p_rootMatrix_029]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_010 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_010 =
      (![g32p_rootMatrix_030, g32p_rootMatrix_027, g32p_rootMatrix_010, g32p_rootMatrix_031]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_011 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_011 =
      (![g32p_rootMatrix_032, g32p_rootMatrix_011, g32p_rootMatrix_033, g32p_rootMatrix_020]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_012 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_012 =
      (![g32p_rootMatrix_033, g32p_rootMatrix_034, g32p_rootMatrix_035, g32p_rootMatrix_012]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_013 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_013 =
      (![g32p_rootMatrix_036, g32p_rootMatrix_031, g32p_rootMatrix_037, g32p_rootMatrix_000]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_014 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_014 =
      (![g32p_rootMatrix_038, g32p_rootMatrix_039, g32p_rootMatrix_040, g32p_rootMatrix_041]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_015 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_015 =
      (![g32p_rootMatrix_042, g32p_rootMatrix_041, g32p_rootMatrix_043, g32p_rootMatrix_044]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_016 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_016 =
      (![g32p_rootMatrix_045, g32p_rootMatrix_038, g32p_rootMatrix_046, g32p_rootMatrix_016]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_017 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_017 =
      (![g32p_rootMatrix_047, g32p_rootMatrix_001, g32p_rootMatrix_048, g32p_rootMatrix_049]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_018 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_018 =
      (![g32p_rootMatrix_046, g32p_rootMatrix_018, g32p_rootMatrix_050, g32p_rootMatrix_051]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_019 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_019 =
      (![g32p_rootMatrix_052, g32p_rootMatrix_049, g32p_rootMatrix_019, g32p_rootMatrix_053]) k := by
  fin_cases k <;> decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_block_00 (r : Fin 16) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k)
      (g32p_rootMatrix (g32p_finBlockIndex 240 0 r)) =
        g32p_rootMatrix (g32p_rootTransition (g32p_finBlockIndex 240 0 r) k) := by
  fin_cases r
  · fin_cases k
    · exact g32p_rootTransition_check_000 0
    · exact g32p_rootTransition_check_000 1
    · exact g32p_rootTransition_check_000 2
    · exact g32p_rootTransition_check_000 3
  · fin_cases k
    · exact g32p_rootTransition_check_001 0
    · exact g32p_rootTransition_check_001 1
    · exact g32p_rootTransition_check_001 2
    · exact g32p_rootTransition_check_001 3
  · fin_cases k
    · exact g32p_rootTransition_check_002 0
    · exact g32p_rootTransition_check_002 1
    · exact g32p_rootTransition_check_002 2
    · exact g32p_rootTransition_check_002 3
  · fin_cases k
    · exact g32p_rootTransition_check_003 0
    · exact g32p_rootTransition_check_003 1
    · exact g32p_rootTransition_check_003 2
    · exact g32p_rootTransition_check_003 3
  · fin_cases k
    · exact g32p_rootTransition_check_004 0
    · exact g32p_rootTransition_check_004 1
    · exact g32p_rootTransition_check_004 2
    · exact g32p_rootTransition_check_004 3
  · fin_cases k
    · exact g32p_rootTransition_check_005 0
    · exact g32p_rootTransition_check_005 1
    · exact g32p_rootTransition_check_005 2
    · exact g32p_rootTransition_check_005 3
  · fin_cases k
    · exact g32p_rootTransition_check_006 0
    · exact g32p_rootTransition_check_006 1
    · exact g32p_rootTransition_check_006 2
    · exact g32p_rootTransition_check_006 3
  · fin_cases k
    · exact g32p_rootTransition_check_007 0
    · exact g32p_rootTransition_check_007 1
    · exact g32p_rootTransition_check_007 2
    · exact g32p_rootTransition_check_007 3
  · fin_cases k
    · exact g32p_rootTransition_check_008 0
    · exact g32p_rootTransition_check_008 1
    · exact g32p_rootTransition_check_008 2
    · exact g32p_rootTransition_check_008 3
  · fin_cases k
    · exact g32p_rootTransition_check_009 0
    · exact g32p_rootTransition_check_009 1
    · exact g32p_rootTransition_check_009 2
    · exact g32p_rootTransition_check_009 3
  · fin_cases k
    · exact g32p_rootTransition_check_010 0
    · exact g32p_rootTransition_check_010 1
    · exact g32p_rootTransition_check_010 2
    · exact g32p_rootTransition_check_010 3
  · fin_cases k
    · exact g32p_rootTransition_check_011 0
    · exact g32p_rootTransition_check_011 1
    · exact g32p_rootTransition_check_011 2
    · exact g32p_rootTransition_check_011 3
  · fin_cases k
    · exact g32p_rootTransition_check_012 0
    · exact g32p_rootTransition_check_012 1
    · exact g32p_rootTransition_check_012 2
    · exact g32p_rootTransition_check_012 3
  · fin_cases k
    · exact g32p_rootTransition_check_013 0
    · exact g32p_rootTransition_check_013 1
    · exact g32p_rootTransition_check_013 2
    · exact g32p_rootTransition_check_013 3
  · fin_cases k
    · exact g32p_rootTransition_check_014 0
    · exact g32p_rootTransition_check_014 1
    · exact g32p_rootTransition_check_014 2
    · exact g32p_rootTransition_check_014 3
  · fin_cases k
    · exact g32p_rootTransition_check_015 0
    · exact g32p_rootTransition_check_015 1
    · exact g32p_rootTransition_check_015 2
    · exact g32p_rootTransition_check_015 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_check_020 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_020 =
      (![g32p_rootMatrix_054, g32p_rootMatrix_020, g32p_rootMatrix_055, g32p_rootMatrix_042]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_021 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_021 =
      (![g32p_rootMatrix_055, g32p_rootMatrix_056, g32p_rootMatrix_057, g32p_rootMatrix_021]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_022 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_022 =
      (![g32p_rootMatrix_058, g32p_rootMatrix_053, g32p_rootMatrix_059, g32p_rootMatrix_001]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_023 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_023 =
      (![g32p_rootMatrix_002, g32p_rootMatrix_060, g32p_rootMatrix_061, g32p_rootMatrix_062]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_024 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_024 =
      (![g32p_rootMatrix_061, g32p_rootMatrix_063, g32p_rootMatrix_064, g32p_rootMatrix_065]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_025 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_025 =
      (![g32p_rootMatrix_066, g32p_rootMatrix_045, g32p_rootMatrix_067, g32p_rootMatrix_068]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_026 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_026 =
      (![g32p_rootMatrix_067, g32p_rootMatrix_028, g32p_rootMatrix_069, g32p_rootMatrix_026]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_027 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_027 =
      (![g32p_rootMatrix_027, g32p_rootMatrix_003, g32p_rootMatrix_070, g32p_rootMatrix_071]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_028 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_028 =
      (![g32p_rootMatrix_064, g32p_rootMatrix_072, g32p_rootMatrix_002, g32p_rootMatrix_028]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_029 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_029 =
      (![g32p_rootMatrix_029, g32p_rootMatrix_029, g32p_rootMatrix_031, g32p_rootMatrix_073]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_030 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_030 =
      (![g32p_rootMatrix_074, g32p_rootMatrix_032, g32p_rootMatrix_030, g32p_rootMatrix_023]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_031 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_031 =
      (![g32p_rootMatrix_031, g32p_rootMatrix_071, g32p_rootMatrix_075, g32p_rootMatrix_002]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_032 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_032 =
      (![g32p_rootMatrix_003, g32p_rootMatrix_076, g32p_rootMatrix_077, g32p_rootMatrix_060]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_033 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_033 =
      (![g32p_rootMatrix_077, g32p_rootMatrix_078, g32p_rootMatrix_079, g32p_rootMatrix_080]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_034 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_034 =
      (![g32p_rootMatrix_034, g32p_rootMatrix_081, g32p_rootMatrix_027, g32p_rootMatrix_034]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_035 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_035 =
      (![g32p_rootMatrix_079, g32p_rootMatrix_035, g32p_rootMatrix_003, g32p_rootMatrix_082]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_036 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_036 =
      (![g32p_rootMatrix_083, g32p_rootMatrix_068, g32p_rootMatrix_084, g32p_rootMatrix_054]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_037 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_037 =
      (![g32p_rootMatrix_084, g32p_rootMatrix_037, g32p_rootMatrix_085, g32p_rootMatrix_035]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_038 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_038 =
      (![g32p_rootMatrix_086, g32p_rootMatrix_007, g32p_rootMatrix_087, g32p_rootMatrix_038]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_039 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_039 =
      (![g32p_rootMatrix_088, g32p_rootMatrix_004, g32p_rootMatrix_089, g32p_rootMatrix_090]) k := by
  fin_cases k <;> decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_block_01 (r : Fin 16) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k)
      (g32p_rootMatrix (g32p_finBlockIndex 240 1 r)) =
        g32p_rootMatrix (g32p_rootTransition (g32p_finBlockIndex 240 1 r) k) := by
  fin_cases r
  · fin_cases k
    · exact g32p_rootTransition_check_016 0
    · exact g32p_rootTransition_check_016 1
    · exact g32p_rootTransition_check_016 2
    · exact g32p_rootTransition_check_016 3
  · fin_cases k
    · exact g32p_rootTransition_check_017 0
    · exact g32p_rootTransition_check_017 1
    · exact g32p_rootTransition_check_017 2
    · exact g32p_rootTransition_check_017 3
  · fin_cases k
    · exact g32p_rootTransition_check_018 0
    · exact g32p_rootTransition_check_018 1
    · exact g32p_rootTransition_check_018 2
    · exact g32p_rootTransition_check_018 3
  · fin_cases k
    · exact g32p_rootTransition_check_019 0
    · exact g32p_rootTransition_check_019 1
    · exact g32p_rootTransition_check_019 2
    · exact g32p_rootTransition_check_019 3
  · fin_cases k
    · exact g32p_rootTransition_check_020 0
    · exact g32p_rootTransition_check_020 1
    · exact g32p_rootTransition_check_020 2
    · exact g32p_rootTransition_check_020 3
  · fin_cases k
    · exact g32p_rootTransition_check_021 0
    · exact g32p_rootTransition_check_021 1
    · exact g32p_rootTransition_check_021 2
    · exact g32p_rootTransition_check_021 3
  · fin_cases k
    · exact g32p_rootTransition_check_022 0
    · exact g32p_rootTransition_check_022 1
    · exact g32p_rootTransition_check_022 2
    · exact g32p_rootTransition_check_022 3
  · fin_cases k
    · exact g32p_rootTransition_check_023 0
    · exact g32p_rootTransition_check_023 1
    · exact g32p_rootTransition_check_023 2
    · exact g32p_rootTransition_check_023 3
  · fin_cases k
    · exact g32p_rootTransition_check_024 0
    · exact g32p_rootTransition_check_024 1
    · exact g32p_rootTransition_check_024 2
    · exact g32p_rootTransition_check_024 3
  · fin_cases k
    · exact g32p_rootTransition_check_025 0
    · exact g32p_rootTransition_check_025 1
    · exact g32p_rootTransition_check_025 2
    · exact g32p_rootTransition_check_025 3
  · fin_cases k
    · exact g32p_rootTransition_check_026 0
    · exact g32p_rootTransition_check_026 1
    · exact g32p_rootTransition_check_026 2
    · exact g32p_rootTransition_check_026 3
  · fin_cases k
    · exact g32p_rootTransition_check_027 0
    · exact g32p_rootTransition_check_027 1
    · exact g32p_rootTransition_check_027 2
    · exact g32p_rootTransition_check_027 3
  · fin_cases k
    · exact g32p_rootTransition_check_028 0
    · exact g32p_rootTransition_check_028 1
    · exact g32p_rootTransition_check_028 2
    · exact g32p_rootTransition_check_028 3
  · fin_cases k
    · exact g32p_rootTransition_check_029 0
    · exact g32p_rootTransition_check_029 1
    · exact g32p_rootTransition_check_029 2
    · exact g32p_rootTransition_check_029 3
  · fin_cases k
    · exact g32p_rootTransition_check_030 0
    · exact g32p_rootTransition_check_030 1
    · exact g32p_rootTransition_check_030 2
    · exact g32p_rootTransition_check_030 3
  · fin_cases k
    · exact g32p_rootTransition_check_031 0
    · exact g32p_rootTransition_check_031 1
    · exact g32p_rootTransition_check_031 2
    · exact g32p_rootTransition_check_031 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_check_040 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_040 =
      (![g32p_rootMatrix_087, g32p_rootMatrix_040, g32p_rootMatrix_091, g32p_rootMatrix_092]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_041 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_041 =
      (![g32p_rootMatrix_093, g32p_rootMatrix_090, g32p_rootMatrix_041, g32p_rootMatrix_094]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_042 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_042 =
      (![g32p_rootMatrix_095, g32p_rootMatrix_042, g32p_rootMatrix_096, g32p_rootMatrix_011]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_043 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_043 =
      (![g32p_rootMatrix_096, g32p_rootMatrix_097, g32p_rootMatrix_098, g32p_rootMatrix_043]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_044 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_044 =
      (![g32p_rootMatrix_099, g32p_rootMatrix_094, g32p_rootMatrix_100, g32p_rootMatrix_004]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_045 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_045 =
      (![g32p_rootMatrix_005, g32p_rootMatrix_101, g32p_rootMatrix_102, g32p_rootMatrix_103]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_046 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_046 =
      (![g32p_rootMatrix_102, g32p_rootMatrix_104, g32p_rootMatrix_105, g32p_rootMatrix_106]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_047 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_047 =
      (![g32p_rootMatrix_107, g32p_rootMatrix_086, g32p_rootMatrix_108, g32p_rootMatrix_109]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_048 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_048 =
      (![g32p_rootMatrix_108, g32p_rootMatrix_050, g32p_rootMatrix_110, g32p_rootMatrix_048]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_049 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_049 =
      (![g32p_rootMatrix_049, g32p_rootMatrix_006, g32p_rootMatrix_111, g32p_rootMatrix_112]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_050 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_050 =
      (![g32p_rootMatrix_105, g32p_rootMatrix_113, g32p_rootMatrix_005, g32p_rootMatrix_050]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_051 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_051 =
      (![g32p_rootMatrix_051, g32p_rootMatrix_051, g32p_rootMatrix_053, g32p_rootMatrix_114]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_052 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_052 =
      (![g32p_rootMatrix_115, g32p_rootMatrix_054, g32p_rootMatrix_052, g32p_rootMatrix_045]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_053 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_053 =
      (![g32p_rootMatrix_053, g32p_rootMatrix_112, g32p_rootMatrix_116, g32p_rootMatrix_005]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_054 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_054 =
      (![g32p_rootMatrix_006, g32p_rootMatrix_117, g32p_rootMatrix_118, g32p_rootMatrix_101]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_055 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_055 =
      (![g32p_rootMatrix_118, g32p_rootMatrix_119, g32p_rootMatrix_120, g32p_rootMatrix_121]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_056 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_056 =
      (![g32p_rootMatrix_056, g32p_rootMatrix_122, g32p_rootMatrix_049, g32p_rootMatrix_056]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_057 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_057 =
      (![g32p_rootMatrix_120, g32p_rootMatrix_057, g32p_rootMatrix_006, g32p_rootMatrix_123]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_058 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_058 =
      (![g32p_rootMatrix_124, g32p_rootMatrix_109, g32p_rootMatrix_125, g32p_rootMatrix_095]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_059 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_059 =
      (![g32p_rootMatrix_125, g32p_rootMatrix_059, g32p_rootMatrix_126, g32p_rootMatrix_057]) k := by
  fin_cases k <;> decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_block_02 (r : Fin 16) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k)
      (g32p_rootMatrix (g32p_finBlockIndex 240 2 r)) =
        g32p_rootMatrix (g32p_rootTransition (g32p_finBlockIndex 240 2 r) k) := by
  fin_cases r
  · fin_cases k
    · exact g32p_rootTransition_check_032 0
    · exact g32p_rootTransition_check_032 1
    · exact g32p_rootTransition_check_032 2
    · exact g32p_rootTransition_check_032 3
  · fin_cases k
    · exact g32p_rootTransition_check_033 0
    · exact g32p_rootTransition_check_033 1
    · exact g32p_rootTransition_check_033 2
    · exact g32p_rootTransition_check_033 3
  · fin_cases k
    · exact g32p_rootTransition_check_034 0
    · exact g32p_rootTransition_check_034 1
    · exact g32p_rootTransition_check_034 2
    · exact g32p_rootTransition_check_034 3
  · fin_cases k
    · exact g32p_rootTransition_check_035 0
    · exact g32p_rootTransition_check_035 1
    · exact g32p_rootTransition_check_035 2
    · exact g32p_rootTransition_check_035 3
  · fin_cases k
    · exact g32p_rootTransition_check_036 0
    · exact g32p_rootTransition_check_036 1
    · exact g32p_rootTransition_check_036 2
    · exact g32p_rootTransition_check_036 3
  · fin_cases k
    · exact g32p_rootTransition_check_037 0
    · exact g32p_rootTransition_check_037 1
    · exact g32p_rootTransition_check_037 2
    · exact g32p_rootTransition_check_037 3
  · fin_cases k
    · exact g32p_rootTransition_check_038 0
    · exact g32p_rootTransition_check_038 1
    · exact g32p_rootTransition_check_038 2
    · exact g32p_rootTransition_check_038 3
  · fin_cases k
    · exact g32p_rootTransition_check_039 0
    · exact g32p_rootTransition_check_039 1
    · exact g32p_rootTransition_check_039 2
    · exact g32p_rootTransition_check_039 3
  · fin_cases k
    · exact g32p_rootTransition_check_040 0
    · exact g32p_rootTransition_check_040 1
    · exact g32p_rootTransition_check_040 2
    · exact g32p_rootTransition_check_040 3
  · fin_cases k
    · exact g32p_rootTransition_check_041 0
    · exact g32p_rootTransition_check_041 1
    · exact g32p_rootTransition_check_041 2
    · exact g32p_rootTransition_check_041 3
  · fin_cases k
    · exact g32p_rootTransition_check_042 0
    · exact g32p_rootTransition_check_042 1
    · exact g32p_rootTransition_check_042 2
    · exact g32p_rootTransition_check_042 3
  · fin_cases k
    · exact g32p_rootTransition_check_043 0
    · exact g32p_rootTransition_check_043 1
    · exact g32p_rootTransition_check_043 2
    · exact g32p_rootTransition_check_043 3
  · fin_cases k
    · exact g32p_rootTransition_check_044 0
    · exact g32p_rootTransition_check_044 1
    · exact g32p_rootTransition_check_044 2
    · exact g32p_rootTransition_check_044 3
  · fin_cases k
    · exact g32p_rootTransition_check_045 0
    · exact g32p_rootTransition_check_045 1
    · exact g32p_rootTransition_check_045 2
    · exact g32p_rootTransition_check_045 3
  · fin_cases k
    · exact g32p_rootTransition_check_046 0
    · exact g32p_rootTransition_check_046 1
    · exact g32p_rootTransition_check_046 2
    · exact g32p_rootTransition_check_046 3
  · fin_cases k
    · exact g32p_rootTransition_check_047 0
    · exact g32p_rootTransition_check_047 1
    · exact g32p_rootTransition_check_047 2
    · exact g32p_rootTransition_check_047 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_check_060 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_060 =
      (![g32p_rootMatrix_101, g32p_rootMatrix_088, g32p_rootMatrix_060, g32p_rootMatrix_099]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_061 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_061 =
      (![g32p_rootMatrix_009, g32p_rootMatrix_127, g32p_rootMatrix_128, g32p_rootMatrix_061]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_062 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_062 =
      (![g32p_rootMatrix_062, g32p_rootMatrix_099, g32p_rootMatrix_129, g32p_rootMatrix_030]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_063 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_063 =
      (![g32p_rootMatrix_063, g32p_rootMatrix_130, g32p_rootMatrix_104, g32p_rootMatrix_120]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_064 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_064 =
      (![g32p_rootMatrix_128, g32p_rootMatrix_131, g32p_rootMatrix_007, g32p_rootMatrix_132]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_065 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_065 =
      (![g32p_rootMatrix_073, g32p_rootMatrix_120, g32p_rootMatrix_065, g32p_rootMatrix_133]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_066 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_066 =
      (![g32p_rootMatrix_008, g32p_rootMatrix_107, g32p_rootMatrix_131, g32p_rootMatrix_066]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_067 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_067 =
      (![g32p_rootMatrix_131, g32p_rootMatrix_067, g32p_rootMatrix_134, g32p_rootMatrix_135]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_068 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_068 =
      (![g32p_rootMatrix_071, g32p_rootMatrix_103, g32p_rootMatrix_068, g32p_rootMatrix_117]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_069 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_069 =
      (![g32p_rootMatrix_134, g32p_rootMatrix_069, g32p_rootMatrix_008, g32p_rootMatrix_136]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_070 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_070 =
      (![g32p_rootMatrix_070, g32p_rootMatrix_070, g32p_rootMatrix_034, g32p_rootMatrix_069]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_071 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_071 =
      (![g32p_rootMatrix_137, g32p_rootMatrix_013, g32p_rootMatrix_071, g32p_rootMatrix_008]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_072 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_072 =
      (![g32p_rootMatrix_072, g32p_rootMatrix_026, g32p_rootMatrix_072, g32p_rootMatrix_072]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_073 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_073 =
      (![g32p_rootMatrix_138, g32p_rootMatrix_073, g32p_rootMatrix_073, g32p_rootMatrix_009]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_074 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_074 =
      (![g32p_rootMatrix_010, g32p_rootMatrix_074, g32p_rootMatrix_074, g32p_rootMatrix_074]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_075 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_075 =
      (![g32p_rootMatrix_075, g32p_rootMatrix_085, g32p_rootMatrix_029, g32p_rootMatrix_075]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_076 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_076 =
      (![g32p_rootMatrix_076, g32p_rootMatrix_030, g32p_rootMatrix_139, g32p_rootMatrix_088]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_077 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_077 =
      (![g32p_rootMatrix_012, g32p_rootMatrix_077, g32p_rootMatrix_140, g32p_rootMatrix_141]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_078 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_078 =
      (![g32p_rootMatrix_081, g32p_rootMatrix_142, g32p_rootMatrix_078, g32p_rootMatrix_105]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_079 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_079 =
      (![g32p_rootMatrix_140, g32p_rootMatrix_143, g32p_rootMatrix_011, g32p_rootMatrix_144]) k := by
  fin_cases k <;> decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_block_03 (r : Fin 16) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k)
      (g32p_rootMatrix (g32p_finBlockIndex 240 3 r)) =
        g32p_rootMatrix (g32p_rootTransition (g32p_finBlockIndex 240 3 r) k) := by
  fin_cases r
  · fin_cases k
    · exact g32p_rootTransition_check_048 0
    · exact g32p_rootTransition_check_048 1
    · exact g32p_rootTransition_check_048 2
    · exact g32p_rootTransition_check_048 3
  · fin_cases k
    · exact g32p_rootTransition_check_049 0
    · exact g32p_rootTransition_check_049 1
    · exact g32p_rootTransition_check_049 2
    · exact g32p_rootTransition_check_049 3
  · fin_cases k
    · exact g32p_rootTransition_check_050 0
    · exact g32p_rootTransition_check_050 1
    · exact g32p_rootTransition_check_050 2
    · exact g32p_rootTransition_check_050 3
  · fin_cases k
    · exact g32p_rootTransition_check_051 0
    · exact g32p_rootTransition_check_051 1
    · exact g32p_rootTransition_check_051 2
    · exact g32p_rootTransition_check_051 3
  · fin_cases k
    · exact g32p_rootTransition_check_052 0
    · exact g32p_rootTransition_check_052 1
    · exact g32p_rootTransition_check_052 2
    · exact g32p_rootTransition_check_052 3
  · fin_cases k
    · exact g32p_rootTransition_check_053 0
    · exact g32p_rootTransition_check_053 1
    · exact g32p_rootTransition_check_053 2
    · exact g32p_rootTransition_check_053 3
  · fin_cases k
    · exact g32p_rootTransition_check_054 0
    · exact g32p_rootTransition_check_054 1
    · exact g32p_rootTransition_check_054 2
    · exact g32p_rootTransition_check_054 3
  · fin_cases k
    · exact g32p_rootTransition_check_055 0
    · exact g32p_rootTransition_check_055 1
    · exact g32p_rootTransition_check_055 2
    · exact g32p_rootTransition_check_055 3
  · fin_cases k
    · exact g32p_rootTransition_check_056 0
    · exact g32p_rootTransition_check_056 1
    · exact g32p_rootTransition_check_056 2
    · exact g32p_rootTransition_check_056 3
  · fin_cases k
    · exact g32p_rootTransition_check_057 0
    · exact g32p_rootTransition_check_057 1
    · exact g32p_rootTransition_check_057 2
    · exact g32p_rootTransition_check_057 3
  · fin_cases k
    · exact g32p_rootTransition_check_058 0
    · exact g32p_rootTransition_check_058 1
    · exact g32p_rootTransition_check_058 2
    · exact g32p_rootTransition_check_058 3
  · fin_cases k
    · exact g32p_rootTransition_check_059 0
    · exact g32p_rootTransition_check_059 1
    · exact g32p_rootTransition_check_059 2
    · exact g32p_rootTransition_check_059 3
  · fin_cases k
    · exact g32p_rootTransition_check_060 0
    · exact g32p_rootTransition_check_060 1
    · exact g32p_rootTransition_check_060 2
    · exact g32p_rootTransition_check_060 3
  · fin_cases k
    · exact g32p_rootTransition_check_061 0
    · exact g32p_rootTransition_check_061 1
    · exact g32p_rootTransition_check_061 2
    · exact g32p_rootTransition_check_061 3
  · fin_cases k
    · exact g32p_rootTransition_check_062 0
    · exact g32p_rootTransition_check_062 1
    · exact g32p_rootTransition_check_062 2
    · exact g32p_rootTransition_check_062 3
  · fin_cases k
    · exact g32p_rootTransition_check_063 0
    · exact g32p_rootTransition_check_063 1
    · exact g32p_rootTransition_check_063 2
    · exact g32p_rootTransition_check_063 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_block_04 (r : Fin 16) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k)
      (g32p_rootMatrix (g32p_finBlockIndex 240 4 r)) =
        g32p_rootMatrix (g32p_rootTransition (g32p_finBlockIndex 240 4 r) k) := by
  fin_cases r
  · fin_cases k
    · exact g32p_rootTransition_check_064 0
    · exact g32p_rootTransition_check_064 1
    · exact g32p_rootTransition_check_064 2
    · exact g32p_rootTransition_check_064 3
  · fin_cases k
    · exact g32p_rootTransition_check_065 0
    · exact g32p_rootTransition_check_065 1
    · exact g32p_rootTransition_check_065 2
    · exact g32p_rootTransition_check_065 3
  · fin_cases k
    · exact g32p_rootTransition_check_066 0
    · exact g32p_rootTransition_check_066 1
    · exact g32p_rootTransition_check_066 2
    · exact g32p_rootTransition_check_066 3
  · fin_cases k
    · exact g32p_rootTransition_check_067 0
    · exact g32p_rootTransition_check_067 1
    · exact g32p_rootTransition_check_067 2
    · exact g32p_rootTransition_check_067 3
  · fin_cases k
    · exact g32p_rootTransition_check_068 0
    · exact g32p_rootTransition_check_068 1
    · exact g32p_rootTransition_check_068 2
    · exact g32p_rootTransition_check_068 3
  · fin_cases k
    · exact g32p_rootTransition_check_069 0
    · exact g32p_rootTransition_check_069 1
    · exact g32p_rootTransition_check_069 2
    · exact g32p_rootTransition_check_069 3
  · fin_cases k
    · exact g32p_rootTransition_check_070 0
    · exact g32p_rootTransition_check_070 1
    · exact g32p_rootTransition_check_070 2
    · exact g32p_rootTransition_check_070 3
  · fin_cases k
    · exact g32p_rootTransition_check_071 0
    · exact g32p_rootTransition_check_071 1
    · exact g32p_rootTransition_check_071 2
    · exact g32p_rootTransition_check_071 3
  · fin_cases k
    · exact g32p_rootTransition_check_072 0
    · exact g32p_rootTransition_check_072 1
    · exact g32p_rootTransition_check_072 2
    · exact g32p_rootTransition_check_072 3
  · fin_cases k
    · exact g32p_rootTransition_check_073 0
    · exact g32p_rootTransition_check_073 1
    · exact g32p_rootTransition_check_073 2
    · exact g32p_rootTransition_check_073 3
  · fin_cases k
    · exact g32p_rootTransition_check_074 0
    · exact g32p_rootTransition_check_074 1
    · exact g32p_rootTransition_check_074 2
    · exact g32p_rootTransition_check_074 3
  · fin_cases k
    · exact g32p_rootTransition_check_075 0
    · exact g32p_rootTransition_check_075 1
    · exact g32p_rootTransition_check_075 2
    · exact g32p_rootTransition_check_075 3
  · fin_cases k
    · exact g32p_rootTransition_check_076 0
    · exact g32p_rootTransition_check_076 1
    · exact g32p_rootTransition_check_076 2
    · exact g32p_rootTransition_check_076 3
  · fin_cases k
    · exact g32p_rootTransition_check_077 0
    · exact g32p_rootTransition_check_077 1
    · exact g32p_rootTransition_check_077 2
    · exact g32p_rootTransition_check_077 3
  · fin_cases k
    · exact g32p_rootTransition_check_078 0
    · exact g32p_rootTransition_check_078 1
    · exact g32p_rootTransition_check_078 2
    · exact g32p_rootTransition_check_078 3
  · fin_cases k
    · exact g32p_rootTransition_check_079 0
    · exact g32p_rootTransition_check_079 1
    · exact g32p_rootTransition_check_079 2
    · exact g32p_rootTransition_check_079 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_check_080 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_080 =
      (![g32p_rootMatrix_080, g32p_rootMatrix_105, g32p_rootMatrix_121, g32p_rootMatrix_145]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_081 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_081 =
      (![g32p_rootMatrix_146, g32p_rootMatrix_012, g32p_rootMatrix_081, g32p_rootMatrix_081]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_082 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_082 =
      (![g32p_rootMatrix_082, g32p_rootMatrix_082, g32p_rootMatrix_082, g32p_rootMatrix_037]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_083 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_083 =
      (![g32p_rootMatrix_013, g32p_rootMatrix_083, g32p_rootMatrix_144, g32p_rootMatrix_124]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_084 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_084 =
      (![g32p_rootMatrix_144, g32p_rootMatrix_147, g32p_rootMatrix_148, g32p_rootMatrix_084]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_085 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_085 =
      (![g32p_rootMatrix_148, g32p_rootMatrix_149, g32p_rootMatrix_013, g32p_rootMatrix_085]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_086 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_086 =
      (![g32p_rootMatrix_014, g32p_rootMatrix_150, g32p_rootMatrix_151, g32p_rootMatrix_152]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_087 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_087 =
      (![g32p_rootMatrix_151, g32p_rootMatrix_153, g32p_rootMatrix_154, g32p_rootMatrix_155]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_088 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_088 =
      (![g32p_rootMatrix_156, g32p_rootMatrix_023, g32p_rootMatrix_157, g32p_rootMatrix_158]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_089 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_089 =
      (![g32p_rootMatrix_157, g32p_rootMatrix_091, g32p_rootMatrix_159, g32p_rootMatrix_089]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_090 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_090 =
      (![g32p_rootMatrix_090, g32p_rootMatrix_015, g32p_rootMatrix_160, g32p_rootMatrix_161]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_091 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_091 =
      (![g32p_rootMatrix_154, g32p_rootMatrix_162, g32p_rootMatrix_014, g32p_rootMatrix_091]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_092 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_092 =
      (![g32p_rootMatrix_092, g32p_rootMatrix_092, g32p_rootMatrix_094, g32p_rootMatrix_163]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_093 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_093 =
      (![g32p_rootMatrix_164, g32p_rootMatrix_095, g32p_rootMatrix_093, g32p_rootMatrix_086]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_094 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_094 =
      (![g32p_rootMatrix_094, g32p_rootMatrix_161, g32p_rootMatrix_165, g32p_rootMatrix_014]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_095 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_095 =
      (![g32p_rootMatrix_015, g32p_rootMatrix_166, g32p_rootMatrix_167, g32p_rootMatrix_150]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_096 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_096 =
      (![g32p_rootMatrix_167, g32p_rootMatrix_168, g32p_rootMatrix_169, g32p_rootMatrix_170]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_097 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_097 =
      (![g32p_rootMatrix_097, g32p_rootMatrix_171, g32p_rootMatrix_090, g32p_rootMatrix_097]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_098 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_098 =
      (![g32p_rootMatrix_169, g32p_rootMatrix_098, g32p_rootMatrix_015, g32p_rootMatrix_172]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_099 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_099 =
      (![g32p_rootMatrix_173, g32p_rootMatrix_158, g32p_rootMatrix_174, g32p_rootMatrix_032]) k := by
  fin_cases k <;> decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_block_05 (r : Fin 16) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k)
      (g32p_rootMatrix (g32p_finBlockIndex 240 5 r)) =
        g32p_rootMatrix (g32p_rootTransition (g32p_finBlockIndex 240 5 r) k) := by
  fin_cases r
  · fin_cases k
    · exact g32p_rootTransition_check_080 0
    · exact g32p_rootTransition_check_080 1
    · exact g32p_rootTransition_check_080 2
    · exact g32p_rootTransition_check_080 3
  · fin_cases k
    · exact g32p_rootTransition_check_081 0
    · exact g32p_rootTransition_check_081 1
    · exact g32p_rootTransition_check_081 2
    · exact g32p_rootTransition_check_081 3
  · fin_cases k
    · exact g32p_rootTransition_check_082 0
    · exact g32p_rootTransition_check_082 1
    · exact g32p_rootTransition_check_082 2
    · exact g32p_rootTransition_check_082 3
  · fin_cases k
    · exact g32p_rootTransition_check_083 0
    · exact g32p_rootTransition_check_083 1
    · exact g32p_rootTransition_check_083 2
    · exact g32p_rootTransition_check_083 3
  · fin_cases k
    · exact g32p_rootTransition_check_084 0
    · exact g32p_rootTransition_check_084 1
    · exact g32p_rootTransition_check_084 2
    · exact g32p_rootTransition_check_084 3
  · fin_cases k
    · exact g32p_rootTransition_check_085 0
    · exact g32p_rootTransition_check_085 1
    · exact g32p_rootTransition_check_085 2
    · exact g32p_rootTransition_check_085 3
  · fin_cases k
    · exact g32p_rootTransition_check_086 0
    · exact g32p_rootTransition_check_086 1
    · exact g32p_rootTransition_check_086 2
    · exact g32p_rootTransition_check_086 3
  · fin_cases k
    · exact g32p_rootTransition_check_087 0
    · exact g32p_rootTransition_check_087 1
    · exact g32p_rootTransition_check_087 2
    · exact g32p_rootTransition_check_087 3
  · fin_cases k
    · exact g32p_rootTransition_check_088 0
    · exact g32p_rootTransition_check_088 1
    · exact g32p_rootTransition_check_088 2
    · exact g32p_rootTransition_check_088 3
  · fin_cases k
    · exact g32p_rootTransition_check_089 0
    · exact g32p_rootTransition_check_089 1
    · exact g32p_rootTransition_check_089 2
    · exact g32p_rootTransition_check_089 3
  · fin_cases k
    · exact g32p_rootTransition_check_090 0
    · exact g32p_rootTransition_check_090 1
    · exact g32p_rootTransition_check_090 2
    · exact g32p_rootTransition_check_090 3
  · fin_cases k
    · exact g32p_rootTransition_check_091 0
    · exact g32p_rootTransition_check_091 1
    · exact g32p_rootTransition_check_091 2
    · exact g32p_rootTransition_check_091 3
  · fin_cases k
    · exact g32p_rootTransition_check_092 0
    · exact g32p_rootTransition_check_092 1
    · exact g32p_rootTransition_check_092 2
    · exact g32p_rootTransition_check_092 3
  · fin_cases k
    · exact g32p_rootTransition_check_093 0
    · exact g32p_rootTransition_check_093 1
    · exact g32p_rootTransition_check_093 2
    · exact g32p_rootTransition_check_093 3
  · fin_cases k
    · exact g32p_rootTransition_check_094 0
    · exact g32p_rootTransition_check_094 1
    · exact g32p_rootTransition_check_094 2
    · exact g32p_rootTransition_check_094 3
  · fin_cases k
    · exact g32p_rootTransition_check_095 0
    · exact g32p_rootTransition_check_095 1
    · exact g32p_rootTransition_check_095 2
    · exact g32p_rootTransition_check_095 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_check_100 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_100 =
      (![g32p_rootMatrix_174, g32p_rootMatrix_100, g32p_rootMatrix_175, g32p_rootMatrix_098]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_101 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_101 =
      (![g32p_rootMatrix_150, g32p_rootMatrix_025, g32p_rootMatrix_101, g32p_rootMatrix_036]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_102 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_102 =
      (![g32p_rootMatrix_018, g32p_rootMatrix_134, g32p_rootMatrix_176, g32p_rootMatrix_102]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_103 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_103 =
      (![g32p_rootMatrix_103, g32p_rootMatrix_036, g32p_rootMatrix_177, g32p_rootMatrix_052]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_104 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_104 =
      (![g32p_rootMatrix_104, g32p_rootMatrix_178, g32p_rootMatrix_153, g32p_rootMatrix_169]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_105 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_105 =
      (![g32p_rootMatrix_176, g32p_rootMatrix_179, g32p_rootMatrix_016, g32p_rootMatrix_180]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_106 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_106 =
      (![g32p_rootMatrix_114, g32p_rootMatrix_169, g32p_rootMatrix_106, g32p_rootMatrix_181]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_107 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_107 =
      (![g32p_rootMatrix_017, g32p_rootMatrix_156, g32p_rootMatrix_179, g32p_rootMatrix_107]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_108 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_108 =
      (![g32p_rootMatrix_179, g32p_rootMatrix_108, g32p_rootMatrix_182, g32p_rootMatrix_183]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_109 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_109 =
      (![g32p_rootMatrix_112, g32p_rootMatrix_152, g32p_rootMatrix_109, g32p_rootMatrix_166]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_110 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_110 =
      (![g32p_rootMatrix_182, g32p_rootMatrix_110, g32p_rootMatrix_017, g32p_rootMatrix_184]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_111 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_111 =
      (![g32p_rootMatrix_111, g32p_rootMatrix_111, g32p_rootMatrix_056, g32p_rootMatrix_110]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_112 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_112 =
      (![g32p_rootMatrix_185, g32p_rootMatrix_022, g32p_rootMatrix_112, g32p_rootMatrix_017]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_113 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_113 =
      (![g32p_rootMatrix_113, g32p_rootMatrix_048, g32p_rootMatrix_113, g32p_rootMatrix_113]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_114 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_114 =
      (![g32p_rootMatrix_186, g32p_rootMatrix_114, g32p_rootMatrix_114, g32p_rootMatrix_018]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_115 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_115 =
      (![g32p_rootMatrix_019, g32p_rootMatrix_115, g32p_rootMatrix_115, g32p_rootMatrix_115]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_116 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_116 =
      (![g32p_rootMatrix_116, g32p_rootMatrix_126, g32p_rootMatrix_051, g32p_rootMatrix_116]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_117 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_117 =
      (![g32p_rootMatrix_117, g32p_rootMatrix_052, g32p_rootMatrix_187, g32p_rootMatrix_025]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_118 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_118 =
      (![g32p_rootMatrix_021, g32p_rootMatrix_118, g32p_rootMatrix_188, g32p_rootMatrix_148]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_119 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_119 =
      (![g32p_rootMatrix_122, g32p_rootMatrix_189, g32p_rootMatrix_119, g32p_rootMatrix_154]) k := by
  fin_cases k <;> decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_block_06 (r : Fin 16) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k)
      (g32p_rootMatrix (g32p_finBlockIndex 240 6 r)) =
        g32p_rootMatrix (g32p_rootTransition (g32p_finBlockIndex 240 6 r) k) := by
  fin_cases r
  · fin_cases k
    · exact g32p_rootTransition_check_096 0
    · exact g32p_rootTransition_check_096 1
    · exact g32p_rootTransition_check_096 2
    · exact g32p_rootTransition_check_096 3
  · fin_cases k
    · exact g32p_rootTransition_check_097 0
    · exact g32p_rootTransition_check_097 1
    · exact g32p_rootTransition_check_097 2
    · exact g32p_rootTransition_check_097 3
  · fin_cases k
    · exact g32p_rootTransition_check_098 0
    · exact g32p_rootTransition_check_098 1
    · exact g32p_rootTransition_check_098 2
    · exact g32p_rootTransition_check_098 3
  · fin_cases k
    · exact g32p_rootTransition_check_099 0
    · exact g32p_rootTransition_check_099 1
    · exact g32p_rootTransition_check_099 2
    · exact g32p_rootTransition_check_099 3
  · fin_cases k
    · exact g32p_rootTransition_check_100 0
    · exact g32p_rootTransition_check_100 1
    · exact g32p_rootTransition_check_100 2
    · exact g32p_rootTransition_check_100 3
  · fin_cases k
    · exact g32p_rootTransition_check_101 0
    · exact g32p_rootTransition_check_101 1
    · exact g32p_rootTransition_check_101 2
    · exact g32p_rootTransition_check_101 3
  · fin_cases k
    · exact g32p_rootTransition_check_102 0
    · exact g32p_rootTransition_check_102 1
    · exact g32p_rootTransition_check_102 2
    · exact g32p_rootTransition_check_102 3
  · fin_cases k
    · exact g32p_rootTransition_check_103 0
    · exact g32p_rootTransition_check_103 1
    · exact g32p_rootTransition_check_103 2
    · exact g32p_rootTransition_check_103 3
  · fin_cases k
    · exact g32p_rootTransition_check_104 0
    · exact g32p_rootTransition_check_104 1
    · exact g32p_rootTransition_check_104 2
    · exact g32p_rootTransition_check_104 3
  · fin_cases k
    · exact g32p_rootTransition_check_105 0
    · exact g32p_rootTransition_check_105 1
    · exact g32p_rootTransition_check_105 2
    · exact g32p_rootTransition_check_105 3
  · fin_cases k
    · exact g32p_rootTransition_check_106 0
    · exact g32p_rootTransition_check_106 1
    · exact g32p_rootTransition_check_106 2
    · exact g32p_rootTransition_check_106 3
  · fin_cases k
    · exact g32p_rootTransition_check_107 0
    · exact g32p_rootTransition_check_107 1
    · exact g32p_rootTransition_check_107 2
    · exact g32p_rootTransition_check_107 3
  · fin_cases k
    · exact g32p_rootTransition_check_108 0
    · exact g32p_rootTransition_check_108 1
    · exact g32p_rootTransition_check_108 2
    · exact g32p_rootTransition_check_108 3
  · fin_cases k
    · exact g32p_rootTransition_check_109 0
    · exact g32p_rootTransition_check_109 1
    · exact g32p_rootTransition_check_109 2
    · exact g32p_rootTransition_check_109 3
  · fin_cases k
    · exact g32p_rootTransition_check_110 0
    · exact g32p_rootTransition_check_110 1
    · exact g32p_rootTransition_check_110 2
    · exact g32p_rootTransition_check_110 3
  · fin_cases k
    · exact g32p_rootTransition_check_111 0
    · exact g32p_rootTransition_check_111 1
    · exact g32p_rootTransition_check_111 2
    · exact g32p_rootTransition_check_111 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_check_120 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_120 =
      (![g32p_rootMatrix_188, g32p_rootMatrix_190, g32p_rootMatrix_020, g32p_rootMatrix_191]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_121 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_121 =
      (![g32p_rootMatrix_121, g32p_rootMatrix_154, g32p_rootMatrix_170, g32p_rootMatrix_192]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_122 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_122 =
      (![g32p_rootMatrix_193, g32p_rootMatrix_021, g32p_rootMatrix_122, g32p_rootMatrix_122]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_123 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_123 =
      (![g32p_rootMatrix_123, g32p_rootMatrix_123, g32p_rootMatrix_123, g32p_rootMatrix_059]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_124 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_124 =
      (![g32p_rootMatrix_022, g32p_rootMatrix_124, g32p_rootMatrix_191, g32p_rootMatrix_173]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_125 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_125 =
      (![g32p_rootMatrix_191, g32p_rootMatrix_194, g32p_rootMatrix_195, g32p_rootMatrix_125]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_126 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_126 =
      (![g32p_rootMatrix_195, g32p_rootMatrix_196, g32p_rootMatrix_022, g32p_rootMatrix_126]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_127 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_127 =
      (![g32p_rootMatrix_130, g32p_rootMatrix_197, g32p_rootMatrix_088, g32p_rootMatrix_127]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_128 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_128 =
      (![g32p_rootMatrix_028, g32p_rootMatrix_128, g32p_rootMatrix_023, g32p_rootMatrix_198]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_129 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_129 =
      (![g32p_rootMatrix_129, g32p_rootMatrix_129, g32p_rootMatrix_199, g32p_rootMatrix_128]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_130 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_130 =
      (![g32p_rootMatrix_159, g32p_rootMatrix_024, g32p_rootMatrix_156, g32p_rootMatrix_190]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_131 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_131 =
      (![g32p_rootMatrix_026, g32p_rootMatrix_170, g32p_rootMatrix_178, g32p_rootMatrix_200]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_132 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_132 =
      (![g32p_rootMatrix_132, g32p_rootMatrix_200, g32p_rootMatrix_133, g32p_rootMatrix_168]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_133 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_133 =
      (![g32p_rootMatrix_133, g32p_rootMatrix_191, g32p_rootMatrix_201, g32p_rootMatrix_024]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_134 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_134 =
      (![g32p_rootMatrix_178, g32p_rootMatrix_202, g32p_rootMatrix_025, g32p_rootMatrix_134]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_135 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_135 =
      (![g32p_rootMatrix_135, g32p_rootMatrix_135, g32p_rootMatrix_117, g32p_rootMatrix_203]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_136 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_136 =
      (![g32p_rootMatrix_204, g32p_rootMatrix_136, g32p_rootMatrix_136, g32p_rootMatrix_070]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_137 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_137 =
      (![g32p_rootMatrix_068, g32p_rootMatrix_137, g32p_rootMatrix_137, g32p_rootMatrix_137]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_138 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_138 =
      (![g32p_rootMatrix_065, g32p_rootMatrix_187, g32p_rootMatrix_138, g32p_rootMatrix_138]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_139 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_139 =
      (![g32p_rootMatrix_139, g32p_rootMatrix_140, g32p_rootMatrix_205, g32p_rootMatrix_139]) k := by
  fin_cases k <;> decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_block_07 (r : Fin 16) (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k)
      (g32p_rootMatrix (g32p_finBlockIndex 240 7 r)) =
        g32p_rootMatrix (g32p_rootTransition (g32p_finBlockIndex 240 7 r) k) := by
  fin_cases r
  · fin_cases k
    · exact g32p_rootTransition_check_112 0
    · exact g32p_rootTransition_check_112 1
    · exact g32p_rootTransition_check_112 2
    · exact g32p_rootTransition_check_112 3
  · fin_cases k
    · exact g32p_rootTransition_check_113 0
    · exact g32p_rootTransition_check_113 1
    · exact g32p_rootTransition_check_113 2
    · exact g32p_rootTransition_check_113 3
  · fin_cases k
    · exact g32p_rootTransition_check_114 0
    · exact g32p_rootTransition_check_114 1
    · exact g32p_rootTransition_check_114 2
    · exact g32p_rootTransition_check_114 3
  · fin_cases k
    · exact g32p_rootTransition_check_115 0
    · exact g32p_rootTransition_check_115 1
    · exact g32p_rootTransition_check_115 2
    · exact g32p_rootTransition_check_115 3
  · fin_cases k
    · exact g32p_rootTransition_check_116 0
    · exact g32p_rootTransition_check_116 1
    · exact g32p_rootTransition_check_116 2
    · exact g32p_rootTransition_check_116 3
  · fin_cases k
    · exact g32p_rootTransition_check_117 0
    · exact g32p_rootTransition_check_117 1
    · exact g32p_rootTransition_check_117 2
    · exact g32p_rootTransition_check_117 3
  · fin_cases k
    · exact g32p_rootTransition_check_118 0
    · exact g32p_rootTransition_check_118 1
    · exact g32p_rootTransition_check_118 2
    · exact g32p_rootTransition_check_118 3
  · fin_cases k
    · exact g32p_rootTransition_check_119 0
    · exact g32p_rootTransition_check_119 1
    · exact g32p_rootTransition_check_119 2
    · exact g32p_rootTransition_check_119 3
  · fin_cases k
    · exact g32p_rootTransition_check_120 0
    · exact g32p_rootTransition_check_120 1
    · exact g32p_rootTransition_check_120 2
    · exact g32p_rootTransition_check_120 3
  · fin_cases k
    · exact g32p_rootTransition_check_121 0
    · exact g32p_rootTransition_check_121 1
    · exact g32p_rootTransition_check_121 2
    · exact g32p_rootTransition_check_121 3
  · fin_cases k
    · exact g32p_rootTransition_check_122 0
    · exact g32p_rootTransition_check_122 1
    · exact g32p_rootTransition_check_122 2
    · exact g32p_rootTransition_check_122 3
  · fin_cases k
    · exact g32p_rootTransition_check_123 0
    · exact g32p_rootTransition_check_123 1
    · exact g32p_rootTransition_check_123 2
    · exact g32p_rootTransition_check_123 3
  · fin_cases k
    · exact g32p_rootTransition_check_124 0
    · exact g32p_rootTransition_check_124 1
    · exact g32p_rootTransition_check_124 2
    · exact g32p_rootTransition_check_124 3
  · fin_cases k
    · exact g32p_rootTransition_check_125 0
    · exact g32p_rootTransition_check_125 1
    · exact g32p_rootTransition_check_125 2
    · exact g32p_rootTransition_check_125 3
  · fin_cases k
    · exact g32p_rootTransition_check_126 0
    · exact g32p_rootTransition_check_126 1
    · exact g32p_rootTransition_check_126 2
    · exact g32p_rootTransition_check_126 3
  · fin_cases k
    · exact g32p_rootTransition_check_127 0
    · exact g32p_rootTransition_check_127 1
    · exact g32p_rootTransition_check_127 2
    · exact g32p_rootTransition_check_127 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_rootTransition_check_140 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_140 =
      (![g32p_rootMatrix_035, g32p_rootMatrix_206, g32p_rootMatrix_032, g32p_rootMatrix_140]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_141 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_141 =
      (![g32p_rootMatrix_145, g32p_rootMatrix_141, g32p_rootMatrix_099, g32p_rootMatrix_207]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_142 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_142 =
      (![g32p_rootMatrix_142, g32p_rootMatrix_033, g32p_rootMatrix_208, g32p_rootMatrix_179]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_143 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_143 =
      (![g32p_rootMatrix_143, g32p_rootMatrix_155, g32p_rootMatrix_142, g32p_rootMatrix_209]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_144 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_144 =
      (![g32p_rootMatrix_037, g32p_rootMatrix_209, g32p_rootMatrix_192, g32p_rootMatrix_153]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_145 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_145 =
      (![g32p_rootMatrix_175, g32p_rootMatrix_180, g32p_rootMatrix_173, g32p_rootMatrix_033]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_146 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_146 =
      (![g32p_rootMatrix_078, g32p_rootMatrix_146, g32p_rootMatrix_146, g32p_rootMatrix_177]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_147 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_147 =
      (![g32p_rootMatrix_147, g32p_rootMatrix_210, g32p_rootMatrix_103, g32p_rootMatrix_147]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_148 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_148 =
      (![g32p_rootMatrix_192, g32p_rootMatrix_148, g32p_rootMatrix_036, g32p_rootMatrix_211]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_149 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_149 =
      (![g32p_rootMatrix_212, g32p_rootMatrix_075, g32p_rootMatrix_149, g32p_rootMatrix_149]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_150 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_150 =
      (![g32p_rootMatrix_060, g32p_rootMatrix_047, g32p_rootMatrix_150, g32p_rootMatrix_058]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_151 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_151 =
      (![g32p_rootMatrix_040, g32p_rootMatrix_182, g32p_rootMatrix_213, g32p_rootMatrix_151]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_152 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_152 =
      (![g32p_rootMatrix_152, g32p_rootMatrix_058, g32p_rootMatrix_214, g32p_rootMatrix_093]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_153 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_153 =
      (![g32p_rootMatrix_153, g32p_rootMatrix_215, g32p_rootMatrix_063, g32p_rootMatrix_079]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_154 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_154 =
      (![g32p_rootMatrix_213, g32p_rootMatrix_216, g32p_rootMatrix_038, g32p_rootMatrix_217]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_155 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_155 =
      (![g32p_rootMatrix_163, g32p_rootMatrix_079, g32p_rootMatrix_155, g32p_rootMatrix_218]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_156 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_156 =
      (![g32p_rootMatrix_039, g32p_rootMatrix_066, g32p_rootMatrix_216, g32p_rootMatrix_156]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_157 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_157 =
      (![g32p_rootMatrix_216, g32p_rootMatrix_157, g32p_rootMatrix_127, g32p_rootMatrix_205]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_158 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_158 =
      (![g32p_rootMatrix_161, g32p_rootMatrix_062, g32p_rootMatrix_158, g32p_rootMatrix_076]) k := by
  fin_cases k <;> decide +kernel

theorem g32p_rootTransition_check_159 (k : Fin 4) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators k) g32p_rootMatrix_159 =
      (![g32p_rootMatrix_127, g32p_rootMatrix_159, g32p_rootMatrix_039, g32p_rootMatrix_219]) k := by
  fin_cases k <;> decide +kernel

end HodgeLean.Foundations.Program

end
end
