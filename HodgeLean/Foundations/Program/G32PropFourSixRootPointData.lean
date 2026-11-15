import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_rootMatrix_000 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_001 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_002 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_003 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_004 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_005 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_006 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_007 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_008 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_009 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_010 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_011 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_012 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_013 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_014 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_015 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_016 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_017 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_018 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_019 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_020 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_021 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_022 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_023 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_024 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_025 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_026 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_027 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_028 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_029 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_030 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨2, 2⟩, ⟨0, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_031 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨1, 2⟩, ⟨0, -1⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_032 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_033 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_034 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨0, 2⟩, ⟨1, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_035 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_036 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_037 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, -1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_038 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_039 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_040 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_041 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_042 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_043 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_044 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_045 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_046 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_047 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_048 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_049 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_050 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_051 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_052 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_053 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-2, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_054 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_055 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_056 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-2, -2⟩, ⟨0, 1⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_057 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_058 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_059 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 2⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_060 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_061 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_062 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_063 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_064 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_065 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_066 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_067 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_068 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_069 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨0, 2⟩, ⟨1, 0⟩, ⟨-1, -2⟩] i

def g32p_rootMatrix_070 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨1, 2⟩, ⟨0, -1⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_071 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨0, 2⟩, ⟨1, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_072 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_073 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_074 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_075 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_076 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨2, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_077 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -2⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_078 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_079 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_080 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_081 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_082 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_083 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_084 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_085 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_086 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_087 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_088 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_089 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_090 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_091 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_092 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_093 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨0, -2⟩, ⟨-1, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_094 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_095 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_096 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_097 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨2, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_098 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_099 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_100 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-2, -1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_101 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_102 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_103 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_104 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_105 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨-1, 1⟩, ⟨2, 1⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_106 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_107 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_108 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_109 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_110 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-2, -2⟩, ⟨0, 1⟩, ⟨2, 1⟩] i

def g32p_rootMatrix_111 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_112 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-2, -2⟩, ⟨0, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_113 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_114 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_115 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_116 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_117 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_118 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨2, 1⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_119 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_120 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_121 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_122 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_123 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_124 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_125 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_126 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_127 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_128 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨2, 2⟩, ⟨0, -1⟩, ⟨-2, -1⟩] i

def g32p_rootMatrix_129 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨2, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_130 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨1, -1⟩, ⟨-2, -1⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_131 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_132 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_133 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_134 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_135 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_136 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_137 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_138 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_139 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_140 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_141 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_142 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_143 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_144 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_145 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_146 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_147 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_148 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_149 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_150 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_151 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_152 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_153 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_154 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-1, -2⟩, ⟨-1, 1⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_155 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_156 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_157 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_158 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_159 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨2, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩] i

def g32p_rootMatrix_160 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_161 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨2, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_162 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_163 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_164 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_165 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_166 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨-1, -2⟩, ⟨0, 1⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_167 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_168 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_169 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_170 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_171 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_172 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_173 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_174 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_175 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_176 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩] i

def g32p_rootMatrix_177 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨-1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_178 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨1, 2⟩, ⟨1, -1⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_179 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_180 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_181 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_182 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_183 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_184 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_185 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_186 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_187 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_188 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_189 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_190 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_191 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_192 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_193 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_194 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨0, -2⟩, ⟨-1, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_195 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_196 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_197 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_198 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_199 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨2, 2⟩, ⟨0, -1⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_200 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_201 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_202 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_203 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_204 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_205 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_206 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_207 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_208 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_209 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_210 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_211 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_212 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_213 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨0, -2⟩, ⟨-1, 0⟩, ⟨1, 2⟩] i

def g32p_rootMatrix_214 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨-1, -2⟩, ⟨0, 1⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_215 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_216 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_217 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_218 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_219 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_220 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_221 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_222 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_223 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_224 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_225 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_226 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_227 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_228 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩] i

def g32p_rootMatrix_229 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩] i

def g32p_rootMatrix_230 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_231 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_232 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_233 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_234 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩] i

def g32p_rootMatrix_235 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩] i

def g32p_rootMatrix_236 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, -1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix_237 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩] i

def g32p_rootMatrix_238 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩] i

def g32p_rootMatrix_239 : HurwitzPrymRex_Mat :=
  fun i _ => ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩] i

def g32p_rootMatrix : Fin 240 → HurwitzPrymRex_Mat :=
  ![g32p_rootMatrix_000, g32p_rootMatrix_001, g32p_rootMatrix_002, g32p_rootMatrix_003, g32p_rootMatrix_004, g32p_rootMatrix_005, g32p_rootMatrix_006, g32p_rootMatrix_007, g32p_rootMatrix_008, g32p_rootMatrix_009, g32p_rootMatrix_010, g32p_rootMatrix_011, g32p_rootMatrix_012, g32p_rootMatrix_013, g32p_rootMatrix_014, g32p_rootMatrix_015, g32p_rootMatrix_016, g32p_rootMatrix_017, g32p_rootMatrix_018, g32p_rootMatrix_019, g32p_rootMatrix_020, g32p_rootMatrix_021, g32p_rootMatrix_022, g32p_rootMatrix_023, g32p_rootMatrix_024, g32p_rootMatrix_025, g32p_rootMatrix_026, g32p_rootMatrix_027, g32p_rootMatrix_028, g32p_rootMatrix_029, g32p_rootMatrix_030, g32p_rootMatrix_031, g32p_rootMatrix_032, g32p_rootMatrix_033, g32p_rootMatrix_034, g32p_rootMatrix_035, g32p_rootMatrix_036, g32p_rootMatrix_037, g32p_rootMatrix_038, g32p_rootMatrix_039, g32p_rootMatrix_040, g32p_rootMatrix_041, g32p_rootMatrix_042, g32p_rootMatrix_043, g32p_rootMatrix_044, g32p_rootMatrix_045, g32p_rootMatrix_046, g32p_rootMatrix_047, g32p_rootMatrix_048, g32p_rootMatrix_049, g32p_rootMatrix_050, g32p_rootMatrix_051, g32p_rootMatrix_052, g32p_rootMatrix_053, g32p_rootMatrix_054, g32p_rootMatrix_055, g32p_rootMatrix_056, g32p_rootMatrix_057, g32p_rootMatrix_058, g32p_rootMatrix_059, g32p_rootMatrix_060, g32p_rootMatrix_061, g32p_rootMatrix_062, g32p_rootMatrix_063, g32p_rootMatrix_064, g32p_rootMatrix_065, g32p_rootMatrix_066, g32p_rootMatrix_067, g32p_rootMatrix_068, g32p_rootMatrix_069, g32p_rootMatrix_070, g32p_rootMatrix_071, g32p_rootMatrix_072, g32p_rootMatrix_073, g32p_rootMatrix_074, g32p_rootMatrix_075, g32p_rootMatrix_076, g32p_rootMatrix_077, g32p_rootMatrix_078, g32p_rootMatrix_079, g32p_rootMatrix_080, g32p_rootMatrix_081, g32p_rootMatrix_082, g32p_rootMatrix_083, g32p_rootMatrix_084, g32p_rootMatrix_085, g32p_rootMatrix_086, g32p_rootMatrix_087, g32p_rootMatrix_088, g32p_rootMatrix_089, g32p_rootMatrix_090, g32p_rootMatrix_091, g32p_rootMatrix_092, g32p_rootMatrix_093, g32p_rootMatrix_094, g32p_rootMatrix_095, g32p_rootMatrix_096, g32p_rootMatrix_097, g32p_rootMatrix_098, g32p_rootMatrix_099, g32p_rootMatrix_100, g32p_rootMatrix_101, g32p_rootMatrix_102, g32p_rootMatrix_103, g32p_rootMatrix_104, g32p_rootMatrix_105, g32p_rootMatrix_106, g32p_rootMatrix_107, g32p_rootMatrix_108, g32p_rootMatrix_109, g32p_rootMatrix_110, g32p_rootMatrix_111, g32p_rootMatrix_112, g32p_rootMatrix_113, g32p_rootMatrix_114, g32p_rootMatrix_115, g32p_rootMatrix_116, g32p_rootMatrix_117, g32p_rootMatrix_118, g32p_rootMatrix_119, g32p_rootMatrix_120, g32p_rootMatrix_121, g32p_rootMatrix_122, g32p_rootMatrix_123, g32p_rootMatrix_124, g32p_rootMatrix_125, g32p_rootMatrix_126, g32p_rootMatrix_127, g32p_rootMatrix_128, g32p_rootMatrix_129, g32p_rootMatrix_130, g32p_rootMatrix_131, g32p_rootMatrix_132, g32p_rootMatrix_133, g32p_rootMatrix_134, g32p_rootMatrix_135, g32p_rootMatrix_136, g32p_rootMatrix_137, g32p_rootMatrix_138, g32p_rootMatrix_139, g32p_rootMatrix_140, g32p_rootMatrix_141, g32p_rootMatrix_142, g32p_rootMatrix_143, g32p_rootMatrix_144, g32p_rootMatrix_145, g32p_rootMatrix_146, g32p_rootMatrix_147, g32p_rootMatrix_148, g32p_rootMatrix_149, g32p_rootMatrix_150, g32p_rootMatrix_151, g32p_rootMatrix_152, g32p_rootMatrix_153, g32p_rootMatrix_154, g32p_rootMatrix_155, g32p_rootMatrix_156, g32p_rootMatrix_157, g32p_rootMatrix_158, g32p_rootMatrix_159, g32p_rootMatrix_160, g32p_rootMatrix_161, g32p_rootMatrix_162, g32p_rootMatrix_163, g32p_rootMatrix_164, g32p_rootMatrix_165, g32p_rootMatrix_166, g32p_rootMatrix_167, g32p_rootMatrix_168, g32p_rootMatrix_169, g32p_rootMatrix_170, g32p_rootMatrix_171, g32p_rootMatrix_172, g32p_rootMatrix_173, g32p_rootMatrix_174, g32p_rootMatrix_175, g32p_rootMatrix_176, g32p_rootMatrix_177, g32p_rootMatrix_178, g32p_rootMatrix_179, g32p_rootMatrix_180, g32p_rootMatrix_181, g32p_rootMatrix_182, g32p_rootMatrix_183, g32p_rootMatrix_184, g32p_rootMatrix_185, g32p_rootMatrix_186, g32p_rootMatrix_187, g32p_rootMatrix_188, g32p_rootMatrix_189, g32p_rootMatrix_190, g32p_rootMatrix_191, g32p_rootMatrix_192, g32p_rootMatrix_193, g32p_rootMatrix_194, g32p_rootMatrix_195, g32p_rootMatrix_196, g32p_rootMatrix_197, g32p_rootMatrix_198, g32p_rootMatrix_199, g32p_rootMatrix_200, g32p_rootMatrix_201, g32p_rootMatrix_202, g32p_rootMatrix_203, g32p_rootMatrix_204, g32p_rootMatrix_205, g32p_rootMatrix_206, g32p_rootMatrix_207, g32p_rootMatrix_208, g32p_rootMatrix_209, g32p_rootMatrix_210, g32p_rootMatrix_211, g32p_rootMatrix_212, g32p_rootMatrix_213, g32p_rootMatrix_214, g32p_rootMatrix_215, g32p_rootMatrix_216, g32p_rootMatrix_217, g32p_rootMatrix_218, g32p_rootMatrix_219, g32p_rootMatrix_220, g32p_rootMatrix_221, g32p_rootMatrix_222, g32p_rootMatrix_223, g32p_rootMatrix_224, g32p_rootMatrix_225, g32p_rootMatrix_226, g32p_rootMatrix_227, g32p_rootMatrix_228, g32p_rootMatrix_229, g32p_rootMatrix_230, g32p_rootMatrix_231, g32p_rootMatrix_232, g32p_rootMatrix_233, g32p_rootMatrix_234, g32p_rootMatrix_235, g32p_rootMatrix_236, g32p_rootMatrix_237, g32p_rootMatrix_238, g32p_rootMatrix_239]

def g32p_rootTransition : Fin 240 → Fin 4 → Fin 240 :=
  ![![1, 2, 0, 3], ![4, 5, 1, 6], ![7, 8, 9, 10], ![11, 10, 12, 13], ![0, 14, 4, 15], ![16, 17, 18, 19], ![20, 19, 21, 22], ![23, 16, 24, 7], ![25, 0, 26, 27], ![24, 9, 28, 29], ![30, 27, 10, 31], ![32, 11, 33, 20], ![33, 34, 35, 12], ![36, 31, 37, 0], ![38, 39, 40, 41], ![42, 41, 43, 44], ![45, 38, 46, 16], ![47, 1, 48, 49], ![46, 18, 50, 51], ![52, 49, 19, 53], ![54, 20, 55, 42], ![55, 56, 57, 21], ![58, 53, 59, 1], ![2, 60, 61, 62], ![61, 63, 64, 65], ![66, 45, 67, 68], ![67, 28, 69, 26], ![27, 3, 70, 71], ![64, 72, 2, 28], ![29, 29, 31, 73], ![74, 32, 30, 23], ![31, 71, 75, 2], ![3, 76, 77, 60], ![77, 78, 79, 80], ![34, 81, 27, 34], ![79, 35, 3, 82], ![83, 68, 84, 54], ![84, 37, 85, 35], ![86, 7, 87, 38], ![88, 4, 89, 90], ![87, 40, 91, 92], ![93, 90, 41, 94], ![95, 42, 96, 11], ![96, 97, 98, 43], ![99, 94, 100, 4], ![5, 101, 102, 103], ![102, 104, 105, 106], ![107, 86, 108, 109], ![108, 50, 110, 48], ![49, 6, 111, 112], ![105, 113, 5, 50], ![51, 51, 53, 114], ![115, 54, 52, 45], ![53, 112, 116, 5], ![6, 117, 118, 101], ![118, 119, 120, 121], ![56, 122, 49, 56], ![120, 57, 6, 123], ![124, 109, 125, 95], ![125, 59, 126, 57], ![101, 88, 60, 99], ![9, 127, 128, 61], ![62, 99, 129, 30], ![63, 130, 104, 120], ![128, 131, 7, 132], ![73, 120, 65, 133], ![8, 107, 131, 66], ![131, 67, 134, 135], ![71, 103, 68, 117], ![134, 69, 8, 136], ![70, 70, 34, 69], ![137, 13, 71, 8], ![72, 26, 72, 72], ![138, 73, 73, 9], ![10, 74, 74, 74], ![75, 85, 29, 75], ![76, 30, 139, 88], ![12, 77, 140, 141], ![81, 142, 78, 105], ![140, 143, 11, 144], ![80, 105, 121, 145], ![146, 12, 81, 81], ![82, 82, 82, 37], ![13, 83, 144, 124], ![144, 147, 148, 84], ![148, 149, 13, 85], ![14, 150, 151, 152], ![151, 153, 154, 155], ![156, 23, 157, 158], ![157, 91, 159, 89], ![90, 15, 160, 161], ![154, 162, 14, 91], ![92, 92, 94, 163], ![164, 95, 93, 86], ![94, 161, 165, 14], ![15, 166, 167, 150], ![167, 168, 169, 170], ![97, 171, 90, 97], ![169, 98, 15, 172], ![173, 158, 174, 32], ![174, 100, 175, 98], ![150, 25, 101, 36], ![18, 134, 176, 102], ![103, 36, 177, 52], ![104, 178, 153, 169], ![176, 179, 16, 180], ![114, 169, 106, 181], ![17, 156, 179, 107], ![179, 108, 182, 183], ![112, 152, 109, 166], ![182, 110, 17, 184], ![111, 111, 56, 110], ![185, 22, 112, 17], ![113, 48, 113, 113], ![186, 114, 114, 18], ![19, 115, 115, 115], ![116, 126, 51, 116], ![117, 52, 187, 25], ![21, 118, 188, 148], ![122, 189, 119, 154], ![188, 190, 20, 191], ![121, 154, 170, 192], ![193, 21, 122, 122], ![123, 123, 123, 59], ![22, 124, 191, 173], ![191, 194, 195, 125], ![195, 196, 22, 126], ![130, 197, 88, 127], ![28, 128, 23, 198], ![129, 129, 199, 128], ![159, 24, 156, 190], ![26, 170, 178, 200], ![132, 200, 133, 168], ![133, 191, 201, 24], ![178, 202, 25, 134], ![135, 135, 117, 203], ![204, 136, 136, 70], ![68, 137, 137, 137], ![65, 187, 138, 138], ![139, 140, 205, 139], ![35, 206, 32, 140], ![145, 141, 99, 207], ![142, 33, 208, 179], ![143, 155, 142, 209], ![37, 209, 192, 153], ![175, 180, 173, 33], ![78, 146, 146, 177], ![147, 210, 103, 147], ![192, 148, 36, 211], ![212, 75, 149, 149], ![60, 47, 150, 58], ![40, 182, 213, 151], ![152, 58, 214, 93], ![153, 215, 63, 79], ![213, 216, 38, 217], ![163, 79, 155, 218], ![39, 66, 216, 156], ![216, 157, 127, 205], ![161, 62, 158, 76], ![127, 159, 39, 219], ![160, 160, 97, 159], ![220, 44, 161, 39], ![162, 89, 162, 162], ![206, 163, 163, 40], ![41, 164, 164, 164], ![165, 175, 92, 165], ![166, 93, 221, 47], ![43, 167, 222, 195], ![171, 223, 168, 64], ![222, 224, 42, 225], ![170, 64, 80, 226], ![198, 43, 171, 171], ![172, 172, 172, 100], ![44, 173, 225, 83], ![225, 199, 141, 174], ![141, 227, 44, 175], ![50, 176, 45, 146], ![177, 177, 147, 176], ![69, 46, 66, 224], ![48, 80, 215, 228], ![180, 228, 181, 78], ![181, 225, 229, 46], ![215, 230, 47, 182], ![183, 183, 166, 231], ![209, 184, 184, 111], ![109, 185, 185, 185], ![106, 221, 186, 186], ![187, 188, 135, 187], ![57, 138, 54, 188], ![189, 55, 232, 216], ![190, 65, 189, 233], ![59, 233, 226, 63], ![85, 217, 83, 55], ![119, 193, 193, 214], ![194, 234, 152, 194], ![226, 195, 58, 235], ![200, 116, 196, 196], ![197, 61, 197, 197], ![168, 198, 198, 129], ![199, 236, 62, 199], ![203, 226, 200, 223], ![201, 201, 132, 201], ![202, 102, 202, 202], ![196, 203, 203, 67], ![236, 181, 204, 178], ![205, 205, 76, 237], ![155, 139, 206, 206], ![207, 207, 207, 77], ![208, 208, 143, 208], ![210, 218, 209, 215], ![184, 84, 210, 210], ![211, 211, 211, 118], ![237, 192, 212, 189], ![91, 213, 86, 193], ![214, 214, 194, 213], ![110, 87, 107, 143], ![89, 121, 130, 212], ![217, 212, 218, 119], ![218, 144, 238, 87], ![233, 219, 219, 160], ![158, 220, 220, 220], ![221, 222, 183, 221], ![98, 186, 95, 222], ![223, 96, 239, 131], ![224, 106, 223, 204], ![100, 204, 145, 104], ![126, 132, 124, 96], ![228, 165, 227, 227], ![231, 145, 228, 142], ![229, 229, 180, 229], ![230, 151, 230, 230], ![227, 231, 231, 108], ![232, 232, 190, 232], ![234, 133, 233, 130], ![219, 125, 234, 234], ![235, 235, 235, 167], ![136, 174, 236, 236], ![149, 237, 237, 157], ![238, 238, 217, 238], ![239, 239, 224, 239]]

end HodgeLean.Foundations.Program
