import HodgeLean.Foundations.Program.G32PropFourSixPacked0191
import HodgeLean.Foundations.Program.G32PropFourSixPacked0187
import HodgeLean.Foundations.Program.G32PropFourSixPacked0008

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalPowerTrace_060 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩]

theorem g32p_literalPowerTrace_check_060 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_060 (k.val + 1)) =
      g32p_literalPowerTrace_060 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_061 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, 0⟩, ⟨1, 2⟩, ⟨2, 0⟩, ⟨-1, 2⟩]

theorem g32p_literalPowerTrace_check_061 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_061 (k.val + 1)) =
      g32p_literalPowerTrace_061 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_062 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨2, 3⟩, ⟨1, 0⟩]

theorem g32p_literalPowerTrace_check_062 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_062 (k.val + 1)) =
      g32p_literalPowerTrace_062 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_063 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-2, 0⟩, ⟨2, -1⟩]

theorem g32p_literalPowerTrace_check_063 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_063 (k.val + 1)) =
      g32p_literalPowerTrace_063 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_064 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 2⟩, ⟨-3, -2⟩, ⟨0, 0⟩, ⟨-1, 2⟩]

theorem g32p_literalPowerTrace_check_064 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_064 (k.val + 1)) =
      g32p_literalPowerTrace_064 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_065 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨0, 4⟩, ⟨0, 0⟩, ⟨-4, -4⟩]

theorem g32p_literalPowerTrace_check_065 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_065 (k.val + 1)) =
      g32p_literalPowerTrace_065 k := by
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

def g32p_literalPowerTrace_066 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]

theorem g32p_literalPowerTrace_check_066 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_066 (k.val + 1)) =
      g32p_literalPowerTrace_066 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_067 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, 3⟩, ⟨-2, -3⟩, ⟨4, 0⟩, ⟨1, 3⟩]

theorem g32p_literalPowerTrace_check_067 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_067 (k.val + 1)) =
      g32p_literalPowerTrace_067 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_068 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, -3⟩, ⟨0, 1⟩]

theorem g32p_literalPowerTrace_check_068 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_068 (k.val + 1)) =
      g32p_literalPowerTrace_068 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_069 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨4, 0⟩]

theorem g32p_literalPowerTrace_check_069 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_069 (k.val + 1)) =
      g32p_literalPowerTrace_069 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_070 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 3⟩, ⟨0, 1⟩]

theorem g32p_literalPowerTrace_check_070 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_070 (k.val + 1)) =
      g32p_literalPowerTrace_070 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_071 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]

theorem g32p_literalPowerTrace_check_071 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_071 (k.val + 1)) =
      g32p_literalPowerTrace_071 k := by
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

def g32p_literalPowerTrace_072 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, -1⟩, ⟨2, 1⟩, ⟨-2, 0⟩, ⟨1, 3⟩]

theorem g32p_literalPowerTrace_check_072 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_072 (k.val + 1)) =
      g32p_literalPowerTrace_072 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_073 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]

theorem g32p_literalPowerTrace_check_073 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_073 (k.val + 1)) =
      g32p_literalPowerTrace_073 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_074 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩]

theorem g32p_literalPowerTrace_check_074 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_074 (k.val + 1)) =
      g32p_literalPowerTrace_074 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_075 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-4, 0⟩, ⟨1, 0⟩]

theorem g32p_literalPowerTrace_check_075 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_075 (k.val + 1)) =
      g32p_literalPowerTrace_075 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_076 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-2, -3⟩, ⟨1, 3⟩, ⟨4, 0⟩, ⟨-2, -3⟩]

theorem g32p_literalPowerTrace_check_076 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_076 (k.val + 1)) =
      g32p_literalPowerTrace_076 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_077 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-2, -1⟩, ⟨1, 3⟩, ⟨0, 0⟩, ⟨-2, -3⟩]

theorem g32p_literalPowerTrace_check_077 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_077 (k.val + 1)) =
      g32p_literalPowerTrace_077 k := by
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

def g32p_literalPowerTrace_078 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-2, 0⟩, ⟨-2, 0⟩, ⟨4, 0⟩, ⟨-2, 0⟩]

theorem g32p_literalPowerTrace_check_078 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_078 (k.val + 1)) =
      g32p_literalPowerTrace_078 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_079 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, 1⟩, ⟨-2, -3⟩, ⟨0, 0⟩, ⟨1, 3⟩]

theorem g32p_literalPowerTrace_check_079 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_079 (k.val + 1)) =
      g32p_literalPowerTrace_079 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_080 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨3, 1⟩]

theorem g32p_literalPowerTrace_check_080 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_080 (k.val + 1)) =
      g32p_literalPowerTrace_080 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_081 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, 1⟩, ⟨2, -1⟩, ⟨0, 0⟩, ⟨3, 1⟩]

theorem g32p_literalPowerTrace_check_081 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_081 (k.val + 1)) =
      g32p_literalPowerTrace_081 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_082 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 0⟩, ⟨-4, -4⟩, ⟨0, 0⟩, ⟨0, 4⟩]

theorem g32p_literalPowerTrace_check_082 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_082 (k.val + 1)) =
      g32p_literalPowerTrace_082 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_083 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, -2⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 4⟩]

theorem g32p_literalPowerTrace_check_083 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_083 (k.val + 1)) =
      g32p_literalPowerTrace_083 k := by
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

def g32p_literalPowerTrace_084 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-4, 0⟩, ⟨0, 1⟩]

theorem g32p_literalPowerTrace_check_084 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_084 (k.val + 1)) =
      g32p_literalPowerTrace_084 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_085 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, -2⟩, ⟨-1, 2⟩, ⟨0, 0⟩, ⟨-3, -2⟩]

theorem g32p_literalPowerTrace_check_085 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_085 (k.val + 1)) =
      g32p_literalPowerTrace_085 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_086 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩]

theorem g32p_literalPowerTrace_check_086 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_086 (k.val + 1)) =
      g32p_literalPowerTrace_086 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_087 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, 2⟩, ⟨-3, -2⟩, ⟨4, 0⟩, ⟨-1, 2⟩]

theorem g32p_literalPowerTrace_check_087 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_087 (k.val + 1)) =
      g32p_literalPowerTrace_087 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_088 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨1, -2⟩, ⟨-3, -2⟩, ⟨-4, 0⟩, ⟨-1, 2⟩]

theorem g32p_literalPowerTrace_check_088 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_088 (k.val + 1)) =
      g32p_literalPowerTrace_088 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_089 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-2, -1⟩, ⟨3, 1⟩, ⟨0, 0⟩, ⟨2, -1⟩]

theorem g32p_literalPowerTrace_check_089 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_089 (k.val + 1)) =
      g32p_literalPowerTrace_089 k := by
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

def g32p_literalPowerTrace_090 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨-4, -4⟩]

theorem g32p_literalPowerTrace_check_090 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_090 (k.val + 1)) =
      g32p_literalPowerTrace_090 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_091 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, -2⟩, ⟨-3, -2⟩, ⟨0, 0⟩, ⟨-1, 2⟩]

theorem g32p_literalPowerTrace_check_091 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_091 (k.val + 1)) =
      g32p_literalPowerTrace_091 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_092 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-2, -2⟩, ⟨0, -2⟩, ⟨-4, 0⟩, ⟨2, 2⟩]

theorem g32p_literalPowerTrace_check_092 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_092 (k.val + 1)) =
      g32p_literalPowerTrace_092 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_093 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-2, 1⟩, ⟨3, 1⟩, ⟨-4, 0⟩, ⟨2, -1⟩]

theorem g32p_literalPowerTrace_check_093 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_093 (k.val + 1)) =
      g32p_literalPowerTrace_093 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_094 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨4, 0⟩]

theorem g32p_literalPowerTrace_check_094 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_094 (k.val + 1)) =
      g32p_literalPowerTrace_094 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_095 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-1, -3⟩, ⟨-2, -3⟩, ⟨-4, 0⟩, ⟨1, 3⟩]

theorem g32p_literalPowerTrace_check_095 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_095 (k.val + 1)) =
      g32p_literalPowerTrace_095 k := by
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

def g32p_literalPowerTrace_096 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, 4⟩, ⟨-4, -4⟩, ⟨4, 0⟩, ⟨0, 4⟩]

theorem g32p_literalPowerTrace_check_096 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_096 (k.val + 1)) =
      g32p_literalPowerTrace_096 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_097 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨0, -4⟩, ⟨-4, -4⟩, ⟨-4, 0⟩, ⟨0, 4⟩]

theorem g32p_literalPowerTrace_check_097 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_097 (k.val + 1)) =
      g32p_literalPowerTrace_097 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_098 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-3, -1⟩, ⟨2, -1⟩, ⟨-4, 0⟩, ⟨3, 1⟩]

theorem g32p_literalPowerTrace_check_098 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_098 (k.val + 1)) =
      g32p_literalPowerTrace_098 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_099 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-4, 0⟩, ⟨4, 0⟩, ⟨-4, 0⟩, ⟨4, 0⟩]

theorem g32p_literalPowerTrace_check_099 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_099 (k.val + 1)) =
      g32p_literalPowerTrace_099 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_100 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-3, -2⟩, ⟨-1, 2⟩, ⟨4, 0⟩, ⟨-3, -2⟩]

theorem g32p_literalPowerTrace_check_100 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_100 (k.val + 1)) =
      g32p_literalPowerTrace_100 k := by
  fin_cases k <;> decide +kernel

def g32p_literalPowerTrace_101 : Fin 4 → HurwitzPrymRex_Zw :=
  ![⟨-4, -4⟩, ⟨0, 4⟩, ⟨4, 0⟩, ⟨-4, -4⟩]

theorem g32p_literalPowerTrace_check_101 (k : Fin 4) :
    g32p_integralTrace (g32p_integralPower g32p_literalMatrix_101 (k.val + 1)) =
      g32p_literalPowerTrace_101 k := by
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

def g32p_literalPowerTrace : Fin 102 → Fin 4 → HurwitzPrymRex_Zw :=
  ![g32p_literalPowerTrace_000, g32p_literalPowerTrace_001, g32p_literalPowerTrace_002, g32p_literalPowerTrace_003, g32p_literalPowerTrace_004, g32p_literalPowerTrace_005, g32p_literalPowerTrace_006, g32p_literalPowerTrace_007, g32p_literalPowerTrace_008, g32p_literalPowerTrace_009, g32p_literalPowerTrace_010, g32p_literalPowerTrace_011, g32p_literalPowerTrace_012, g32p_literalPowerTrace_013, g32p_literalPowerTrace_014, g32p_literalPowerTrace_015, g32p_literalPowerTrace_016, g32p_literalPowerTrace_017, g32p_literalPowerTrace_018, g32p_literalPowerTrace_019, g32p_literalPowerTrace_020, g32p_literalPowerTrace_021, g32p_literalPowerTrace_022, g32p_literalPowerTrace_023, g32p_literalPowerTrace_024, g32p_literalPowerTrace_025, g32p_literalPowerTrace_026, g32p_literalPowerTrace_027, g32p_literalPowerTrace_028, g32p_literalPowerTrace_029, g32p_literalPowerTrace_030, g32p_literalPowerTrace_031, g32p_literalPowerTrace_032, g32p_literalPowerTrace_033, g32p_literalPowerTrace_034, g32p_literalPowerTrace_035, g32p_literalPowerTrace_036, g32p_literalPowerTrace_037, g32p_literalPowerTrace_038, g32p_literalPowerTrace_039, g32p_literalPowerTrace_040, g32p_literalPowerTrace_041, g32p_literalPowerTrace_042, g32p_literalPowerTrace_043, g32p_literalPowerTrace_044, g32p_literalPowerTrace_045, g32p_literalPowerTrace_046, g32p_literalPowerTrace_047, g32p_literalPowerTrace_048, g32p_literalPowerTrace_049, g32p_literalPowerTrace_050, g32p_literalPowerTrace_051, g32p_literalPowerTrace_052, g32p_literalPowerTrace_053, g32p_literalPowerTrace_054, g32p_literalPowerTrace_055, g32p_literalPowerTrace_056, g32p_literalPowerTrace_057, g32p_literalPowerTrace_058, g32p_literalPowerTrace_059, g32p_literalPowerTrace_060, g32p_literalPowerTrace_061, g32p_literalPowerTrace_062, g32p_literalPowerTrace_063, g32p_literalPowerTrace_064, g32p_literalPowerTrace_065, g32p_literalPowerTrace_066, g32p_literalPowerTrace_067, g32p_literalPowerTrace_068, g32p_literalPowerTrace_069, g32p_literalPowerTrace_070, g32p_literalPowerTrace_071, g32p_literalPowerTrace_072, g32p_literalPowerTrace_073, g32p_literalPowerTrace_074, g32p_literalPowerTrace_075, g32p_literalPowerTrace_076, g32p_literalPowerTrace_077, g32p_literalPowerTrace_078, g32p_literalPowerTrace_079, g32p_literalPowerTrace_080, g32p_literalPowerTrace_081, g32p_literalPowerTrace_082, g32p_literalPowerTrace_083, g32p_literalPowerTrace_084, g32p_literalPowerTrace_085, g32p_literalPowerTrace_086, g32p_literalPowerTrace_087, g32p_literalPowerTrace_088, g32p_literalPowerTrace_089, g32p_literalPowerTrace_090, g32p_literalPowerTrace_091, g32p_literalPowerTrace_092, g32p_literalPowerTrace_093, g32p_literalPowerTrace_094, g32p_literalPowerTrace_095, g32p_literalPowerTrace_096, g32p_literalPowerTrace_097, g32p_literalPowerTrace_098, g32p_literalPowerTrace_099, g32p_literalPowerTrace_100, g32p_literalPowerTrace_101]

theorem g32p_literalPowerTrace_check (c : Fin 102) (k : Fin 4) :
    g32p_integralTrace
      (g32p_integralPower (g32p_literalRepresentativeMatrix c) (k.val + 1)) =
      g32p_literalPowerTrace c k := by
  fin_cases c
  · exact g32p_literalPowerTrace_check_000 k
  · exact g32p_literalPowerTrace_check_001 k
  · exact g32p_literalPowerTrace_check_002 k
  · exact g32p_literalPowerTrace_check_003 k
  · exact g32p_literalPowerTrace_check_004 k
  · exact g32p_literalPowerTrace_check_005 k
  · exact g32p_literalPowerTrace_check_006 k
  · exact g32p_literalPowerTrace_check_007 k
  · exact g32p_literalPowerTrace_check_008 k
  · exact g32p_literalPowerTrace_check_009 k
  · exact g32p_literalPowerTrace_check_010 k
  · exact g32p_literalPowerTrace_check_011 k
  · exact g32p_literalPowerTrace_check_012 k
  · exact g32p_literalPowerTrace_check_013 k
  · exact g32p_literalPowerTrace_check_014 k
  · exact g32p_literalPowerTrace_check_015 k
  · exact g32p_literalPowerTrace_check_016 k
  · exact g32p_literalPowerTrace_check_017 k
  · exact g32p_literalPowerTrace_check_018 k
  · exact g32p_literalPowerTrace_check_019 k
  · exact g32p_literalPowerTrace_check_020 k
  · exact g32p_literalPowerTrace_check_021 k
  · exact g32p_literalPowerTrace_check_022 k
  · exact g32p_literalPowerTrace_check_023 k
  · exact g32p_literalPowerTrace_check_024 k
  · exact g32p_literalPowerTrace_check_025 k
  · exact g32p_literalPowerTrace_check_026 k
  · exact g32p_literalPowerTrace_check_027 k
  · exact g32p_literalPowerTrace_check_028 k
  · exact g32p_literalPowerTrace_check_029 k
  · exact g32p_literalPowerTrace_check_030 k
  · exact g32p_literalPowerTrace_check_031 k
  · exact g32p_literalPowerTrace_check_032 k
  · exact g32p_literalPowerTrace_check_033 k
  · exact g32p_literalPowerTrace_check_034 k
  · exact g32p_literalPowerTrace_check_035 k
  · exact g32p_literalPowerTrace_check_036 k
  · exact g32p_literalPowerTrace_check_037 k
  · exact g32p_literalPowerTrace_check_038 k
  · exact g32p_literalPowerTrace_check_039 k
  · exact g32p_literalPowerTrace_check_040 k
  · exact g32p_literalPowerTrace_check_041 k
  · exact g32p_literalPowerTrace_check_042 k
  · exact g32p_literalPowerTrace_check_043 k
  · exact g32p_literalPowerTrace_check_044 k
  · exact g32p_literalPowerTrace_check_045 k
  · exact g32p_literalPowerTrace_check_046 k
  · exact g32p_literalPowerTrace_check_047 k
  · exact g32p_literalPowerTrace_check_048 k
  · exact g32p_literalPowerTrace_check_049 k
  · exact g32p_literalPowerTrace_check_050 k
  · exact g32p_literalPowerTrace_check_051 k
  · exact g32p_literalPowerTrace_check_052 k
  · exact g32p_literalPowerTrace_check_053 k
  · exact g32p_literalPowerTrace_check_054 k
  · exact g32p_literalPowerTrace_check_055 k
  · exact g32p_literalPowerTrace_check_056 k
  · exact g32p_literalPowerTrace_check_057 k
  · exact g32p_literalPowerTrace_check_058 k
  · exact g32p_literalPowerTrace_check_059 k
  · exact g32p_literalPowerTrace_check_060 k
  · exact g32p_literalPowerTrace_check_061 k
  · exact g32p_literalPowerTrace_check_062 k
  · exact g32p_literalPowerTrace_check_063 k
  · exact g32p_literalPowerTrace_check_064 k
  · exact g32p_literalPowerTrace_check_065 k
  · exact g32p_literalPowerTrace_check_066 k
  · exact g32p_literalPowerTrace_check_067 k
  · exact g32p_literalPowerTrace_check_068 k
  · exact g32p_literalPowerTrace_check_069 k
  · exact g32p_literalPowerTrace_check_070 k
  · exact g32p_literalPowerTrace_check_071 k
  · exact g32p_literalPowerTrace_check_072 k
  · exact g32p_literalPowerTrace_check_073 k
  · exact g32p_literalPowerTrace_check_074 k
  · exact g32p_literalPowerTrace_check_075 k
  · exact g32p_literalPowerTrace_check_076 k
  · exact g32p_literalPowerTrace_check_077 k
  · exact g32p_literalPowerTrace_check_078 k
  · exact g32p_literalPowerTrace_check_079 k
  · exact g32p_literalPowerTrace_check_080 k
  · exact g32p_literalPowerTrace_check_081 k
  · exact g32p_literalPowerTrace_check_082 k
  · exact g32p_literalPowerTrace_check_083 k
  · exact g32p_literalPowerTrace_check_084 k
  · exact g32p_literalPowerTrace_check_085 k
  · exact g32p_literalPowerTrace_check_086 k
  · exact g32p_literalPowerTrace_check_087 k
  · exact g32p_literalPowerTrace_check_088 k
  · exact g32p_literalPowerTrace_check_089 k
  · exact g32p_literalPowerTrace_check_090 k
  · exact g32p_literalPowerTrace_check_091 k
  · exact g32p_literalPowerTrace_check_092 k
  · exact g32p_literalPowerTrace_check_093 k
  · exact g32p_literalPowerTrace_check_094 k
  · exact g32p_literalPowerTrace_check_095 k
  · exact g32p_literalPowerTrace_check_096 k
  · exact g32p_literalPowerTrace_check_097 k
  · exact g32p_literalPowerTrace_check_098 k
  · exact g32p_literalPowerTrace_check_099 k
  · exact g32p_literalPowerTrace_check_100 k
  · exact g32p_literalPowerTrace_check_101 k

theorem g32p_literalPowerTrace_actual (c : Fin 102) (k : Fin 4) :
    g32p_rho.character (g32p_literalRepresentative c ^ (k.val + 1)) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalPowerTrace c k) := by
  rw [g32p_literalRepresentative_powerTrace, g32p_literalPowerTrace_check]

theorem g32p_literalPowerTrace_conj {c d : Fin 102}
    (h : IsConj (g32p_literalRepresentative c) (g32p_literalRepresentative d)) :
    g32p_literalPowerTrace c = g32p_literalPowerTrace d := by
  funext k
  apply HurwitzPrymRex_ev_injective g32h_omega_sq_add
  rw [← g32p_literalPowerTrace_actual, ← g32p_literalPowerTrace_actual]
  exact g32p_powerTrace_eq_of_isConj h _

def g32p_powerTraceCode (f : Fin 4 → HurwitzPrymRex_Zw) : ℤ :=
  (List.ofFn fun k : Fin 4 => [(f k).re, (f k).om]).flatten.foldr
    (fun a b => a + 64 * b) 0

def g32p_powerTraceDecode (z : ℤ) : Fin 102 :=
  (if z < 68719480703 then (if z < -4470003728319 then (if z < -13331510587586 then (if z < -17592186044416 then (if z < -17867062902784 then (if z < -17867097505662 then 37 else (if z < -17867064999936 then 31 else 34)) else (if z < -17867030397058 then 65 else (if z < -17866995794180 then 90 else 101))) else (if z < -13331577696322 then (if z < -13331644804926 then 49 else (if z < -13331612299200 then 44 else 41)) else (if z < -13331577696190 then 77 else (if z < -13331545190464 then 19 else 20)))) else (if z < -9002183823491 then (if z < -9002250932353 then (if z < -9002318040957 then 76 else (if z < -9002285535231 then 28 else 27)) else (if z < -9002250932095 then 85 else (if z < -9002218426369 then 51 else 55))) else (if z < -8796092489728 then (if z < -8796159598464 then 100 else (if z < -8796093554688 then 56 else 46)) else (if z < -8796025380992 then 25 else (if z < -4470020505665 then 11 else 54))))) else (if z < -4260607283134 then (if z < -4463510945727 then (if z < -4466765725633 then (if z < -4466832834495 then 39 else (if z < -4466765725759 then 32 else 15)) else (if z < -4466698616897 then 66 else (if z < -4463527723073 then 35 else 42))) else (if z < -4260674392002 then (if z < -4398063022144 then 12 else (if z < -4398029467584 then 26 else 47)) else (if z < -4260640853952 then 93 else (if z < -4260607283266 then 63 else 89)))) else (if z < -137438945280 then (if z < -274877906944 then (if z < -4260573745216 then 3 else (if z < -4260540174398 then 58 else 2)) else (if z < -137506070526 then 38 else (if z < -137438961664 then 24 else 43))) else (if z < -68702703615 then (if z < -137371852802 then 21 else (if z < -68736258049 then 78 else 73)) else (if z < 65481478143 then (if z < 65464700929 then 22 else 14) else (if z < 68652371967 then 53 else 75)))))) else (if z < 4604238225473 then (if z < 4394808242112 then (if z < 274844352510 then (if z < 71957483521 then (if z < 68719480961 then 71 else (if z < 68786589697 then 40 else 6)) else (if z < 71974260735 then 9 else (if z < 274810814460 then 62 else 99))) else (if z < 274911461378 then (if z < 274877890560 then 94 else (if z < 274877923328 then 69 else 18)) else (if z < 274945032196 then 5 else (if z < 4394791465024 then 0 else 68)))) else (if z < 4401301024704 then (if z < 4398046244930 then (if z < 4397979135936 then 33 else (if z < 4398046244798 then 84 else 86)) else (if z < 4398113353792 then 10 else (if z < 4401284247616 then 45 else 36))) else (if z < 4604137578429 then (if z < 4466748948545 then 70 else (if z < 4466782502847 then 16 else 60)) else (if z < 4604204687297 then (if z < 4604171116479 then 98 else 80) else (if z < 4604204687423 then 8 else 81))))) else (if z < 13262791106367 then (if z < 8727407628287 then (if z < 8727340519425 then (if z < 4604271796291 then 48 else (if z < 8727305899905 then 1 else 88)) else (if z < 8727373008767 then 17 else (if z < 8727373009025 then 91 else 64))) else (if z < 8933531451392 then (if z < 8727440117887 then 61 else (if z < 8933464342398 then 87 else 92)) else (if z < 8933532499968 then 29 else (if z < 8933598560386 then 30 else 4)))) else (if z < 17592117870336 then (if z < 13262858215487 then (if z < 13262825725887 then 95 else (if z < 13262858215361 then 72 else 23)) else (if z < 13262892834881 then 79 else (if z < 13262925324481 then 7 else 67))) else (if z < 17592187109376 then (if z < 17592152489856 then 97 else (if z < 17592184979456 then 83 else 82)) else (if z < 17592252088576 then (if z < 17592219598976 then 13 else 52) else (if z < 17867063951360 then 96 else 57)))))))

def g32p_powerTraceCanonical : Fin 102 → Fin 102 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 25, 51, 52, 53, 54, 55, 56, 57, 58, 29, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 43, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]

theorem g32p_literalPowerTrace_decode : ∀ c : Fin 102,
    g32p_powerTraceDecode (g32p_powerTraceCode (g32p_literalPowerTrace c)) =
      g32p_powerTraceCanonical c := by
  decide +kernel

def g32p_powerTraceRepresentative : Fin 99 → Fin 102 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57, 58, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]

theorem g32p_powerTraceRepresentative_injective :
    Function.Injective g32p_powerTraceRepresentative := by
  decide +kernel

theorem g32p_powerTraceRepresentative_fixed : ∀ i : Fin 99,
    g32p_powerTraceCanonical (g32p_powerTraceRepresentative i) =
      g32p_powerTraceRepresentative i := by
  decide +kernel

theorem g32p_powerTrace_classes_injective :
    Function.Injective (fun i : Fin 99 =>
      ConjClasses.mk (g32p_literalRepresentative (g32p_powerTraceRepresentative i))) := by
  intro i j h
  have hs := g32p_literalPowerTrace_conj (ConjClasses.mk_eq_mk_iff_isConj.mp h)
  have he := congrArg (fun f => g32p_powerTraceDecode (g32p_powerTraceCode f)) hs
  rw [g32p_literalPowerTrace_decode, g32p_literalPowerTrace_decode,
    g32p_powerTraceRepresentative_fixed, g32p_powerTraceRepresentative_fixed] at he
  exact g32p_powerTraceRepresentative_injective he

theorem g32p_conjugacyClasses_card_lower_bound :
    99 ≤ Nat.card (ConjClasses g32p_G) := by
  have h := Nat.card_le_card_of_injective _ g32p_powerTrace_classes_injective
  simpa only [Nat.card_fin] using h

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

theorem g32p_generator_determinant_unit (i : Fin 4) :
    g32p_determinant (b4b_generators i) = g32p_omegaUnit ^ (![1, 2, 0, 0] i : ℕ) := by
  apply Units.ext
  rw [g32p_determinant_val, g32p_generator_determinant, Units.val_pow_eq_pow_val,
    g32p_omegaUnit_val]
  fin_cases i <;> simp

theorem g32p_word_determinant (w : List (Fin 4)) :
    g32p_determinant (g32p_word w) =
      g32p_omegaUnit ^ (w.map (fun i => (![1, 2, 0, 0] i : ℕ))).sum := by
  induction w with
  | nil => simp only [g32p_word, List.map_nil, List.prod_nil, map_one, List.sum_nil, pow_zero]
  | cons i is ih =>
    change g32p_determinant (b4b_generators i * g32p_word is) =
      g32p_omegaUnit ^ ((![1, 2, 0, 0] i : ℕ) +
        (is.map (fun i => (![1, 2, 0, 0] i : ℕ))).sum)
    rw [map_mul, g32p_generator_determinant_unit, ih, pow_add]

theorem g32p_omegaUnit_pow_mod_three (n : ℕ) :
    g32p_omegaUnit ^ n = g32p_omegaUnit ^ (n % 3) := by
  apply pow_eq_pow_of_modEq _ g32p_omegaUnit_primitive.pow_eq_one
  simp [Nat.ModEq]

theorem g32p_archiveGenerator_determinant (i : Fin 4) :
    g32p_determinant (g32p_word (g32p_archiveWords i)) = g32p_omegaUnit := by
  rw [g32p_word_determinant, g32p_omegaUnit_pow_mod_three]
  fin_cases i <;> norm_num [g32p_archiveWords]

theorem g32p_archiveWord_determinant (w : List (Fin 4)) :
    g32p_determinant (g32p_archiveWord w) = g32p_omegaUnit ^ w.length := by
  induction w with
  | nil => simp only [g32p_archiveWord, List.map_nil, List.prod_nil, map_one,
      List.length_nil, pow_zero]
  | cons i is ih =>
    change g32p_determinant (g32p_word (g32p_archiveWords i) * g32p_archiveWord is) =
      g32p_omegaUnit ^ (is.length + 1)
    rw [map_mul, g32p_archiveGenerator_determinant, ih, pow_succ']

theorem g32p_literalRepresentative_determinant (c : Fin 102) :
    g32p_determinant (g32p_literalRepresentative c) =
      g32p_omegaUnit ^ ((g32p_literalRepresentativeWord c).length % 3) := by
  rw [g32p_literalRepresentative, g32p_archiveWord_determinant,
    g32p_omegaUnit_pow_mod_three]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

def g32p_determinantRootPair : Fin 3 → HurwitzPrymRex_Zw :=
  ![⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]

def g32p_literalDeterminantPair (c : Fin 102) : HurwitzPrymRex_Zw :=
  g32p_determinantRootPair (Fin.ofNat 3 (g32p_literalRepresentativeWord c).length)

def g32p_determinantTraceRowIndex : Fin 8 → Fin 408 :=
  ![0, 51, 102, 153, 204, 205, 306, 307]

def g32p_determinantTracePair (c : Fin 102) (k : Fin 8) : HurwitzPrymRex_Zw :=
  let d := g32p_literalDeterminantPair c
  let dd := HurwitzPrymRex_Zw.mul d d
  let t := g32p_literalPowerTrace c 0
  ![d, dd, HurwitzPrymRex_Zw.mul d t, HurwitzPrymRex_Zw.mul dd t,
    dd, ⟨1, 0⟩, ⟨1, 0⟩, d] k

theorem g32p_determinantRootPair_eval (n : Fin 3) :
    HurwitzPrymRex_ev g32h_omega (g32p_determinantRootPair n) = g32h_omega ^ n.val := by
  fin_cases n <;> norm_num [g32p_determinantRootPair, HurwitzPrymRex_ev]
  linear_combination -g32h_omega_sq_add

theorem g32p_literalDeterminantPair_eval (c : Fin 102) :
    HurwitzPrymRex_ev g32h_omega (g32p_literalDeterminantPair c) =
      (g32p_determinant (g32p_literalRepresentative c) : ℂ) := by
  rw [g32p_literalRepresentative_determinant, Units.val_pow_eq_pow_val, g32p_omegaUnit_val]
  exact g32p_determinantRootPair_eval _

end HodgeLean.Foundations.Program

end
end
