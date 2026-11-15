import HodgeLean.Foundations.Program.G32PropFourSixPacked0442
import HodgeLean.Foundations.Program.G32PropFourSixCharacterCoverage
import HodgeLean.Foundations.Program.G32PropFourSixPacked0441
import HodgeLean.Foundations.Program.G32PropFourSixPacked0187
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_families_decode_066 :
    g32p_familiesDecode (g32p_familiesCode 66) = 66 := by
  decide +kernel

theorem g32p_families_conjugate_066 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 66) c =
      g32p_literalBar (g32p_literalCharacterValue 66 c) := by
  decide +kernel

theorem g32p_families_indicator_066 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 66 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 66 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 66 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_067 :
    g32p_familiesDecode (g32p_familiesCode 67) = 67 := by
  decide +kernel

theorem g32p_families_conjugate_067 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 67) c =
      g32p_literalBar (g32p_literalCharacterValue 67 c) := by
  decide +kernel

theorem g32p_families_indicator_067 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 67 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 67 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 67 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_068 :
    g32p_familiesDecode (g32p_familiesCode 68) = 68 := by
  decide +kernel

theorem g32p_families_conjugate_068 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 68) c =
      g32p_literalBar (g32p_literalCharacterValue 68 c) := by
  decide +kernel

theorem g32p_families_indicator_068 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 68 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 68 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 68 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_069 :
    g32p_familiesDecode (g32p_familiesCode 69) = 69 := by
  decide +kernel

theorem g32p_families_conjugate_069 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 69) c =
      g32p_literalBar (g32p_literalCharacterValue 69 c) := by
  decide +kernel

theorem g32p_families_indicator_069 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 69 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 69 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 69 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_070 :
    g32p_familiesDecode (g32p_familiesCode 70) = 70 := by
  decide +kernel

theorem g32p_families_conjugate_070 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 70) c =
      g32p_literalBar (g32p_literalCharacterValue 70 c) := by
  decide +kernel

theorem g32p_families_indicator_070 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 70 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 70 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 70 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_071 :
    g32p_familiesDecode (g32p_familiesCode 71) = 71 := by
  decide +kernel

theorem g32p_families_conjugate_071 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 71) c =
      g32p_literalBar (g32p_literalCharacterValue 71 c) := by
  decide +kernel

theorem g32p_families_indicator_071 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 71 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 71 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 71 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_families_decode_072 :
    g32p_familiesDecode (g32p_familiesCode 72) = 72 := by
  decide +kernel

theorem g32p_families_conjugate_072 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 72) c =
      g32p_literalBar (g32p_literalCharacterValue 72 c) := by
  decide +kernel

theorem g32p_families_indicator_072 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 72 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 72 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 72 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_073 :
    g32p_familiesDecode (g32p_familiesCode 73) = 73 := by
  decide +kernel

theorem g32p_families_conjugate_073 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 73) c =
      g32p_literalBar (g32p_literalCharacterValue 73 c) := by
  decide +kernel

theorem g32p_families_indicator_073 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 73 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 73 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 73 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_074 :
    g32p_familiesDecode (g32p_familiesCode 74) = 74 := by
  decide +kernel

theorem g32p_families_conjugate_074 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 74) c =
      g32p_literalBar (g32p_literalCharacterValue 74 c) := by
  decide +kernel

theorem g32p_families_indicator_074 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 74 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 74 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 74 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_075 :
    g32p_familiesDecode (g32p_familiesCode 75) = 75 := by
  decide +kernel

theorem g32p_families_conjugate_075 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 75) c =
      g32p_literalBar (g32p_literalCharacterValue 75 c) := by
  decide +kernel

theorem g32p_families_indicator_075 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 75 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 75 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 75 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_076 :
    g32p_familiesDecode (g32p_familiesCode 76) = 76 := by
  decide +kernel

theorem g32p_families_conjugate_076 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 76) c =
      g32p_literalBar (g32p_literalCharacterValue 76 c) := by
  decide +kernel

theorem g32p_families_indicator_076 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 76 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 76 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 76 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_077 :
    g32p_familiesDecode (g32p_familiesCode 77) = 77 := by
  decide +kernel

theorem g32p_families_conjugate_077 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 77) c =
      g32p_literalBar (g32p_literalCharacterValue 77 c) := by
  decide +kernel

theorem g32p_families_indicator_077 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 77 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 77 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 77 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_families_decode_078 :
    g32p_familiesDecode (g32p_familiesCode 78) = 78 := by
  decide +kernel

theorem g32p_families_conjugate_078 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 78) c =
      g32p_literalBar (g32p_literalCharacterValue 78 c) := by
  decide +kernel

theorem g32p_families_indicator_078 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 78 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 78 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 78 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_079 :
    g32p_familiesDecode (g32p_familiesCode 79) = 79 := by
  decide +kernel

theorem g32p_families_conjugate_079 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 79) c =
      g32p_literalBar (g32p_literalCharacterValue 79 c) := by
  decide +kernel

theorem g32p_families_indicator_079 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 79 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 79 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 79 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_080 :
    g32p_familiesDecode (g32p_familiesCode 80) = 80 := by
  decide +kernel

theorem g32p_families_conjugate_080 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 80) c =
      g32p_literalBar (g32p_literalCharacterValue 80 c) := by
  decide +kernel

theorem g32p_families_indicator_080 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 80 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 80 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 80 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_081 :
    g32p_familiesDecode (g32p_familiesCode 81) = 81 := by
  decide +kernel

theorem g32p_families_conjugate_081 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 81) c =
      g32p_literalBar (g32p_literalCharacterValue 81 c) := by
  decide +kernel

theorem g32p_families_indicator_081 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 81 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 81 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 81 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_082 :
    g32p_familiesDecode (g32p_familiesCode 82) = 82 := by
  decide +kernel

theorem g32p_families_conjugate_082 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 82) c =
      g32p_literalBar (g32p_literalCharacterValue 82 c) := by
  decide +kernel

theorem g32p_families_indicator_082 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 82 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 82 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 82 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_083 :
    g32p_familiesDecode (g32p_familiesCode 83) = 83 := by
  decide +kernel

theorem g32p_families_conjugate_083 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 83) c =
      g32p_literalBar (g32p_literalCharacterValue 83 c) := by
  decide +kernel

theorem g32p_families_indicator_083 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 83 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 83 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 83 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_families_decode_084 :
    g32p_familiesDecode (g32p_familiesCode 84) = 84 := by
  decide +kernel

theorem g32p_families_conjugate_084 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 84) c =
      g32p_literalBar (g32p_literalCharacterValue 84 c) := by
  decide +kernel

theorem g32p_families_indicator_084 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 84 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 84 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 84 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_085 :
    g32p_familiesDecode (g32p_familiesCode 85) = 85 := by
  decide +kernel

theorem g32p_families_conjugate_085 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 85) c =
      g32p_literalBar (g32p_literalCharacterValue 85 c) := by
  decide +kernel

theorem g32p_families_indicator_085 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 85 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 85 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 85 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_086 :
    g32p_familiesDecode (g32p_familiesCode 86) = 86 := by
  decide +kernel

theorem g32p_families_conjugate_086 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 86) c =
      g32p_literalBar (g32p_literalCharacterValue 86 c) := by
  decide +kernel

theorem g32p_families_indicator_086 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 86 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 86 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 86 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_087 :
    g32p_familiesDecode (g32p_familiesCode 87) = 87 := by
  decide +kernel

theorem g32p_families_conjugate_087 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 87) c =
      g32p_literalBar (g32p_literalCharacterValue 87 c) := by
  decide +kernel

theorem g32p_families_indicator_087 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 87 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 87 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 87 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_088 :
    g32p_familiesDecode (g32p_familiesCode 88) = 88 := by
  decide +kernel

theorem g32p_families_conjugate_088 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 88) c =
      g32p_literalBar (g32p_literalCharacterValue 88 c) := by
  decide +kernel

theorem g32p_families_indicator_088 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 88 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 88 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 88 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_089 :
    g32p_familiesDecode (g32p_familiesCode 89) = 89 := by
  decide +kernel

theorem g32p_families_conjugate_089 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 89) c =
      g32p_literalBar (g32p_literalCharacterValue 89 c) := by
  decide +kernel

theorem g32p_families_indicator_089 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 89 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 89 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 89 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_families_decode_090 :
    g32p_familiesDecode (g32p_familiesCode 90) = 90 := by
  decide +kernel

theorem g32p_families_conjugate_090 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 90) c =
      g32p_literalBar (g32p_literalCharacterValue 90 c) := by
  decide +kernel

theorem g32p_families_indicator_090 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 90 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 90 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 90 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_091 :
    g32p_familiesDecode (g32p_familiesCode 91) = 91 := by
  decide +kernel

theorem g32p_families_conjugate_091 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 91) c =
      g32p_literalBar (g32p_literalCharacterValue 91 c) := by
  decide +kernel

theorem g32p_families_indicator_091 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 91 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 91 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 91 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_092 :
    g32p_familiesDecode (g32p_familiesCode 92) = 92 := by
  decide +kernel

theorem g32p_families_conjugate_092 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 92) c =
      g32p_literalBar (g32p_literalCharacterValue 92 c) := by
  decide +kernel

theorem g32p_families_indicator_092 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 92 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 92 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 92 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_093 :
    g32p_familiesDecode (g32p_familiesCode 93) = 93 := by
  decide +kernel

theorem g32p_families_conjugate_093 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 93) c =
      g32p_literalBar (g32p_literalCharacterValue 93 c) := by
  decide +kernel

theorem g32p_families_indicator_093 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 93 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 93 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 93 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_094 :
    g32p_familiesDecode (g32p_familiesCode 94) = 94 := by
  decide +kernel

theorem g32p_families_conjugate_094 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 94) c =
      g32p_literalBar (g32p_literalCharacterValue 94 c) := by
  decide +kernel

theorem g32p_families_indicator_094 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 94 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 94 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 94 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_095 :
    g32p_familiesDecode (g32p_familiesCode 95) = 95 := by
  decide +kernel

theorem g32p_families_conjugate_095 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 95) c =
      g32p_literalBar (g32p_literalCharacterValue 95 c) := by
  decide +kernel

theorem g32p_families_indicator_095 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 95 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 95 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 95 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_families_decode_096 :
    g32p_familiesDecode (g32p_familiesCode 96) = 96 := by
  decide +kernel

theorem g32p_families_conjugate_096 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 96) c =
      g32p_literalBar (g32p_literalCharacterValue 96 c) := by
  decide +kernel

theorem g32p_families_indicator_096 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 96 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 96 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 96 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_097 :
    g32p_familiesDecode (g32p_familiesCode 97) = 97 := by
  decide +kernel

theorem g32p_families_conjugate_097 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 97) c =
      g32p_literalBar (g32p_literalCharacterValue 97 c) := by
  decide +kernel

theorem g32p_families_indicator_097 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 97 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 97 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 97 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_098 :
    g32p_familiesDecode (g32p_familiesCode 98) = 98 := by
  decide +kernel

theorem g32p_families_conjugate_098 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 98) c =
      g32p_literalBar (g32p_literalCharacterValue 98 c) := by
  decide +kernel

theorem g32p_families_indicator_098 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 98 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 98 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 98 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_099 :
    g32p_familiesDecode (g32p_familiesCode 99) = 99 := by
  decide +kernel

theorem g32p_families_conjugate_099 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 99) c =
      g32p_literalBar (g32p_literalCharacterValue 99 c) := by
  decide +kernel

theorem g32p_families_indicator_099 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 99 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 99 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 99 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_100 :
    g32p_familiesDecode (g32p_familiesCode 100) = 100 := by
  decide +kernel

theorem g32p_families_conjugate_100 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 100) c =
      g32p_literalBar (g32p_literalCharacterValue 100 c) := by
  decide +kernel

theorem g32p_families_indicator_100 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 100 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 100 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 100 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel

theorem g32p_families_decode_101 :
    g32p_familiesDecode (g32p_familiesCode 101) = 101 := by
  decide +kernel

theorem g32p_families_conjugate_101 : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesConjugate 101) c =
      g32p_literalBar (g32p_literalCharacterValue 101 c) := by
  decide +kernel

theorem g32p_families_indicator_101 :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 101 (g32p_literalColumn (g32p_familiesSquare c))).re) =
        155520 * g32p_familiesIndicator 101 ∧
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) *
      (g32p_literalCharacterValue 101 (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_families_decode (i : Fin 102) :
    g32p_familiesDecode (g32p_familiesCode i) = i := by
  fin_cases i
  · exact g32p_families_decode_000
  · exact g32p_families_decode_001
  · exact g32p_families_decode_002
  · exact g32p_families_decode_003
  · exact g32p_families_decode_004
  · exact g32p_families_decode_005
  · exact g32p_families_decode_006
  · exact g32p_families_decode_007
  · exact g32p_families_decode_008
  · exact g32p_families_decode_009
  · exact g32p_families_decode_010
  · exact g32p_families_decode_011
  · exact g32p_families_decode_012
  · exact g32p_families_decode_013
  · exact g32p_families_decode_014
  · exact g32p_families_decode_015
  · exact g32p_families_decode_016
  · exact g32p_families_decode_017
  · exact g32p_families_decode_018
  · exact g32p_families_decode_019
  · exact g32p_families_decode_020
  · exact g32p_families_decode_021
  · exact g32p_families_decode_022
  · exact g32p_families_decode_023
  · exact g32p_families_decode_024
  · exact g32p_families_decode_025
  · exact g32p_families_decode_026
  · exact g32p_families_decode_027
  · exact g32p_families_decode_028
  · exact g32p_families_decode_029
  · exact g32p_families_decode_030
  · exact g32p_families_decode_031
  · exact g32p_families_decode_032
  · exact g32p_families_decode_033
  · exact g32p_families_decode_034
  · exact g32p_families_decode_035
  · exact g32p_families_decode_036
  · exact g32p_families_decode_037
  · exact g32p_families_decode_038
  · exact g32p_families_decode_039
  · exact g32p_families_decode_040
  · exact g32p_families_decode_041
  · exact g32p_families_decode_042
  · exact g32p_families_decode_043
  · exact g32p_families_decode_044
  · exact g32p_families_decode_045
  · exact g32p_families_decode_046
  · exact g32p_families_decode_047
  · exact g32p_families_decode_048
  · exact g32p_families_decode_049
  · exact g32p_families_decode_050
  · exact g32p_families_decode_051
  · exact g32p_families_decode_052
  · exact g32p_families_decode_053
  · exact g32p_families_decode_054
  · exact g32p_families_decode_055
  · exact g32p_families_decode_056
  · exact g32p_families_decode_057
  · exact g32p_families_decode_058
  · exact g32p_families_decode_059
  · exact g32p_families_decode_060
  · exact g32p_families_decode_061
  · exact g32p_families_decode_062
  · exact g32p_families_decode_063
  · exact g32p_families_decode_064
  · exact g32p_families_decode_065
  · exact g32p_families_decode_066
  · exact g32p_families_decode_067
  · exact g32p_families_decode_068
  · exact g32p_families_decode_069
  · exact g32p_families_decode_070
  · exact g32p_families_decode_071
  · exact g32p_families_decode_072
  · exact g32p_families_decode_073
  · exact g32p_families_decode_074
  · exact g32p_families_decode_075
  · exact g32p_families_decode_076
  · exact g32p_families_decode_077
  · exact g32p_families_decode_078
  · exact g32p_families_decode_079
  · exact g32p_families_decode_080
  · exact g32p_families_decode_081
  · exact g32p_families_decode_082
  · exact g32p_families_decode_083
  · exact g32p_families_decode_084
  · exact g32p_families_decode_085
  · exact g32p_families_decode_086
  · exact g32p_families_decode_087
  · exact g32p_families_decode_088
  · exact g32p_families_decode_089
  · exact g32p_families_decode_090
  · exact g32p_families_decode_091
  · exact g32p_families_decode_092
  · exact g32p_families_decode_093
  · exact g32p_families_decode_094
  · exact g32p_families_decode_095
  · exact g32p_families_decode_096
  · exact g32p_families_decode_097
  · exact g32p_families_decode_098
  · exact g32p_families_decode_099
  · exact g32p_families_decode_100
  · exact g32p_families_decode_101

theorem g32p_families_conjugate (i : Fin 102) :
    ∀ c : Fin 102, g32p_literalCharacterValue (g32p_familiesConjugate i) c = g32p_literalBar (g32p_literalCharacterValue i c) := by
  fin_cases i
  · exact g32p_families_conjugate_000
  · exact g32p_families_conjugate_001
  · exact g32p_families_conjugate_002
  · exact g32p_families_conjugate_003
  · exact g32p_families_conjugate_004
  · exact g32p_families_conjugate_005
  · exact g32p_families_conjugate_006
  · exact g32p_families_conjugate_007
  · exact g32p_families_conjugate_008
  · exact g32p_families_conjugate_009
  · exact g32p_families_conjugate_010
  · exact g32p_families_conjugate_011
  · exact g32p_families_conjugate_012
  · exact g32p_families_conjugate_013
  · exact g32p_families_conjugate_014
  · exact g32p_families_conjugate_015
  · exact g32p_families_conjugate_016
  · exact g32p_families_conjugate_017
  · exact g32p_families_conjugate_018
  · exact g32p_families_conjugate_019
  · exact g32p_families_conjugate_020
  · exact g32p_families_conjugate_021
  · exact g32p_families_conjugate_022
  · exact g32p_families_conjugate_023
  · exact g32p_families_conjugate_024
  · exact g32p_families_conjugate_025
  · exact g32p_families_conjugate_026
  · exact g32p_families_conjugate_027
  · exact g32p_families_conjugate_028
  · exact g32p_families_conjugate_029
  · exact g32p_families_conjugate_030
  · exact g32p_families_conjugate_031
  · exact g32p_families_conjugate_032
  · exact g32p_families_conjugate_033
  · exact g32p_families_conjugate_034
  · exact g32p_families_conjugate_035
  · exact g32p_families_conjugate_036
  · exact g32p_families_conjugate_037
  · exact g32p_families_conjugate_038
  · exact g32p_families_conjugate_039
  · exact g32p_families_conjugate_040
  · exact g32p_families_conjugate_041
  · exact g32p_families_conjugate_042
  · exact g32p_families_conjugate_043
  · exact g32p_families_conjugate_044
  · exact g32p_families_conjugate_045
  · exact g32p_families_conjugate_046
  · exact g32p_families_conjugate_047
  · exact g32p_families_conjugate_048
  · exact g32p_families_conjugate_049
  · exact g32p_families_conjugate_050
  · exact g32p_families_conjugate_051
  · exact g32p_families_conjugate_052
  · exact g32p_families_conjugate_053
  · exact g32p_families_conjugate_054
  · exact g32p_families_conjugate_055
  · exact g32p_families_conjugate_056
  · exact g32p_families_conjugate_057
  · exact g32p_families_conjugate_058
  · exact g32p_families_conjugate_059
  · exact g32p_families_conjugate_060
  · exact g32p_families_conjugate_061
  · exact g32p_families_conjugate_062
  · exact g32p_families_conjugate_063
  · exact g32p_families_conjugate_064
  · exact g32p_families_conjugate_065
  · exact g32p_families_conjugate_066
  · exact g32p_families_conjugate_067
  · exact g32p_families_conjugate_068
  · exact g32p_families_conjugate_069
  · exact g32p_families_conjugate_070
  · exact g32p_families_conjugate_071
  · exact g32p_families_conjugate_072
  · exact g32p_families_conjugate_073
  · exact g32p_families_conjugate_074
  · exact g32p_families_conjugate_075
  · exact g32p_families_conjugate_076
  · exact g32p_families_conjugate_077
  · exact g32p_families_conjugate_078
  · exact g32p_families_conjugate_079
  · exact g32p_families_conjugate_080
  · exact g32p_families_conjugate_081
  · exact g32p_families_conjugate_082
  · exact g32p_families_conjugate_083
  · exact g32p_families_conjugate_084
  · exact g32p_families_conjugate_085
  · exact g32p_families_conjugate_086
  · exact g32p_families_conjugate_087
  · exact g32p_families_conjugate_088
  · exact g32p_families_conjugate_089
  · exact g32p_families_conjugate_090
  · exact g32p_families_conjugate_091
  · exact g32p_families_conjugate_092
  · exact g32p_families_conjugate_093
  · exact g32p_families_conjugate_094
  · exact g32p_families_conjugate_095
  · exact g32p_families_conjugate_096
  · exact g32p_families_conjugate_097
  · exact g32p_families_conjugate_098
  · exact g32p_families_conjugate_099
  · exact g32p_families_conjugate_100
  · exact g32p_families_conjugate_101

theorem g32p_families_indicator (i : Fin 102) :
    (∑ c : Fin 102, (g32p_literalSize c : ℤ) * (g32p_literalCharacterValue i (g32p_literalColumn (g32p_familiesSquare c))).re) = 155520 * g32p_familiesIndicator i ∧ (∑ c : Fin 102, (g32p_literalSize c : ℤ) * (g32p_literalCharacterValue i (g32p_literalColumn (g32p_familiesSquare c))).om) = 0 := by
  fin_cases i
  · exact g32p_families_indicator_000
  · exact g32p_families_indicator_001
  · exact g32p_families_indicator_002
  · exact g32p_families_indicator_003
  · exact g32p_families_indicator_004
  · exact g32p_families_indicator_005
  · exact g32p_families_indicator_006
  · exact g32p_families_indicator_007
  · exact g32p_families_indicator_008
  · exact g32p_families_indicator_009
  · exact g32p_families_indicator_010
  · exact g32p_families_indicator_011
  · exact g32p_families_indicator_012
  · exact g32p_families_indicator_013
  · exact g32p_families_indicator_014
  · exact g32p_families_indicator_015
  · exact g32p_families_indicator_016
  · exact g32p_families_indicator_017
  · exact g32p_families_indicator_018
  · exact g32p_families_indicator_019
  · exact g32p_families_indicator_020
  · exact g32p_families_indicator_021
  · exact g32p_families_indicator_022
  · exact g32p_families_indicator_023
  · exact g32p_families_indicator_024
  · exact g32p_families_indicator_025
  · exact g32p_families_indicator_026
  · exact g32p_families_indicator_027
  · exact g32p_families_indicator_028
  · exact g32p_families_indicator_029
  · exact g32p_families_indicator_030
  · exact g32p_families_indicator_031
  · exact g32p_families_indicator_032
  · exact g32p_families_indicator_033
  · exact g32p_families_indicator_034
  · exact g32p_families_indicator_035
  · exact g32p_families_indicator_036
  · exact g32p_families_indicator_037
  · exact g32p_families_indicator_038
  · exact g32p_families_indicator_039
  · exact g32p_families_indicator_040
  · exact g32p_families_indicator_041
  · exact g32p_families_indicator_042
  · exact g32p_families_indicator_043
  · exact g32p_families_indicator_044
  · exact g32p_families_indicator_045
  · exact g32p_families_indicator_046
  · exact g32p_families_indicator_047
  · exact g32p_families_indicator_048
  · exact g32p_families_indicator_049
  · exact g32p_families_indicator_050
  · exact g32p_families_indicator_051
  · exact g32p_families_indicator_052
  · exact g32p_families_indicator_053
  · exact g32p_families_indicator_054
  · exact g32p_families_indicator_055
  · exact g32p_families_indicator_056
  · exact g32p_families_indicator_057
  · exact g32p_families_indicator_058
  · exact g32p_families_indicator_059
  · exact g32p_families_indicator_060
  · exact g32p_families_indicator_061
  · exact g32p_families_indicator_062
  · exact g32p_families_indicator_063
  · exact g32p_families_indicator_064
  · exact g32p_families_indicator_065
  · exact g32p_families_indicator_066
  · exact g32p_families_indicator_067
  · exact g32p_families_indicator_068
  · exact g32p_families_indicator_069
  · exact g32p_families_indicator_070
  · exact g32p_families_indicator_071
  · exact g32p_families_indicator_072
  · exact g32p_families_indicator_073
  · exact g32p_families_indicator_074
  · exact g32p_families_indicator_075
  · exact g32p_families_indicator_076
  · exact g32p_families_indicator_077
  · exact g32p_families_indicator_078
  · exact g32p_families_indicator_079
  · exact g32p_families_indicator_080
  · exact g32p_families_indicator_081
  · exact g32p_families_indicator_082
  · exact g32p_families_indicator_083
  · exact g32p_families_indicator_084
  · exact g32p_families_indicator_085
  · exact g32p_families_indicator_086
  · exact g32p_families_indicator_087
  · exact g32p_families_indicator_088
  · exact g32p_families_indicator_089
  · exact g32p_families_indicator_090
  · exact g32p_families_indicator_091
  · exact g32p_families_indicator_092
  · exact g32p_families_indicator_093
  · exact g32p_families_indicator_094
  · exact g32p_families_indicator_095
  · exact g32p_families_indicator_096
  · exact g32p_families_indicator_097
  · exact g32p_families_indicator_098
  · exact g32p_families_indicator_099
  · exact g32p_families_indicator_100
  · exact g32p_families_indicator_101


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory HodgeLean.Papers

set_option maxHeartbeats 400000

/-- Evaluation respects the integral conjugation operation.
Source: `conj_omega`; G32 v0.16, Appendix A. -/
theorem g32p_families_bar_eval (z : HurwitzPrymRex_Zw) :
    HurwitzPrymRex_ev g32h_omega (g32p_literalBar z) =
      star (HurwitzPrymRex_ev g32h_omega z) := by
  have hs : star g32h_omega = -1 - g32h_omega :=
    conj_omega g32h_omega g32h_omega_sq_add
  simp only [g32p_literalBar, HurwitzPrymRex_ev, Int.cast_sub, Int.cast_neg,
    star_add, star_mul, star_intCast, hs]
  ring

/-- The two-column decoder makes the complex rows injective.
Source: `g32p_families_decode`; G32 v0.16, Appendix A. -/
theorem g32p_families_rows_injective :
    Function.Injective g32p_literalComplexValue := by
  intro i j h
  have hv (c : Fin 102) : g32p_literalCharacterValue i c =
      g32p_literalCharacterValue j c := by
    apply HurwitzPrymRex_ev_injective g32h_omega_sq_add
    have he := congrFun h (g32p_literalColumnInverse c)
    simpa only [g32p_literalComplexValue, g32p_literalColumn_rightInverse c] using he
  have hc : g32p_familiesCode i = g32p_familiesCode j := by
    unfold g32p_familiesCode
    rw [hv 15, hv 4]
  simpa only [g32p_families_decode] using congrArg g32p_familiesDecode hc

/-- Surjective class labels detect equality of table rows.
Source: `g32p_families_rows_injective`. -/
theorem g32p_families_character_index (label : g32p_G → Fin 102)
    (hsurj : Function.Surjective label) (W : Fin 102 → FDRep ℂ g32p_G)
    (hW : ∀ i g, (W i).character g = g32p_literalComplexValue i (label g))
    {i j : Fin 102} (h : (W i).character = (W j).character) : i = j := by
  apply g32p_families_rows_injective
  funext c
  obtain ⟨g, rfl⟩ := hsurj c
  rw [← hW, ← hW, h]

/-- Different realized rows give different simple objects.
Source: FDRep character invariance under isomorphism. -/
theorem g32p_families_distinct (label : g32p_G → Fin 102)
    (hsurj : Function.Surjective label) (W : Fin 102 → FDRep ℂ g32p_G)
    (hW : ∀ i g, (W i).character g = g32p_literalComplexValue i (label g))
    (i j : Fin 102) (hij : i ≠ j) : IsEmpty (W i ≅ W j) :=
  ⟨fun e => hij (g32p_families_character_index label hsurj W hW (FDRep.char_iso e))⟩

/-- The realized rows have the recorded conjugation permutation.
Source: `g32p_families_conjugate`; G32 v0.16, Appendix A. -/
theorem g32p_families_character_conjugate (label : g32p_G → Fin 102)
    (W : Fin 102 → FDRep ℂ g32p_G)
    (hW : ∀ i g, (W i).character g = g32p_literalComplexValue i (label g))
    (i : Fin 102) (g : g32p_G) :
    (W (g32p_familiesConjugate i)).character g = star ((W i).character g) := by
  rw [hW, hW]
  unfold g32p_literalComplexValue
  rw [g32p_families_conjugate, g32p_families_bar_eval]

/-- The selected pair rows match the conjugation permutation.
Source: G32 v0.16, Proposition 4.6; `certificates.json`. -/
theorem g32p_families_selected_conjugate :
    (∀ j, g32p_familiesConjugate (g32p_familiesPair j) = g32p_familiesBar j) ∧
    (∀ j, g32p_familiesConjugate (g32p_familiesQuat j) = g32p_familiesQuat j) ∧
    (∀ j, g32p_familiesIndicator (g32p_familiesQuat j) = -1) := by
  decide +kernel

/-- None of the selected pair rows is self-dual.
Source: character conjugation and the two-column decoder. -/
theorem g32p_families_pair_not_selfDual (label : g32p_G → Fin 102)
    (hsurj : Function.Surjective label) (W : Fin 102 → FDRep ℂ g32p_G)
    (hW : ∀ i g, (W i).character g = g32p_literalComplexValue i (label g))
    (j : Fin 44) : ¬ g32p_SelfDual (W (g32p_familiesPair j)) := by
  intro hs
  have he : (W (g32p_familiesBar j)).character =
      (W (g32p_familiesPair j)).character := by
    funext g
    rw [← g32p_families_selected_conjugate.1 j,
      g32p_families_character_conjugate label W hW, hs g]
  exact g32p_families_indices.2.2.2 j j
    (g32p_families_character_index label hsurj W hW he).symm

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory HodgeLean.Papers
open scoped Classical

set_option maxHeartbeats 400000

/-- The finite indicator sums interpreted in the complex coefficient field.
Source: Serre, Linear Representations of Finite Groups, §13.2; table certificates. -/
theorem g32p_families_indicator_complex (i : Fin 102) :
    ∑ c : Fin 102, (g32p_literalSize c : ℂ) *
      g32p_literalComplexValue i (g32p_familiesSquare c) =
        155520 * (g32p_familiesIndicator i : ℂ) := by
  have h := g32p_families_indicator i
  unfold g32p_literalComplexValue HurwitzPrymRex_ev
  simp_rw [mul_add, ← mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have hr : (∑ c : Fin 102, (g32p_literalSize c : ℂ) *
      ((g32p_literalCharacterValue i
        (g32p_literalColumn (g32p_familiesSquare c))).re : ℂ)) =
        155520 * (g32p_familiesIndicator i : ℂ) := by exact_mod_cast h.1
  have hi : (∑ c : Fin 102, (g32p_literalSize c : ℂ) *
      ((g32p_literalCharacterValue i
        (g32p_literalColumn (g32p_familiesSquare c))).om : ℂ)) = 0 := by
    exact_mod_cast h.2
  rw [hr, hi, zero_mul, add_zero]

/-- Transport of the finite indicator sums through a square-compatible class map.
Source: Serre, Linear Representations of Finite Groups, §13.2. -/
theorem g32p_families_indicator_actual (label : g32p_G → Fin 102)
    (hcard : ∀ c, Fintype.card {g : g32p_G // label g = c} = g32p_literalSize c)
    (hsquare : ∀ g, label (g * g) = g32p_familiesSquare (label g))
    (W : Fin 102 → FDRep ℂ g32p_G)
    (hW : ∀ i g, (W i).character g = g32p_literalComplexValue i (label g))
    (i : Fin 102) :
    ∑ g, (W i).character (g * g) = 155520 * (g32p_familiesIndicator i : ℂ) := by
  rw [g32p_sum_class_fibers label g32p_literalSize
    (fun c => g32p_literalComplexValue i (g32p_familiesSquare c))
    (fun g => (W i).character (g * g))
    (fun c => by simpa only [← Nat.card_eq_fintype_card] using hcard c)
    (fun g => by rw [hW, hsquare])]
  exact g32p_families_indicator_complex i

/-- The four designated rows are quaternionic after square-class transport.
Source: G32 v0.16, Proposition 4.6; Serre, §13.2, Proposition 39. -/
theorem g32p_families_quaternionic (label : g32p_G → Fin 102)
    (hcard : ∀ c, Fintype.card {g : g32p_G // label g = c} = g32p_literalSize c)
    (hsquare : ∀ g, label (g * g) = g32p_familiesSquare (label g))
    (W : Fin 102 → FDRep ℂ g32p_G)
    (hW : ∀ i g, (W i).character g = g32p_literalComplexValue i (label g))
    (j : Fin 4) : g32p_Quaternionic (W (g32p_familiesQuat j)) := by
  refine ⟨?_, ?_⟩
  · intro g
    have h := g32p_families_character_conjugate label W hW (g32p_familiesQuat j) g
    rw [g32p_families_selected_conjugate.2.1 j] at h
    exact h.symm
  · rw [g32p_families_indicator_actual label hcard hsquare W hW,
      g32p_families_selected_conjugate.2.2 j]
    have hc : Fintype.card g32p_G = 155520 := by
      rw [← Nat.card_eq_fintype_card]
      exact (Nat.card_coe_set_eq (g32h_G : Set (Matrix (Fin 4) (Fin 4) ℂ))).trans
        HurwitzPrymRex_g32_ncard
    rw [hc]
    norm_num

/-- Every row with indicator minus one belongs to the designated four.
Source: G32 v0.16, Appendix A. -/
theorem g32p_families_indicator_selection : ∀ i : Fin 102,
    g32p_familiesIndicator i = -1 → ∃ j, i = g32p_familiesQuat j := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory HodgeLean.Papers
open scoped Classical

set_option maxHeartbeats 400000

/-- All simple objects occur among the 102 realized rows when the representatives
cover the group.
Source: Serre, Linear Representations of Finite Groups, §2.5; character independence. -/
theorem g32p_families_simple_coverage (label : g32p_G → Fin 102)
    (hrep : ∀ c, label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (label g)))
    (W : Fin 102 → FDRep ℂ g32p_G) (hS : ∀ i, Simple (W i))
    (hW : ∀ i g, (W i).character g = g32p_literalComplexValue i (label g))
    (σ : FDRep ℂ g32p_G) [Simple σ] : ∃ i, Nonempty (σ ≅ W i) := by
  exact g32p_simple_coverage_of_class_count label g32p_literalRepresentative hconj W hS
    (g32p_families_distinct label (fun c => ⟨g32p_literalRepresentative c, hrep c⟩) W hW) σ

/-- Non-self-dual simple objects occur in the selected 44 pairs.
Source: G32 v0.16, Proposition 4.6; the finite row partition. -/
theorem g32p_families_pair_coverage (label : g32p_G → Fin 102)
    (hrep : ∀ c, label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (label g)))
    (W : Fin 102 → FDRep ℂ g32p_G) (hS : ∀ i, Simple (W i))
    (hW : ∀ i g, (W i).character g = g32p_literalComplexValue i (label g))
    (σ : FDRep ℂ g32p_G) [Simple σ] (hσ : ¬ g32p_SelfDual σ) :
    ∃ j, Nonempty (σ ≅ W (g32p_familiesPair j)) ∨
      Nonempty (σ ≅ W (g32p_familiesBar j)) := by
  obtain ⟨i, ⟨e⟩⟩ := g32p_families_simple_coverage label hrep hconj W hS hW σ
  rcases g32p_families_partition i with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | hi
  · exact ⟨j, Or.inl ⟨e⟩⟩
  · exact ⟨j, Or.inr ⟨e⟩⟩
  · apply False.elim
    apply hσ
    intro g
    rw [FDRep.char_iso e]
    have h := g32p_families_character_conjugate label W hW (g32p_familiesQuat j) g
    rw [g32p_families_selected_conjugate.2.1 j] at h
    exact h.symm
  · apply False.elim
    apply hσ
    intro g
    rw [FDRep.char_iso e]
    have h := g32p_families_character_conjugate label W hW i g
    rw [hi] at h
    exact h.symm

/-- Quaternionic simple objects occur in the selected four rows.
Source: G32 v0.16, Proposition 4.6; Serre, §13.2. -/
theorem g32p_families_quaternionic_coverage (label : g32p_G → Fin 102)
    (hrep : ∀ c, label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (label g)))
    (hcard : ∀ c, Fintype.card {g : g32p_G // label g = c} = g32p_literalSize c)
    (hsquare : ∀ g, label (g * g) = g32p_familiesSquare (label g))
    (W : Fin 102 → FDRep ℂ g32p_G) (hS : ∀ i, Simple (W i))
    (hW : ∀ i g, (W i).character g = g32p_literalComplexValue i (label g))
    (σ : FDRep ℂ g32p_G) [Simple σ] (hσ : g32p_Quaternionic σ) :
    ∃ j, Nonempty (σ ≅ W (g32p_familiesQuat j)) := by
  obtain ⟨i, ⟨e⟩⟩ := g32p_families_simple_coverage label hrep hconj W hS hW σ
  have hh := hσ.2
  rw [FDRep.char_iso e,
    g32p_families_indicator_actual label hcard hsquare W hW] at hh
  have hc : Fintype.card g32p_G = 155520 := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_coe_set_eq (g32h_G : Set (Matrix (Fin 4) (Fin 4) ℂ))).trans
      HurwitzPrymRex_g32_ncard
  rw [hc] at hh
  have hi : g32p_familiesIndicator i = -1 := by
    have hr := congrArg Complex.re hh
    norm_num at hr
    exact_mod_cast (by linarith : (g32p_familiesIndicator i : ℝ) = -1)
  obtain ⟨j, rfl⟩ := g32p_families_indicator_selection i hi
  exact ⟨j, ⟨e⟩⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory HodgeLean.Papers

set_option maxHeartbeats 400000

/-- The natural row has the exact traces of the natural matrices.
Source: G32 v0.16, Appendix A; `g32p_literalRepresentative_character`. -/
theorem g32p_families_natural_values : ∀ c : Fin 102,
    g32p_literalCharacterValue (g32p_familiesPair 2) c =
      g32p_literalNaturalRow c := by
  decide +kernel

/-- Coordinate two is the natural four-dimensional representation.
Source: G32 v0.16, Proposition 4.6; the literal natural trace certificates. -/
theorem g32p_families_natural_iso (label : g32p_G → Fin 102)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (label g)))
    (W : Fin 102 → FDRep ℂ g32p_G) (hS : ∀ i, Simple (W i))
    (hW : ∀ i g, (W i).character g = g32p_literalComplexValue i (label g)) :
    Nonempty (W (g32p_familiesPair 2) ≅ g32p_rho) := by
  letI := hS (g32p_familiesPair 2)
  letI := g32p_rho_simple
  apply g32p_simple_iso_of_character_eq
  funext g
  rw [hW]
  unfold g32p_literalComplexValue
  rw [g32p_families_natural_values]
  rw [← g32p_literalRepresentative_character]
  obtain ⟨u, hu⟩ := isConj_iff.mp (hconj g)
  rw [← hu, FDRep.char_conj]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalReconstructionCoefficients_000 : List (Fin 408 × ℤ) :=
  [(1, 27), (2, -816), (3, -3531), (6, 25), (7, -408), (8, 13800), (9, 16100), (10, 6900), (11, 8050), (12, -2300), (16, 1021), (18, 1229), (19, -4728), (21, -1942), (24, -791), (25, 132), (26, -25), (27, -13800), (28, -25), (32, 1484), (33, -816), (34, -587), (35, 2123), (36, -11500), (42, -4600), (43, -18578), (47, 2709), (48, -5750), (50, 6900), (51, 2310), (52, 2363), (53, -1884), (54, 1922), (58, 2788), (59, -4600), (60, 4600), (65, -2300), (68, 26), (69, 2311), (70, 4550), (71, 416), (72, -1421), (75, 1175), (77, -2825), (79, -2409), (82, -2465), (83, -1908), (84, 426), (86, 2882), (93, 18400), (98, 505), (101, -4600), (102, 9200), (115, -52), (120, -4600), (121, -1150), (122, 4600), (125, -6900), (127, 2300), (131, -25), (135, 9200), (142, 180), (144, -156), (148, -6900), (154, 16100), (158, -180), (162, 128), (171, -16100), (195, 78), (196, 6900), (203, -1150), (210, 1430), (211, 129), (219, 308), (227, -6900), (237, -386), (247, 231), (250, -2335), (257, 26), (261, -102), (271, -1), (272, -375), (275, -411), (277, 9200), (297, -2402), (299, -102), (301, 13800), (304, 2300), (305, 2300), (312, 51), (313, 2173), (379, 2300), (391, -14950), (406, 17250)]

theorem g32p_literalReconstructionIdentity_000 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_000 j =
      if (0 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_001 : List (Fin 408 × ℤ) :=
  [(1, -1), (2, -8), (3, -20), (6, 1), (7, -4), (8, 96), (9, 112), (10, 48), (11, 56), (12, -16), (16, 9), (18, 7), (19, -32), (21, -15), (24, -7), (26, -1), (27, -96), (28, -1), (32, 8), (33, -9), (34, -5), (35, 18), (36, -80), (42, -32), (43, -128), (47, 23), (48, -40), (50, 48), (51, 32), (52, 32), (53, -16), (58, 32), (59, -32), (60, 32), (65, -16), (69, 32), (70, 32), (72, -16), (75, 16), (77, -32), (79, -32), (82, -32), (83, -16), (84, 16), (86, 32), (93, 128), (101, -32), (102, 64), (120, -32), (121, -8), (122, 32), (125, -48), (127, 16), (135, 64), (148, -48), (154, 112), (171, -112), (196, 48), (203, -8), (210, 16), (227, -48), (250, -32), (277, 64), (297, -16), (301, 96), (304, 16), (305, 16), (313, 16), (379, 16), (391, -104), (406, 120)]

theorem g32p_literalReconstructionIdentity_001 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_001 j =
      if (1 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_002 : List (Fin 408 × ℤ) :=
  [(51, 1)]

theorem g32p_literalReconstructionIdentity_002 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_002 j =
      if (2 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_003 : List (Fin 408 × ℤ) :=
  [(1, -10), (2, 336), (3, 1446), (4, 1), (6, -10), (7, 168), (8, -5664), (9, -6608), (10, -2832), (11, -3304), (12, 944), (16, -418), (18, -502), (19, 1939), (21, 796), (24, 326), (25, -48), (26, 10), (27, 5664), (28, 10), (32, -608), (33, 336), (34, 242), (35, -866), (36, 4721), (42, 1888), (43, 7629), (47, -1110), (48, 2360), (50, -2832), (51, -988), (52, -1010), (53, 784), (54, -764), (58, -1180), (59, 1888), (60, -1888), (65, 944), (68, -10), (69, -990), (70, -1865), (71, -160), (72, 598), (75, -502), (77, 1194), (79, 1034), (82, 1050), (83, 796), (84, -204), (86, -1208), (93, -7553), (98, -198), (101, 1888), (102, -3776), (115, 20), (120, 1888), (121, 472), (122, -1888), (125, 2832), (127, -944), (131, 10), (135, -3776), (142, -72), (144, 60), (148, 2832), (154, -6608), (156, 1), (158, 72), (162, -53), (171, 6607), (186, -1), (195, -30), (196, -2832), (203, 472), (210, -608), (211, -51), (219, -125), (227, 2832), (237, 157), (247, -94), (250, 1002), (253, 1), (257, -10), (261, 44), (272, 150), (275, 167), (277, -3776), (297, 987), (299, 41), (301, -5662), (304, -944), (305, -944), (312, -22), (313, -890), (379, -944), (391, 6136), (406, -7081)]

theorem g32p_literalReconstructionIdentity_003 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_003 j =
      if (3 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_004 : List (Fin 408 × ℤ) :=
  [(3, 1), (19, -2), (25, 1), (27, -4), (32, -1), (36, -3), (43, -2), (49, -1), (50, 3), (51, -2), (52, -2), (53, 1), (58, -2), (60, 3), (65, -2), (69, -2), (70, 2), (72, 1), (75, -1), (77, 2), (79, 2), (82, 2), (83, 1), (84, -1), (86, -2), (93, 8), (101, -2), (102, 3), (120, -2), (125, -3), (127, 5), (135, 3), (148, -5), (154, 5), (156, 1), (171, -6), (186, -1), (196, 2), (210, -1), (227, -2), (250, 2), (257, 1), (277, 3), (297, -1), (301, 4), (304, -1), (305, -1), (379, 1), (391, -3), (406, 3)]

theorem g32p_literalReconstructionIdentity_004 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_004 j =
      if (4 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_005 : List (Fin 408 × ℤ) :=
  [(1, -1), (2, 8), (3, 31), (7, 4), (8, -120), (9, -139), (10, -60), (11, -69), (12, 19), (14, 1), (15, 1), (16, -11), (18, -11), (19, 38), (21, 18), (24, 7), (25, -1), (27, 114), (32, -14), (33, 7), (34, 4), (35, -25), (36, 95), (42, 40), (43, 156), (47, -27), (48, 48), (50, -57), (51, -38), (52, -38), (53, 19), (58, -38), (59, 38), (60, -38), (65, 19), (69, -38), (70, -38), (72, 19), (75, -19), (77, 38), (79, 38), (82, 38), (83, 19), (84, -19), (86, -38), (93, -152), (101, 38), (102, -76), (120, 38), (121, 9), (122, -38), (125, 57), (127, -19), (135, -76), (148, 57), (154, -133), (171, 133), (196, -57), (203, 10), (210, -19), (227, 57), (250, 38), (277, -76), (297, 19), (301, -114), (304, -21), (305, -19), (313, -18), (379, -19), (391, 125), (406, -144)]

theorem g32p_literalReconstructionIdentity_005 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_005 j =
      if (5 : Fin 102) = j then 1 else 0 := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalReconstructionCoefficients_006 : List (Fin 408 × ℤ) :=
  [(102, 1)]

theorem g32p_literalReconstructionIdentity_006 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_006 j =
      if (6 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_007 : List (Fin 408 × ℤ) :=
  [(1, -1), (2, 8), (3, 29), (7, 4), (8, -119), (9, -136), (10, -59), (11, -68), (12, 20), (14, 1), (15, 1), (16, -11), (18, -11), (19, 40), (21, 18), (24, 7), (25, -3), (27, 120), (32, -12), (33, 7), (34, 4), (35, -25), (36, 100), (42, 39), (43, 160), (47, -27), (48, 50), (50, -60), (51, -40), (52, -40), (53, 20), (58, -40), (59, 40), (60, -40), (65, 20), (69, -40), (70, -40), (72, 20), (75, -20), (77, 40), (79, 40), (82, 40), (83, 20), (84, -20), (86, -40), (93, -160), (101, 40), (102, -80), (120, 40), (121, 9), (122, -40), (125, 60), (127, -20), (135, -80), (148, 60), (154, -140), (171, 140), (172, -1), (196, -60), (203, 10), (210, -20), (227, 60), (250, 40), (277, -80), (297, 20), (301, -120), (304, -19), (305, -20), (313, -18), (379, -20), (391, 128), (406, -150)]

theorem g32p_literalReconstructionIdentity_007 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_007 j =
      if (7 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_008 : List (Fin 408 × ℤ) :=
  [(19, -1), (51, -4), (52, -4), (53, 2), (58, -4), (60, 3), (65, -1), (69, -4), (70, 1), (72, 2), (75, -2), (77, 4), (79, 4), (82, 4), (83, 2), (84, -2), (86, -4), (93, 4), (101, -1), (102, 2), (122, -1), (125, -2), (127, 4), (135, 1), (148, -3), (210, -2), (250, 4), (277, 1), (297, 1), (305, -2), (391, -1)]

theorem g32p_literalReconstructionIdentity_008 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_008 j =
      if (8 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_009 : List (Fin 408 × ℤ) :=
  [(1, -27), (2, 886), (3, 3839), (6, -27), (7, 443), (8, -15012), (9, -17514), (10, -7506), (11, -8757), (12, 2502), (16, -1105), (18, -1334), (19, 5143), (21, 2106), (24, 862), (25, -135), (26, 27), (27, 15012), (28, 27), (32, -1615), (33, 886), (34, 639), (35, -2296), (36, 12510), (42, 5004), (43, 20217), (47, -2937), (48, 6255), (50, -7506), (51, -2559), (52, -2620), (53, 2063), (54, -2068), (58, -3078), (59, 5004), (60, -5004), (65, 2502), (68, -27), (69, -2564), (70, -4944), (71, -438), (72, 1561), (75, -1302), (77, 3117), (79, 2679), (82, 2727), (83, 2092), (84, -496), (86, -3162), (93, -20016), (98, -536), (101, 5004), (102, -10008), (107, -2), (115, 55), (120, 5004), (121, 1251), (122, -5004), (125, 7506), (127, -2502), (131, 27), (135, -10008), (142, -195), (144, 165), (148, 7506), (154, -17514), (158, 196), (162, -141), (171, 17514), (195, -82), (196, -7506), (203, 1251), (210, -1585), (211, -142), (219, -339), (227, 7506), (237, 423), (247, -256), (250, 2595), (253, 2), (257, -26), (261, 114), (272, 405), (275, 445), (277, -10008), (297, 2616), (299, 112), (301, -15012), (304, -2502), (305, -2502), (312, -62), (313, -2363), (379, -2502), (391, 16263), (406, -18765)]

theorem g32p_literalReconstructionIdentity_009 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_009 j =
      if (9 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_010 : List (Fin 408 × ℤ) :=
  [(1, 21), (2, -660), (3, -2850), (6, 20), (7, -330), (8, 11148), (9, 13006), (10, 5574), (11, 6503), (12, -1858), (16, 824), (18, 991), (19, -3819), (21, -1568), (24, -640), (25, 102), (26, -20), (27, -11148), (28, -20), (32, 1198), (33, -660), (34, -475), (35, 1711), (36, -9290), (42, -3716), (43, -15010), (47, 2187), (48, -4645), (50, 5574), (51, 1896), (52, 1939), (53, -1530), (54, 1534), (58, 2279), (59, -3716), (60, 3716), (65, -1858), (68, 21), (69, 1898), (70, 3675), (71, 328), (72, -1159), (75, 964), (77, -2308), (79, -1980), (82, -2020), (83, -1551), (84, 366), (86, 2347), (93, 14864), (98, 401), (101, -3716), (102, 7432), (115, -41), (120, -3716), (121, -929), (122, 3716), (125, -5574), (127, 1858), (131, -20), (135, 7432), (142, 144), (144, -123), (148, -5574), (154, 13006), (158, -144), (162, 102), (171, -13006), (195, 61), (196, 5574), (203, -929), (210, 1171), (211, 103), (219, 248), (227, -5574), (237, -310), (247, 186), (250, -1919), (253, 1), (257, 20), (261, -81), (272, -300), (275, -333), (277, 7432), (297, -1940), (299, -84), (301, 11148), (304, 1858), (305, 1858), (312, 41), (313, 1754), (379, 1858), (391, -12077), (406, 13935)]

theorem g32p_literalReconstructionIdentity_010 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_010 j =
      if (10 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_011 : List (Fin 408 × ℤ) :=
  [(1, 14), (2, -402), (3, -1731), (6, 12), (7, -201), (8, 6768), (9, 7896), (10, 3384), (11, 3948), (12, -1128), (16, 503), (18, 603), (19, -2318), (21, -955), (24, -388), (25, 64), (26, -11), (27, -6768), (28, -12), (32, 727), (33, -402), (34, -288), (35, 1045), (36, -5640), (42, -2256), (43, -9110), (47, 1333), (48, -2820), (50, 3384), (51, 1149), (52, 1173), (53, -925), (54, 924), (58, 1377), (59, -2256), (60, 2256), (65, -1128), (68, 13), (69, 1148), (70, 2238), (71, 203), (72, -704), (75, 584), (77, -1395), (79, -1192), (82, -1223), (83, -936), (84, 224), (86, 1426), (93, 9024), (98, 244), (101, -2256), (102, 4512), (107, -1), (115, -25), (120, -2256), (121, -564), (122, 2256), (125, -3384), (127, 1128), (131, -12), (135, 4512), (142, 86), (144, -76), (148, -3384), (154, 7896), (158, -86), (162, 57), (171, -7896), (195, 37), (196, 3384), (203, -564), (210, 703), (211, 61), (219, 145), (227, -3384), (237, -180), (247, 107), (250, -1158), (253, 3), (257, 12), (261, -45), (272, -180), (275, -198), (277, 4512), (297, -1172), (299, -52), (301, 6768), (304, 1128), (305, 1128), (312, 22), (313, 1064), (379, 1128), (391, -7332), (406, 8460)]

theorem g32p_literalReconstructionIdentity_011 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_011 j =
      if (11 : Fin 102) = j then 1 else 0 := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalReconstructionCoefficients_012 : List (Fin 408 × ℤ) :=
  [(1, -2), (2, 64), (3, 276), (6, -2), (7, 32), (8, -1080), (9, -1260), (10, -540), (11, -630), (12, 180), (16, -80), (18, -96), (19, 370), (21, 152), (24, 62), (25, -10), (26, 2), (27, 1080), (28, 2), (32, -116), (33, 64), (34, 46), (35, -166), (36, 900), (42, 360), (43, 1454), (47, -212), (48, 450), (50, -540), (51, -184), (52, -188), (53, 150), (54, -153), (58, -223), (59, 360), (60, -360), (65, 180), (68, -2), (69, -184), (70, -356), (71, -31), (72, 112), (75, -93), (77, 225), (79, 193), (82, 196), (83, 153), (84, -34), (86, -228), (93, -1440), (98, -40), (101, 360), (102, -720), (115, 4), (120, 360), (121, 90), (122, -360), (125, 540), (127, -180), (131, 2), (135, -720), (142, -14), (144, 11), (148, 540), (154, -1260), (158, 14), (162, -10), (171, 1260), (195, -6), (196, -540), (203, 90), (210, -116), (211, -10), (219, -24), (227, 540), (237, 30), (247, -18), (250, 187), (257, -2), (261, 8), (272, 30), (275, 32), (277, -720), (297, 188), (299, 8), (301, -1080), (304, -180), (305, -180), (312, -4), (313, -170), (379, -180), (391, 1170), (406, -1350)]

theorem g32p_literalReconstructionIdentity_012 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_012 j =
      if (12 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_013 : List (Fin 408 × ℤ) :=
  [(1, -13), (2, 402), (3, 1726), (6, -12), (7, 201), (8, -6756), (9, -7882), (10, -3378), (11, -3941), (12, 1126), (16, -503), (18, -601), (19, 2314), (21, 954), (24, 388), (25, -64), (26, 12), (27, 6756), (28, 13), (32, -725), (33, 402), (34, 288), (35, -1045), (36, 5630), (42, 2252), (43, 9093), (47, -1332), (48, 2815), (50, -3378), (51, -1145), (52, -1169), (53, 923), (54, -924), (58, -1373), (59, 2252), (60, -2252), (65, 1126), (68, -13), (69, -1144), (70, -2234), (71, -203), (72, 702), (75, -582), (77, 1391), (79, 1188), (82, 1219), (83, 934), (84, -222), (86, -1422), (93, -9008), (98, -244), (101, 2252), (102, -4504), (107, 1), (115, 25), (120, 2252), (121, 563), (122, -2252), (125, 3378), (127, -1126), (131, 12), (135, -4504), (142, -86), (144, 76), (148, 3378), (154, -7882), (158, 86), (162, -57), (171, 7882), (195, -37), (196, -3378), (203, 563), (210, -701), (211, -61), (219, -145), (227, 3378), (237, 180), (247, -107), (250, 1154), (253, -3), (257, -12), (261, 45), (272, 180), (275, 198), (277, -4504), (297, 1170), (299, 52), (301, -6756), (304, -1126), (305, -1126), (312, -22), (313, -1063), (379, -1126), (391, 7319), (406, -8445)]

theorem g32p_literalReconstructionIdentity_013 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_013 j =
      if (13 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_014 : List (Fin 408 × ℤ) :=
  [(1, 3), (2, -96), (3, -414), (6, 3), (7, -48), (8, 1620), (9, 1890), (10, 810), (11, 945), (12, -270), (16, 120), (18, 144), (19, -555), (21, -228), (24, -93), (25, 15), (26, -3), (27, -1620), (28, -3), (32, 174), (33, -96), (34, -69), (35, 249), (36, -1350), (42, -540), (43, -2181), (47, 318), (48, -675), (50, 810), (51, 276), (52, 284), (53, -224), (54, 226), (58, 335), (59, -540), (60, 540), (65, -270), (68, 3), (69, 278), (70, 534), (71, 47), (72, -168), (75, 141), (77, -336), (79, -288), (82, -294), (83, -228), (84, 52), (86, 340), (93, 2160), (98, 58), (101, -540), (102, 1080), (115, -6), (120, -540), (121, -135), (122, 540), (125, -810), (127, 270), (131, -3), (135, 1080), (142, 21), (144, -17), (148, -810), (154, 1890), (158, -21), (162, 15), (171, -1890), (195, 9), (196, 810), (203, -135), (210, 173), (211, 15), (219, 36), (227, -810), (237, -45), (247, 27), (250, -281), (257, 3), (261, -12), (272, -45), (275, -48), (277, 1080), (297, -282), (299, -12), (301, 1620), (304, 270), (305, 270), (312, 6), (313, 255), (379, 270), (391, -1755), (406, 2025)]

theorem g32p_literalReconstructionIdentity_014 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_014 j =
      if (14 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_015 : List (Fin 408 × ℤ) :=
  [(1, 5), (2, -168), (3, -723), (6, 5), (7, -84), (8, 2832), (9, 3304), (10, 1416), (11, 1652), (12, -472), (16, 209), (18, 251), (19, -971), (21, -398), (24, -163), (25, 24), (26, -5), (27, -2832), (28, -5), (32, 304), (33, -168), (34, -121), (35, 433), (36, -2360), (42, -944), (43, -3814), (47, 555), (48, -1180), (50, 1416), (51, 494), (52, 505), (53, -392), (54, 382), (58, 590), (59, -944), (60, 944), (65, -472), (68, 5), (69, 495), (70, 932), (71, 80), (72, -299), (75, 251), (77, -597), (79, -517), (82, -525), (83, -398), (84, 102), (86, 604), (93, 3776), (98, 99), (101, -944), (102, 1888), (115, -10), (120, -944), (121, -236), (122, 944), (125, -1416), (127, 472), (131, -5), (135, 1888), (142, 36), (144, -30), (148, -1416), (154, 3304), (158, -36), (162, 27), (171, -3304), (195, 15), (196, 1416), (203, -236), (210, 304), (211, 26), (219, 63), (227, -1416), (237, -79), (247, 47), (250, -501), (253, -1), (257, 5), (261, -22), (271, -1), (272, -75), (275, -82), (277, 1888), (297, -493), (299, -18), (301, 2832), (304, 472), (305, 472), (312, 11), (313, 445), (379, 472), (391, -3068), (406, 3540)]

theorem g32p_literalReconstructionIdentity_015 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_015 j =
      if (15 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_016 : List (Fin 408 × ℤ) :=
  [(2, 6), (3, 21), (7, 3), (8, -84), (9, -98), (10, -42), (11, -49), (12, 14), (16, -7), (18, -7), (19, 28), (21, 12), (24, 5), (27, 84), (32, -9), (33, 5), (34, 4), (35, -14), (36, 70), (42, 28), (43, 114), (47, -17), (48, 35), (50, -42), (51, -28), (52, -28), (53, 14), (58, -28), (59, 28), (60, -28), (65, 14), (69, -28), (70, -28), (72, 14), (75, -14), (77, 28), (79, 28), (82, 28), (83, 14), (84, -14), (86, -28), (93, -112), (101, 28), (102, -56), (120, 28), (121, 7), (122, -28), (125, 42), (127, -14), (135, -56), (148, 42), (154, -98), (171, 98), (196, -42), (203, 7), (210, -14), (227, 42), (250, 28), (277, -56), (297, 14), (301, -84), (304, -14), (305, -14), (313, -13), (379, -14), (391, 91), (406, -105)]

theorem g32p_literalReconstructionIdentity_016 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_016 j =
      if (16 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_017 : List (Fin 408 × ℤ) :=
  [(1, -1), (2, 32), (3, 138), (6, -1), (7, 16), (8, -540), (9, -630), (10, -270), (11, -315), (12, 90), (16, -40), (18, -48), (19, 185), (21, 76), (24, 31), (25, -5), (26, 1), (27, 540), (28, 1), (32, -58), (33, 32), (34, 23), (35, -83), (36, 450), (42, 180), (43, 727), (47, -106), (48, 225), (50, -270), (51, -92), (52, -94), (53, 75), (54, -75), (58, -111), (59, 180), (60, -180), (65, 90), (68, -1), (69, -92), (70, -178), (71, -16), (72, 56), (75, -47), (77, 112), (79, 96), (82, 98), (83, 75), (84, -18), (86, -114), (93, -720), (98, -19), (101, 180), (102, -360), (115, 2), (120, 180), (121, 45), (122, -180), (125, 270), (127, -90), (131, 1), (135, -360), (142, -7), (144, 6), (148, 270), (154, -630), (158, 7), (162, -5), (171, 630), (195, -3), (196, -270), (203, 45), (210, -57), (211, -5), (219, -12), (227, 270), (237, 15), (247, -9), (250, 93), (257, -1), (261, 4), (272, 15), (275, 16), (277, -360), (297, 94), (299, 4), (301, -540), (304, -90), (305, -90), (312, -2), (313, -85), (379, -90), (391, 585), (406, -675)]

theorem g32p_literalReconstructionIdentity_017 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_017 j =
      if (17 : Fin 102) = j then 1 else 0 := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalReconstructionCoefficients_018 : List (Fin 408 × ℤ) :=
  [(1, 5), (2, -168), (3, -723), (6, 5), (7, -84), (8, 2832), (9, 3304), (10, 1416), (11, 1652), (12, -472), (16, 209), (18, 251), (19, -970), (21, -398), (24, -163), (25, 24), (26, -5), (27, -2832), (28, -5), (32, 304), (33, -168), (34, -121), (35, 433), (36, -2360), (42, -944), (43, -3814), (47, 555), (48, -1180), (50, 1416), (51, 494), (52, 505), (53, -392), (54, 382), (58, 590), (59, -944), (60, 944), (65, -472), (68, 5), (69, 495), (70, 934), (71, 80), (72, -299), (75, 251), (77, -597), (79, -517), (82, -525), (83, -398), (84, 102), (86, 604), (93, 3776), (98, 99), (101, -944), (102, 1888), (115, -10), (120, -944), (121, -236), (122, 944), (125, -1416), (127, 472), (131, -5), (135, 1888), (142, 36), (144, -30), (148, -1416), (154, 3304), (158, -36), (162, 26), (171, -3304), (195, 15), (196, 1416), (203, -236), (210, 304), (211, 26), (219, 62), (227, -1416), (237, -78), (247, 47), (250, -501), (257, 4), (261, -21), (272, -75), (275, -84), (277, 1888), (297, -493), (299, -22), (301, 2832), (304, 472), (305, 472), (312, 11), (313, 445), (379, 472), (391, -3068), (406, 3540)]

theorem g32p_literalReconstructionIdentity_018 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_018 j =
      if (18 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_019 : List (Fin 408 × ℤ) :=
  [(1, 5), (2, -168), (3, -723), (6, 5), (7, -84), (8, 2832), (9, 3304), (10, 1416), (11, 1652), (12, -472), (16, 209), (18, 251), (19, -969), (21, -398), (24, -163), (25, 24), (26, -5), (27, -2832), (28, -5), (32, 304), (33, -168), (34, -121), (35, 433), (36, -2360), (42, -944), (43, -3814), (47, 555), (48, -1180), (50, 1416), (51, 494), (52, 505), (53, -392), (54, 382), (58, 590), (59, -944), (60, 944), (65, -472), (68, 5), (69, 495), (70, 933), (71, 80), (72, -299), (75, 251), (77, -597), (79, -517), (82, -525), (83, -398), (84, 102), (86, 604), (93, 3776), (98, 99), (101, -944), (102, 1888), (115, -10), (120, -944), (121, -236), (122, 944), (125, -1416), (127, 472), (131, -5), (135, 1888), (142, 36), (144, -30), (148, -1416), (154, 3304), (158, -36), (162, 26), (171, -3304), (195, 15), (196, 1416), (203, -236), (210, 304), (211, 26), (219, 62), (227, -1416), (237, -78), (247, 47), (250, -501), (257, 5), (261, -22), (272, -75), (275, -84), (277, 1888), (297, -493), (299, -22), (301, 2832), (304, 472), (305, 472), (312, 11), (313, 445), (379, 472), (391, -3068), (406, 3540)]

theorem g32p_literalReconstructionIdentity_019 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_019 j =
      if (19 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_020 : List (Fin 408 × ℤ) :=
  [(2, 4), (3, 14), (7, 2), (8, -60), (9, -70), (10, -30), (11, -35), (12, 10), (16, -5), (18, -5), (19, 20), (21, 9), (24, 4), (26, -1), (27, 60), (32, -5), (33, 4), (34, 3), (35, -10), (36, 50), (42, 20), (43, 81), (47, -13), (48, 25), (50, -30), (51, -20), (52, -20), (53, 10), (58, -20), (59, 20), (60, -20), (65, 10), (69, -20), (70, -20), (72, 10), (75, -10), (77, 20), (79, 20), (82, 20), (83, 10), (84, -10), (86, -20), (93, -80), (101, 20), (102, -40), (120, 20), (121, 5), (122, -20), (125, 30), (127, -10), (135, -40), (148, 30), (154, -70), (171, 70), (196, -30), (203, 5), (210, -10), (227, 30), (250, 20), (277, -40), (297, 10), (301, -60), (304, -10), (305, -10), (313, -9), (379, -10), (391, 65), (406, -75)]

theorem g32p_literalReconstructionIdentity_020 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_020 j =
      if (20 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_021 : List (Fin 408 × ℤ) :=
  [(1, -1), (2, 32), (3, 138), (6, -1), (7, 16), (8, -540), (9, -630), (10, -270), (11, -315), (12, 90), (16, -40), (18, -48), (19, 185), (21, 76), (24, 31), (25, -5), (26, 1), (27, 540), (28, 1), (32, -58), (33, 32), (34, 23), (35, -83), (36, 450), (42, 180), (43, 727), (47, -106), (48, 225), (50, -270), (51, -91), (52, -93), (53, 74), (54, -76), (58, -110), (59, 180), (60, -180), (65, 90), (68, -1), (69, -91), (70, -178), (71, -16), (72, 56), (75, -46), (77, 110), (79, 95), (82, 97), (83, 76), (84, -17), (86, -113), (93, -720), (98, -20), (101, 180), (102, -360), (115, 2), (120, 180), (121, 45), (122, -180), (125, 270), (127, -90), (131, 1), (135, -360), (142, -7), (144, 6), (148, 270), (154, -630), (158, 7), (162, -5), (171, 630), (195, -3), (196, -270), (203, 45), (210, -56), (211, -5), (219, -12), (227, 270), (237, 15), (247, -9), (250, 92), (257, -1), (261, 4), (272, 15), (275, 16), (277, -360), (297, 94), (299, 4), (301, -540), (304, -90), (305, -90), (312, -2), (313, -85), (379, -90), (391, 585), (406, -675)]

theorem g32p_literalReconstructionIdentity_021 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_021 j =
      if (21 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_022 : List (Fin 408 × ℤ) :=
  [(2, 4), (3, 15), (7, 2), (8, -60), (9, -70), (10, -30), (11, -35), (12, 10), (16, -5), (18, -5), (19, 20), (21, 9), (24, 4), (25, 1), (27, 60), (28, -1), (32, -6), (33, 4), (34, 3), (35, -10), (36, 50), (42, 20), (43, 81), (47, -13), (48, 25), (50, -30), (51, -20), (52, -20), (53, 10), (58, -20), (59, 20), (60, -20), (65, 10), (69, -20), (70, -20), (72, 10), (75, -10), (77, 20), (79, 20), (82, 20), (83, 10), (84, -10), (86, -20), (93, -80), (101, 20), (102, -40), (120, 20), (121, 5), (122, -20), (125, 30), (127, -10), (135, -40), (148, 30), (154, -70), (171, 70), (196, -30), (203, 5), (210, -10), (227, 30), (250, 20), (277, -40), (297, 10), (301, -60), (304, -10), (305, -10), (313, -9), (379, -10), (391, 65), (406, -75)]

theorem g32p_literalReconstructionIdentity_022 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_022 j =
      if (22 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_023 : List (Fin 408 × ℤ) :=
  [(1, 1), (2, -32), (3, -138), (6, 1), (7, -16), (8, 540), (9, 630), (10, 270), (11, 315), (12, -90), (16, 40), (18, 48), (19, -185), (21, -76), (24, -31), (25, 5), (26, -1), (27, -540), (28, -1), (32, 58), (33, -32), (34, -23), (35, 83), (36, -450), (42, -180), (43, -727), (47, 106), (48, -225), (50, 270), (51, 90), (52, 92), (53, -74), (54, 77), (58, 109), (59, -180), (60, 180), (65, -90), (68, 1), (69, 90), (70, 178), (71, 17), (72, -55), (75, 46), (77, -110), (79, -94), (82, -96), (83, -75), (84, 16), (86, 112), (93, 720), (98, 19), (101, -180), (102, 360), (115, -2), (120, -180), (121, -45), (122, 180), (125, -270), (127, 90), (131, -1), (135, 360), (142, 7), (144, -6), (148, -270), (154, 630), (158, -7), (162, 5), (171, -630), (195, 3), (196, 270), (203, -45), (210, 56), (211, 5), (219, 12), (227, -270), (237, -15), (247, 9), (250, -91), (257, 1), (261, -4), (272, -15), (275, -16), (277, 360), (297, -94), (299, -4), (301, 540), (304, 90), (305, 90), (312, 2), (313, 85), (379, 90), (391, -585), (406, 675)]

theorem g32p_literalReconstructionIdentity_023 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_023 j =
      if (23 : Fin 102) = j then 1 else 0 := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_literalReconstructionCoefficients_024 : List (Fin 408 × ℤ) :=
  [(1, -5), (2, 168), (3, 723), (6, -5), (7, 84), (8, -2832), (9, -3304), (10, -1416), (11, -1652), (12, 472), (16, -209), (18, -251), (19, 970), (21, 398), (24, 163), (25, -24), (26, 5), (27, 2832), (28, 5), (32, -304), (33, 168), (34, 121), (35, -433), (36, 2360), (42, 944), (43, 3814), (47, -555), (48, 1180), (50, -1416), (51, -494), (52, -505), (53, 392), (54, -382), (58, -590), (59, 944), (60, -944), (65, 472), (68, -5), (69, -495), (70, -932), (71, -80), (72, 299), (75, -251), (77, 597), (79, 517), (82, 525), (83, 398), (84, -102), (86, -604), (93, -3776), (98, -99), (101, 944), (102, -1888), (115, 10), (120, 944), (121, 236), (122, -944), (125, 1416), (127, -472), (131, 5), (135, -1888), (142, -36), (144, 30), (148, 1416), (154, -3304), (158, 36), (162, -27), (171, 3304), (195, -15), (196, -1416), (203, 236), (210, -304), (211, -26), (219, -63), (227, 1416), (237, 80), (247, -48), (250, 501), (253, 1), (257, -5), (261, 22), (272, 75), (275, 83), (277, -1888), (297, 494), (299, 20), (301, -2832), (304, -472), (305, -472), (312, -11), (313, -445), (379, -472), (391, 3068), (406, -3540)]

theorem g32p_literalReconstructionIdentity_024 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_024 j =
      if (24 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_025 : List (Fin 408 × ℤ) :=
  [(1, 5), (2, -168), (3, -723), (6, 5), (7, -84), (8, 2832), (9, 3304), (10, 1416), (11, 1652), (12, -472), (16, 209), (18, 251), (19, -970), (21, -398), (24, -163), (25, 24), (26, -5), (27, -2832), (28, -5), (32, 304), (33, -168), (34, -121), (35, 433), (36, -2360), (42, -944), (43, -3814), (47, 555), (48, -1180), (50, 1416), (51, 494), (52, 505), (53, -392), (54, 382), (58, 590), (59, -944), (60, 944), (65, -472), (68, 5), (69, 495), (70, 933), (71, 80), (72, -299), (75, 251), (77, -597), (79, -517), (82, -525), (83, -398), (84, 102), (86, 604), (93, 3776), (98, 99), (101, -944), (102, 1888), (115, -10), (120, -944), (121, -236), (122, 944), (125, -1416), (127, 472), (131, -5), (135, 1888), (142, 36), (144, -30), (148, -1416), (154, 3304), (158, -36), (162, 26), (171, -3304), (195, 15), (196, 1416), (203, -236), (210, 304), (211, 25), (219, 62), (227, -1416), (237, -78), (247, 46), (250, -501), (257, 5), (261, -21), (272, -75), (275, -83), (277, 1888), (297, -493), (299, -20), (301, 2832), (304, 472), (305, 472), (312, 10), (313, 445), (379, 472), (391, -3068), (406, 3540)]

theorem g32p_literalReconstructionIdentity_025 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_025 j =
      if (25 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_026 : List (Fin 408 × ℤ) :=
  [(2, -6), (3, -20), (7, -3), (8, 84), (9, 98), (10, 42), (11, 49), (12, -14), (16, 8), (18, 7), (19, -28), (21, -13), (24, -5), (27, -84), (32, 8), (33, -6), (34, -4), (35, 14), (36, -70), (42, -28), (43, -113), (47, 18), (48, -35), (50, 42), (51, 28), (52, 28), (53, -14), (58, 28), (59, -28), (60, 28), (65, -14), (69, 28), (70, 28), (72, -14), (75, 14), (77, -28), (79, -28), (82, -28), (83, -14), (84, 14), (86, 28), (93, 112), (101, -28), (102, 56), (120, -28), (121, -7), (122, 28), (125, -42), (127, 14), (135, 56), (148, -42), (154, 98), (171, -98), (196, 42), (203, -7), (210, 14), (227, -42), (250, -28), (277, 56), (297, -14), (301, 84), (304, 14), (305, 14), (313, 13), (379, 14), (391, -91), (406, 105)]

theorem g32p_literalReconstructionIdentity_026 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_026 j =
      if (26 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_027 : List (Fin 408 × ℤ) :=
  [(1, -1), (2, 32), (3, 138), (6, -1), (7, 16), (8, -540), (9, -630), (10, -270), (11, -315), (12, 90), (16, -40), (18, -48), (19, 185), (21, 76), (24, 31), (25, -5), (26, 1), (27, 540), (28, 1), (32, -58), (33, 32), (34, 23), (35, -83), (36, 450), (42, 180), (43, 727), (47, -106), (48, 225), (50, -270), (51, -92), (52, -95), (53, 74), (54, -74), (58, -111), (59, 180), (60, -180), (65, 90), (68, -1), (69, -93), (70, -178), (71, -16), (72, 56), (75, -47), (77, 112), (79, 96), (82, 98), (83, 75), (84, -18), (86, -114), (93, -720), (98, -19), (101, 180), (102, -360), (115, 2), (120, 180), (121, 45), (122, -180), (125, 270), (127, -90), (131, 1), (135, -360), (142, -7), (144, 6), (148, 270), (154, -630), (158, 7), (162, -5), (171, 630), (195, -3), (196, -270), (203, 45), (210, -57), (211, -5), (219, -12), (227, 270), (237, 15), (247, -9), (250, 94), (257, -1), (261, 4), (272, 15), (275, 16), (277, -360), (297, 94), (299, 4), (301, -540), (304, -90), (305, -90), (312, -2), (313, -85), (379, -90), (391, 585), (406, -675)]

theorem g32p_literalReconstructionIdentity_027 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_027 j =
      if (27 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_028 : List (Fin 408 × ℤ) :=
  [(2, 4), (3, 14), (7, 2), (8, -60), (9, -70), (10, -30), (11, -35), (12, 10), (16, -5), (18, -5), (19, 20), (21, 8), (24, 4), (27, 60), (32, -6), (33, 4), (34, 3), (35, -10), (36, 50), (42, 20), (43, 81), (47, -12), (48, 25), (50, -30), (51, -20), (52, -20), (53, 10), (58, -20), (59, 20), (60, -20), (65, 10), (69, -20), (70, -20), (72, 10), (75, -10), (77, 20), (79, 20), (82, 20), (83, 10), (84, -10), (86, -20), (93, -80), (101, 20), (102, -40), (120, 20), (121, 5), (122, -20), (125, 30), (127, -10), (135, -40), (148, 30), (154, -70), (171, 70), (196, -30), (203, 5), (210, -10), (227, 30), (250, 20), (277, -40), (297, 10), (301, -60), (304, -10), (305, -10), (313, -10), (379, -10), (391, 65), (406, -75)]

theorem g32p_literalReconstructionIdentity_028 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_028 j =
      if (28 : Fin 102) = j then 1 else 0 := by
  decide +kernel

def g32p_literalReconstructionCoefficients_029 : List (Fin 408 × ℤ) :=
  [(1, -1), (2, 32), (3, 138), (6, -1), (7, 16), (8, -540), (9, -630), (10, -270), (11, -315), (12, 90), (16, -40), (18, -48), (19, 185), (21, 76), (24, 31), (25, -5), (26, 1), (27, 540), (28, 1), (32, -58), (33, 32), (34, 23), (35, -83), (36, 450), (42, 180), (43, 727), (47, -106), (48, 225), (50, -270), (51, -91), (52, -93), (53, 74), (54, -76), (58, -110), (59, 180), (60, -180), (65, 90), (68, -1), (69, -91), (70, -178), (71, -16), (72, 55), (75, -46), (77, 111), (79, 95), (82, 97), (83, 75), (84, -17), (86, -113), (93, -720), (98, -19), (101, 180), (102, -360), (115, 2), (120, 180), (121, 45), (122, -180), (125, 270), (127, -90), (131, 1), (135, -360), (142, -7), (144, 6), (148, 270), (154, -630), (158, 7), (162, -5), (171, 630), (195, -3), (196, -270), (203, 45), (210, -57), (211, -5), (219, -12), (227, 270), (237, 15), (247, -9), (250, 92), (257, -1), (261, 4), (272, 15), (275, 16), (277, -360), (297, 94), (299, 4), (301, -540), (304, -90), (305, -90), (312, -2), (313, -85), (379, -90), (391, 585), (406, -675)]

theorem g32p_literalReconstructionIdentity_029 : ∀ j : Fin 102,
    g32p_literalReconstructionProduct g32p_literalReconstructionCoefficients_029 j =
      if (29 : Fin 102) = j then 1 else 0 := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end
