import HodgeLean.Foundations.Program.G32PropFourSixPacked0452
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0453
import HodgeLean.Foundations.Program.G32PropFourSixPacked0454
import HodgeLean.Foundations.Program.G32PropFourSixPacked0455
import HodgeLean.Foundations.Program.G32PropFourSixPacked0456
import HodgeLean.Foundations.Program.G32PropFourSixCharacters
import HodgeLean.Foundations.Program.G32PropFourSixPacked0451
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixRowComparison
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0003

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_restrictionCount_102 :
    (Finset.univ.filter (fun i => g32p_row02_restrictionBucket i = 102)).card = g32p_row02_restrictionSizes 102 := by
  decide +kernel

theorem g32p_row02_restrictionCount_103 :
    (Finset.univ.filter (fun i => g32p_row02_restrictionBucket i = 103)).card = g32p_row02_restrictionSizes 103 := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_restrictionCount_104 :
    (Finset.univ.filter (fun i => g32p_row02_restrictionBucket i = 104)).card = g32p_row02_restrictionSizes 104 := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_restrictionExponent_0 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 0 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 0 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_1 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 1 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 1 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_2 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 2 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 2 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_3 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 3 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 3 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_4 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 4 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 4 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_5 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 5 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 5 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_6 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 6 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 6 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_7 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 7 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 7 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_8 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 8 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 8 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_9 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 9 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 9 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_10 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 10 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 10 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_11 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 11 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 11 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_12 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 12 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 12 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_13 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 13 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 13 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_14 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 14 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 14 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_15 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 15 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 15 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_16 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 16 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 16 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_17 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 17 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 17 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_18 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 18 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 18 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_19 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 19 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 19 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_20 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 20 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 20 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_21 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 21 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 21 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_22 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 22 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 22 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_23 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 23 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 23 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_24 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 24 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 24 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_25 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 25 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 25 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_26 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 26 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 26 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_27 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 27 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 27 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_28 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 28 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 28 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_29 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 29 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 29 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_30 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 30 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 30 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_31 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 31 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 31 r)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_restrictionExponent_32 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 32 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 32 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_33 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 33 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 33 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_34 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 34 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 34 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_35 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 35 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 35 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_36 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 36 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 36 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_37 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 37 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 37 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_38 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 38 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 38 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_39 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 39 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 39 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_40 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 40 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 40 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_41 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 41 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 41 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_42 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 42 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 42 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_43 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 43 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 43 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_44 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 44 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 44 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_45 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 45 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 45 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_46 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 46 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 46 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_47 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 47 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 47 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_48 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 48 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 48 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_49 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 49 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 49 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_50 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 50 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 50 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_51 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 51 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 51 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_52 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 52 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 52 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_53 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 53 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 53 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_54 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 54 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 54 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_55 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 55 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 55 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_56 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 56 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 56 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_57 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 57 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 57 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_58 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 58 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 58 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_59 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 59 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 59 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_60 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 60 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 60 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_61 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 61 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 61 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_62 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 62 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 62 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_63 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 63 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 63 r)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_restrictionExponent_64 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 64 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 64 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_65 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 65 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 65 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_66 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 66 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 66 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_67 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 67 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 67 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_68 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 68 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 68 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_69 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 69 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 69 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_70 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 70 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 70 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_71 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 71 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 71 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_72 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 72 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 72 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_73 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 73 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 73 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_74 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 74 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 74 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_75 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 75 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 75 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_76 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 76 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 76 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_77 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 77 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 77 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_78 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 78 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 78 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_79 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 79 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 79 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_80 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 80 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 80 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_81 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 81 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 81 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_82 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 82 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 82 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_83 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 83 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 83 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_84 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 84 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 84 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_85 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 85 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 85 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_86 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 86 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 86 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_87 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 87 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 87 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_88 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 88 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 88 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_89 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 89 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 89 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_90 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 90 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 90 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_91 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 91 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 91 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_92 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 92 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 92 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_93 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 93 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 93 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_94 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 94 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 94 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_95 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 95 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 95 r)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_restrictionExponent_96 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 96 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 96 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_97 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 97 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 97 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_98 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 98 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 98 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_99 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 99 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 99 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_100 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 100 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 100 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_101 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 101 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 101 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_102 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 102 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 102 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_103 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 103 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 103 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_104 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 104 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 104 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_105 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 105 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 105 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_106 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 106 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 106 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_107 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 107 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 107 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_108 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 108 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 108 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_109 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 109 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 109 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_110 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 110 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 110 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_111 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 111 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 111 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_112 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 112 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 112 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_113 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 113 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 113 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_114 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 114 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 114 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_115 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 115 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 115 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_116 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 116 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 116 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_117 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 117 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 117 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_118 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 118 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 118 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_119 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 119 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 119 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_120 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 120 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 120 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_121 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 121 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 121 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_122 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 122 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 122 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_123 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 123 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 123 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_124 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 124 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 124 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_125 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 125 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 125 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_126 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 126 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 126 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_127 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 127 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 127 r)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_restrictionExponent_128 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 128 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 128 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_129 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 129 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 129 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_130 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 130 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 130 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_131 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 131 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 131 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_132 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 132 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 132 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_133 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 133 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 133 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_134 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 134 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 134 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_135 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 135 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 135 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_136 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 136 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 136 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_137 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 137 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 137 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_138 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 138 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 138 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_139 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 139 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 139 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_140 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 140 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 140 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_141 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 141 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 141 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_142 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 142 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 142 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_143 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 143 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 143 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_144 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 144 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 144 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_145 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 145 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 145 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_146 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 146 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 146 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_147 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 147 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 147 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_148 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 148 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 148 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_149 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 149 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 149 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_150 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 150 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 150 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_151 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 151 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 151 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_152 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 152 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 152 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_153 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 153 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 153 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_154 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 154 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 154 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_155 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 155 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 155 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_156 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 156 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 156 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_157 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 157 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 157 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_158 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 158 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 158 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_159 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 159 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 159 r)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_restrictionExponent_160 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 160 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 160 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_161 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 161 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 161 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_162 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 162 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 162 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_163 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 163 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 163 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_164 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 164 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 164 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_165 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 165 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 165 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_166 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 166 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 166 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_167 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 167 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 167 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_168 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 168 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 168 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_169 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 169 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 169 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_170 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 170 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 170 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_171 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 171 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 171 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_172 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 172 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 172 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_173 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 173 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 173 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_174 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 174 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 174 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_175 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 175 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 175 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_176 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 176 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 176 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_177 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 177 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 177 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_178 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 178 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 178 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_179 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 179 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 179 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_180 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 180 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 180 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_181 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 181 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 181 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_182 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 182 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 182 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_183 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 183 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 183 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_184 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 184 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 184 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_185 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 185 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 185 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_186 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 186 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 186 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_187 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 187 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 187 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_188 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 188 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 188 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_189 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 189 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 189 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_190 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 190 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 190 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_191 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 191 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 191 r)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_restrictionExponent_192 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 192 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 192 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_193 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 193 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 193 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_194 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 194 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 194 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_195 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 195 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 195 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_196 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 196 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 196 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_197 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 197 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 197 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_198 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 198 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 198 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_199 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 199 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 199 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_200 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 200 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 200 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_201 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 201 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 201 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_202 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 202 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 202 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_203 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 203 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 203 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_204 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 204 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 204 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_205 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 205 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 205 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_206 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 206 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 206 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_207 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 207 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 207 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_208 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 208 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 208 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_209 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 209 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 209 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_210 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 210 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 210 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_211 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 211 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 211 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_212 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 212 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 212 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_213 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 213 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 213 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_214 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 214 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 214 r)) := by
  decide +kernel

theorem g32p_row02_restrictionExponent_215 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row02_characterValues (g32p_finBlockIndex 3456 215 r))⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 215 r)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_restrictionCounts (a : Fin 105) :
    (Finset.univ.filter (fun i => g32p_row02_restrictionBucket i = a)).card = g32p_row02_restrictionSizes a := by
  fin_cases a
  · exact g32p_row02_restrictionCount_0
  · exact g32p_row02_restrictionCount_1
  · exact g32p_row02_restrictionCount_2
  · exact g32p_row02_restrictionCount_3
  · exact g32p_row02_restrictionCount_4
  · exact g32p_row02_restrictionCount_5
  · exact g32p_row02_restrictionCount_6
  · exact g32p_row02_restrictionCount_7
  · exact g32p_row02_restrictionCount_8
  · exact g32p_row02_restrictionCount_9
  · exact g32p_row02_restrictionCount_10
  · exact g32p_row02_restrictionCount_11
  · exact g32p_row02_restrictionCount_12
  · exact g32p_row02_restrictionCount_13
  · exact g32p_row02_restrictionCount_14
  · exact g32p_row02_restrictionCount_15
  · exact g32p_row02_restrictionCount_16
  · exact g32p_row02_restrictionCount_17
  · exact g32p_row02_restrictionCount_18
  · exact g32p_row02_restrictionCount_19
  · exact g32p_row02_restrictionCount_20
  · exact g32p_row02_restrictionCount_21
  · exact g32p_row02_restrictionCount_22
  · exact g32p_row02_restrictionCount_23
  · exact g32p_row02_restrictionCount_24
  · exact g32p_row02_restrictionCount_25
  · exact g32p_row02_restrictionCount_26
  · exact g32p_row02_restrictionCount_27
  · exact g32p_row02_restrictionCount_28
  · exact g32p_row02_restrictionCount_29
  · exact g32p_row02_restrictionCount_30
  · exact g32p_row02_restrictionCount_31
  · exact g32p_row02_restrictionCount_32
  · exact g32p_row02_restrictionCount_33
  · exact g32p_row02_restrictionCount_34
  · exact g32p_row02_restrictionCount_35
  · exact g32p_row02_restrictionCount_36
  · exact g32p_row02_restrictionCount_37
  · exact g32p_row02_restrictionCount_38
  · exact g32p_row02_restrictionCount_39
  · exact g32p_row02_restrictionCount_40
  · exact g32p_row02_restrictionCount_41
  · exact g32p_row02_restrictionCount_42
  · exact g32p_row02_restrictionCount_43
  · exact g32p_row02_restrictionCount_44
  · exact g32p_row02_restrictionCount_45
  · exact g32p_row02_restrictionCount_46
  · exact g32p_row02_restrictionCount_47
  · exact g32p_row02_restrictionCount_48
  · exact g32p_row02_restrictionCount_49
  · exact g32p_row02_restrictionCount_50
  · exact g32p_row02_restrictionCount_51
  · exact g32p_row02_restrictionCount_52
  · exact g32p_row02_restrictionCount_53
  · exact g32p_row02_restrictionCount_54
  · exact g32p_row02_restrictionCount_55
  · exact g32p_row02_restrictionCount_56
  · exact g32p_row02_restrictionCount_57
  · exact g32p_row02_restrictionCount_58
  · exact g32p_row02_restrictionCount_59
  · exact g32p_row02_restrictionCount_60
  · exact g32p_row02_restrictionCount_61
  · exact g32p_row02_restrictionCount_62
  · exact g32p_row02_restrictionCount_63
  · exact g32p_row02_restrictionCount_64
  · exact g32p_row02_restrictionCount_65
  · exact g32p_row02_restrictionCount_66
  · exact g32p_row02_restrictionCount_67
  · exact g32p_row02_restrictionCount_68
  · exact g32p_row02_restrictionCount_69
  · exact g32p_row02_restrictionCount_70
  · exact g32p_row02_restrictionCount_71
  · exact g32p_row02_restrictionCount_72
  · exact g32p_row02_restrictionCount_73
  · exact g32p_row02_restrictionCount_74
  · exact g32p_row02_restrictionCount_75
  · exact g32p_row02_restrictionCount_76
  · exact g32p_row02_restrictionCount_77
  · exact g32p_row02_restrictionCount_78
  · exact g32p_row02_restrictionCount_79
  · exact g32p_row02_restrictionCount_80
  · exact g32p_row02_restrictionCount_81
  · exact g32p_row02_restrictionCount_82
  · exact g32p_row02_restrictionCount_83
  · exact g32p_row02_restrictionCount_84
  · exact g32p_row02_restrictionCount_85
  · exact g32p_row02_restrictionCount_86
  · exact g32p_row02_restrictionCount_87
  · exact g32p_row02_restrictionCount_88
  · exact g32p_row02_restrictionCount_89
  · exact g32p_row02_restrictionCount_90
  · exact g32p_row02_restrictionCount_91
  · exact g32p_row02_restrictionCount_92
  · exact g32p_row02_restrictionCount_93
  · exact g32p_row02_restrictionCount_94
  · exact g32p_row02_restrictionCount_95
  · exact g32p_row02_restrictionCount_96
  · exact g32p_row02_restrictionCount_97
  · exact g32p_row02_restrictionCount_98
  · exact g32p_row02_restrictionCount_99
  · exact g32p_row02_restrictionCount_100
  · exact g32p_row02_restrictionCount_101
  · exact g32p_row02_restrictionCount_102
  · exact g32p_row02_restrictionCount_103
  · exact g32p_row02_restrictionCount_104

theorem g32p_row02_restrictionExponent (i : Fin 3456) :
    (Multiplicative.toAdd (g32p_row02_characterValues i)⁻¹).val =
      g32p_row02_restrictionExponents (g32p_row02_restrictionBucket i) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row02_restrictionExponent_0
  · exact g32p_row02_restrictionExponent_1
  · exact g32p_row02_restrictionExponent_2
  · exact g32p_row02_restrictionExponent_3
  · exact g32p_row02_restrictionExponent_4
  · exact g32p_row02_restrictionExponent_5
  · exact g32p_row02_restrictionExponent_6
  · exact g32p_row02_restrictionExponent_7
  · exact g32p_row02_restrictionExponent_8
  · exact g32p_row02_restrictionExponent_9
  · exact g32p_row02_restrictionExponent_10
  · exact g32p_row02_restrictionExponent_11
  · exact g32p_row02_restrictionExponent_12
  · exact g32p_row02_restrictionExponent_13
  · exact g32p_row02_restrictionExponent_14
  · exact g32p_row02_restrictionExponent_15
  · exact g32p_row02_restrictionExponent_16
  · exact g32p_row02_restrictionExponent_17
  · exact g32p_row02_restrictionExponent_18
  · exact g32p_row02_restrictionExponent_19
  · exact g32p_row02_restrictionExponent_20
  · exact g32p_row02_restrictionExponent_21
  · exact g32p_row02_restrictionExponent_22
  · exact g32p_row02_restrictionExponent_23
  · exact g32p_row02_restrictionExponent_24
  · exact g32p_row02_restrictionExponent_25
  · exact g32p_row02_restrictionExponent_26
  · exact g32p_row02_restrictionExponent_27
  · exact g32p_row02_restrictionExponent_28
  · exact g32p_row02_restrictionExponent_29
  · exact g32p_row02_restrictionExponent_30
  · exact g32p_row02_restrictionExponent_31
  · exact g32p_row02_restrictionExponent_32
  · exact g32p_row02_restrictionExponent_33
  · exact g32p_row02_restrictionExponent_34
  · exact g32p_row02_restrictionExponent_35
  · exact g32p_row02_restrictionExponent_36
  · exact g32p_row02_restrictionExponent_37
  · exact g32p_row02_restrictionExponent_38
  · exact g32p_row02_restrictionExponent_39
  · exact g32p_row02_restrictionExponent_40
  · exact g32p_row02_restrictionExponent_41
  · exact g32p_row02_restrictionExponent_42
  · exact g32p_row02_restrictionExponent_43
  · exact g32p_row02_restrictionExponent_44
  · exact g32p_row02_restrictionExponent_45
  · exact g32p_row02_restrictionExponent_46
  · exact g32p_row02_restrictionExponent_47
  · exact g32p_row02_restrictionExponent_48
  · exact g32p_row02_restrictionExponent_49
  · exact g32p_row02_restrictionExponent_50
  · exact g32p_row02_restrictionExponent_51
  · exact g32p_row02_restrictionExponent_52
  · exact g32p_row02_restrictionExponent_53
  · exact g32p_row02_restrictionExponent_54
  · exact g32p_row02_restrictionExponent_55
  · exact g32p_row02_restrictionExponent_56
  · exact g32p_row02_restrictionExponent_57
  · exact g32p_row02_restrictionExponent_58
  · exact g32p_row02_restrictionExponent_59
  · exact g32p_row02_restrictionExponent_60
  · exact g32p_row02_restrictionExponent_61
  · exact g32p_row02_restrictionExponent_62
  · exact g32p_row02_restrictionExponent_63
  · exact g32p_row02_restrictionExponent_64
  · exact g32p_row02_restrictionExponent_65
  · exact g32p_row02_restrictionExponent_66
  · exact g32p_row02_restrictionExponent_67
  · exact g32p_row02_restrictionExponent_68
  · exact g32p_row02_restrictionExponent_69
  · exact g32p_row02_restrictionExponent_70
  · exact g32p_row02_restrictionExponent_71
  · exact g32p_row02_restrictionExponent_72
  · exact g32p_row02_restrictionExponent_73
  · exact g32p_row02_restrictionExponent_74
  · exact g32p_row02_restrictionExponent_75
  · exact g32p_row02_restrictionExponent_76
  · exact g32p_row02_restrictionExponent_77
  · exact g32p_row02_restrictionExponent_78
  · exact g32p_row02_restrictionExponent_79
  · exact g32p_row02_restrictionExponent_80
  · exact g32p_row02_restrictionExponent_81
  · exact g32p_row02_restrictionExponent_82
  · exact g32p_row02_restrictionExponent_83
  · exact g32p_row02_restrictionExponent_84
  · exact g32p_row02_restrictionExponent_85
  · exact g32p_row02_restrictionExponent_86
  · exact g32p_row02_restrictionExponent_87
  · exact g32p_row02_restrictionExponent_88
  · exact g32p_row02_restrictionExponent_89
  · exact g32p_row02_restrictionExponent_90
  · exact g32p_row02_restrictionExponent_91
  · exact g32p_row02_restrictionExponent_92
  · exact g32p_row02_restrictionExponent_93
  · exact g32p_row02_restrictionExponent_94
  · exact g32p_row02_restrictionExponent_95
  · exact g32p_row02_restrictionExponent_96
  · exact g32p_row02_restrictionExponent_97
  · exact g32p_row02_restrictionExponent_98
  · exact g32p_row02_restrictionExponent_99
  · exact g32p_row02_restrictionExponent_100
  · exact g32p_row02_restrictionExponent_101
  · exact g32p_row02_restrictionExponent_102
  · exact g32p_row02_restrictionExponent_103
  · exact g32p_row02_restrictionExponent_104
  · exact g32p_row02_restrictionExponent_105
  · exact g32p_row02_restrictionExponent_106
  · exact g32p_row02_restrictionExponent_107
  · exact g32p_row02_restrictionExponent_108
  · exact g32p_row02_restrictionExponent_109
  · exact g32p_row02_restrictionExponent_110
  · exact g32p_row02_restrictionExponent_111
  · exact g32p_row02_restrictionExponent_112
  · exact g32p_row02_restrictionExponent_113
  · exact g32p_row02_restrictionExponent_114
  · exact g32p_row02_restrictionExponent_115
  · exact g32p_row02_restrictionExponent_116
  · exact g32p_row02_restrictionExponent_117
  · exact g32p_row02_restrictionExponent_118
  · exact g32p_row02_restrictionExponent_119
  · exact g32p_row02_restrictionExponent_120
  · exact g32p_row02_restrictionExponent_121
  · exact g32p_row02_restrictionExponent_122
  · exact g32p_row02_restrictionExponent_123
  · exact g32p_row02_restrictionExponent_124
  · exact g32p_row02_restrictionExponent_125
  · exact g32p_row02_restrictionExponent_126
  · exact g32p_row02_restrictionExponent_127
  · exact g32p_row02_restrictionExponent_128
  · exact g32p_row02_restrictionExponent_129
  · exact g32p_row02_restrictionExponent_130
  · exact g32p_row02_restrictionExponent_131
  · exact g32p_row02_restrictionExponent_132
  · exact g32p_row02_restrictionExponent_133
  · exact g32p_row02_restrictionExponent_134
  · exact g32p_row02_restrictionExponent_135
  · exact g32p_row02_restrictionExponent_136
  · exact g32p_row02_restrictionExponent_137
  · exact g32p_row02_restrictionExponent_138
  · exact g32p_row02_restrictionExponent_139
  · exact g32p_row02_restrictionExponent_140
  · exact g32p_row02_restrictionExponent_141
  · exact g32p_row02_restrictionExponent_142
  · exact g32p_row02_restrictionExponent_143
  · exact g32p_row02_restrictionExponent_144
  · exact g32p_row02_restrictionExponent_145
  · exact g32p_row02_restrictionExponent_146
  · exact g32p_row02_restrictionExponent_147
  · exact g32p_row02_restrictionExponent_148
  · exact g32p_row02_restrictionExponent_149
  · exact g32p_row02_restrictionExponent_150
  · exact g32p_row02_restrictionExponent_151
  · exact g32p_row02_restrictionExponent_152
  · exact g32p_row02_restrictionExponent_153
  · exact g32p_row02_restrictionExponent_154
  · exact g32p_row02_restrictionExponent_155
  · exact g32p_row02_restrictionExponent_156
  · exact g32p_row02_restrictionExponent_157
  · exact g32p_row02_restrictionExponent_158
  · exact g32p_row02_restrictionExponent_159
  · exact g32p_row02_restrictionExponent_160
  · exact g32p_row02_restrictionExponent_161
  · exact g32p_row02_restrictionExponent_162
  · exact g32p_row02_restrictionExponent_163
  · exact g32p_row02_restrictionExponent_164
  · exact g32p_row02_restrictionExponent_165
  · exact g32p_row02_restrictionExponent_166
  · exact g32p_row02_restrictionExponent_167
  · exact g32p_row02_restrictionExponent_168
  · exact g32p_row02_restrictionExponent_169
  · exact g32p_row02_restrictionExponent_170
  · exact g32p_row02_restrictionExponent_171
  · exact g32p_row02_restrictionExponent_172
  · exact g32p_row02_restrictionExponent_173
  · exact g32p_row02_restrictionExponent_174
  · exact g32p_row02_restrictionExponent_175
  · exact g32p_row02_restrictionExponent_176
  · exact g32p_row02_restrictionExponent_177
  · exact g32p_row02_restrictionExponent_178
  · exact g32p_row02_restrictionExponent_179
  · exact g32p_row02_restrictionExponent_180
  · exact g32p_row02_restrictionExponent_181
  · exact g32p_row02_restrictionExponent_182
  · exact g32p_row02_restrictionExponent_183
  · exact g32p_row02_restrictionExponent_184
  · exact g32p_row02_restrictionExponent_185
  · exact g32p_row02_restrictionExponent_186
  · exact g32p_row02_restrictionExponent_187
  · exact g32p_row02_restrictionExponent_188
  · exact g32p_row02_restrictionExponent_189
  · exact g32p_row02_restrictionExponent_190
  · exact g32p_row02_restrictionExponent_191
  · exact g32p_row02_restrictionExponent_192
  · exact g32p_row02_restrictionExponent_193
  · exact g32p_row02_restrictionExponent_194
  · exact g32p_row02_restrictionExponent_195
  · exact g32p_row02_restrictionExponent_196
  · exact g32p_row02_restrictionExponent_197
  · exact g32p_row02_restrictionExponent_198
  · exact g32p_row02_restrictionExponent_199
  · exact g32p_row02_restrictionExponent_200
  · exact g32p_row02_restrictionExponent_201
  · exact g32p_row02_restrictionExponent_202
  · exact g32p_row02_restrictionExponent_203
  · exact g32p_row02_restrictionExponent_204
  · exact g32p_row02_restrictionExponent_205
  · exact g32p_row02_restrictionExponent_206
  · exact g32p_row02_restrictionExponent_207
  · exact g32p_row02_restrictionExponent_208
  · exact g32p_row02_restrictionExponent_209
  · exact g32p_row02_restrictionExponent_210
  · exact g32p_row02_restrictionExponent_211
  · exact g32p_row02_restrictionExponent_212
  · exact g32p_row02_restrictionExponent_213
  · exact g32p_row02_restrictionExponent_214
  · exact g32p_row02_restrictionExponent_215

end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

theorem g32p_root_six_omega : g32p_root 6 ^ 2 = g32h_omega := by
  rw [g32p_root, ← Complex.exp_nat_mul, g32h_omega]
  congr 1
  ring

theorem g32p_root_fifteen_omega : g32p_root 15 ^ 5 = g32h_omega := by
  rw [g32p_root, ← Complex.exp_nat_mul, g32h_omega]
  congr 1
  ring

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_restriction_root_omega (m : ℕ) (hm : m = 3 ∨ m = 6 ∨ m = 12 ∨ m = 15) :
    g32p_root m ^ (m / 3) = g32h_omega := by
  rcases hm with rfl | rfl | rfl | rfl
  all_goals rw [g32p_root, ← Complex.exp_nat_mul, g32h_omega]; congr 1 <;> norm_num <;> ring

end HodgeLean.Foundations.Program

end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_restriction_from_buckets
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 3456),
      g32p_restrictionTrace τ τbar θ j (g32p_row02_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row02_restrictionCoefficients j (g32p_row02_restrictionBucket i))) :
    ∃ v ∈ g32VectorTable, v.i = 2 ∧
      papersA τ τbar θ g32p_row02_finiteSupplier.H (g32p_complexCharacter g32p_row02_finiteSupplier) =
        g32SparseVec v.coords := by
  classical
  let H := g32p_row02_finiteSupplier.H
  letI : Fintype H := Fintype.ofFinite H
  have hsum (j : Fin 48) :
      (∑ h : H, g32p_restrictionTrace τ τbar θ j h *
        ((g32p_complexCharacter g32p_row02_finiteSupplier) h⁻¹ : ℂ)) =
      ((g32p_row02_pairingTerms j).map (fun x => (x.1 : ℂ) *
        HurwitzPrymRex_ev (g32p_root 6 ^ (6 / 3)) x.2.1 *
          g32p_root 6 ^ x.2.2)).sum := by
    exact g32p_restriction_bucket_sums g32p_row02_finiteSupplier
      g32p_row02_groupEquiv g32p_row02_characterValues g32p_row02_finiteSupplier_value
      g32p_row02_restrictionBucket g32p_row02_restrictionSizes g32p_row02_restrictionExponents
      g32p_row02_restrictionCounts g32p_row02_restrictionExponent
      τ τbar θ g32p_row02_pairingTerms g32p_row02_restrictionCoefficients
      g32p_row02_restrictionLabels (g32p_restriction_root_omega 6 (by decide)) htrace
      g32p_row02_restrictionDecode g32p_row02_restrictionTerms j
  apply g32p_row02_restriction_of_sums _ τ τbar θ (g32p_complexCharacter g32p_row02_finiteSupplier)
    (g32p_root 6) (g32p_root_primitive g32p_row02_finiteSupplier)
    (by rw [Fintype.card_eq_nat_card]; exact g32p_row02_finiteSupplier_order)
  · intro j
    simpa only [g32p_restrictionTrace, dite_eq_left j.isLt] using hsum ⟨j.val, by omega⟩
  · intro j
    have hn : ¬ 44 + j.val < 44 := by omega
    simpa only [g32p_restrictionTrace, dite_eq_right hn, Nat.add_sub_cancel_left] using
      hsum ⟨44 + j.val, by omega⟩


theorem g32p_row02_restriction_from_family
    (classify : g32p_G → Fin 102)
    (hclass : ∀ i, classify (g32p_row02_groupEquiv i) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket i))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (hτ : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyPair j) (classify g))
    (hbar : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyBar j) (classify g))
    (hθ : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyQuat j) (classify g)) :
    ∃ v ∈ g32VectorTable, v.i = 2 ∧
      papersA τ τbar θ g32p_row02_finiteSupplier.H
        (g32p_complexCharacter g32p_row02_finiteSupplier) = g32SparseVec v.coords := by
  apply g32p_row02_restriction_from_buckets τ τbar θ
  intro j i
  rw [g32p_row02_restrictionFamily, ← hclass]
  exact g32p_restriction_family_trace τ τbar θ _ _
    (fun j => hτ j _) (fun j => hbar j _) (fun j => hθ j _) j


theorem g32p_row02_restriction_supplier_witness
    (hsupplier : ∃ r ∈ g32WitnessTable, r.i = 2 ∧ r.m = g32p_row02_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row02_finiteSupplier.H ∧
      (g32p_exponents g32p_row02_finiteSupplier).Perm (expandExps r.exps))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 3456),
      g32p_restrictionTrace τ τbar θ j (g32p_row02_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row02_restrictionCoefficients j (g32p_row02_restrictionBucket i))) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 2 ∧ r.m = S.m ∧ r.orderH = Nat.card S.H ∧
        (g32p_exponents S).Perm (expandExps r.exps)) ∧
      (∃ v ∈ g32VectorTable, v.i = 2 ∧ papersA τ τbar θ S.H χc = g32SparseVec v.coords) := by
  exact ⟨g32p_row02_finiteSupplier, g32p_complexCharacter g32p_row02_finiteSupplier,
    g32p_complexCharacter_apply _, hsupplier, g32p_row02_restriction_from_buckets τ τbar θ htrace⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_integrationClasses_000 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 0 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 0 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_001 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 1 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 1 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_002 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 2 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 2 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_003 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 3 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 3 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_004 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 4 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 4 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_005 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 5 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 5 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_006 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 6 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 6 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_007 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 7 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 7 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_008 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 8 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 8 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_009 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 9 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 9 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_010 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 10 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 10 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_011 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 11 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 11 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_012 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 12 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 12 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_013 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 13 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 13 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_014 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 14 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 14 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_015 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 15 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 15 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_016 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 16 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 16 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_017 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 17 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 17 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_018 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 18 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 18 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_019 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 19 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 19 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_020 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 20 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 20 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_021 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 21 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 21 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_022 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 22 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 22 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_023 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 23 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 23 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_024 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 24 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 24 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_025 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 25 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 25 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_026 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 26 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 26 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_027 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 27 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 27 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_028 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 28 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 28 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_029 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 29 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 29 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_030 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 30 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 30 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_031 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 31 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 31 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_032 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 32 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 32 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_033 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 33 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 33 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_034 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 34 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 34 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_035 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 35 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 35 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_036 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 36 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 36 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_037 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 37 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 37 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_038 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 38 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 38 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_039 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 39 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 39 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_040 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 40 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 40 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_041 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 41 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 41 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_042 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 42 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 42 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_043 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 43 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 43 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_044 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 44 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 44 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_045 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 45 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 45 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_046 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 46 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 46 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_047 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 47 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 47 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_048 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 48 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 48 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_049 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 49 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 49 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_050 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 50 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 50 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_051 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 51 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 51 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_052 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 52 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 52 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_053 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 53 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 53 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_054 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 54 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 54 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_055 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 55 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 55 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_056 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 56 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 56 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_057 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 57 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 57 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_058 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 58 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 58 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_059 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 59 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 59 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_060 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 60 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 60 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_061 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 61 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 61 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_062 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 62 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 62 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_063 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 63 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 63 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_064 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 64 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 64 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_065 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 65 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 65 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_066 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 66 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 66 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_067 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 67 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 67 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_068 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 68 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 68 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_069 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 69 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 69 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_070 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 70 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 70 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_071 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 71 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 71 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_072 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 72 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 72 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_073 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 73 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 73 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_074 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 74 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 74 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_075 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 75 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 75 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_076 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 76 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 76 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_077 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 77 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 77 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_078 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 78 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 78 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_079 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 79 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 79 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_080 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 80 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 80 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_081 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 81 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 81 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_082 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 82 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 82 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_083 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 83 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 83 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_084 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 84 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 84 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_085 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 85 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 85 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_086 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 86 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 86 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_087 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 87 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 87 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_088 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 88 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 88 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_089 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 89 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 89 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_090 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 90 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 90 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_091 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 91 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 91 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_092 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 92 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 92 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_093 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 93 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 93 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_094 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 94 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 94 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_095 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 95 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 95 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_096 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 96 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 96 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_097 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 97 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 97 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_098 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 98 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 98 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_099 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 99 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 99 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_100 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 100 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 100 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_101 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 101 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 101 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_102 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 102 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 102 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_103 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 103 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 103 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_104 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 104 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 104 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_105 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 105 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 105 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_106 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 106 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 106 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_107 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 107 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 107 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_108 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 108 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 108 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_109 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 109 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 109 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_110 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 110 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 110 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_111 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 111 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 111 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_112 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 112 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 112 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_113 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 113 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 113 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_114 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 114 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 114 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_115 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 115 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 115 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_116 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 116 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 116 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_117 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 117 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 117 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_118 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 118 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 118 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_119 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 119 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 119 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_120 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 120 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 120 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_121 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 121 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 121 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_122 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 122 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 122 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_123 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 123 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 123 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_124 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 124 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 124 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_125 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 125 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 125 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_126 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 126 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 126 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_127 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 127 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 127 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_128 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 128 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 128 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_129 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 129 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 129 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_130 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 130 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 130 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_131 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 131 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 131 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_132 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 132 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 132 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_133 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 133 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 133 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_134 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 134 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 134 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_135 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 135 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 135 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_136 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 136 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 136 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_137 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 137 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 137 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_138 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 138 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 138 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_139 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 139 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 139 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_140 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 140 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 140 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_141 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 141 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 141 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_142 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 142 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 142 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_143 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 143 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 143 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_144 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 144 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 144 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_145 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 145 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 145 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_146 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 146 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 146 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_147 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 147 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 147 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_148 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 148 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 148 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_149 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 149 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 149 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_150 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 150 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 150 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_151 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 151 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 151 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_152 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 152 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 152 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_153 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 153 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 153 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_154 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 154 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 154 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_155 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 155 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 155 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_156 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 156 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 156 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_157 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 157 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 157 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_158 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 158 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 158 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_159 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 159 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 159 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_160 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 160 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 160 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_161 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 161 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 161 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_162 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 162 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 162 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_163 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 163 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 163 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_164 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 164 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 164 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_165 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 165 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 165 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_166 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 166 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 166 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_167 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 167 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 167 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_168 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 168 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 168 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_169 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 169 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 169 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_170 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 170 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 170 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_171 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 171 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 171 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_172 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 172 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 172 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_173 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 173 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 173 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_174 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 174 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 174 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_175 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 175 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 175 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_176 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 176 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 176 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_177 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 177 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 177 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_178 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 178 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 178 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_179 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 179 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 179 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_180 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 180 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 180 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_181 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 181 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 181 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_182 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 182 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 182 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_183 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 183 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 183 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_184 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 184 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 184 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_185 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 185 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 185 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_186 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 186 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 186 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_187 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 187 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 187 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_188 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 188 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 188 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_189 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 189 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 189 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_190 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 190 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 190 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_191 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 191 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 191 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_192 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 192 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 192 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_193 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 193 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 193 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_194 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 194 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 194 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_195 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 195 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 195 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_196 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 196 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 196 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_197 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 197 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 197 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_198 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 198 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 198 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_199 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 199 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 199 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_200 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 200 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 200 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_201 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 201 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 201 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_202 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 202 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 202 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_203 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 203 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 203 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_204 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 204 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 204 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_205 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 205 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 205 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_206 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 206 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 206 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_207 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 207 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 207 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_208 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 208 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 208 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_209 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 209 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 209 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_210 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 210 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 210 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_211 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 211 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 211 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_212 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 212 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 212 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_213 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 213 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 213 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_214 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 214 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 214 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses_215 : ∀ r : Fin 16,
    g32p_row02_supplierClassifier (g32p_finBlockIndex 3456 215 r) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket (g32p_finBlockIndex 3456 215 r)) := by
  decide +kernel

theorem g32p_row02_integrationClasses (i : Fin 3456) :
    g32p_integrationLabel (g32p_row02_groupEquiv i) =
      g32p_row02_restrictionClasses (g32p_row02_restrictionBucket i) := by
  rw [g32p_integrationLabel_of_isConj (g32p_row02_groupEquiv_isConj i)]
  apply g32p_forall_fin_blocks (fun i => g32p_row02_supplierClassifier i =
    g32p_row02_restrictionClasses (g32p_row02_restrictionBucket i)) ?_ i
  intro q r
  fin_cases q
  · exact g32p_row02_integrationClasses_000 r
  · exact g32p_row02_integrationClasses_001 r
  · exact g32p_row02_integrationClasses_002 r
  · exact g32p_row02_integrationClasses_003 r
  · exact g32p_row02_integrationClasses_004 r
  · exact g32p_row02_integrationClasses_005 r
  · exact g32p_row02_integrationClasses_006 r
  · exact g32p_row02_integrationClasses_007 r
  · exact g32p_row02_integrationClasses_008 r
  · exact g32p_row02_integrationClasses_009 r
  · exact g32p_row02_integrationClasses_010 r
  · exact g32p_row02_integrationClasses_011 r
  · exact g32p_row02_integrationClasses_012 r
  · exact g32p_row02_integrationClasses_013 r
  · exact g32p_row02_integrationClasses_014 r
  · exact g32p_row02_integrationClasses_015 r
  · exact g32p_row02_integrationClasses_016 r
  · exact g32p_row02_integrationClasses_017 r
  · exact g32p_row02_integrationClasses_018 r
  · exact g32p_row02_integrationClasses_019 r
  · exact g32p_row02_integrationClasses_020 r
  · exact g32p_row02_integrationClasses_021 r
  · exact g32p_row02_integrationClasses_022 r
  · exact g32p_row02_integrationClasses_023 r
  · exact g32p_row02_integrationClasses_024 r
  · exact g32p_row02_integrationClasses_025 r
  · exact g32p_row02_integrationClasses_026 r
  · exact g32p_row02_integrationClasses_027 r
  · exact g32p_row02_integrationClasses_028 r
  · exact g32p_row02_integrationClasses_029 r
  · exact g32p_row02_integrationClasses_030 r
  · exact g32p_row02_integrationClasses_031 r
  · exact g32p_row02_integrationClasses_032 r
  · exact g32p_row02_integrationClasses_033 r
  · exact g32p_row02_integrationClasses_034 r
  · exact g32p_row02_integrationClasses_035 r
  · exact g32p_row02_integrationClasses_036 r
  · exact g32p_row02_integrationClasses_037 r
  · exact g32p_row02_integrationClasses_038 r
  · exact g32p_row02_integrationClasses_039 r
  · exact g32p_row02_integrationClasses_040 r
  · exact g32p_row02_integrationClasses_041 r
  · exact g32p_row02_integrationClasses_042 r
  · exact g32p_row02_integrationClasses_043 r
  · exact g32p_row02_integrationClasses_044 r
  · exact g32p_row02_integrationClasses_045 r
  · exact g32p_row02_integrationClasses_046 r
  · exact g32p_row02_integrationClasses_047 r
  · exact g32p_row02_integrationClasses_048 r
  · exact g32p_row02_integrationClasses_049 r
  · exact g32p_row02_integrationClasses_050 r
  · exact g32p_row02_integrationClasses_051 r
  · exact g32p_row02_integrationClasses_052 r
  · exact g32p_row02_integrationClasses_053 r
  · exact g32p_row02_integrationClasses_054 r
  · exact g32p_row02_integrationClasses_055 r
  · exact g32p_row02_integrationClasses_056 r
  · exact g32p_row02_integrationClasses_057 r
  · exact g32p_row02_integrationClasses_058 r
  · exact g32p_row02_integrationClasses_059 r
  · exact g32p_row02_integrationClasses_060 r
  · exact g32p_row02_integrationClasses_061 r
  · exact g32p_row02_integrationClasses_062 r
  · exact g32p_row02_integrationClasses_063 r
  · exact g32p_row02_integrationClasses_064 r
  · exact g32p_row02_integrationClasses_065 r
  · exact g32p_row02_integrationClasses_066 r
  · exact g32p_row02_integrationClasses_067 r
  · exact g32p_row02_integrationClasses_068 r
  · exact g32p_row02_integrationClasses_069 r
  · exact g32p_row02_integrationClasses_070 r
  · exact g32p_row02_integrationClasses_071 r
  · exact g32p_row02_integrationClasses_072 r
  · exact g32p_row02_integrationClasses_073 r
  · exact g32p_row02_integrationClasses_074 r
  · exact g32p_row02_integrationClasses_075 r
  · exact g32p_row02_integrationClasses_076 r
  · exact g32p_row02_integrationClasses_077 r
  · exact g32p_row02_integrationClasses_078 r
  · exact g32p_row02_integrationClasses_079 r
  · exact g32p_row02_integrationClasses_080 r
  · exact g32p_row02_integrationClasses_081 r
  · exact g32p_row02_integrationClasses_082 r
  · exact g32p_row02_integrationClasses_083 r
  · exact g32p_row02_integrationClasses_084 r
  · exact g32p_row02_integrationClasses_085 r
  · exact g32p_row02_integrationClasses_086 r
  · exact g32p_row02_integrationClasses_087 r
  · exact g32p_row02_integrationClasses_088 r
  · exact g32p_row02_integrationClasses_089 r
  · exact g32p_row02_integrationClasses_090 r
  · exact g32p_row02_integrationClasses_091 r
  · exact g32p_row02_integrationClasses_092 r
  · exact g32p_row02_integrationClasses_093 r
  · exact g32p_row02_integrationClasses_094 r
  · exact g32p_row02_integrationClasses_095 r
  · exact g32p_row02_integrationClasses_096 r
  · exact g32p_row02_integrationClasses_097 r
  · exact g32p_row02_integrationClasses_098 r
  · exact g32p_row02_integrationClasses_099 r
  · exact g32p_row02_integrationClasses_100 r
  · exact g32p_row02_integrationClasses_101 r
  · exact g32p_row02_integrationClasses_102 r
  · exact g32p_row02_integrationClasses_103 r
  · exact g32p_row02_integrationClasses_104 r
  · exact g32p_row02_integrationClasses_105 r
  · exact g32p_row02_integrationClasses_106 r
  · exact g32p_row02_integrationClasses_107 r
  · exact g32p_row02_integrationClasses_108 r
  · exact g32p_row02_integrationClasses_109 r
  · exact g32p_row02_integrationClasses_110 r
  · exact g32p_row02_integrationClasses_111 r
  · exact g32p_row02_integrationClasses_112 r
  · exact g32p_row02_integrationClasses_113 r
  · exact g32p_row02_integrationClasses_114 r
  · exact g32p_row02_integrationClasses_115 r
  · exact g32p_row02_integrationClasses_116 r
  · exact g32p_row02_integrationClasses_117 r
  · exact g32p_row02_integrationClasses_118 r
  · exact g32p_row02_integrationClasses_119 r
  · exact g32p_row02_integrationClasses_120 r
  · exact g32p_row02_integrationClasses_121 r
  · exact g32p_row02_integrationClasses_122 r
  · exact g32p_row02_integrationClasses_123 r
  · exact g32p_row02_integrationClasses_124 r
  · exact g32p_row02_integrationClasses_125 r
  · exact g32p_row02_integrationClasses_126 r
  · exact g32p_row02_integrationClasses_127 r
  · exact g32p_row02_integrationClasses_128 r
  · exact g32p_row02_integrationClasses_129 r
  · exact g32p_row02_integrationClasses_130 r
  · exact g32p_row02_integrationClasses_131 r
  · exact g32p_row02_integrationClasses_132 r
  · exact g32p_row02_integrationClasses_133 r
  · exact g32p_row02_integrationClasses_134 r
  · exact g32p_row02_integrationClasses_135 r
  · exact g32p_row02_integrationClasses_136 r
  · exact g32p_row02_integrationClasses_137 r
  · exact g32p_row02_integrationClasses_138 r
  · exact g32p_row02_integrationClasses_139 r
  · exact g32p_row02_integrationClasses_140 r
  · exact g32p_row02_integrationClasses_141 r
  · exact g32p_row02_integrationClasses_142 r
  · exact g32p_row02_integrationClasses_143 r
  · exact g32p_row02_integrationClasses_144 r
  · exact g32p_row02_integrationClasses_145 r
  · exact g32p_row02_integrationClasses_146 r
  · exact g32p_row02_integrationClasses_147 r
  · exact g32p_row02_integrationClasses_148 r
  · exact g32p_row02_integrationClasses_149 r
  · exact g32p_row02_integrationClasses_150 r
  · exact g32p_row02_integrationClasses_151 r
  · exact g32p_row02_integrationClasses_152 r
  · exact g32p_row02_integrationClasses_153 r
  · exact g32p_row02_integrationClasses_154 r
  · exact g32p_row02_integrationClasses_155 r
  · exact g32p_row02_integrationClasses_156 r
  · exact g32p_row02_integrationClasses_157 r
  · exact g32p_row02_integrationClasses_158 r
  · exact g32p_row02_integrationClasses_159 r
  · exact g32p_row02_integrationClasses_160 r
  · exact g32p_row02_integrationClasses_161 r
  · exact g32p_row02_integrationClasses_162 r
  · exact g32p_row02_integrationClasses_163 r
  · exact g32p_row02_integrationClasses_164 r
  · exact g32p_row02_integrationClasses_165 r
  · exact g32p_row02_integrationClasses_166 r
  · exact g32p_row02_integrationClasses_167 r
  · exact g32p_row02_integrationClasses_168 r
  · exact g32p_row02_integrationClasses_169 r
  · exact g32p_row02_integrationClasses_170 r
  · exact g32p_row02_integrationClasses_171 r
  · exact g32p_row02_integrationClasses_172 r
  · exact g32p_row02_integrationClasses_173 r
  · exact g32p_row02_integrationClasses_174 r
  · exact g32p_row02_integrationClasses_175 r
  · exact g32p_row02_integrationClasses_176 r
  · exact g32p_row02_integrationClasses_177 r
  · exact g32p_row02_integrationClasses_178 r
  · exact g32p_row02_integrationClasses_179 r
  · exact g32p_row02_integrationClasses_180 r
  · exact g32p_row02_integrationClasses_181 r
  · exact g32p_row02_integrationClasses_182 r
  · exact g32p_row02_integrationClasses_183 r
  · exact g32p_row02_integrationClasses_184 r
  · exact g32p_row02_integrationClasses_185 r
  · exact g32p_row02_integrationClasses_186 r
  · exact g32p_row02_integrationClasses_187 r
  · exact g32p_row02_integrationClasses_188 r
  · exact g32p_row02_integrationClasses_189 r
  · exact g32p_row02_integrationClasses_190 r
  · exact g32p_row02_integrationClasses_191 r
  · exact g32p_row02_integrationClasses_192 r
  · exact g32p_row02_integrationClasses_193 r
  · exact g32p_row02_integrationClasses_194 r
  · exact g32p_row02_integrationClasses_195 r
  · exact g32p_row02_integrationClasses_196 r
  · exact g32p_row02_integrationClasses_197 r
  · exact g32p_row02_integrationClasses_198 r
  · exact g32p_row02_integrationClasses_199 r
  · exact g32p_row02_integrationClasses_200 r
  · exact g32p_row02_integrationClasses_201 r
  · exact g32p_row02_integrationClasses_202 r
  · exact g32p_row02_integrationClasses_203 r
  · exact g32p_row02_integrationClasses_204 r
  · exact g32p_row02_integrationClasses_205 r
  · exact g32p_row02_integrationClasses_206 r
  · exact g32p_row02_integrationClasses_207 r
  · exact g32p_row02_integrationClasses_208 r
  · exact g32p_row02_integrationClasses_209 r
  · exact g32p_row02_integrationClasses_210 r
  · exact g32p_row02_integrationClasses_211 r
  · exact g32p_row02_integrationClasses_212 r
  · exact g32p_row02_integrationClasses_213 r
  · exact g32p_row02_integrationClasses_214 r
  · exact g32p_row02_integrationClasses_215 r

theorem g32p_row02_integrationRestriction
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (g32p_integrationLabel g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (g32p_integrationLabel g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (g32p_integrationLabel g)) :
    ∃ v ∈ g32VectorTable, v.i = 2 ∧
      papersA τ τbar θ (g32p_recordedSuppliers 1).H
        (g32p_recordedSupplierCharacters 1) = g32SparseVec v.coords := by
  exact g32p_row02_restriction_from_family g32p_integrationLabel g32p_row02_integrationClasses
    τ τbar θ ht hb hq

#print axioms g32p_row02_integrationRestriction

theorem g32p_row02_integrationNode (j : Fin 48) (i : Fin 3456) :
    g32p_comparisonAssemblyValue (g32p_integrationLabel (g32p_row02_groupEquiv i)) j =
      HurwitzPrymRex_ev g32h_omega
        (g32p_row02_restrictionCoefficients j (g32p_row02_restrictionBucket i)) := by
  rw [g32p_row02_integrationClasses, g32p_row02_restrictionFamily]
  exact g32p_integration_value_coefficient _ _

end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row03_pairingTerms : Fin 48 → List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  ![g32p_row03_terms_0, g32p_row03_terms_1, g32p_row03_terms_2, g32p_row03_terms_3, g32p_row03_terms_4, g32p_row03_terms_5, g32p_row03_terms_6, g32p_row03_terms_7, g32p_row03_terms_8, g32p_row03_terms_9, g32p_row03_terms_10, g32p_row03_terms_11, g32p_row03_terms_12, g32p_row03_terms_13, g32p_row03_terms_14, g32p_row03_terms_15, g32p_row03_terms_16, g32p_row03_terms_17, g32p_row03_terms_18, g32p_row03_terms_19, g32p_row03_terms_20, g32p_row03_terms_21, g32p_row03_terms_22, g32p_row03_terms_23, g32p_row03_terms_24, g32p_row03_terms_25, g32p_row03_terms_26, g32p_row03_terms_27, g32p_row03_terms_28, g32p_row03_terms_29, g32p_row03_terms_30, g32p_row03_terms_31, g32p_row03_terms_32, g32p_row03_terms_33, g32p_row03_terms_34, g32p_row03_terms_35, g32p_row03_terms_36, g32p_row03_terms_37, g32p_row03_terms_38, g32p_row03_terms_39, g32p_row03_terms_40, g32p_row03_terms_41, g32p_row03_terms_42, g32p_row03_terms_43, g32p_row03_terms_44, g32p_row03_terms_45, g32p_row03_terms_46, g32p_row03_terms_47]

def g32p_row03_pairingQuotients : Fin 48 → List ℤ :=
  ![[0, 720, 0, 720, 0, -1440], [], [], [], [], [], [], [-4320, -5040, -1440, 2160, 2880, 1440], [], [], [], [0, 720, 0, 720, 0, -1440], [], [], [], [], [], [], [], [], [0, 720, 0, 720, 0, -1440], [], [], [], [], [-4320, -5040, -1440, 2160, 2880, 1440], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def g32p_row03_freeCoordinates : Fin 44 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def g32p_row03_quaternionicMultiplicities : Fin 4 → ℤ :=
  ![0, 0, 0, 0]

theorem g32p_row03_pairingFree (j : Fin 44) :
    g32p_cyclotomicPairingCheck 4320 (g32p_row03_freeCoordinates j)
      (g32p_pairingCoefficients 6 (g32p_row03_pairingTerms ⟨j.val, by omega⟩))
      [1, -1, 1] (g32p_row03_pairingQuotients ⟨j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row03_pairing_0
  · exact g32p_row03_pairing_1
  · exact g32p_row03_pairing_2
  · exact g32p_row03_pairing_3
  · exact g32p_row03_pairing_4
  · exact g32p_row03_pairing_5
  · exact g32p_row03_pairing_6
  · exact g32p_row03_pairing_7
  · exact g32p_row03_pairing_8
  · exact g32p_row03_pairing_9
  · exact g32p_row03_pairing_10
  · exact g32p_row03_pairing_11
  · exact g32p_row03_pairing_12
  · exact g32p_row03_pairing_13
  · exact g32p_row03_pairing_14
  · exact g32p_row03_pairing_15
  · exact g32p_row03_pairing_16
  · exact g32p_row03_pairing_17
  · exact g32p_row03_pairing_18
  · exact g32p_row03_pairing_19
  · exact g32p_row03_pairing_20
  · exact g32p_row03_pairing_21
  · exact g32p_row03_pairing_22
  · exact g32p_row03_pairing_23
  · exact g32p_row03_pairing_24
  · exact g32p_row03_pairing_25
  · exact g32p_row03_pairing_26
  · exact g32p_row03_pairing_27
  · exact g32p_row03_pairing_28
  · exact g32p_row03_pairing_29
  · exact g32p_row03_pairing_30
  · exact g32p_row03_pairing_31
  · exact g32p_row03_pairing_32
  · exact g32p_row03_pairing_33
  · exact g32p_row03_pairing_34
  · exact g32p_row03_pairing_35
  · exact g32p_row03_pairing_36
  · exact g32p_row03_pairing_37
  · exact g32p_row03_pairing_38
  · exact g32p_row03_pairing_39
  · exact g32p_row03_pairing_40
  · exact g32p_row03_pairing_41
  · exact g32p_row03_pairing_42
  · exact g32p_row03_pairing_43

theorem g32p_row03_pairingQuat (j : Fin 4) :
    g32p_cyclotomicPairingCheck 4320 (g32p_row03_quaternionicMultiplicities j)
      (g32p_pairingCoefficients 6 (g32p_row03_pairingTerms ⟨44 + j.val, by omega⟩))
      [1, -1, 1] (g32p_row03_pairingQuotients ⟨44 + j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row03_pairing_44
  · exact g32p_row03_pairing_45
  · exact g32p_row03_pairing_46
  · exact g32p_row03_pairing_47

theorem g32p_row03_restriction_of_sums {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H]
    (τ τbar : Fin 44 → FDRep ℂ G) (θ : Fin 4 → FDRep ℂ G) (χ : H →* ℂˣ)
    (z : ℂ) (hz : IsPrimitiveRoot z 6) (horder : Fintype.card H = 4320)
    (hfree : ∀ j : Fin 44,
      (∑ h : H, ((τ j).character h - (τbar j).character h) * (χ h⁻¹ : ℂ)) =
        ((g32p_row03_pairingTerms ⟨j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (6 / 3)) x.2.1 * z ^ x.2.2)).sum)
    (hquat : ∀ j : Fin 4,
      (∑ h : H, (θ j).character h * (χ h⁻¹ : ℂ)) =
        ((g32p_row03_pairingTerms ⟨44 + j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (6 / 3)) x.2.1 * z ^ x.2.2)).sum) :
    ∃ v ∈ g32VectorTable,
      v.i = 3 ∧ papersA τ τbar θ H χ = g32SparseVec v.coords := by
  obtain ⟨v, hv, hi, hc⟩ := g32p_row03_coordinates
  refine ⟨v, hv, hi, ?_⟩
  rw [hc]
  refine (g32p_polynomialPairing_row H τ τbar θ χ 6
    g32p_row03_freeCoordinates g32p_row03_quaternionicMultiplicities
    g32p_row03_pairingTerms [1, -1, 1] g32p_row03_pairingQuotients z
    (g32p_pairing_modulus_six hz) hfree hquat
    (by rw [horder]; exact g32p_row03_pairingFree)
    (by rw [horder]; exact g32p_row03_pairingQuat)).trans ?_
  apply Prod.ext
  · rfl
  · funext j
    fin_cases j <;> rfl

end HodgeLean.Foundations.Program

end
