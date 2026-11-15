import HodgeLean.Foundations.Program.G32PropFourSixPacked0507
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0508
import HodgeLean.Foundations.Program.G32PropFourSixPacked0509
import HodgeLean.Foundations.Program.G32PropFourSixPacked0510
import HodgeLean.Foundations.Program.G32PropFourSixPacked0457
import HodgeLean.Foundations.Program.G32PropFourSixPacked0451
import HodgeLean.Foundations.Program.G32PropFourSixPacked0367
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixRowComparison
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0004

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row17_restrictionCount_70 :
    (Finset.univ.filter (fun i => g32p_row17_restrictionBucket i = 70)).card = g32p_row17_restrictionSizes 70 := by
  decide +kernel

theorem g32p_row17_restrictionCount_71 :
    (Finset.univ.filter (fun i => g32p_row17_restrictionBucket i = 71)).card = g32p_row17_restrictionSizes 71 := by
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

theorem g32p_row17_restrictionExponent_0 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 0 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 0 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_1 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 1 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 1 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_2 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 2 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 2 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_3 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 3 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 3 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_4 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 4 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 4 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_5 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 5 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 5 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_6 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 6 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 6 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_7 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 7 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 7 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_8 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 8 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 8 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_9 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 9 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 9 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_10 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 10 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 10 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_11 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 11 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 11 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_12 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 12 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 12 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_13 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 13 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 13 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_14 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 14 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 14 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_15 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 15 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 15 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_16 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 16 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 16 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_17 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 17 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 17 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_18 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 18 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 18 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_19 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 19 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 19 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_20 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 20 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 20 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_21 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 21 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 21 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_22 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 22 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 22 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_23 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 23 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 23 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_24 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 24 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 24 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_25 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 25 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 25 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_26 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 26 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 26 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_27 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 27 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 27 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_28 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 28 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 28 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_29 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 29 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 29 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_30 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 30 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 30 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_31 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 31 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 31 r)) := by
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

theorem g32p_row17_restrictionExponent_32 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 32 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 32 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_33 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 33 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 33 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_34 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 34 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 34 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_35 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 35 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 35 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_36 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 36 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 36 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_37 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 37 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 37 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_38 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 38 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 38 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_39 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 39 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 39 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_40 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 40 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 40 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_41 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 41 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 41 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_42 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 42 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 42 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_43 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 43 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 43 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_44 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 44 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 44 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_45 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 45 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 45 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_46 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 46 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 46 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_47 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 47 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 47 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_48 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 48 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 48 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_49 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 49 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 49 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_50 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 50 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 50 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_51 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 51 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 51 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_52 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 52 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 52 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_53 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 53 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 53 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_54 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 54 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 54 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_55 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 55 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 55 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_56 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 56 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 56 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_57 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 57 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 57 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_58 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 58 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 58 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_59 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 59 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 59 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_60 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 60 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 60 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_61 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 61 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 61 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_62 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 62 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 62 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_63 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 63 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 63 r)) := by
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

theorem g32p_row17_restrictionExponent_64 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 64 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 64 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_65 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 65 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 65 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_66 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 66 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 66 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_67 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 67 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 67 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_68 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 68 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 68 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_69 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 69 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 69 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_70 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 70 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 70 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_71 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 71 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 71 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_72 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 72 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 72 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_73 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 73 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 73 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_74 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 74 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 74 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_75 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 75 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 75 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_76 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 76 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 76 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_77 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 77 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 77 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_78 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 78 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 78 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_79 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 79 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 79 r)) := by
  decide +kernel

theorem g32p_row17_restrictionExponent_80 : ∀ r : Fin 16,
    (Multiplicative.toAdd (g32p_row17_characterValues (g32p_finBlockIndex 1296 80 r))⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 80 r)) := by
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

theorem g32p_row17_restrictionCounts (a : Fin 72) :
    (Finset.univ.filter (fun i => g32p_row17_restrictionBucket i = a)).card = g32p_row17_restrictionSizes a := by
  fin_cases a
  · exact g32p_row17_restrictionCount_0
  · exact g32p_row17_restrictionCount_1
  · exact g32p_row17_restrictionCount_2
  · exact g32p_row17_restrictionCount_3
  · exact g32p_row17_restrictionCount_4
  · exact g32p_row17_restrictionCount_5
  · exact g32p_row17_restrictionCount_6
  · exact g32p_row17_restrictionCount_7
  · exact g32p_row17_restrictionCount_8
  · exact g32p_row17_restrictionCount_9
  · exact g32p_row17_restrictionCount_10
  · exact g32p_row17_restrictionCount_11
  · exact g32p_row17_restrictionCount_12
  · exact g32p_row17_restrictionCount_13
  · exact g32p_row17_restrictionCount_14
  · exact g32p_row17_restrictionCount_15
  · exact g32p_row17_restrictionCount_16
  · exact g32p_row17_restrictionCount_17
  · exact g32p_row17_restrictionCount_18
  · exact g32p_row17_restrictionCount_19
  · exact g32p_row17_restrictionCount_20
  · exact g32p_row17_restrictionCount_21
  · exact g32p_row17_restrictionCount_22
  · exact g32p_row17_restrictionCount_23
  · exact g32p_row17_restrictionCount_24
  · exact g32p_row17_restrictionCount_25
  · exact g32p_row17_restrictionCount_26
  · exact g32p_row17_restrictionCount_27
  · exact g32p_row17_restrictionCount_28
  · exact g32p_row17_restrictionCount_29
  · exact g32p_row17_restrictionCount_30
  · exact g32p_row17_restrictionCount_31
  · exact g32p_row17_restrictionCount_32
  · exact g32p_row17_restrictionCount_33
  · exact g32p_row17_restrictionCount_34
  · exact g32p_row17_restrictionCount_35
  · exact g32p_row17_restrictionCount_36
  · exact g32p_row17_restrictionCount_37
  · exact g32p_row17_restrictionCount_38
  · exact g32p_row17_restrictionCount_39
  · exact g32p_row17_restrictionCount_40
  · exact g32p_row17_restrictionCount_41
  · exact g32p_row17_restrictionCount_42
  · exact g32p_row17_restrictionCount_43
  · exact g32p_row17_restrictionCount_44
  · exact g32p_row17_restrictionCount_45
  · exact g32p_row17_restrictionCount_46
  · exact g32p_row17_restrictionCount_47
  · exact g32p_row17_restrictionCount_48
  · exact g32p_row17_restrictionCount_49
  · exact g32p_row17_restrictionCount_50
  · exact g32p_row17_restrictionCount_51
  · exact g32p_row17_restrictionCount_52
  · exact g32p_row17_restrictionCount_53
  · exact g32p_row17_restrictionCount_54
  · exact g32p_row17_restrictionCount_55
  · exact g32p_row17_restrictionCount_56
  · exact g32p_row17_restrictionCount_57
  · exact g32p_row17_restrictionCount_58
  · exact g32p_row17_restrictionCount_59
  · exact g32p_row17_restrictionCount_60
  · exact g32p_row17_restrictionCount_61
  · exact g32p_row17_restrictionCount_62
  · exact g32p_row17_restrictionCount_63
  · exact g32p_row17_restrictionCount_64
  · exact g32p_row17_restrictionCount_65
  · exact g32p_row17_restrictionCount_66
  · exact g32p_row17_restrictionCount_67
  · exact g32p_row17_restrictionCount_68
  · exact g32p_row17_restrictionCount_69
  · exact g32p_row17_restrictionCount_70
  · exact g32p_row17_restrictionCount_71

theorem g32p_row17_restrictionExponent (i : Fin 1296) :
    (Multiplicative.toAdd (g32p_row17_characterValues i)⁻¹).val =
      g32p_row17_restrictionExponents (g32p_row17_restrictionBucket i) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row17_restrictionExponent_0
  · exact g32p_row17_restrictionExponent_1
  · exact g32p_row17_restrictionExponent_2
  · exact g32p_row17_restrictionExponent_3
  · exact g32p_row17_restrictionExponent_4
  · exact g32p_row17_restrictionExponent_5
  · exact g32p_row17_restrictionExponent_6
  · exact g32p_row17_restrictionExponent_7
  · exact g32p_row17_restrictionExponent_8
  · exact g32p_row17_restrictionExponent_9
  · exact g32p_row17_restrictionExponent_10
  · exact g32p_row17_restrictionExponent_11
  · exact g32p_row17_restrictionExponent_12
  · exact g32p_row17_restrictionExponent_13
  · exact g32p_row17_restrictionExponent_14
  · exact g32p_row17_restrictionExponent_15
  · exact g32p_row17_restrictionExponent_16
  · exact g32p_row17_restrictionExponent_17
  · exact g32p_row17_restrictionExponent_18
  · exact g32p_row17_restrictionExponent_19
  · exact g32p_row17_restrictionExponent_20
  · exact g32p_row17_restrictionExponent_21
  · exact g32p_row17_restrictionExponent_22
  · exact g32p_row17_restrictionExponent_23
  · exact g32p_row17_restrictionExponent_24
  · exact g32p_row17_restrictionExponent_25
  · exact g32p_row17_restrictionExponent_26
  · exact g32p_row17_restrictionExponent_27
  · exact g32p_row17_restrictionExponent_28
  · exact g32p_row17_restrictionExponent_29
  · exact g32p_row17_restrictionExponent_30
  · exact g32p_row17_restrictionExponent_31
  · exact g32p_row17_restrictionExponent_32
  · exact g32p_row17_restrictionExponent_33
  · exact g32p_row17_restrictionExponent_34
  · exact g32p_row17_restrictionExponent_35
  · exact g32p_row17_restrictionExponent_36
  · exact g32p_row17_restrictionExponent_37
  · exact g32p_row17_restrictionExponent_38
  · exact g32p_row17_restrictionExponent_39
  · exact g32p_row17_restrictionExponent_40
  · exact g32p_row17_restrictionExponent_41
  · exact g32p_row17_restrictionExponent_42
  · exact g32p_row17_restrictionExponent_43
  · exact g32p_row17_restrictionExponent_44
  · exact g32p_row17_restrictionExponent_45
  · exact g32p_row17_restrictionExponent_46
  · exact g32p_row17_restrictionExponent_47
  · exact g32p_row17_restrictionExponent_48
  · exact g32p_row17_restrictionExponent_49
  · exact g32p_row17_restrictionExponent_50
  · exact g32p_row17_restrictionExponent_51
  · exact g32p_row17_restrictionExponent_52
  · exact g32p_row17_restrictionExponent_53
  · exact g32p_row17_restrictionExponent_54
  · exact g32p_row17_restrictionExponent_55
  · exact g32p_row17_restrictionExponent_56
  · exact g32p_row17_restrictionExponent_57
  · exact g32p_row17_restrictionExponent_58
  · exact g32p_row17_restrictionExponent_59
  · exact g32p_row17_restrictionExponent_60
  · exact g32p_row17_restrictionExponent_61
  · exact g32p_row17_restrictionExponent_62
  · exact g32p_row17_restrictionExponent_63
  · exact g32p_row17_restrictionExponent_64
  · exact g32p_row17_restrictionExponent_65
  · exact g32p_row17_restrictionExponent_66
  · exact g32p_row17_restrictionExponent_67
  · exact g32p_row17_restrictionExponent_68
  · exact g32p_row17_restrictionExponent_69
  · exact g32p_row17_restrictionExponent_70
  · exact g32p_row17_restrictionExponent_71
  · exact g32p_row17_restrictionExponent_72
  · exact g32p_row17_restrictionExponent_73
  · exact g32p_row17_restrictionExponent_74
  · exact g32p_row17_restrictionExponent_75
  · exact g32p_row17_restrictionExponent_76
  · exact g32p_row17_restrictionExponent_77
  · exact g32p_row17_restrictionExponent_78
  · exact g32p_row17_restrictionExponent_79
  · exact g32p_row17_restrictionExponent_80

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row17_restriction_from_buckets
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 1296),
      g32p_restrictionTrace τ τbar θ j (g32p_row17_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row17_restrictionCoefficients j (g32p_row17_restrictionBucket i))) :
    ∃ v ∈ g32VectorTable, v.i = 17 ∧
      papersA τ τbar θ g32p_row17_finiteSupplier.H (g32p_complexCharacter g32p_row17_finiteSupplier) =
        g32SparseVec v.coords := by
  classical
  let H := g32p_row17_finiteSupplier.H
  letI : Fintype H := Fintype.ofFinite H
  have hsum (j : Fin 48) :
      (∑ h : H, g32p_restrictionTrace τ τbar θ j h *
        ((g32p_complexCharacter g32p_row17_finiteSupplier) h⁻¹ : ℂ)) =
      ((g32p_row17_pairingTerms j).map (fun x => (x.1 : ℂ) *
        HurwitzPrymRex_ev (g32p_root 6 ^ (6 / 3)) x.2.1 *
          g32p_root 6 ^ x.2.2)).sum := by
    exact g32p_restriction_bucket_sums g32p_row17_finiteSupplier
      g32p_row17_groupEquiv g32p_row17_characterValues g32p_row17_finiteSupplier_value
      g32p_row17_restrictionBucket g32p_row17_restrictionSizes g32p_row17_restrictionExponents
      g32p_row17_restrictionCounts g32p_row17_restrictionExponent
      τ τbar θ g32p_row17_pairingTerms g32p_row17_restrictionCoefficients
      g32p_row17_restrictionLabels (g32p_restriction_root_omega 6 (by decide)) htrace
      g32p_row17_restrictionDecode g32p_row17_restrictionTerms j
  apply g32p_row17_restriction_of_sums _ τ τbar θ (g32p_complexCharacter g32p_row17_finiteSupplier)
    (g32p_root 6) (g32p_root_primitive g32p_row17_finiteSupplier)
    (by rw [Fintype.card_eq_nat_card]; exact g32p_row17_finiteSupplier_order)
  · intro j
    simpa only [g32p_restrictionTrace, dite_eq_left j.isLt] using hsum ⟨j.val, by omega⟩
  · intro j
    have hn : ¬ 44 + j.val < 44 := by omega
    simpa only [g32p_restrictionTrace, dite_eq_right hn, Nat.add_sub_cancel_left] using
      hsum ⟨44 + j.val, by omega⟩


theorem g32p_row17_restriction_from_family
    (classify : g32p_G → Fin 102)
    (hclass : ∀ i, classify (g32p_row17_groupEquiv i) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket i))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (hτ : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyPair j) (classify g))
    (hbar : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyBar j) (classify g))
    (hθ : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_restrictionFamilyQuat j) (classify g)) :
    ∃ v ∈ g32VectorTable, v.i = 17 ∧
      papersA τ τbar θ g32p_row17_finiteSupplier.H
        (g32p_complexCharacter g32p_row17_finiteSupplier) = g32SparseVec v.coords := by
  apply g32p_row17_restriction_from_buckets τ τbar θ
  intro j i
  rw [g32p_row17_restrictionFamily, ← hclass]
  exact g32p_restriction_family_trace τ τbar θ _ _
    (fun j => hτ j _) (fun j => hbar j _) (fun j => hθ j _) j


theorem g32p_row17_restriction_supplier_witness
    (hsupplier : ∃ r ∈ g32WitnessTable, r.i = 17 ∧ r.m = g32p_row17_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row17_finiteSupplier.H ∧
      (g32p_exponents g32p_row17_finiteSupplier).Perm (expandExps r.exps))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (htrace : ∀ (j : Fin 48) (i : Fin 1296),
      g32p_restrictionTrace τ τbar θ j (g32p_row17_groupEquiv i) =
        HurwitzPrymRex_ev g32h_omega (g32p_row17_restrictionCoefficients j (g32p_row17_restrictionBucket i))) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 17 ∧ r.m = S.m ∧ r.orderH = Nat.card S.H ∧
        (g32p_exponents S).Perm (expandExps r.exps)) ∧
      (∃ v ∈ g32VectorTable, v.i = 17 ∧ papersA τ τbar θ S.H χc = g32SparseVec v.coords) := by
  exact ⟨g32p_row17_finiteSupplier, g32p_complexCharacter g32p_row17_finiteSupplier,
    g32p_complexCharacter_apply _, hsupplier, g32p_row17_restriction_from_buckets τ τbar θ htrace⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row17_integrationClasses_000 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 0 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 0 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_001 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 1 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 1 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_002 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 2 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 2 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_003 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 3 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 3 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_004 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 4 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 4 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_005 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 5 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 5 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_006 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 6 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 6 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_007 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 7 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 7 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_008 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 8 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 8 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_009 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 9 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 9 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_010 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 10 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 10 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_011 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 11 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 11 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_012 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 12 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 12 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_013 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 13 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 13 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_014 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 14 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 14 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_015 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 15 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 15 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_016 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 16 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 16 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_017 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 17 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 17 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_018 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 18 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 18 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_019 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 19 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 19 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_020 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 20 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 20 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_021 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 21 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 21 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_022 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 22 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 22 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_023 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 23 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 23 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_024 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 24 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 24 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_025 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 25 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 25 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_026 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 26 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 26 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_027 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 27 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 27 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_028 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 28 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 28 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_029 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 29 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 29 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_030 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 30 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 30 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_031 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 31 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 31 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_032 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 32 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 32 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_033 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 33 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 33 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_034 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 34 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 34 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_035 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 35 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 35 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_036 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 36 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 36 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_037 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 37 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 37 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_038 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 38 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 38 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_039 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 39 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 39 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_040 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 40 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 40 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_041 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 41 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 41 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_042 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 42 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 42 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_043 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 43 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 43 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_044 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 44 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 44 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_045 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 45 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 45 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_046 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 46 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 46 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_047 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 47 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 47 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_048 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 48 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 48 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_049 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 49 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 49 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_050 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 50 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 50 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_051 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 51 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 51 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_052 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 52 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 52 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_053 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 53 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 53 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_054 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 54 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 54 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_055 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 55 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 55 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_056 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 56 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 56 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_057 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 57 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 57 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_058 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 58 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 58 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_059 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 59 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 59 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_060 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 60 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 60 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_061 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 61 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 61 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_062 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 62 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 62 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_063 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 63 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 63 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_064 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 64 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 64 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_065 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 65 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 65 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_066 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 66 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 66 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_067 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 67 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 67 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_068 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 68 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 68 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_069 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 69 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 69 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_070 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 70 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 70 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_071 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 71 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 71 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_072 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 72 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 72 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_073 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 73 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 73 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_074 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 74 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 74 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_075 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 75 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 75 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_076 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 76 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 76 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_077 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 77 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 77 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_078 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 78 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 78 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_079 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 79 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 79 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses_080 : ∀ r : Fin 16,
    g32p_row17_supplierClassifier (g32p_finBlockIndex 1296 80 r) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket (g32p_finBlockIndex 1296 80 r)) := by
  decide +kernel

theorem g32p_row17_integrationClasses (i : Fin 1296) :
    g32p_integrationLabel (g32p_row17_groupEquiv i) =
      g32p_row17_restrictionClasses (g32p_row17_restrictionBucket i) := by
  rw [g32p_integrationLabel_of_isConj (g32p_row17_groupEquiv_isConj i)]
  apply g32p_forall_fin_blocks (fun i => g32p_row17_supplierClassifier i =
    g32p_row17_restrictionClasses (g32p_row17_restrictionBucket i)) ?_ i
  intro q r
  fin_cases q
  · exact g32p_row17_integrationClasses_000 r
  · exact g32p_row17_integrationClasses_001 r
  · exact g32p_row17_integrationClasses_002 r
  · exact g32p_row17_integrationClasses_003 r
  · exact g32p_row17_integrationClasses_004 r
  · exact g32p_row17_integrationClasses_005 r
  · exact g32p_row17_integrationClasses_006 r
  · exact g32p_row17_integrationClasses_007 r
  · exact g32p_row17_integrationClasses_008 r
  · exact g32p_row17_integrationClasses_009 r
  · exact g32p_row17_integrationClasses_010 r
  · exact g32p_row17_integrationClasses_011 r
  · exact g32p_row17_integrationClasses_012 r
  · exact g32p_row17_integrationClasses_013 r
  · exact g32p_row17_integrationClasses_014 r
  · exact g32p_row17_integrationClasses_015 r
  · exact g32p_row17_integrationClasses_016 r
  · exact g32p_row17_integrationClasses_017 r
  · exact g32p_row17_integrationClasses_018 r
  · exact g32p_row17_integrationClasses_019 r
  · exact g32p_row17_integrationClasses_020 r
  · exact g32p_row17_integrationClasses_021 r
  · exact g32p_row17_integrationClasses_022 r
  · exact g32p_row17_integrationClasses_023 r
  · exact g32p_row17_integrationClasses_024 r
  · exact g32p_row17_integrationClasses_025 r
  · exact g32p_row17_integrationClasses_026 r
  · exact g32p_row17_integrationClasses_027 r
  · exact g32p_row17_integrationClasses_028 r
  · exact g32p_row17_integrationClasses_029 r
  · exact g32p_row17_integrationClasses_030 r
  · exact g32p_row17_integrationClasses_031 r
  · exact g32p_row17_integrationClasses_032 r
  · exact g32p_row17_integrationClasses_033 r
  · exact g32p_row17_integrationClasses_034 r
  · exact g32p_row17_integrationClasses_035 r
  · exact g32p_row17_integrationClasses_036 r
  · exact g32p_row17_integrationClasses_037 r
  · exact g32p_row17_integrationClasses_038 r
  · exact g32p_row17_integrationClasses_039 r
  · exact g32p_row17_integrationClasses_040 r
  · exact g32p_row17_integrationClasses_041 r
  · exact g32p_row17_integrationClasses_042 r
  · exact g32p_row17_integrationClasses_043 r
  · exact g32p_row17_integrationClasses_044 r
  · exact g32p_row17_integrationClasses_045 r
  · exact g32p_row17_integrationClasses_046 r
  · exact g32p_row17_integrationClasses_047 r
  · exact g32p_row17_integrationClasses_048 r
  · exact g32p_row17_integrationClasses_049 r
  · exact g32p_row17_integrationClasses_050 r
  · exact g32p_row17_integrationClasses_051 r
  · exact g32p_row17_integrationClasses_052 r
  · exact g32p_row17_integrationClasses_053 r
  · exact g32p_row17_integrationClasses_054 r
  · exact g32p_row17_integrationClasses_055 r
  · exact g32p_row17_integrationClasses_056 r
  · exact g32p_row17_integrationClasses_057 r
  · exact g32p_row17_integrationClasses_058 r
  · exact g32p_row17_integrationClasses_059 r
  · exact g32p_row17_integrationClasses_060 r
  · exact g32p_row17_integrationClasses_061 r
  · exact g32p_row17_integrationClasses_062 r
  · exact g32p_row17_integrationClasses_063 r
  · exact g32p_row17_integrationClasses_064 r
  · exact g32p_row17_integrationClasses_065 r
  · exact g32p_row17_integrationClasses_066 r
  · exact g32p_row17_integrationClasses_067 r
  · exact g32p_row17_integrationClasses_068 r
  · exact g32p_row17_integrationClasses_069 r
  · exact g32p_row17_integrationClasses_070 r
  · exact g32p_row17_integrationClasses_071 r
  · exact g32p_row17_integrationClasses_072 r
  · exact g32p_row17_integrationClasses_073 r
  · exact g32p_row17_integrationClasses_074 r
  · exact g32p_row17_integrationClasses_075 r
  · exact g32p_row17_integrationClasses_076 r
  · exact g32p_row17_integrationClasses_077 r
  · exact g32p_row17_integrationClasses_078 r
  · exact g32p_row17_integrationClasses_079 r
  · exact g32p_row17_integrationClasses_080 r

theorem g32p_row17_integrationRestriction
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (g32p_integrationLabel g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (g32p_integrationLabel g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (g32p_integrationLabel g)) :
    ∃ v ∈ g32VectorTable, v.i = 17 ∧
      papersA τ τbar θ (g32p_recordedSuppliers 16).H
        (g32p_recordedSupplierCharacters 16) = g32SparseVec v.coords := by
  exact g32p_row17_restriction_from_family g32p_integrationLabel g32p_row17_integrationClasses
    τ τbar θ ht hb hq

#print axioms g32p_row17_integrationRestriction

theorem g32p_row17_integrationNode (j : Fin 48) (i : Fin 1296) :
    g32p_comparisonAssemblyValue (g32p_integrationLabel (g32p_row17_groupEquiv i)) j =
      HurwitzPrymRex_ev g32h_omega
        (g32p_row17_restrictionCoefficients j (g32p_row17_restrictionBucket i)) := by
  rw [g32p_row17_integrationClasses, g32p_row17_restrictionFamily]
  exact g32p_integration_value_coefficient _ _

end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row18_pairingTerms : Fin 48 → List (ℕ × HurwitzPrymRex_Zw × ℕ) :=
  ![g32p_row18_terms_0, g32p_row18_terms_1, g32p_row18_terms_2, g32p_row18_terms_3, g32p_row18_terms_4, g32p_row18_terms_5, g32p_row18_terms_6, g32p_row18_terms_7, g32p_row18_terms_8, g32p_row18_terms_9, g32p_row18_terms_10, g32p_row18_terms_11, g32p_row18_terms_12, g32p_row18_terms_13, g32p_row18_terms_14, g32p_row18_terms_15, g32p_row18_terms_16, g32p_row18_terms_17, g32p_row18_terms_18, g32p_row18_terms_19, g32p_row18_terms_20, g32p_row18_terms_21, g32p_row18_terms_22, g32p_row18_terms_23, g32p_row18_terms_24, g32p_row18_terms_25, g32p_row18_terms_26, g32p_row18_terms_27, g32p_row18_terms_28, g32p_row18_terms_29, g32p_row18_terms_30, g32p_row18_terms_31, g32p_row18_terms_32, g32p_row18_terms_33, g32p_row18_terms_34, g32p_row18_terms_35, g32p_row18_terms_36, g32p_row18_terms_37, g32p_row18_terms_38, g32p_row18_terms_39, g32p_row18_terms_40, g32p_row18_terms_41, g32p_row18_terms_42, g32p_row18_terms_43, g32p_row18_terms_44, g32p_row18_terms_45, g32p_row18_terms_46, g32p_row18_terms_47]

def g32p_row18_pairingQuotients : Fin 48 → List ℤ :=
  ![[], [], [], [], [36, 48, 12, -12, -24, -24], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [-36, -48, -12, 12, 24, 24], [], [], [], [], [], [], [36, 48, 12, -12, -24, -24], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def g32p_row18_freeCoordinates : Fin 44 → ℤ :=
  ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def g32p_row18_quaternionicMultiplicities : Fin 4 → ℤ :=
  ![0, 0, 0, 0]

theorem g32p_row18_pairingFree (j : Fin 44) :
    g32p_cyclotomicPairingCheck 36 (g32p_row18_freeCoordinates j)
      (g32p_pairingCoefficients 6 (g32p_row18_pairingTerms ⟨j.val, by omega⟩))
      [1, -1, 1] (g32p_row18_pairingQuotients ⟨j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row18_pairing_0
  · exact g32p_row18_pairing_1
  · exact g32p_row18_pairing_2
  · exact g32p_row18_pairing_3
  · exact g32p_row18_pairing_4
  · exact g32p_row18_pairing_5
  · exact g32p_row18_pairing_6
  · exact g32p_row18_pairing_7
  · exact g32p_row18_pairing_8
  · exact g32p_row18_pairing_9
  · exact g32p_row18_pairing_10
  · exact g32p_row18_pairing_11
  · exact g32p_row18_pairing_12
  · exact g32p_row18_pairing_13
  · exact g32p_row18_pairing_14
  · exact g32p_row18_pairing_15
  · exact g32p_row18_pairing_16
  · exact g32p_row18_pairing_17
  · exact g32p_row18_pairing_18
  · exact g32p_row18_pairing_19
  · exact g32p_row18_pairing_20
  · exact g32p_row18_pairing_21
  · exact g32p_row18_pairing_22
  · exact g32p_row18_pairing_23
  · exact g32p_row18_pairing_24
  · exact g32p_row18_pairing_25
  · exact g32p_row18_pairing_26
  · exact g32p_row18_pairing_27
  · exact g32p_row18_pairing_28
  · exact g32p_row18_pairing_29
  · exact g32p_row18_pairing_30
  · exact g32p_row18_pairing_31
  · exact g32p_row18_pairing_32
  · exact g32p_row18_pairing_33
  · exact g32p_row18_pairing_34
  · exact g32p_row18_pairing_35
  · exact g32p_row18_pairing_36
  · exact g32p_row18_pairing_37
  · exact g32p_row18_pairing_38
  · exact g32p_row18_pairing_39
  · exact g32p_row18_pairing_40
  · exact g32p_row18_pairing_41
  · exact g32p_row18_pairing_42
  · exact g32p_row18_pairing_43

theorem g32p_row18_pairingQuat (j : Fin 4) :
    g32p_cyclotomicPairingCheck 36 (g32p_row18_quaternionicMultiplicities j)
      (g32p_pairingCoefficients 6 (g32p_row18_pairingTerms ⟨44 + j.val, by omega⟩))
      [1, -1, 1] (g32p_row18_pairingQuotients ⟨44 + j.val, by omega⟩) = true := by
  fin_cases j
  · exact g32p_row18_pairing_44
  · exact g32p_row18_pairing_45
  · exact g32p_row18_pairing_46
  · exact g32p_row18_pairing_47

theorem g32p_row18_restriction_of_sums {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H]
    (τ τbar : Fin 44 → FDRep ℂ G) (θ : Fin 4 → FDRep ℂ G) (χ : H →* ℂˣ)
    (z : ℂ) (hz : IsPrimitiveRoot z 6) (horder : Fintype.card H = 36)
    (hfree : ∀ j : Fin 44,
      (∑ h : H, ((τ j).character h - (τbar j).character h) * (χ h⁻¹ : ℂ)) =
        ((g32p_row18_pairingTerms ⟨j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (6 / 3)) x.2.1 * z ^ x.2.2)).sum)
    (hquat : ∀ j : Fin 4,
      (∑ h : H, (θ j).character h * (χ h⁻¹ : ℂ)) =
        ((g32p_row18_pairingTerms ⟨44 + j.val, by omega⟩).map (fun x => (x.1 : ℂ) *
          HurwitzPrymRex_ev (z ^ (6 / 3)) x.2.1 * z ^ x.2.2)).sum) :
    ∃ v ∈ g32VectorTable,
      v.i = 18 ∧ papersA τ τbar θ H χ = g32SparseVec v.coords := by
  obtain ⟨v, hv, hi, hc⟩ := g32p_row18_coordinates
  refine ⟨v, hv, hi, ?_⟩
  rw [hc]
  refine (g32p_polynomialPairing_row H τ τbar θ χ 6
    g32p_row18_freeCoordinates g32p_row18_quaternionicMultiplicities
    g32p_row18_pairingTerms [1, -1, 1] g32p_row18_pairingQuotients z
    (g32p_pairing_modulus_six hz) hfree hquat
    (by rw [horder]; exact g32p_row18_pairingFree)
    (by rw [horder]; exact g32p_row18_pairingQuat)).trans ?_
  apply Prod.ext
  · rfl
  · funext j
    fin_cases j <;> rfl

end HodgeLean.Foundations.Program

end
