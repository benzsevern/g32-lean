import HodgeLean.Foundations.Program.G32PropFourSixPacked0507

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row17_restrictionFamily_0 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 0 a = g32p_restrictionFamilyCoefficient 0 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_0 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 0 a = none → g32p_row17_restrictionCoefficients 0 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 0 a = some t →
      g32p_row17_restrictionCoefficients 0 a = (g32p_row17_pairingTerms 0)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 0)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_0 : ∀ t : Fin (g32p_row17_pairingTerms 0).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 0 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 0)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_1 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 1 a = g32p_restrictionFamilyCoefficient 1 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_1 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 1 a = none → g32p_row17_restrictionCoefficients 1 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 1 a = some t →
      g32p_row17_restrictionCoefficients 1 a = (g32p_row17_pairingTerms 1)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 1)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_1 : ∀ t : Fin (g32p_row17_pairingTerms 1).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 1 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 1)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_2 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 2 a = g32p_restrictionFamilyCoefficient 2 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_2 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 2 a = none → g32p_row17_restrictionCoefficients 2 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 2 a = some t →
      g32p_row17_restrictionCoefficients 2 a = (g32p_row17_pairingTerms 2)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 2)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_2 : ∀ t : Fin (g32p_row17_pairingTerms 2).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 2 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 2)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_3 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 3 a = g32p_restrictionFamilyCoefficient 3 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_3 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 3 a = none → g32p_row17_restrictionCoefficients 3 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 3 a = some t →
      g32p_row17_restrictionCoefficients 3 a = (g32p_row17_pairingTerms 3)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 3)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_3 : ∀ t : Fin (g32p_row17_pairingTerms 3).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 3 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 3)[t].1 := by
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

theorem g32p_row17_restrictionFamily_4 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 4 a = g32p_restrictionFamilyCoefficient 4 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_4 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 4 a = none → g32p_row17_restrictionCoefficients 4 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 4 a = some t →
      g32p_row17_restrictionCoefficients 4 a = (g32p_row17_pairingTerms 4)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 4)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_4 : ∀ t : Fin (g32p_row17_pairingTerms 4).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 4 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 4)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_5 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 5 a = g32p_restrictionFamilyCoefficient 5 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_5 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 5 a = none → g32p_row17_restrictionCoefficients 5 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 5 a = some t →
      g32p_row17_restrictionCoefficients 5 a = (g32p_row17_pairingTerms 5)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 5)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_5 : ∀ t : Fin (g32p_row17_pairingTerms 5).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 5 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 5)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_6 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 6 a = g32p_restrictionFamilyCoefficient 6 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_6 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 6 a = none → g32p_row17_restrictionCoefficients 6 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 6 a = some t →
      g32p_row17_restrictionCoefficients 6 a = (g32p_row17_pairingTerms 6)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 6)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_6 : ∀ t : Fin (g32p_row17_pairingTerms 6).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 6 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 6)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_7 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 7 a = g32p_restrictionFamilyCoefficient 7 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_7 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 7 a = none → g32p_row17_restrictionCoefficients 7 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 7 a = some t →
      g32p_row17_restrictionCoefficients 7 a = (g32p_row17_pairingTerms 7)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 7)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_7 : ∀ t : Fin (g32p_row17_pairingTerms 7).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 7 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 7)[t].1 := by
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

theorem g32p_row17_restrictionFamily_8 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 8 a = g32p_restrictionFamilyCoefficient 8 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_8 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 8 a = none → g32p_row17_restrictionCoefficients 8 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 8 a = some t →
      g32p_row17_restrictionCoefficients 8 a = (g32p_row17_pairingTerms 8)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 8)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_8 : ∀ t : Fin (g32p_row17_pairingTerms 8).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 8 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 8)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_9 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 9 a = g32p_restrictionFamilyCoefficient 9 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_9 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 9 a = none → g32p_row17_restrictionCoefficients 9 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 9 a = some t →
      g32p_row17_restrictionCoefficients 9 a = (g32p_row17_pairingTerms 9)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 9)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_9 : ∀ t : Fin (g32p_row17_pairingTerms 9).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 9 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 9)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_10 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 10 a = g32p_restrictionFamilyCoefficient 10 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_10 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 10 a = none → g32p_row17_restrictionCoefficients 10 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 10 a = some t →
      g32p_row17_restrictionCoefficients 10 a = (g32p_row17_pairingTerms 10)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 10)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_10 : ∀ t : Fin (g32p_row17_pairingTerms 10).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 10 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 10)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_11 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 11 a = g32p_restrictionFamilyCoefficient 11 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_11 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 11 a = none → g32p_row17_restrictionCoefficients 11 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 11 a = some t →
      g32p_row17_restrictionCoefficients 11 a = (g32p_row17_pairingTerms 11)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 11)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_11 : ∀ t : Fin (g32p_row17_pairingTerms 11).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 11 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 11)[t].1 := by
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

theorem g32p_row17_restrictionFamily_12 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 12 a = g32p_restrictionFamilyCoefficient 12 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_12 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 12 a = none → g32p_row17_restrictionCoefficients 12 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 12 a = some t →
      g32p_row17_restrictionCoefficients 12 a = (g32p_row17_pairingTerms 12)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 12)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_12 : ∀ t : Fin (g32p_row17_pairingTerms 12).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 12 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 12)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_13 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 13 a = g32p_restrictionFamilyCoefficient 13 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_13 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 13 a = none → g32p_row17_restrictionCoefficients 13 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 13 a = some t →
      g32p_row17_restrictionCoefficients 13 a = (g32p_row17_pairingTerms 13)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 13)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_13 : ∀ t : Fin (g32p_row17_pairingTerms 13).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 13 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 13)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_14 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 14 a = g32p_restrictionFamilyCoefficient 14 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_14 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 14 a = none → g32p_row17_restrictionCoefficients 14 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 14 a = some t →
      g32p_row17_restrictionCoefficients 14 a = (g32p_row17_pairingTerms 14)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 14)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_14 : ∀ t : Fin (g32p_row17_pairingTerms 14).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 14 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 14)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_15 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 15 a = g32p_restrictionFamilyCoefficient 15 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_15 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 15 a = none → g32p_row17_restrictionCoefficients 15 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 15 a = some t →
      g32p_row17_restrictionCoefficients 15 a = (g32p_row17_pairingTerms 15)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 15)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_15 : ∀ t : Fin (g32p_row17_pairingTerms 15).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 15 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 15)[t].1 := by
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

theorem g32p_row17_restrictionFamily_16 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 16 a = g32p_restrictionFamilyCoefficient 16 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_16 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 16 a = none → g32p_row17_restrictionCoefficients 16 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 16 a = some t →
      g32p_row17_restrictionCoefficients 16 a = (g32p_row17_pairingTerms 16)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 16)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_16 : ∀ t : Fin (g32p_row17_pairingTerms 16).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 16 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 16)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_17 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 17 a = g32p_restrictionFamilyCoefficient 17 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_17 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 17 a = none → g32p_row17_restrictionCoefficients 17 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 17 a = some t →
      g32p_row17_restrictionCoefficients 17 a = (g32p_row17_pairingTerms 17)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 17)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_17 : ∀ t : Fin (g32p_row17_pairingTerms 17).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 17 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 17)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_18 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 18 a = g32p_restrictionFamilyCoefficient 18 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_18 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 18 a = none → g32p_row17_restrictionCoefficients 18 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 18 a = some t →
      g32p_row17_restrictionCoefficients 18 a = (g32p_row17_pairingTerms 18)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 18)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_18 : ∀ t : Fin (g32p_row17_pairingTerms 18).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 18 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 18)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_19 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 19 a = g32p_restrictionFamilyCoefficient 19 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_19 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 19 a = none → g32p_row17_restrictionCoefficients 19 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 19 a = some t →
      g32p_row17_restrictionCoefficients 19 a = (g32p_row17_pairingTerms 19)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 19)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_19 : ∀ t : Fin (g32p_row17_pairingTerms 19).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 19 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 19)[t].1 := by
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

theorem g32p_row17_restrictionFamily_20 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 20 a = g32p_restrictionFamilyCoefficient 20 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_20 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 20 a = none → g32p_row17_restrictionCoefficients 20 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 20 a = some t →
      g32p_row17_restrictionCoefficients 20 a = (g32p_row17_pairingTerms 20)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 20)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_20 : ∀ t : Fin (g32p_row17_pairingTerms 20).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 20 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 20)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_21 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 21 a = g32p_restrictionFamilyCoefficient 21 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_21 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 21 a = none → g32p_row17_restrictionCoefficients 21 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 21 a = some t →
      g32p_row17_restrictionCoefficients 21 a = (g32p_row17_pairingTerms 21)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 21)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_21 : ∀ t : Fin (g32p_row17_pairingTerms 21).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 21 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 21)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_22 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 22 a = g32p_restrictionFamilyCoefficient 22 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_22 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 22 a = none → g32p_row17_restrictionCoefficients 22 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 22 a = some t →
      g32p_row17_restrictionCoefficients 22 a = (g32p_row17_pairingTerms 22)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 22)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_22 : ∀ t : Fin (g32p_row17_pairingTerms 22).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 22 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 22)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_23 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 23 a = g32p_restrictionFamilyCoefficient 23 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_23 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 23 a = none → g32p_row17_restrictionCoefficients 23 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 23 a = some t →
      g32p_row17_restrictionCoefficients 23 a = (g32p_row17_pairingTerms 23)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 23)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_23 : ∀ t : Fin (g32p_row17_pairingTerms 23).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 23 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 23)[t].1 := by
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

theorem g32p_row17_restrictionFamily_24 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 24 a = g32p_restrictionFamilyCoefficient 24 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_24 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 24 a = none → g32p_row17_restrictionCoefficients 24 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 24 a = some t →
      g32p_row17_restrictionCoefficients 24 a = (g32p_row17_pairingTerms 24)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 24)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_24 : ∀ t : Fin (g32p_row17_pairingTerms 24).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 24 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 24)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_25 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 25 a = g32p_restrictionFamilyCoefficient 25 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_25 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 25 a = none → g32p_row17_restrictionCoefficients 25 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 25 a = some t →
      g32p_row17_restrictionCoefficients 25 a = (g32p_row17_pairingTerms 25)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 25)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_25 : ∀ t : Fin (g32p_row17_pairingTerms 25).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 25 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 25)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_26 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 26 a = g32p_restrictionFamilyCoefficient 26 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_26 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 26 a = none → g32p_row17_restrictionCoefficients 26 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 26 a = some t →
      g32p_row17_restrictionCoefficients 26 a = (g32p_row17_pairingTerms 26)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 26)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_26 : ∀ t : Fin (g32p_row17_pairingTerms 26).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 26 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 26)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_27 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 27 a = g32p_restrictionFamilyCoefficient 27 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_27 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 27 a = none → g32p_row17_restrictionCoefficients 27 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 27 a = some t →
      g32p_row17_restrictionCoefficients 27 a = (g32p_row17_pairingTerms 27)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 27)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_27 : ∀ t : Fin (g32p_row17_pairingTerms 27).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 27 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 27)[t].1 := by
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

theorem g32p_row17_restrictionFamily_28 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 28 a = g32p_restrictionFamilyCoefficient 28 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_28 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 28 a = none → g32p_row17_restrictionCoefficients 28 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 28 a = some t →
      g32p_row17_restrictionCoefficients 28 a = (g32p_row17_pairingTerms 28)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 28)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_28 : ∀ t : Fin (g32p_row17_pairingTerms 28).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 28 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 28)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_29 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 29 a = g32p_restrictionFamilyCoefficient 29 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_29 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 29 a = none → g32p_row17_restrictionCoefficients 29 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 29 a = some t →
      g32p_row17_restrictionCoefficients 29 a = (g32p_row17_pairingTerms 29)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 29)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_29 : ∀ t : Fin (g32p_row17_pairingTerms 29).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 29 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 29)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_30 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 30 a = g32p_restrictionFamilyCoefficient 30 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_30 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 30 a = none → g32p_row17_restrictionCoefficients 30 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 30 a = some t →
      g32p_row17_restrictionCoefficients 30 a = (g32p_row17_pairingTerms 30)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 30)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_30 : ∀ t : Fin (g32p_row17_pairingTerms 30).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 30 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 30)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_31 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 31 a = g32p_restrictionFamilyCoefficient 31 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_31 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 31 a = none → g32p_row17_restrictionCoefficients 31 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 31 a = some t →
      g32p_row17_restrictionCoefficients 31 a = (g32p_row17_pairingTerms 31)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 31)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_31 : ∀ t : Fin (g32p_row17_pairingTerms 31).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 31 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 31)[t].1 := by
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

theorem g32p_row17_restrictionFamily_32 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 32 a = g32p_restrictionFamilyCoefficient 32 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_32 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 32 a = none → g32p_row17_restrictionCoefficients 32 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 32 a = some t →
      g32p_row17_restrictionCoefficients 32 a = (g32p_row17_pairingTerms 32)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 32)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_32 : ∀ t : Fin (g32p_row17_pairingTerms 32).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 32 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 32)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_33 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 33 a = g32p_restrictionFamilyCoefficient 33 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_33 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 33 a = none → g32p_row17_restrictionCoefficients 33 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 33 a = some t →
      g32p_row17_restrictionCoefficients 33 a = (g32p_row17_pairingTerms 33)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 33)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_33 : ∀ t : Fin (g32p_row17_pairingTerms 33).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 33 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 33)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_34 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 34 a = g32p_restrictionFamilyCoefficient 34 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_34 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 34 a = none → g32p_row17_restrictionCoefficients 34 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 34 a = some t →
      g32p_row17_restrictionCoefficients 34 a = (g32p_row17_pairingTerms 34)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 34)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_34 : ∀ t : Fin (g32p_row17_pairingTerms 34).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 34 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 34)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_35 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 35 a = g32p_restrictionFamilyCoefficient 35 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_35 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 35 a = none → g32p_row17_restrictionCoefficients 35 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 35 a = some t →
      g32p_row17_restrictionCoefficients 35 a = (g32p_row17_pairingTerms 35)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 35)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_35 : ∀ t : Fin (g32p_row17_pairingTerms 35).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 35 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 35)[t].1 := by
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

theorem g32p_row17_restrictionFamily_36 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 36 a = g32p_restrictionFamilyCoefficient 36 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_36 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 36 a = none → g32p_row17_restrictionCoefficients 36 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 36 a = some t →
      g32p_row17_restrictionCoefficients 36 a = (g32p_row17_pairingTerms 36)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 36)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_36 : ∀ t : Fin (g32p_row17_pairingTerms 36).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 36 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 36)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_37 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 37 a = g32p_restrictionFamilyCoefficient 37 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_37 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 37 a = none → g32p_row17_restrictionCoefficients 37 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 37 a = some t →
      g32p_row17_restrictionCoefficients 37 a = (g32p_row17_pairingTerms 37)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 37)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_37 : ∀ t : Fin (g32p_row17_pairingTerms 37).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 37 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 37)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_38 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 38 a = g32p_restrictionFamilyCoefficient 38 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_38 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 38 a = none → g32p_row17_restrictionCoefficients 38 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 38 a = some t →
      g32p_row17_restrictionCoefficients 38 a = (g32p_row17_pairingTerms 38)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 38)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_38 : ∀ t : Fin (g32p_row17_pairingTerms 38).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 38 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 38)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_39 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 39 a = g32p_restrictionFamilyCoefficient 39 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_39 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 39 a = none → g32p_row17_restrictionCoefficients 39 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 39 a = some t →
      g32p_row17_restrictionCoefficients 39 a = (g32p_row17_pairingTerms 39)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 39)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_39 : ∀ t : Fin (g32p_row17_pairingTerms 39).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 39 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 39)[t].1 := by
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

theorem g32p_row17_restrictionFamily_40 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 40 a = g32p_restrictionFamilyCoefficient 40 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_40 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 40 a = none → g32p_row17_restrictionCoefficients 40 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 40 a = some t →
      g32p_row17_restrictionCoefficients 40 a = (g32p_row17_pairingTerms 40)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 40)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_40 : ∀ t : Fin (g32p_row17_pairingTerms 40).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 40 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 40)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_41 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 41 a = g32p_restrictionFamilyCoefficient 41 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_41 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 41 a = none → g32p_row17_restrictionCoefficients 41 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 41 a = some t →
      g32p_row17_restrictionCoefficients 41 a = (g32p_row17_pairingTerms 41)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 41)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_41 : ∀ t : Fin (g32p_row17_pairingTerms 41).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 41 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 41)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_42 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 42 a = g32p_restrictionFamilyCoefficient 42 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_42 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 42 a = none → g32p_row17_restrictionCoefficients 42 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 42 a = some t →
      g32p_row17_restrictionCoefficients 42 a = (g32p_row17_pairingTerms 42)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 42)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_42 : ∀ t : Fin (g32p_row17_pairingTerms 42).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 42 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 42)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_43 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 43 a = g32p_restrictionFamilyCoefficient 43 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_43 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 43 a = none → g32p_row17_restrictionCoefficients 43 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 43 a = some t →
      g32p_row17_restrictionCoefficients 43 a = (g32p_row17_pairingTerms 43)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 43)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_43 : ∀ t : Fin (g32p_row17_pairingTerms 43).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 43 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 43)[t].1 := by
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

theorem g32p_row17_restrictionFamily_44 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 44 a = g32p_restrictionFamilyCoefficient 44 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_44 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 44 a = none → g32p_row17_restrictionCoefficients 44 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 44 a = some t →
      g32p_row17_restrictionCoefficients 44 a = (g32p_row17_pairingTerms 44)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 44)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_44 : ∀ t : Fin (g32p_row17_pairingTerms 44).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 44 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 44)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_45 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 45 a = g32p_restrictionFamilyCoefficient 45 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_45 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 45 a = none → g32p_row17_restrictionCoefficients 45 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 45 a = some t →
      g32p_row17_restrictionCoefficients 45 a = (g32p_row17_pairingTerms 45)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 45)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_45 : ∀ t : Fin (g32p_row17_pairingTerms 45).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 45 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 45)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_46 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 46 a = g32p_restrictionFamilyCoefficient 46 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_46 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 46 a = none → g32p_row17_restrictionCoefficients 46 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 46 a = some t →
      g32p_row17_restrictionCoefficients 46 a = (g32p_row17_pairingTerms 46)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 46)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_46 : ∀ t : Fin (g32p_row17_pairingTerms 46).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 46 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 46)[t].1 := by
  decide +kernel

theorem g32p_row17_restrictionFamily_47 : ∀ a : Fin 72,
    g32p_row17_restrictionCoefficients 47 a = g32p_restrictionFamilyCoefficient 47 (g32p_row17_restrictionClasses a) := by
  decide +kernel

theorem g32p_row17_restrictionDecode_47 : ∀ a : Fin 72,
    (g32p_row17_restrictionLabels 47 a = none → g32p_row17_restrictionCoefficients 47 a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels 47 a = some t →
      g32p_row17_restrictionCoefficients 47 a = (g32p_row17_pairingTerms 47)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms 47)[t].2.2 := by
  decide +kernel

theorem g32p_row17_restrictionTerms_47 : ∀ t : Fin (g32p_row17_pairingTerms 47).length,
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels 47 a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms 47)[t].1 := by
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

theorem g32p_row17_restrictionFamily (j : Fin 48) (a : Fin 72) :
    g32p_row17_restrictionCoefficients j a = g32p_restrictionFamilyCoefficient j (g32p_row17_restrictionClasses a) := by
  fin_cases j
  · exact g32p_row17_restrictionFamily_0 a
  · exact g32p_row17_restrictionFamily_1 a
  · exact g32p_row17_restrictionFamily_2 a
  · exact g32p_row17_restrictionFamily_3 a
  · exact g32p_row17_restrictionFamily_4 a
  · exact g32p_row17_restrictionFamily_5 a
  · exact g32p_row17_restrictionFamily_6 a
  · exact g32p_row17_restrictionFamily_7 a
  · exact g32p_row17_restrictionFamily_8 a
  · exact g32p_row17_restrictionFamily_9 a
  · exact g32p_row17_restrictionFamily_10 a
  · exact g32p_row17_restrictionFamily_11 a
  · exact g32p_row17_restrictionFamily_12 a
  · exact g32p_row17_restrictionFamily_13 a
  · exact g32p_row17_restrictionFamily_14 a
  · exact g32p_row17_restrictionFamily_15 a
  · exact g32p_row17_restrictionFamily_16 a
  · exact g32p_row17_restrictionFamily_17 a
  · exact g32p_row17_restrictionFamily_18 a
  · exact g32p_row17_restrictionFamily_19 a
  · exact g32p_row17_restrictionFamily_20 a
  · exact g32p_row17_restrictionFamily_21 a
  · exact g32p_row17_restrictionFamily_22 a
  · exact g32p_row17_restrictionFamily_23 a
  · exact g32p_row17_restrictionFamily_24 a
  · exact g32p_row17_restrictionFamily_25 a
  · exact g32p_row17_restrictionFamily_26 a
  · exact g32p_row17_restrictionFamily_27 a
  · exact g32p_row17_restrictionFamily_28 a
  · exact g32p_row17_restrictionFamily_29 a
  · exact g32p_row17_restrictionFamily_30 a
  · exact g32p_row17_restrictionFamily_31 a
  · exact g32p_row17_restrictionFamily_32 a
  · exact g32p_row17_restrictionFamily_33 a
  · exact g32p_row17_restrictionFamily_34 a
  · exact g32p_row17_restrictionFamily_35 a
  · exact g32p_row17_restrictionFamily_36 a
  · exact g32p_row17_restrictionFamily_37 a
  · exact g32p_row17_restrictionFamily_38 a
  · exact g32p_row17_restrictionFamily_39 a
  · exact g32p_row17_restrictionFamily_40 a
  · exact g32p_row17_restrictionFamily_41 a
  · exact g32p_row17_restrictionFamily_42 a
  · exact g32p_row17_restrictionFamily_43 a
  · exact g32p_row17_restrictionFamily_44 a
  · exact g32p_row17_restrictionFamily_45 a
  · exact g32p_row17_restrictionFamily_46 a
  · exact g32p_row17_restrictionFamily_47 a

theorem g32p_row17_restrictionDecode (j : Fin 48) (a : Fin 72) :
    (g32p_row17_restrictionLabels j a = none → g32p_row17_restrictionCoefficients j a = ⟨0,0⟩) ∧
    ∀ t, g32p_row17_restrictionLabels j a = some t →
      g32p_row17_restrictionCoefficients j a = (g32p_row17_pairingTerms j)[t].2.1 ∧
      g32p_row17_restrictionExponents a = (g32p_row17_pairingTerms j)[t].2.2 := by
  fin_cases j
  · exact g32p_row17_restrictionDecode_0 a
  · exact g32p_row17_restrictionDecode_1 a
  · exact g32p_row17_restrictionDecode_2 a
  · exact g32p_row17_restrictionDecode_3 a
  · exact g32p_row17_restrictionDecode_4 a
  · exact g32p_row17_restrictionDecode_5 a
  · exact g32p_row17_restrictionDecode_6 a
  · exact g32p_row17_restrictionDecode_7 a
  · exact g32p_row17_restrictionDecode_8 a
  · exact g32p_row17_restrictionDecode_9 a
  · exact g32p_row17_restrictionDecode_10 a
  · exact g32p_row17_restrictionDecode_11 a
  · exact g32p_row17_restrictionDecode_12 a
  · exact g32p_row17_restrictionDecode_13 a
  · exact g32p_row17_restrictionDecode_14 a
  · exact g32p_row17_restrictionDecode_15 a
  · exact g32p_row17_restrictionDecode_16 a
  · exact g32p_row17_restrictionDecode_17 a
  · exact g32p_row17_restrictionDecode_18 a
  · exact g32p_row17_restrictionDecode_19 a
  · exact g32p_row17_restrictionDecode_20 a
  · exact g32p_row17_restrictionDecode_21 a
  · exact g32p_row17_restrictionDecode_22 a
  · exact g32p_row17_restrictionDecode_23 a
  · exact g32p_row17_restrictionDecode_24 a
  · exact g32p_row17_restrictionDecode_25 a
  · exact g32p_row17_restrictionDecode_26 a
  · exact g32p_row17_restrictionDecode_27 a
  · exact g32p_row17_restrictionDecode_28 a
  · exact g32p_row17_restrictionDecode_29 a
  · exact g32p_row17_restrictionDecode_30 a
  · exact g32p_row17_restrictionDecode_31 a
  · exact g32p_row17_restrictionDecode_32 a
  · exact g32p_row17_restrictionDecode_33 a
  · exact g32p_row17_restrictionDecode_34 a
  · exact g32p_row17_restrictionDecode_35 a
  · exact g32p_row17_restrictionDecode_36 a
  · exact g32p_row17_restrictionDecode_37 a
  · exact g32p_row17_restrictionDecode_38 a
  · exact g32p_row17_restrictionDecode_39 a
  · exact g32p_row17_restrictionDecode_40 a
  · exact g32p_row17_restrictionDecode_41 a
  · exact g32p_row17_restrictionDecode_42 a
  · exact g32p_row17_restrictionDecode_43 a
  · exact g32p_row17_restrictionDecode_44 a
  · exact g32p_row17_restrictionDecode_45 a
  · exact g32p_row17_restrictionDecode_46 a
  · exact g32p_row17_restrictionDecode_47 a

theorem g32p_row17_restrictionTerms (j : Fin 48) (t : Fin (g32p_row17_pairingTerms j).length) :
    (∑ a ∈ Finset.univ.filter (fun a => g32p_row17_restrictionLabels j a = some t), g32p_row17_restrictionSizes a) =
      (g32p_row17_pairingTerms j)[t].1 := by
  revert t
  fin_cases j
  · exact g32p_row17_restrictionTerms_0
  · exact g32p_row17_restrictionTerms_1
  · exact g32p_row17_restrictionTerms_2
  · exact g32p_row17_restrictionTerms_3
  · exact g32p_row17_restrictionTerms_4
  · exact g32p_row17_restrictionTerms_5
  · exact g32p_row17_restrictionTerms_6
  · exact g32p_row17_restrictionTerms_7
  · exact g32p_row17_restrictionTerms_8
  · exact g32p_row17_restrictionTerms_9
  · exact g32p_row17_restrictionTerms_10
  · exact g32p_row17_restrictionTerms_11
  · exact g32p_row17_restrictionTerms_12
  · exact g32p_row17_restrictionTerms_13
  · exact g32p_row17_restrictionTerms_14
  · exact g32p_row17_restrictionTerms_15
  · exact g32p_row17_restrictionTerms_16
  · exact g32p_row17_restrictionTerms_17
  · exact g32p_row17_restrictionTerms_18
  · exact g32p_row17_restrictionTerms_19
  · exact g32p_row17_restrictionTerms_20
  · exact g32p_row17_restrictionTerms_21
  · exact g32p_row17_restrictionTerms_22
  · exact g32p_row17_restrictionTerms_23
  · exact g32p_row17_restrictionTerms_24
  · exact g32p_row17_restrictionTerms_25
  · exact g32p_row17_restrictionTerms_26
  · exact g32p_row17_restrictionTerms_27
  · exact g32p_row17_restrictionTerms_28
  · exact g32p_row17_restrictionTerms_29
  · exact g32p_row17_restrictionTerms_30
  · exact g32p_row17_restrictionTerms_31
  · exact g32p_row17_restrictionTerms_32
  · exact g32p_row17_restrictionTerms_33
  · exact g32p_row17_restrictionTerms_34
  · exact g32p_row17_restrictionTerms_35
  · exact g32p_row17_restrictionTerms_36
  · exact g32p_row17_restrictionTerms_37
  · exact g32p_row17_restrictionTerms_38
  · exact g32p_row17_restrictionTerms_39
  · exact g32p_row17_restrictionTerms_40
  · exact g32p_row17_restrictionTerms_41
  · exact g32p_row17_restrictionTerms_42
  · exact g32p_row17_restrictionTerms_43
  · exact g32p_row17_restrictionTerms_44
  · exact g32p_row17_restrictionTerms_45
  · exact g32p_row17_restrictionTerms_46
  · exact g32p_row17_restrictionTerms_47

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row17_restrictionCount_0 :
    (Finset.univ.filter (fun i => g32p_row17_restrictionBucket i = 0)).card = g32p_row17_restrictionSizes 0 := by
  decide +kernel

theorem g32p_row17_restrictionCount_1 :
    (Finset.univ.filter (fun i => g32p_row17_restrictionBucket i = 1)).card = g32p_row17_restrictionSizes 1 := by
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

theorem g32p_row17_restrictionCount_2 :
    (Finset.univ.filter (fun i => g32p_row17_restrictionBucket i = 2)).card = g32p_row17_restrictionSizes 2 := by
  decide +kernel

theorem g32p_row17_restrictionCount_3 :
    (Finset.univ.filter (fun i => g32p_row17_restrictionBucket i = 3)).card = g32p_row17_restrictionSizes 3 := by
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

theorem g32p_row17_restrictionCount_4 :
    (Finset.univ.filter (fun i => g32p_row17_restrictionBucket i = 4)).card = g32p_row17_restrictionSizes 4 := by
  decide +kernel

theorem g32p_row17_restrictionCount_5 :
    (Finset.univ.filter (fun i => g32p_row17_restrictionBucket i = 5)).card = g32p_row17_restrictionSizes 5 := by
  decide +kernel


end HodgeLean.Foundations.Program

end
end
