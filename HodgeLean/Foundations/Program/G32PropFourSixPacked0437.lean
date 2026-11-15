import HodgeLean.Foundations.Program.G32PropFourSixPacked0436
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup32_matrix_000 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 0 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 0 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 0 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 0 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 0 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_001 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 1 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 1 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 1 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 1 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 1 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_002 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 2 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 2 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 2 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 2 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 2 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_003 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 3 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 3 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 3 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 3 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 3 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_004 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 4 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 4 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 4 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 4 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 4 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_005 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 5 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 5 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 5 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 5 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 5 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_006 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 6 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 6 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 6 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 6 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 6 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_007 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 7 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 7 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 7 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 7 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 7 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_008 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 8 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 8 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 8 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 8 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 8 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_009 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 9 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 9 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 9 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_009 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 9 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 9 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 9 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_009 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 9 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_010 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 10 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 10 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 10 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_010 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 10 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 10 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 10 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_010 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 10 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_011 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 11 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 11 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 11 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_011 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 11 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 11 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 11 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_011 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 11 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_012 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 12 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 12 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 12 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_012 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 12 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 12 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 12 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_012 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 12 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_013 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 13 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 13 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 13 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_013 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 13 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 13 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 13 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_013 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 13 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_014 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 14 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 14 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 14 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_014 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 14 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 14 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 14 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_014 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 14 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_015 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 15 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 15 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 15 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_015 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 15 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 15 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 15 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_015 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 15 r) ∈ g32p_supplierGroup32_support := by
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

theorem g32p_supplierGroup32_matrix_016 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 16 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 16 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 16 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_016 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 16 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 16 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 16 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_016 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 16 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_017 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 17 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 17 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 17 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_017 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 17 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 17 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 17 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_017 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 17 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_018 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 18 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 18 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 18 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_018 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 18 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 18 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 18 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_018 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 18 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_019 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 19 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 19 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 19 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_019 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 19 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 19 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 19 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_019 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 19 r) ∈ g32p_supplierGroup32_support := by
  decide +kernel

theorem g32p_supplierGroup32_matrix_020 : ∀ r : Fin 16,
    g32p_row49_groupNodes (g32p_finBlockIndex 324 20 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 20 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 20 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup32_class_020 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup32_source (g32p_finBlockIndex 324 20 r)).1 (g32p_supplierGroup32_source (g32p_finBlockIndex 324 20 r)).2 =
      g32p_supplierGroup32_classify (g32p_finBlockIndex 324 20 r) := by
  decide +kernel

theorem g32p_supplierGroup32_support_020 : ∀ r : Fin 16,
    g32p_supplierGroup32_classify (g32p_finBlockIndex 324 20 r) ∈ g32p_supplierGroup32_support := by
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

theorem g32p_supplierGroup32_matrix (i : Fin 324) :
    g32p_row49_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source i).1 (g32p_supplierGroup32_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row49_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup32_source i).1 (g32p_supplierGroup32_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup32_matrix_000 r
  · exact g32p_supplierGroup32_matrix_001 r
  · exact g32p_supplierGroup32_matrix_002 r
  · exact g32p_supplierGroup32_matrix_003 r
  · exact g32p_supplierGroup32_matrix_004 r
  · exact g32p_supplierGroup32_matrix_005 r
  · exact g32p_supplierGroup32_matrix_006 r
  · exact g32p_supplierGroup32_matrix_007 r
  · exact g32p_supplierGroup32_matrix_008 r
  · exact g32p_supplierGroup32_matrix_009 r
  · exact g32p_supplierGroup32_matrix_010 r
  · exact g32p_supplierGroup32_matrix_011 r
  · exact g32p_supplierGroup32_matrix_012 r
  · exact g32p_supplierGroup32_matrix_013 r
  · exact g32p_supplierGroup32_matrix_014 r
  · exact g32p_supplierGroup32_matrix_015 r
  · exact g32p_supplierGroup32_matrix_016 r
  · exact g32p_supplierGroup32_matrix_017 r
  · exact g32p_supplierGroup32_matrix_018 r
  · exact g32p_supplierGroup32_matrix_019 r
  · exact g32p_supplierGroup32_matrix_020 r

theorem g32p_supplierGroup32_class (i : Fin 324) :
    g32p_supplierForest_classes (g32p_supplierGroup32_source i).1 (g32p_supplierGroup32_source i).2 =
      g32p_supplierGroup32_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup32_source i).1 (g32p_supplierGroup32_source i).2 =
      g32p_supplierGroup32_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup32_class_000 r
  · exact g32p_supplierGroup32_class_001 r
  · exact g32p_supplierGroup32_class_002 r
  · exact g32p_supplierGroup32_class_003 r
  · exact g32p_supplierGroup32_class_004 r
  · exact g32p_supplierGroup32_class_005 r
  · exact g32p_supplierGroup32_class_006 r
  · exact g32p_supplierGroup32_class_007 r
  · exact g32p_supplierGroup32_class_008 r
  · exact g32p_supplierGroup32_class_009 r
  · exact g32p_supplierGroup32_class_010 r
  · exact g32p_supplierGroup32_class_011 r
  · exact g32p_supplierGroup32_class_012 r
  · exact g32p_supplierGroup32_class_013 r
  · exact g32p_supplierGroup32_class_014 r
  · exact g32p_supplierGroup32_class_015 r
  · exact g32p_supplierGroup32_class_016 r
  · exact g32p_supplierGroup32_class_017 r
  · exact g32p_supplierGroup32_class_018 r
  · exact g32p_supplierGroup32_class_019 r
  · exact g32p_supplierGroup32_class_020 r

theorem g32p_supplierGroup32_support_mem (i : Fin 324) :
    g32p_supplierGroup32_classify i ∈ g32p_supplierGroup32_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup32_classify i ∈ g32p_supplierGroup32_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup32_support_000 r
  · exact g32p_supplierGroup32_support_001 r
  · exact g32p_supplierGroup32_support_002 r
  · exact g32p_supplierGroup32_support_003 r
  · exact g32p_supplierGroup32_support_004 r
  · exact g32p_supplierGroup32_support_005 r
  · exact g32p_supplierGroup32_support_006 r
  · exact g32p_supplierGroup32_support_007 r
  · exact g32p_supplierGroup32_support_008 r
  · exact g32p_supplierGroup32_support_009 r
  · exact g32p_supplierGroup32_support_010 r
  · exact g32p_supplierGroup32_support_011 r
  · exact g32p_supplierGroup32_support_012 r
  · exact g32p_supplierGroup32_support_013 r
  · exact g32p_supplierGroup32_support_014 r
  · exact g32p_supplierGroup32_support_015 r
  · exact g32p_supplierGroup32_support_016 r
  · exact g32p_supplierGroup32_support_017 r
  · exact g32p_supplierGroup32_support_018 r
  · exact g32p_supplierGroup32_support_019 r
  · exact g32p_supplierGroup32_support_020 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row49_supplierClassifier : Fin 324 → Fin 102 := g32p_supplierGroup32_classify

theorem g32p_row49_groupEquiv_isConj (i : Fin 324) :
    IsConj (g32p_row49_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row49_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup32_source i).1 (g32p_supplierGroup32_source i).2
  rw [g32p_supplierGroup32_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row49_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup32_matrix i)

def g32p_row49_supplierClass (h : (g32p_recordedSuppliers 48).H) : Fin 102 :=
  g32p_row49_supplierClassifier (g32p_row49_groupEquiv.symm h)

theorem g32p_row49_supplierClass_isConj (h : (g32p_recordedSuppliers 48).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row49_supplierClass h)) := by
  have he : (g32p_row49_groupEquiv (g32p_row49_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 48).H => (a : g32p_G))
      (g32p_row49_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row49_supplierClassifier (g32p_row49_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row49_groupEquiv_isConj (g32p_row49_groupEquiv.symm h)

theorem g32p_row49_supplierClass_iff (h : (g32p_recordedSuppliers 48).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row49_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row49_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row49_supplierClass_isConj h).symm

theorem g32p_row49_supplierClass_mem_support (h : (g32p_recordedSuppliers 48).H) :
    g32p_row49_supplierClass h ∈ g32p_supplierGroup32_support :=
  g32p_supplierGroup32_support_mem (g32p_row49_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row49_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 0) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 0) (g32p_literalTraceValue 48 0)
      [1, 0, -1, 0, 1] [] = true := by
  rw [g32p_row49_traceCoefficients_000]
  decide +kernel

theorem g32p_row49_traceCoefficients_001 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 1 = [2, 0, 0, 0, 0, 0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 1) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 1) (g32p_literalTraceValue 48 1)
      [1, 0, -1, 0, 1] [7776, 0, 7776, 0, 7776] = true := by
  rw [g32p_row49_traceCoefficients_001]
  decide +kernel

theorem g32p_row49_traceCoefficients_002 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 2 = [2, 0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 2) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 2) (g32p_literalTraceValue 48 2)
      [1, 0, -1, 0, 1] [] = true := by
  rw [g32p_row49_traceCoefficients_002]
  decide +kernel

theorem g32p_row49_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 4 = [1, 0, 0, 0, 1, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 4) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 4) (g32p_literalTraceValue 48 4)
      [1, 0, -1, 0, 1] [2592, 0, 2592, 0, 2592] = true := by
  rw [g32p_row49_traceCoefficients_004]
  decide +kernel

theorem g32p_row49_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 6 = [4, 0, 0, 0, 4, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 6) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 6) (g32p_literalTraceValue 48 6)
      [1, 0, -1, 0, 1] [1296, 0, 1296, 0, 1296] = true := by
  rw [g32p_row49_traceCoefficients_006]
  decide +kernel

theorem g32p_row49_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 11 = [1, 0, 0, 0, 4, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 11) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 11) (g32p_literalTraceValue 48 11)
      [1, 0, -1, 0, 1] [648, 0, 648, 0, 648] = true := by
  rw [g32p_row49_traceCoefficients_011]
  decide +kernel

theorem g32p_row49_traceCoefficients_013 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 13 = [0, 9, 0, 0, 0, 0, 0, 9] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_013 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 13) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 13) (g32p_literalTraceValue 48 13)
      [1, 0, -1, 0, 1] [0, 2592, 0, 2592] = true := by
  rw [g32p_row49_traceCoefficients_013]
  decide +kernel

theorem g32p_row49_traceCoefficients_021 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 21 = [0, 9, 0, 0, 0, 9, 0, 9, 0, 0, 0, 9] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_021 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 21) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 21) (g32p_literalTraceValue 48 21)
      [1, 0, -1, 0, 1] [0, 324, 0, 324, 0, 324, 0, 324] = true := by
  rw [g32p_row49_traceCoefficients_021]
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

theorem g32p_row49_traceCoefficients_024 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 24 = [0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 24) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 24) (g32p_literalTraceValue 48 24)
      [1, 0, -1, 0, 1] [1944, 0, 2592, 0, 648, 0, 648] = true := by
  rw [g32p_row49_traceCoefficients_024]
  decide +kernel

theorem g32p_row49_traceCoefficients_028 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 28 = [0, 0, 2, 0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_028 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 28) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 28) (g32p_literalTraceValue 48 28)
      [1, 0, -1, 0, 1] [0, 0, 7776] = true := by
  rw [g32p_row49_traceCoefficients_028]
  decide +kernel

theorem g32p_row49_traceCoefficients_030 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 30 = [0, 9, 0, 9, 0, 0, 0, 9, 0, 9] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_030 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 30) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 30) (g32p_literalTraceValue 48 30)
      [1, 0, -1, 0, 1] [0, 324, 0, 648, 0, 324] = true := by
  rw [g32p_row49_traceCoefficients_030]
  decide +kernel

theorem g32p_row49_traceCoefficients_032 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 32 = [0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 32) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 32) (g32p_literalTraceValue 48 32)
      [1, 0, -1, 0, 1] [0, 0, 1296, 0, 1296, 0, 1296] = true := by
  rw [g32p_row49_traceCoefficients_032]
  decide +kernel

theorem g32p_row49_traceCoefficients_034 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 34 = [0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 9] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_034 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 34) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 34) (g32p_literalTraceValue 48 34)
      [1, 0, -1, 0, 1] [0, 0, 0, 0, 0, 2592, 0, 2592] = true := by
  rw [g32p_row49_traceCoefficients_034]
  decide +kernel

theorem g32p_row49_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 35 = [4, 0, 0, 0, 4, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 35) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 35) (g32p_literalTraceValue 48 35)
      [1, 0, -1, 0, 1] [1296, 0, 1296, 0, 1296] = true := by
  rw [g32p_row49_traceCoefficients_035]
  decide +kernel

theorem g32p_row49_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 37 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 37) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 37) (g32p_literalTraceValue 48 37)
      [1, 0, -1, 0, 1] [-155520] = true := by
  rw [g32p_row49_traceCoefficients_037]
  decide +kernel

theorem g32p_row49_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 44 = [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 44) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 44) (g32p_literalTraceValue 48 44)
      [1, 0, -1, 0, 1] [-7776, 0, 0, 0, 7776, 0, 7776] = true := by
  rw [g32p_row49_traceCoefficients_044]
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

theorem g32p_row49_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 45 = [4, 0, 0, 0, 4, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 45) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 45) (g32p_literalTraceValue 48 45)
      [1, 0, -1, 0, 1] [1296, 0, 1296, 0, 1296] = true := by
  rw [g32p_row49_traceCoefficients_045]
  decide +kernel

theorem g32p_row49_traceCoefficients_046 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 46 = [0, 0, 0, 9, 0, 9, 0, 0, 0, 9, 0, 9] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_046 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 46) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 46) (g32p_literalTraceValue 48 46)
      [1, 0, -1, 0, 1] [0, 0, 0, 324, 0, 648, 0, 324] = true := by
  rw [g32p_row49_traceCoefficients_046]
  decide +kernel

theorem g32p_row49_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 56 = [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 56) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 56) (g32p_literalTraceValue 48 56)
      [1, 0, -1, 0, 1] [0, 0, 648, 0, 2592, 0, 2592] = true := by
  rw [g32p_row49_traceCoefficients_056]
  decide +kernel

theorem g32p_row49_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 67 = [0, 0, 0, 0, 2, 0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 67) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 67) (g32p_literalTraceValue 48 67)
      [1, 0, -1, 0, 1] [7776, 0, 7776, 0, 7776] = true := by
  rw [g32p_row49_traceCoefficients_067]
  decide +kernel

theorem g32p_row49_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 69 = [0, 0, 0, 9, 0, 0, 0, 0, 0, 9] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 69) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 69) (g32p_literalTraceValue 48 69)
      [1, 0, -1, 0, 1] [0, 0, 0, 2592, 0, 2592] = true := by
  rw [g32p_row49_traceCoefficients_069]
  decide +kernel

theorem g32p_row49_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 75 = [0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 75) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 75) (g32p_literalTraceValue 48 75)
      [1, 0, -1, 0, 1] [0, 0, 1296, 0, 1296, 0, 1296] = true := by
  rw [g32p_row49_traceCoefficients_075]
  decide +kernel

theorem g32p_row49_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 76 = [0, 0, 0, 0, 2, 0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 76) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 76) (g32p_literalTraceValue 48 76)
      [1, 0, -1, 0, 1] [7776, 0, 7776, 0, 7776] = true := by
  rw [g32p_row49_traceCoefficients_076]
  decide +kernel

theorem g32p_row49_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 78 = [4, 0, 0, 0, 1, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 78) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 78) (g32p_literalTraceValue 48 78)
      [1, 0, -1, 0, 1] [648, 0, 648, 0, 648] = true := by
  rw [g32p_row49_traceCoefficients_078]
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

theorem g32p_row49_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 84 = [0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 84) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 84) (g32p_literalTraceValue 48 84)
      [1, 0, -1, 0, 1] [0, 0, 1296, 0, 1296, 0, 1296] = true := by
  rw [g32p_row49_traceCoefficients_084]
  decide +kernel

theorem g32p_row49_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 87 = [2, 0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 87) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 87) (g32p_literalTraceValue 48 87)
      [1, 0, -1, 0, 1] [] = true := by
  rw [g32p_row49_traceCoefficients_087]
  decide +kernel

theorem g32p_row49_traceCoefficients_088 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 88 = [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 88) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 88) (g32p_literalTraceValue 48 88)
      [1, 0, -1, 0, 1] [7776, 0, 7776, 0, 7776, 0, 7776] = true := by
  rw [g32p_row49_traceCoefficients_088]
  decide +kernel

theorem g32p_row49_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 92 = [0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 92) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 92) (g32p_literalTraceValue 48 92)
      [1, 0, -1, 0, 1] [-1944, 0, 648, 0, 648, 0, 648] = true := by
  rw [g32p_row49_traceCoefficients_092]
  decide +kernel

theorem g32p_row49_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 93 = [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 93) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 93) (g32p_literalTraceValue 48 93)
      [1, 0, -1, 0, 1] [7776, 0, 7776, 0, 7776, 0, 7776] = true := by
  rw [g32p_row49_traceCoefficients_093]
  decide +kernel

theorem g32p_row49_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 95 = [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 95) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 95) (g32p_literalTraceValue 48 95)
      [1, 0, -1, 0, 1] [-7776, 0, 0, 0, 7776, 0, 7776] = true := by
  rw [g32p_row49_traceCoefficients_095]
  decide +kernel

theorem g32p_row49_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 96 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 96) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 96) (g32p_literalTraceValue 48 96)
      [1, 0, -1, 0, 1] [] = true := by
  rw [g32p_row49_traceCoefficients_096]
  decide +kernel

theorem g32p_row49_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 97 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 97) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 97) (g32p_literalTraceValue 48 97)
      [1, 0, -1, 0, 1] [0, 0, 0, 0, 155520, 0, 155520] = true := by
  rw [g32p_row49_traceCoefficients_097]
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

theorem g32p_row49_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 98 = [0, 0, 2, 0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 98) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 98) (g32p_literalTraceValue 48 98)
      [1, 0, -1, 0, 1] [0, 0, 7776] = true := by
  rw [g32p_row49_traceCoefficients_098]
  decide +kernel

theorem g32p_row49_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 99 = [0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 99) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 99) (g32p_literalTraceValue 48 99)
      [1, 0, -1, 0, 1] [155520, 0, 155520] = true := by
  rw [g32p_row49_traceCoefficients_099]
  decide +kernel

theorem g32p_row49_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 100 = [2, 0, 0, 0, 0, 0, 0, 0, 2] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 100) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 100) (g32p_literalTraceValue 48 100)
      [1, 0, -1, 0, 1] [7776, 0, 7776, 0, 7776] = true := by
  rw [g32p_row49_traceCoefficients_100]
  decide +kernel

theorem g32p_row49_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 101 = [0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row49_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 101) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) 101) (g32p_literalTraceValue 48 101)
      [1, 0, -1, 0, 1] [155520, 0, 155520, 0, 155520] = true := by
  rw [g32p_row49_traceCoefficients_101]
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

def g32p_row49_generatorIndex : Fin 8 → Fin 408 :=
  ![48, 99, 150, 201, 300, 301, 402, 403]

theorem g32p_row49_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup32_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 48 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 48 g32p_row49_supplierClass
    g32p_row49_supplierClass_isConj g32p_supplierGroup32_support g32p_row49_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row49_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup32_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row49_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 48 c false (g32p_row49_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 48 c true (g32p_row49_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 48 c false (g32p_row49_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 48 c true (g32p_row49_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 48 c false (g32p_row49_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 48 c false (g32p_row49_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 48 c true (g32p_row49_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 48 c true (g32p_row49_coinduced_zero c hc true) 3

theorem g32p_row49_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup32_support →
      g32p_literalTraceValue (g32p_row49_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row49_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup32_support →
      g32p_literalTraceValue (g32p_row49_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row49_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup32_support →
      g32p_literalTraceValue (g32p_row49_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row49_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup32_support →
      g32p_literalTraceValue (g32p_row49_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row49_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup32_support →
      g32p_literalTraceValue (g32p_row49_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row49_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup32_support →
      g32p_literalTraceValue (g32p_row49_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row49_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup32_support →
      g32p_literalTraceValue (g32p_row49_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row49_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup32_support) :
    g32p_literalTraceValue (g32p_row49_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup32_support →
    g32p_literalTraceValue (g32p_row49_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row49_zeroTrace_block_00 r k
  · exact g32p_row49_zeroTrace_block_01 r k
  · exact g32p_row49_zeroTrace_block_02 r k
  · exact g32p_row49_zeroTrace_block_03 r k
  · exact g32p_row49_zeroTrace_block_04 r k
  · exact g32p_row49_zeroTrace_block_05 r k
  · exact g32p_row49_zeroTrace_block_06 r k

theorem g32p_row49_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup32_support) :
    (g32p_recordedInductionGenerators (g32p_row49_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row49_generatorIndex k) c) := by
  rw [g32p_row49_recordedGenerator_zero c hc k, g32p_row49_zeroTrace_arithmetic c k hc]
  norm_num [HurwitzPrymRex_ev]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def g32p_row49_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [7776, 0, 7776, 0, 7776] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [2592, 0, 2592, 0, 2592] else []))) else (if i.val < 9 then (if i.val < 7 then [1296, 0, 1296, 0, 1296] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [648, 0, 648, 0, 648])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [0, 2592, 0, 2592] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [0, 324, 0, 324, 0, 324, 0, 324] else []) else (if i.val < 24 then [] else [1944, 0, 2592, 0, 648, 0, 648]))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [0, 0, 7776] else (if i.val < 30 then [] else [0, 324, 0, 648, 0, 324]))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [0, 0, 1296, 0, 1296, 0, 1296] else [])) else (if i.val < 36 then (if i.val < 35 then [0, 0, 0, 0, 0, 2592, 0, 2592] else [1296, 0, 1296, 0, 1296]) else (if i.val < 37 then [] else [-155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [-7776, 0, 0, 0, 7776, 0, 7776] else (if i.val < 46 then [1296, 0, 1296, 0, 1296] else [0, 0, 0, 324, 0, 648, 0, 324])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else [0, 0, 648, 0, 2592, 0, 2592]))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [] else (if i.val < 68 then [7776, 0, 7776, 0, 7776] else []))) else (if i.val < 72 then (if i.val < 70 then [0, 0, 0, 2592, 0, 2592] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else [0, 0, 1296, 0, 1296, 0, 1296]))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [7776, 0, 7776, 0, 7776] else (if i.val < 78 then [] else [648, 0, 648, 0, 648])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [0, 0, 1296, 0, 1296, 0, 1296])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [7776, 0, 7776, 0, 7776, 0, 7776])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [-1944, 0, 648, 0, 648, 0, 648] else (if i.val < 94 then [7776, 0, 7776, 0, 7776, 0, 7776] else []))) else (if i.val < 98 then (if i.val < 96 then [-7776, 0, 0, 0, 7776, 0, 7776] else (if i.val < 97 then [] else [0, 0, 0, 0, 155520, 0, 155520])) else (if i.val < 100 then (if i.val < 99 then [0, 0, 7776] else [155520, 0, 155520]) else (if i.val < 101 then [7776, 0, 7776, 0, 7776] else [155520, 0, 155520, 0, 155520])))))))

theorem g32p_row49_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup32_support) :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer c) 12
      (g32p_supplierTraceCoefficients g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) c) (g32p_literalTraceValue 48 c)
      [1, 0, -1, 0, 1] (g32p_row49_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row49_tracePolynomial_000
  · exact g32p_row49_tracePolynomial_001
  · exact g32p_row49_tracePolynomial_002
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_004
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_006
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (18 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_021
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_024
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_028
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_030
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_034
  · exact g32p_row49_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_044
  · exact g32p_row49_tracePolynomial_045
  · exact g32p_row49_tracePolynomial_046
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (65 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_075
  · exact g32p_row49_tracePolynomial_076
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_078
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (82 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_084
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_087
  · exact g32p_row49_tracePolynomial_088
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_092
  · exact g32p_row49_tracePolynomial_093
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup32_support) hc)
  · exact g32p_row49_tracePolynomial_095
  · exact g32p_row49_tracePolynomial_096
  · exact g32p_row49_tracePolynomial_097
  · exact g32p_row49_tracePolynomial_098
  · exact g32p_row49_tracePolynomial_099
  · exact g32p_row49_tracePolynomial_100
  · exact g32p_row49_tracePolynomial_101

theorem g32p_row49_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 48 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 48 c) := by
  by_cases hc : c ∈ g32p_supplierGroup32_support
  · have hclass (j : Fin 324) :
        IsConj (g32p_literalRepresentative c) (g32p_row49_groupEquiv j : g32p_G) ↔
          g32p_row49_supplierClassifier j = c := by
      simpa only [g32p_row49_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row49_supplierClass_iff (g32p_row49_groupEquiv j) c
    have hχ (j : Fin 324) :
        (g32p_recordedSupplierCharacters 48 (g32p_row49_groupEquiv j) : ℂ) =
          g32p_root 12 ^ (Multiplicative.toAdd (g32p_row49_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 48 (show (g32p_recordedSuppliers 48).H from g32p_row49_groupEquiv j)]
      change g32p_root 12 ^ (Multiplicative.toAdd
        (g32p_row49_characterValues (g32p_row49_groupEquiv.symm (g32p_row49_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 48).H (g32p_recordedSupplierCharacters 48)
      (g32p_literalRepresentative c) g32p_row49_groupEquiv g32p_row49_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row49_characterValues j)).val) c 12 324
      (g32p_literalCentralizer c) (g32p_literalTraceValue 48 c) [1, 0, -1, 0, 1]
      (g32p_row49_traceQuotient c) (g32p_root 12) (by decide)
      g32p_row49_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_twelve
        (g32p_root_primitive (g32p_recordedSuppliers 48)))
      (g32p_row49_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 12 (by decide)] at h
    exact h
  · exact g32p_row49_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row49_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row49_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row49_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row49_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
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

theorem g32p_row49_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row49_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row49_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 48 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
