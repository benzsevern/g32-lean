import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0228
import HodgeLean.Foundations.Program.G32PropFourSixPacked0229
import HodgeLean.Foundations.Program.G32PropFourSixPacked0230
import HodgeLean.Foundations.Program.G32PropFourSixPacked0236
import HodgeLean.Foundations.Program.G32PropFourSixPacked0237
import HodgeLean.Foundations.Program.G32PropFourSixPacked0238
import HodgeLean.Foundations.Program.G32PropFourSixPacked0240
import HodgeLean.Foundations.Program.G32PropFourSixPacked0249
import HodgeLean.Foundations.Program.G32PropFourSixPacked0250
import HodgeLean.Foundations.Program.G32PropFourSixPacked0251
import HodgeLean.Foundations.Program.G32PropFourSixPacked0252

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_118746 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_118746 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118746 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_028020 := by
  decide +kernel

theorem g32p_supplierForest_actual_118746 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118746) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_118746
    g32p_supplierForest_actual_028020

def g32p_supplierForest_node_118748 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118748 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118748 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124671 := by
  decide +kernel

theorem g32p_supplierForest_actual_118748 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118748) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_118748
    g32p_supplierForest_actual_124671

def g32p_supplierForest_node_118758 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_118758 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118758 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_116599 := by
  decide +kernel

theorem g32p_supplierForest_actual_118758 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118758) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_118758
    g32p_supplierForest_actual_116599

def g32p_supplierForest_node_118783 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118783 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118783 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154154 := by
  decide +kernel

theorem g32p_supplierForest_actual_118783 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118783) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_118783
    g32p_supplierForest_actual_154154

def g32p_supplierForest_node_118784 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118784 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118784 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108051 := by
  decide +kernel

theorem g32p_supplierForest_actual_118784 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118784) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_118784
    g32p_supplierForest_actual_108051

def g32p_supplierForest_node_118811 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_118811 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118811 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_105067 := by
  decide +kernel

theorem g32p_supplierForest_actual_118811 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118811) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_118811
    g32p_supplierForest_actual_105067

def g32p_supplierForest_node_118837 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_118837 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118837 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_038347 := by
  decide +kernel

theorem g32p_supplierForest_actual_118837 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118837) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 3 g32p_supplierForest_edge_118837
    g32p_supplierForest_actual_038347

def g32p_supplierForest_node_118855 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_118855 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118855 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153255 := by
  decide +kernel

theorem g32p_supplierForest_actual_118855 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118855) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_118855
    g32p_supplierForest_actual_153255

def g32p_supplierForest_node_118867 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_118867 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118867 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_126033 := by
  decide +kernel

theorem g32p_supplierForest_actual_118867 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118867) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_118867
    g32p_supplierForest_actual_126033

def g32p_supplierForest_node_118874 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_118874 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118874 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_116353 := by
  decide +kernel

theorem g32p_supplierForest_actual_118874 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118874) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_118874
    g32p_supplierForest_actual_116353

def g32p_supplierForest_node_118885 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_118885 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118885 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_025245 := by
  decide +kernel

theorem g32p_supplierForest_actual_118885 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118885) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_118885
    g32p_supplierForest_actual_025245

def g32p_supplierForest_node_118917 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118917 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118917 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_032015 := by
  decide +kernel

theorem g32p_supplierForest_actual_118917 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118917) ∧
        IsConj g (g32p_literalRepresentative 65) := by
  exact g32p_archive_step_lift _ _ 65 2 g32p_supplierForest_edge_118917
    g32p_supplierForest_actual_032015

def g32p_supplierForest_node_118940 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_118940 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118940 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_126154 := by
  decide +kernel

theorem g32p_supplierForest_actual_118940 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118940) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_118940
    g32p_supplierForest_actual_126154

def g32p_supplierForest_node_118953 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_118953 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118953 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_111642 := by
  decide +kernel

theorem g32p_supplierForest_actual_118953 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118953) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_118953
    g32p_supplierForest_actual_111642

def g32p_supplierForest_node_118955 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_118955 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118955 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_120752 := by
  decide +kernel

theorem g32p_supplierForest_actual_118955 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118955) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 3 g32p_supplierForest_edge_118955
    g32p_supplierForest_actual_120752

def g32p_supplierForest_node_118957 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_118957 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118957 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123922 := by
  decide +kernel

theorem g32p_supplierForest_actual_118957 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118957) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_118957
    g32p_supplierForest_actual_123922

def g32p_supplierForest_node_118969 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_118969 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118969 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120309 := by
  decide +kernel

theorem g32p_supplierForest_actual_118969 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118969) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_118969
    g32p_supplierForest_actual_120309

def g32p_supplierForest_node_118978 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_118978 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118978 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_040017 := by
  decide +kernel

theorem g32p_supplierForest_actual_118978 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118978) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_118978
    g32p_supplierForest_actual_040017

def g32p_supplierForest_node_119009 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_119009 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119009 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_038782 := by
  decide +kernel

theorem g32p_supplierForest_actual_119009 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119009) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_119009
    g32p_supplierForest_actual_038782

def g32p_supplierForest_node_119063 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_119063 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119063 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126811 := by
  decide +kernel

theorem g32p_supplierForest_actual_119063 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119063) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_119063
    g32p_supplierForest_actual_126811

def g32p_supplierForest_node_119078 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_119078 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119078 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126245 := by
  decide +kernel

theorem g32p_supplierForest_actual_119078 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119078) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 1 g32p_supplierForest_edge_119078
    g32p_supplierForest_actual_126245

def g32p_supplierForest_node_119083 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_119083 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119083 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123233 := by
  decide +kernel

theorem g32p_supplierForest_actual_119083 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119083) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_119083
    g32p_supplierForest_actual_123233

def g32p_supplierForest_node_119145 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_119145 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119145 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120057 := by
  decide +kernel

theorem g32p_supplierForest_actual_119145 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119145) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_119145
    g32p_supplierForest_actual_120057

def g32p_supplierForest_node_119151 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119151 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119151 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_044177 := by
  decide +kernel

theorem g32p_supplierForest_actual_119151 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119151) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_119151
    g32p_supplierForest_actual_044177

def g32p_supplierForest_node_119170 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119170 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119170 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_119912 := by
  decide +kernel

theorem g32p_supplierForest_actual_119170 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119170) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_119170
    g32p_supplierForest_actual_119912

def g32p_supplierForest_node_119172 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119172 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119172 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038972 := by
  decide +kernel

theorem g32p_supplierForest_actual_119172 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119172) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_119172
    g32p_supplierForest_actual_038972

def g32p_supplierForest_node_119194 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119194 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119194 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122025 := by
  decide +kernel

theorem g32p_supplierForest_actual_119194 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119194) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_119194
    g32p_supplierForest_actual_122025

def g32p_supplierForest_node_119228 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119228 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119228 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108121 := by
  decide +kernel

theorem g32p_supplierForest_actual_119228 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119228) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_119228
    g32p_supplierForest_actual_108121

def g32p_supplierForest_node_119230 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119230 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119230 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121697 := by
  decide +kernel

theorem g32p_supplierForest_actual_119230 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119230) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_119230
    g32p_supplierForest_actual_121697

def g32p_supplierForest_node_119241 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_119241 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119241 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154322 := by
  decide +kernel

theorem g32p_supplierForest_actual_119241 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119241) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 2 g32p_supplierForest_edge_119241
    g32p_supplierForest_actual_154322

def g32p_supplierForest_node_119244 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119244 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119244 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_037654 := by
  decide +kernel

theorem g32p_supplierForest_actual_119244 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119244) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_119244
    g32p_supplierForest_actual_037654

def g32p_supplierForest_node_119287 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_119287 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119287 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123387 := by
  decide +kernel

theorem g32p_supplierForest_actual_119287 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119287) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 1 g32p_supplierForest_edge_119287
    g32p_supplierForest_actual_123387

def g32p_supplierForest_node_119299 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_119299 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119299 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_040363 := by
  decide +kernel

theorem g32p_supplierForest_actual_119299 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119299) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_119299
    g32p_supplierForest_actual_040363

def g32p_supplierForest_node_119309 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_119309 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119309 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_106353 := by
  decide +kernel

theorem g32p_supplierForest_actual_119309 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119309) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_119309
    g32p_supplierForest_actual_106353

def g32p_supplierForest_node_119334 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119334 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119334 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_119695 := by
  decide +kernel

theorem g32p_supplierForest_actual_119334 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119334) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_119334
    g32p_supplierForest_actual_119695

def g32p_supplierForest_node_119346 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_119346 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119346 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_040402 := by
  decide +kernel

theorem g32p_supplierForest_actual_119346 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119346) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 0 g32p_supplierForest_edge_119346
    g32p_supplierForest_actual_040402

def g32p_supplierForest_node_119348 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_119348 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119348 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_102467 := by
  decide +kernel

theorem g32p_supplierForest_actual_119348 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119348) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_119348
    g32p_supplierForest_actual_102467

def g32p_supplierForest_node_119378 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119378 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119378 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_113927 := by
  decide +kernel

theorem g32p_supplierForest_actual_119378 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119378) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 0 g32p_supplierForest_edge_119378
    g32p_supplierForest_actual_113927

def g32p_supplierForest_node_119410 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119410 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119410 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120158 := by
  decide +kernel

theorem g32p_supplierForest_actual_119410 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119410) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_119410
    g32p_supplierForest_actual_120158

def g32p_supplierForest_node_119412 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119412 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119412 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117201 := by
  decide +kernel

theorem g32p_supplierForest_actual_119412 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119412) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_119412
    g32p_supplierForest_actual_117201

def g32p_supplierForest_node_119445 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_119445 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119445 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_111908 := by
  decide +kernel

theorem g32p_supplierForest_actual_119445 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119445) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_119445
    g32p_supplierForest_actual_111908

def g32p_supplierForest_node_119466 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119466 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119466 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_103846 := by
  decide +kernel

theorem g32p_supplierForest_actual_119466 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119466) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_119466
    g32p_supplierForest_actual_103846

def g32p_supplierForest_node_119507 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119507 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119507 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121369 := by
  decide +kernel

theorem g32p_supplierForest_actual_119507 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119507) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_119507
    g32p_supplierForest_actual_121369

def g32p_supplierForest_node_119525 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_119525 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119525 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_115180 := by
  decide +kernel

theorem g32p_supplierForest_actual_119525 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119525) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_119525
    g32p_supplierForest_actual_115180

def g32p_supplierForest_node_119585 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_119585 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119585 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113162 := by
  decide +kernel

theorem g32p_supplierForest_actual_119585 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119585) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_119585
    g32p_supplierForest_actual_113162

def g32p_supplierForest_node_119587 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_119587 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119587 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123409 := by
  decide +kernel

theorem g32p_supplierForest_actual_119587 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119587) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_119587
    g32p_supplierForest_actual_123409

def g32p_supplierForest_node_119590 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119590 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119590 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_114972 := by
  decide +kernel

theorem g32p_supplierForest_actual_119590 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119590) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_119590
    g32p_supplierForest_actual_114972

def g32p_supplierForest_node_119604 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_119604 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119604 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_041460 := by
  decide +kernel

theorem g32p_supplierForest_actual_119604 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119604) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_119604
    g32p_supplierForest_actual_041460

def g32p_supplierForest_node_119637 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_119637 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119637 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_044352 := by
  decide +kernel

theorem g32p_supplierForest_actual_119637 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119637) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 2 g32p_supplierForest_edge_119637
    g32p_supplierForest_actual_044352

def g32p_supplierForest_node_119642 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_119642 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119642 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102378 := by
  decide +kernel

theorem g32p_supplierForest_actual_119642 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119642) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_119642
    g32p_supplierForest_actual_102378

def g32p_supplierForest_node_119653 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_119653 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119653 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_114480 := by
  decide +kernel

theorem g32p_supplierForest_actual_119653 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119653) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_119653
    g32p_supplierForest_actual_114480

def g32p_supplierForest_node_119737 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119737 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119737 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_126557 := by
  decide +kernel

theorem g32p_supplierForest_actual_119737 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119737) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_119737
    g32p_supplierForest_actual_126557

def g32p_supplierForest_node_119752 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_119752 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119752 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_026735 := by
  decide +kernel

theorem g32p_supplierForest_actual_119752 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119752) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_119752
    g32p_supplierForest_actual_026735

def g32p_supplierForest_node_119796 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119796 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119796 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_116599 := by
  decide +kernel

theorem g32p_supplierForest_actual_119796 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119796) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_119796
    g32p_supplierForest_actual_116599

def g32p_supplierForest_node_119833 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_119833 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119833 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_119438 := by
  decide +kernel

theorem g32p_supplierForest_actual_119833 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119833) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_119833
    g32p_supplierForest_actual_119438

def g32p_supplierForest_node_119902 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119902 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119902 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113047 := by
  decide +kernel

theorem g32p_supplierForest_actual_119902 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119902) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_119902
    g32p_supplierForest_actual_113047

def g32p_supplierForest_node_119934 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_119934 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119934 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_110059 := by
  decide +kernel

theorem g32p_supplierForest_actual_119934 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119934) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_119934
    g32p_supplierForest_actual_110059

def g32p_supplierForest_node_119955 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_119955 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119955 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_032537 := by
  decide +kernel

theorem g32p_supplierForest_actual_119955 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119955) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_119955
    g32p_supplierForest_actual_032537

def g32p_supplierForest_node_119958 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119958 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119958 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102197 := by
  decide +kernel

theorem g32p_supplierForest_actual_119958 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119958) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_119958
    g32p_supplierForest_actual_102197

def g32p_supplierForest_node_119973 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_119973 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119973 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_034543 := by
  decide +kernel

theorem g32p_supplierForest_actual_119973 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119973) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_119973
    g32p_supplierForest_actual_034543

def g32p_supplierForest_node_119993 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_119993 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119993 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122334 := by
  decide +kernel

theorem g32p_supplierForest_actual_119993 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119993) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_119993
    g32p_supplierForest_actual_122334

def g32p_supplierForest_node_120066 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120066 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120066 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122365 := by
  decide +kernel

theorem g32p_supplierForest_actual_120066 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120066) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_120066
    g32p_supplierForest_actual_122365

def g32p_supplierForest_node_120086 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_120086 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120086 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118469 := by
  decide +kernel

theorem g32p_supplierForest_actual_120086 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120086) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 2 g32p_supplierForest_edge_120086
    g32p_supplierForest_actual_118469

def g32p_supplierForest_node_120095 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_120095 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120095 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117152 := by
  decide +kernel

theorem g32p_supplierForest_actual_120095 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120095) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_120095
    g32p_supplierForest_actual_117152

def g32p_supplierForest_node_120111 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_120111 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120111 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154702 := by
  decide +kernel

theorem g32p_supplierForest_actual_120111 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120111) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 3 g32p_supplierForest_edge_120111
    g32p_supplierForest_actual_154702

def g32p_supplierForest_node_120128 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_120128 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120128 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_114972 := by
  decide +kernel

theorem g32p_supplierForest_actual_120128 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120128) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_120128
    g32p_supplierForest_actual_114972

def g32p_supplierForest_node_120143 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_120143 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120143 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038226 := by
  decide +kernel

theorem g32p_supplierForest_actual_120143 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120143) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_120143
    g32p_supplierForest_actual_038226

def g32p_supplierForest_node_120155 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120155 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120155 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_044023 := by
  decide +kernel

theorem g32p_supplierForest_actual_120155 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120155) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_120155
    g32p_supplierForest_actual_044023

def g32p_supplierForest_node_120168 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120168 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120168 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_103540 := by
  decide +kernel

theorem g32p_supplierForest_actual_120168 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120168) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_120168
    g32p_supplierForest_actual_103540

def g32p_supplierForest_node_120186 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_120186 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120186 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118491 := by
  decide +kernel

theorem g32p_supplierForest_actual_120186 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120186) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 3 g32p_supplierForest_edge_120186
    g32p_supplierForest_actual_118491

def g32p_supplierForest_node_120202 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120202 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120202 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038171 := by
  decide +kernel

theorem g32p_supplierForest_actual_120202 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120202) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_120202
    g32p_supplierForest_actual_038171

def g32p_supplierForest_node_120218 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_120218 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120218 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_119390 := by
  decide +kernel

theorem g32p_supplierForest_actual_120218 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120218) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_120218
    g32p_supplierForest_actual_119390

def g32p_supplierForest_node_120242 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_120242 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120242 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_126285 := by
  decide +kernel

theorem g32p_supplierForest_actual_120242 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120242) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_120242
    g32p_supplierForest_actual_126285

def g32p_supplierForest_node_120246 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_120246 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120246 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_126825 := by
  decide +kernel

theorem g32p_supplierForest_actual_120246 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120246) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_120246
    g32p_supplierForest_actual_126825

def g32p_supplierForest_node_120310 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120310 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120310 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_121899 := by
  decide +kernel

theorem g32p_supplierForest_actual_120310 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120310) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_120310
    g32p_supplierForest_actual_121899

def g32p_supplierForest_node_120328 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_120328 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120328 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_111908 := by
  decide +kernel

theorem g32p_supplierForest_actual_120328 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120328) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_120328
    g32p_supplierForest_actual_111908

def g32p_supplierForest_node_120341 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120341 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120341 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043456 := by
  decide +kernel

theorem g32p_supplierForest_actual_120341 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120341) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_120341
    g32p_supplierForest_actual_043456

def g32p_supplierForest_node_120409 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_120409 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120409 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118702 := by
  decide +kernel

theorem g32p_supplierForest_actual_120409 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120409) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_120409
    g32p_supplierForest_actual_118702

def g32p_supplierForest_node_120418 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120418 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120418 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_112293 := by
  decide +kernel

theorem g32p_supplierForest_actual_120418 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120418) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 0 g32p_supplierForest_edge_120418
    g32p_supplierForest_actual_112293

def g32p_supplierForest_node_120530 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_120530 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120530 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115456 := by
  decide +kernel

theorem g32p_supplierForest_actual_120530 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120530) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_120530
    g32p_supplierForest_actual_115456

def g32p_supplierForest_node_120540 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_120540 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120540 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_125340 := by
  decide +kernel

theorem g32p_supplierForest_actual_120540 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120540) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_120540
    g32p_supplierForest_actual_125340

def g32p_supplierForest_node_120577 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120577 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120577 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_106353 := by
  decide +kernel

theorem g32p_supplierForest_actual_120577 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120577) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_120577
    g32p_supplierForest_actual_106353

def g32p_supplierForest_node_120590 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120590 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120590 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127007 := by
  decide +kernel

theorem g32p_supplierForest_actual_120590 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120590) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_120590
    g32p_supplierForest_actual_127007

def g32p_supplierForest_node_120605 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_120605 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120605 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_043149 := by
  decide +kernel

theorem g32p_supplierForest_actual_120605 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120605) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 1 g32p_supplierForest_edge_120605
    g32p_supplierForest_actual_043149

def g32p_supplierForest_node_120692 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120692 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120692 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043264 := by
  decide +kernel

theorem g32p_supplierForest_actual_120692 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120692) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_120692
    g32p_supplierForest_actual_043264

def g32p_supplierForest_node_120707 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120707 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120707 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_103811 := by
  decide +kernel

theorem g32p_supplierForest_actual_120707 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120707) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_120707
    g32p_supplierForest_actual_103811

def g32p_supplierForest_node_120714 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_120714 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120714 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118501 := by
  decide +kernel

theorem g32p_supplierForest_actual_120714 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120714) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_120714
    g32p_supplierForest_actual_118501

def g32p_supplierForest_node_120733 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120733 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120733 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126551 := by
  decide +kernel

theorem g32p_supplierForest_actual_120733 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120733) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_120733
    g32p_supplierForest_actual_126551

def g32p_supplierForest_node_120785 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_120785 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120785 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_033709 := by
  decide +kernel

theorem g32p_supplierForest_actual_120785 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120785) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_120785
    g32p_supplierForest_actual_033709

def g32p_supplierForest_node_120787 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120787 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120787 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120779 := by
  decide +kernel

theorem g32p_supplierForest_actual_120787 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120787) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_120787
    g32p_supplierForest_actual_120779

def g32p_supplierForest_node_120796 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_120796 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120796 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_107278 := by
  decide +kernel

theorem g32p_supplierForest_actual_120796 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120796) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_120796
    g32p_supplierForest_actual_107278

def g32p_supplierForest_node_120842 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_120842 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120842 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_108238 := by
  decide +kernel

theorem g32p_supplierForest_actual_120842 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120842) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 1 g32p_supplierForest_edge_120842
    g32p_supplierForest_actual_108238

def g32p_supplierForest_node_120853 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_120853 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120853 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_109870 := by
  decide +kernel

theorem g32p_supplierForest_actual_120853 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120853) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_120853
    g32p_supplierForest_actual_109870

def g32p_supplierForest_node_120927 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_120927 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120927 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_110268 := by
  decide +kernel

theorem g32p_supplierForest_actual_120927 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120927) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_120927
    g32p_supplierForest_actual_110268

def g32p_supplierForest_node_120960 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_120960 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120960 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_105874 := by
  decide +kernel

theorem g32p_supplierForest_actual_120960 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120960) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_120960
    g32p_supplierForest_actual_105874

def g32p_supplierForest_node_121071 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_121071 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121071 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_105167 := by
  decide +kernel

theorem g32p_supplierForest_actual_121071 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121071) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 3 g32p_supplierForest_edge_121071
    g32p_supplierForest_actual_105167

def g32p_supplierForest_node_121115 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_121115 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121115 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_121999 := by
  decide +kernel

theorem g32p_supplierForest_actual_121115 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121115) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_121115
    g32p_supplierForest_actual_121999

def g32p_supplierForest_node_121134 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121134 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121134 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_116249 := by
  decide +kernel

theorem g32p_supplierForest_actual_121134 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121134) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_121134
    g32p_supplierForest_actual_116249

def g32p_supplierForest_node_121196 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_121196 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121196 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_102482 := by
  decide +kernel

theorem g32p_supplierForest_actual_121196 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121196) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 0 g32p_supplierForest_edge_121196
    g32p_supplierForest_actual_102482

def g32p_supplierForest_node_121197 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_121197 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121197 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_125477 := by
  decide +kernel

theorem g32p_supplierForest_actual_121197 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121197) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 3 g32p_supplierForest_edge_121197
    g32p_supplierForest_actual_125477

def g32p_supplierForest_node_121236 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_121236 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121236 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_110831 := by
  decide +kernel

theorem g32p_supplierForest_actual_121236 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121236) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_121236
    g32p_supplierForest_actual_110831

def g32p_supplierForest_node_121244 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121244 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121244 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127299 := by
  decide +kernel

theorem g32p_supplierForest_actual_121244 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121244) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_121244
    g32p_supplierForest_actual_127299

def g32p_supplierForest_node_121253 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_121253 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121253 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_124295 := by
  decide +kernel

theorem g32p_supplierForest_actual_121253 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121253) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 1 g32p_supplierForest_edge_121253
    g32p_supplierForest_actual_124295

def g32p_supplierForest_node_121285 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_121285 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121285 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037619 := by
  decide +kernel

theorem g32p_supplierForest_actual_121285 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121285) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 2 g32p_supplierForest_edge_121285
    g32p_supplierForest_actual_037619

def g32p_supplierForest_node_121295 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_121295 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121295 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_026803 := by
  decide +kernel

theorem g32p_supplierForest_actual_121295 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121295) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_121295
    g32p_supplierForest_actual_026803

def g32p_supplierForest_node_121332 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121332 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121332 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113655 := by
  decide +kernel

theorem g32p_supplierForest_actual_121332 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121332) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_121332
    g32p_supplierForest_actual_113655

def g32p_supplierForest_node_121395 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_121395 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121395 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_125865 := by
  decide +kernel

theorem g32p_supplierForest_actual_121395 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121395) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_121395
    g32p_supplierForest_actual_125865

def g32p_supplierForest_node_121411 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_121411 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121411 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_102253 := by
  decide +kernel

theorem g32p_supplierForest_actual_121411 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121411) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_121411
    g32p_supplierForest_actual_102253

def g32p_supplierForest_node_121462 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_121462 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121462 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_024636 := by
  decide +kernel

theorem g32p_supplierForest_actual_121462 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121462) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_121462
    g32p_supplierForest_actual_024636

def g32p_supplierForest_node_121468 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_121468 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121468 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104373 := by
  decide +kernel

theorem g32p_supplierForest_actual_121468 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121468) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_121468
    g32p_supplierForest_actual_104373

def g32p_supplierForest_node_121470 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_121470 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121470 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_043104 := by
  decide +kernel

theorem g32p_supplierForest_actual_121470 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121470) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_121470
    g32p_supplierForest_actual_043104

def g32p_supplierForest_node_121525 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_121525 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121525 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_114041 := by
  decide +kernel

theorem g32p_supplierForest_actual_121525 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121525) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_121525
    g32p_supplierForest_actual_114041

def g32p_supplierForest_node_121558 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_121558 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121558 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_124751 := by
  decide +kernel

theorem g32p_supplierForest_actual_121558 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121558) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_121558
    g32p_supplierForest_actual_124751

def g32p_supplierForest_node_121578 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_121578 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121578 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_044296 := by
  decide +kernel

theorem g32p_supplierForest_actual_121578 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121578) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 0 g32p_supplierForest_edge_121578
    g32p_supplierForest_actual_044296

def g32p_supplierForest_node_121585 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_121585 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121585 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_034356 := by
  decide +kernel

theorem g32p_supplierForest_actual_121585 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121585) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_121585
    g32p_supplierForest_actual_034356

def g32p_supplierForest_node_121619 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_121619 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121619 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123977 := by
  decide +kernel

theorem g32p_supplierForest_actual_121619 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121619) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_121619
    g32p_supplierForest_actual_123977

def g32p_supplierForest_node_121631 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_121631 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121631 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_116876 := by
  decide +kernel

theorem g32p_supplierForest_actual_121631 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121631) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_121631
    g32p_supplierForest_actual_116876

def g32p_supplierForest_node_121634 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_121634 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121634 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_127175 := by
  decide +kernel

theorem g32p_supplierForest_actual_121634 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121634) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_121634
    g32p_supplierForest_actual_127175

def g32p_supplierForest_node_121674 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121674 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121674 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122670 := by
  decide +kernel

theorem g32p_supplierForest_actual_121674 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121674) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_121674
    g32p_supplierForest_actual_122670

def g32p_supplierForest_node_121689 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_121689 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121689 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123563 := by
  decide +kernel

theorem g32p_supplierForest_actual_121689 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121689) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_121689
    g32p_supplierForest_actual_123563

def g32p_supplierForest_node_121700 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121700 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121700 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_043406 := by
  decide +kernel

theorem g32p_supplierForest_actual_121700 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121700) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 0 g32p_supplierForest_edge_121700
    g32p_supplierForest_actual_043406

def g32p_supplierForest_node_121742 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_121742 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121742 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127528 := by
  decide +kernel

theorem g32p_supplierForest_actual_121742 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121742) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_121742
    g32p_supplierForest_actual_127528

def g32p_supplierForest_node_121755 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_121755 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121755 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_111311 := by
  decide +kernel

theorem g32p_supplierForest_actual_121755 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121755) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_121755
    g32p_supplierForest_actual_111311

def g32p_supplierForest_node_121766 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121766 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121766 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_126054 := by
  decide +kernel

theorem g32p_supplierForest_actual_121766 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121766) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_121766
    g32p_supplierForest_actual_126054

def g32p_supplierForest_node_121774 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_121774 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121774 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_127007 := by
  decide +kernel

theorem g32p_supplierForest_actual_121774 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121774) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_121774
    g32p_supplierForest_actual_127007

def g32p_supplierForest_node_121792 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_121792 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121792 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_107509 := by
  decide +kernel

theorem g32p_supplierForest_actual_121792 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121792) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_121792
    g32p_supplierForest_actual_107509

def g32p_supplierForest_node_121841 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121841 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121841 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_043594 := by
  decide +kernel

theorem g32p_supplierForest_actual_121841 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121841) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_121841
    g32p_supplierForest_actual_043594

def g32p_supplierForest_node_121870 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121870 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121870 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_110003 := by
  decide +kernel

theorem g32p_supplierForest_actual_121870 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121870) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_121870
    g32p_supplierForest_actual_110003

def g32p_supplierForest_node_121927 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_121927 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121927 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_041737 := by
  decide +kernel

theorem g32p_supplierForest_actual_121927 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121927) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_121927
    g32p_supplierForest_actual_041737

def g32p_supplierForest_node_121952 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_121952 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121952 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_027046 := by
  decide +kernel

theorem g32p_supplierForest_actual_121952 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121952) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_121952
    g32p_supplierForest_actual_027046

def g32p_supplierForest_node_121967 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_121967 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121967 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123847 := by
  decide +kernel

theorem g32p_supplierForest_actual_121967 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121967) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_121967
    g32p_supplierForest_actual_123847

def g32p_supplierForest_node_121982 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121982 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121982 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_121443 := by
  decide +kernel

theorem g32p_supplierForest_actual_121982 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121982) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_121982
    g32p_supplierForest_actual_121443

def g32p_supplierForest_node_121987 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_121987 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121987 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_120906 := by
  decide +kernel

theorem g32p_supplierForest_actual_121987 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121987) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_121987
    g32p_supplierForest_actual_120906

def g32p_supplierForest_node_122048 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_122048 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122048 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_104825 := by
  decide +kernel

theorem g32p_supplierForest_actual_122048 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122048) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 1 g32p_supplierForest_edge_122048
    g32p_supplierForest_actual_104825

def g32p_supplierForest_node_122056 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_122056 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122056 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115751 := by
  decide +kernel

theorem g32p_supplierForest_actual_122056 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122056) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_122056
    g32p_supplierForest_actual_115751

def g32p_supplierForest_node_122079 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_122079 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122079 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_125014 := by
  decide +kernel

theorem g32p_supplierForest_actual_122079 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122079) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_122079
    g32p_supplierForest_actual_125014

def g32p_supplierForest_node_122120 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_122120 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122120 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_034430 := by
  decide +kernel

theorem g32p_supplierForest_actual_122120 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122120) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_122120
    g32p_supplierForest_actual_034430

def g32p_supplierForest_node_122154 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_122154 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122154 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_154749 := by
  decide +kernel

theorem g32p_supplierForest_actual_122154 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122154) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 1 g32p_supplierForest_edge_122154
    g32p_supplierForest_actual_154749

def g32p_supplierForest_node_122171 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_122171 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122171 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120751 := by
  decide +kernel

theorem g32p_supplierForest_actual_122171 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122171) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_122171
    g32p_supplierForest_actual_120751

def g32p_supplierForest_node_122184 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_122184 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122184 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_041853 := by
  decide +kernel

theorem g32p_supplierForest_actual_122184 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122184) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_122184
    g32p_supplierForest_actual_041853

def g32p_supplierForest_node_122195 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_122195 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122195 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_117975 := by
  decide +kernel

theorem g32p_supplierForest_actual_122195 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122195) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_122195
    g32p_supplierForest_actual_117975

def g32p_supplierForest_node_122216 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_122216 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122216 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_106889 := by
  decide +kernel

theorem g32p_supplierForest_actual_122216 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122216) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_122216
    g32p_supplierForest_actual_106889

def g32p_supplierForest_node_122218 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_122218 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122218 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_127431 := by
  decide +kernel

theorem g32p_supplierForest_actual_122218 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122218) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_122218
    g32p_supplierForest_actual_127431

def g32p_supplierForest_node_122222 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122222 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122222 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122286 := by
  decide +kernel

theorem g32p_supplierForest_actual_122222 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122222) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_122222
    g32p_supplierForest_actual_122286

def g32p_supplierForest_node_122245 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122245 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122245 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_107777 := by
  decide +kernel

theorem g32p_supplierForest_actual_122245 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122245) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 1 g32p_supplierForest_edge_122245
    g32p_supplierForest_actual_107777

def g32p_supplierForest_node_122257 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_122257 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122257 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153218 := by
  decide +kernel

theorem g32p_supplierForest_actual_122257 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122257) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 1 g32p_supplierForest_edge_122257
    g32p_supplierForest_actual_153218

def g32p_supplierForest_node_122282 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_122282 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122282 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_154130 := by
  decide +kernel

theorem g32p_supplierForest_actual_122282 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122282) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 1 g32p_supplierForest_edge_122282
    g32p_supplierForest_actual_154130

def g32p_supplierForest_node_122312 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_122312 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122312 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_125379 := by
  decide +kernel

theorem g32p_supplierForest_actual_122312 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122312) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_122312
    g32p_supplierForest_actual_125379

def g32p_supplierForest_node_122315 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_122315 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122315 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127787 := by
  decide +kernel

theorem g32p_supplierForest_actual_122315 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122315) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_122315
    g32p_supplierForest_actual_127787

def g32p_supplierForest_node_122320 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_122320 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122320 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154938 := by
  decide +kernel

theorem g32p_supplierForest_actual_122320 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122320) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 2 g32p_supplierForest_edge_122320
    g32p_supplierForest_actual_154938

def g32p_supplierForest_node_122329 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_122329 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122329 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_106162 := by
  decide +kernel

theorem g32p_supplierForest_actual_122329 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122329) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 3 g32p_supplierForest_edge_122329
    g32p_supplierForest_actual_106162

def g32p_supplierForest_node_122338 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_122338 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122338 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_103688 := by
  decide +kernel

theorem g32p_supplierForest_actual_122338 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122338) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_122338
    g32p_supplierForest_actual_103688

def g32p_supplierForest_node_122341 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_122341 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122341 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122689 := by
  decide +kernel

theorem g32p_supplierForest_actual_122341 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122341) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_122341
    g32p_supplierForest_actual_122689

def g32p_supplierForest_node_122371 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122371 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122371 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_121260 := by
  decide +kernel

theorem g32p_supplierForest_actual_122371 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122371) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_122371
    g32p_supplierForest_actual_121260

def g32p_supplierForest_node_122387 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_122387 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122387 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122383 := by
  decide +kernel

theorem g32p_supplierForest_actual_122387 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122387) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_122387
    g32p_supplierForest_actual_122383

def g32p_supplierForest_node_122413 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122413 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122413 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_040156 := by
  decide +kernel

theorem g32p_supplierForest_actual_122413 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122413) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_122413
    g32p_supplierForest_actual_040156

def g32p_supplierForest_node_122450 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_122450 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122450 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_039552 := by
  decide +kernel

theorem g32p_supplierForest_actual_122450 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122450) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_122450
    g32p_supplierForest_actual_039552

def g32p_supplierForest_node_122458 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_122458 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122458 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_102004 := by
  decide +kernel

theorem g32p_supplierForest_actual_122458 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122458) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_122458
    g32p_supplierForest_actual_102004

def g32p_supplierForest_node_122471 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122471 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122471 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_125078 := by
  decide +kernel

theorem g32p_supplierForest_actual_122471 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122471) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_122471
    g32p_supplierForest_actual_125078

def g32p_supplierForest_node_122478 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_122478 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122478 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_034921 := by
  decide +kernel

theorem g32p_supplierForest_actual_122478 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122478) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 3 g32p_supplierForest_edge_122478
    g32p_supplierForest_actual_034921

def g32p_supplierForest_node_122524 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_122524 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122524 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_026172 := by
  decide +kernel

theorem g32p_supplierForest_actual_122524 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122524) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 1 g32p_supplierForest_edge_122524
    g32p_supplierForest_actual_026172

def g32p_supplierForest_node_122530 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_122530 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122530 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_103646 := by
  decide +kernel

theorem g32p_supplierForest_actual_122530 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122530) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_122530
    g32p_supplierForest_actual_103646

def g32p_supplierForest_node_122575 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_122575 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122575 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_104539 := by
  decide +kernel

theorem g32p_supplierForest_actual_122575 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122575) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_122575
    g32p_supplierForest_actual_104539

def g32p_supplierForest_node_122609 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122609 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122609 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_119438 := by
  decide +kernel

theorem g32p_supplierForest_actual_122609 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122609) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_122609
    g32p_supplierForest_actual_119438

def g32p_supplierForest_node_122627 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122627 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122627 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_032193 := by
  decide +kernel

theorem g32p_supplierForest_actual_122627 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122627) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 3 g32p_supplierForest_edge_122627
    g32p_supplierForest_actual_032193

def g32p_supplierForest_node_122667 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_122667 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122667 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_127668 := by
  decide +kernel

theorem g32p_supplierForest_actual_122667 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122667) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_122667
    g32p_supplierForest_actual_127668

def g32p_supplierForest_node_122698 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_122698 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122698 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_105069 := by
  decide +kernel

theorem g32p_supplierForest_actual_122698 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122698) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_122698
    g32p_supplierForest_actual_105069

def g32p_supplierForest_node_122714 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_122714 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122714 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_126090 := by
  decide +kernel

theorem g32p_supplierForest_actual_122714 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122714) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_122714
    g32p_supplierForest_actual_126090

def g32p_supplierForest_node_122717 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122717 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122717 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_114549 := by
  decide +kernel

theorem g32p_supplierForest_actual_122717 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122717) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_122717
    g32p_supplierForest_actual_114549

def g32p_supplierForest_node_122719 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_122719 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122719 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109232 := by
  decide +kernel

theorem g32p_supplierForest_actual_122719 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122719) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_122719
    g32p_supplierForest_actual_109232

def g32p_supplierForest_node_122726 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_122726 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122726 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_035568 := by
  decide +kernel

theorem g32p_supplierForest_actual_122726 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122726) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_122726
    g32p_supplierForest_actual_035568

def g32p_supplierForest_node_122731 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_122731 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122731 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_104823 := by
  decide +kernel

theorem g32p_supplierForest_actual_122731 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122731) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 1 g32p_supplierForest_edge_122731
    g32p_supplierForest_actual_104823

def g32p_supplierForest_node_122738 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_122738 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122738 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_107058 := by
  decide +kernel

theorem g32p_supplierForest_actual_122738 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122738) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_122738
    g32p_supplierForest_actual_107058

def g32p_supplierForest_node_122769 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_122769 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122769 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038267 := by
  decide +kernel

theorem g32p_supplierForest_actual_122769 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122769) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_122769
    g32p_supplierForest_actual_038267

def g32p_supplierForest_node_122771 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_122771 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122771 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_036020 := by
  decide +kernel

theorem g32p_supplierForest_actual_122771 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122771) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_122771
    g32p_supplierForest_actual_036020

def g32p_supplierForest_node_122796 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122796 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122796 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037445 := by
  decide +kernel

theorem g32p_supplierForest_actual_122796 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122796) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_122796
    g32p_supplierForest_actual_037445

def g32p_supplierForest_node_122817 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122817 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122817 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108558 := by
  decide +kernel

theorem g32p_supplierForest_actual_122817 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122817) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_122817
    g32p_supplierForest_actual_108558

def g32p_supplierForest_node_122857 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122857 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122857 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_040193 := by
  decide +kernel

theorem g32p_supplierForest_actual_122857 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122857) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_122857
    g32p_supplierForest_actual_040193

def g32p_supplierForest_node_122860 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122860 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122860 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112793 := by
  decide +kernel

theorem g32p_supplierForest_actual_122860 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122860) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_122860
    g32p_supplierForest_actual_112793

def g32p_supplierForest_node_122884 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_122884 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122884 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_104659 := by
  decide +kernel

theorem g32p_supplierForest_actual_122884 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122884) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_122884
    g32p_supplierForest_actual_104659

def g32p_supplierForest_node_122895 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_122895 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122895 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_035620 := by
  decide +kernel

theorem g32p_supplierForest_actual_122895 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122895) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_122895
    g32p_supplierForest_actual_035620

def g32p_supplierForest_node_122936 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122936 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122936 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122708 := by
  decide +kernel

theorem g32p_supplierForest_actual_122936 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122936) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_122936
    g32p_supplierForest_actual_122708

def g32p_supplierForest_node_122937 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122937 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122937 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_119695 := by
  decide +kernel

theorem g32p_supplierForest_actual_122937 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122937) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_122937
    g32p_supplierForest_actual_119695

def g32p_supplierForest_node_122953 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_122953 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122953 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112763 := by
  decide +kernel

theorem g32p_supplierForest_actual_122953 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122953) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_122953
    g32p_supplierForest_actual_112763

def g32p_supplierForest_node_122976 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122976 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122976 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_118570 := by
  decide +kernel

theorem g32p_supplierForest_actual_122976 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122976) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_122976
    g32p_supplierForest_actual_118570

def g32p_supplierForest_node_122979 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122979 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122979 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_036100 := by
  decide +kernel

theorem g32p_supplierForest_actual_122979 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122979) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_122979
    g32p_supplierForest_actual_036100

def g32p_supplierForest_node_123040 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_123040 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123040 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_040975 := by
  decide +kernel

theorem g32p_supplierForest_actual_123040 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123040) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_123040
    g32p_supplierForest_actual_040975

def g32p_supplierForest_node_123070 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_123070 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123070 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_041072 := by
  decide +kernel

theorem g32p_supplierForest_actual_123070 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123070) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_123070
    g32p_supplierForest_actual_041072

def g32p_supplierForest_node_123104 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123104 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123104 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_025485 := by
  decide +kernel

theorem g32p_supplierForest_actual_123104 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123104) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_123104
    g32p_supplierForest_actual_025485

def g32p_supplierForest_node_123107 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_123107 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123107 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_126948 := by
  decide +kernel

theorem g32p_supplierForest_actual_123107 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123107) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_123107
    g32p_supplierForest_actual_126948

def g32p_supplierForest_node_123150 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_123150 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123150 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_120951 := by
  decide +kernel

theorem g32p_supplierForest_actual_123150 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123150) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 0 g32p_supplierForest_edge_123150
    g32p_supplierForest_actual_120951

def g32p_supplierForest_node_123170 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_123170 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123170 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122083 := by
  decide +kernel

theorem g32p_supplierForest_actual_123170 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123170) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_123170
    g32p_supplierForest_actual_122083

def g32p_supplierForest_node_123178 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_123178 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123178 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_112423 := by
  decide +kernel

theorem g32p_supplierForest_actual_123178 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123178) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_123178
    g32p_supplierForest_actual_112423

def g32p_supplierForest_node_123181 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_123181 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123181 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_109501 := by
  decide +kernel

theorem g32p_supplierForest_actual_123181 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123181) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_123181
    g32p_supplierForest_actual_109501

def g32p_supplierForest_node_123206 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_123206 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123206 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152758 := by
  decide +kernel

theorem g32p_supplierForest_actual_123206 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123206) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_123206
    g32p_supplierForest_actual_152758

def g32p_supplierForest_node_123246 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_123246 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123246 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_119390 := by
  decide +kernel

theorem g32p_supplierForest_actual_123246 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123246) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_123246
    g32p_supplierForest_actual_119390

def g32p_supplierForest_node_123247 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_123247 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123247 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112958 := by
  decide +kernel

theorem g32p_supplierForest_actual_123247 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123247) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_123247
    g32p_supplierForest_actual_112958

def g32p_supplierForest_node_123259 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_123259 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123259 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104310 := by
  decide +kernel

theorem g32p_supplierForest_actual_123259 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123259) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_123259
    g32p_supplierForest_actual_104310

def g32p_supplierForest_node_123283 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123283 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123283 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152952 := by
  decide +kernel

theorem g32p_supplierForest_actual_123283 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123283) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_123283
    g32p_supplierForest_actual_152952

def g32p_supplierForest_node_123287 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123287 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123287 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_109197 := by
  decide +kernel

theorem g32p_supplierForest_actual_123287 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123287) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_123287
    g32p_supplierForest_actual_109197

def g32p_supplierForest_node_123328 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123328 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123328 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120182 := by
  decide +kernel

theorem g32p_supplierForest_actual_123328 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123328) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_123328
    g32p_supplierForest_actual_120182

def g32p_supplierForest_node_123335 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_123335 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123335 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108166 := by
  decide +kernel

theorem g32p_supplierForest_actual_123335 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123335) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_123335
    g32p_supplierForest_actual_108166

def g32p_supplierForest_node_123336 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_123336 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123336 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_039819 := by
  decide +kernel

theorem g32p_supplierForest_actual_123336 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123336) ∧
        IsConj g (g32p_literalRepresentative 65) := by
  exact g32p_archive_step_lift _ _ 65 3 g32p_supplierForest_edge_123336
    g32p_supplierForest_actual_039819

def g32p_supplierForest_node_123361 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_123361 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123361 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_032779 := by
  decide +kernel

theorem g32p_supplierForest_actual_123361 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123361) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_123361
    g32p_supplierForest_actual_032779

def g32p_supplierForest_node_123368 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123368 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123368 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_102599 := by
  decide +kernel

theorem g32p_supplierForest_actual_123368 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123368) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_123368
    g32p_supplierForest_actual_102599

def g32p_supplierForest_node_123371 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_123371 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123371 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_038824 := by
  decide +kernel

theorem g32p_supplierForest_actual_123371 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123371) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_123371
    g32p_supplierForest_actual_038824

def g32p_supplierForest_node_123373 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_123373 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123373 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_032842 := by
  decide +kernel

theorem g32p_supplierForest_actual_123373 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123373) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_123373
    g32p_supplierForest_actual_032842

def g32p_supplierForest_node_123402 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_123402 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123402 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_106764 := by
  decide +kernel

theorem g32p_supplierForest_actual_123402 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123402) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_123402
    g32p_supplierForest_actual_106764

def g32p_supplierForest_node_123456 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_123456 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123456 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123449 := by
  decide +kernel

theorem g32p_supplierForest_actual_123456 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123456) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_123456
    g32p_supplierForest_actual_123449

def g32p_supplierForest_node_123517 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_123517 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123517 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153008 := by
  decide +kernel

theorem g32p_supplierForest_actual_123517 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123517) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_123517
    g32p_supplierForest_actual_153008

def g32p_supplierForest_node_123579 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123579 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123579 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115148 := by
  decide +kernel

theorem g32p_supplierForest_actual_123579 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123579) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_123579
    g32p_supplierForest_actual_115148

def g32p_supplierForest_node_123599 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_123599 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123599 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153536 := by
  decide +kernel

theorem g32p_supplierForest_actual_123599 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123599) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 3 g32p_supplierForest_edge_123599
    g32p_supplierForest_actual_153536

def g32p_supplierForest_node_123605 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123605 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123605 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152846 := by
  decide +kernel

theorem g32p_supplierForest_actual_123605 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123605) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 0 g32p_supplierForest_edge_123605
    g32p_supplierForest_actual_152846

def g32p_supplierForest_node_123615 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_123615 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123615 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121261 := by
  decide +kernel

theorem g32p_supplierForest_actual_123615 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123615) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 1 g32p_supplierForest_edge_123615
    g32p_supplierForest_actual_121261

def g32p_supplierForest_node_123618 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_123618 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123618 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121260 := by
  decide +kernel

theorem g32p_supplierForest_actual_123618 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123618) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_123618
    g32p_supplierForest_actual_121260

def g32p_supplierForest_node_123656 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_123656 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123656 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037804 := by
  decide +kernel

theorem g32p_supplierForest_actual_123656 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123656) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_123656
    g32p_supplierForest_actual_037804

def g32p_supplierForest_node_123676 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_123676 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123676 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_033817 := by
  decide +kernel

theorem g32p_supplierForest_actual_123676 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123676) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 1 g32p_supplierForest_edge_123676
    g32p_supplierForest_actual_033817

def g32p_supplierForest_node_123682 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_123682 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123682 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120933 := by
  decide +kernel

theorem g32p_supplierForest_actual_123682 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123682) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_123682
    g32p_supplierForest_actual_120933

def g32p_supplierForest_node_123691 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_123691 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123691 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_111748 := by
  decide +kernel

theorem g32p_supplierForest_actual_123691 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123691) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_123691
    g32p_supplierForest_actual_111748

def g32p_supplierForest_node_123771 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_123771 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123771 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_124997 := by
  decide +kernel

theorem g32p_supplierForest_actual_123771 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123771) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_123771
    g32p_supplierForest_actual_124997

def g32p_supplierForest_node_123804 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_123804 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123804 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_111205 := by
  decide +kernel

theorem g32p_supplierForest_actual_123804 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123804) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_123804
    g32p_supplierForest_actual_111205

def g32p_supplierForest_node_123811 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123811 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123811 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118872 := by
  decide +kernel

theorem g32p_supplierForest_actual_123811 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123811) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_123811
    g32p_supplierForest_actual_118872

def g32p_supplierForest_node_123833 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_123833 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123833 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_035794 := by
  decide +kernel

theorem g32p_supplierForest_actual_123833 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123833) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 3 g32p_supplierForest_edge_123833
    g32p_supplierForest_actual_035794

def g32p_supplierForest_node_123868 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_123868 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123868 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122334 := by
  decide +kernel

theorem g32p_supplierForest_actual_123868 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123868) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_123868
    g32p_supplierForest_actual_122334

def g32p_supplierForest_node_123886 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123886 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123886 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_123125 := by
  decide +kernel

theorem g32p_supplierForest_actual_123886 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123886) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_123886
    g32p_supplierForest_actual_123125

def g32p_supplierForest_node_123890 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123890 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123890 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153107 := by
  decide +kernel

theorem g32p_supplierForest_actual_123890 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123890) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_123890
    g32p_supplierForest_actual_153107

def g32p_supplierForest_node_123919 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_123919 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123919 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154931 := by
  decide +kernel

theorem g32p_supplierForest_actual_123919 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123919) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 2 g32p_supplierForest_edge_123919
    g32p_supplierForest_actual_154931

def g32p_supplierForest_node_123927 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_123927 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123927 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_036136 := by
  decide +kernel

theorem g32p_supplierForest_actual_123927 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123927) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_123927
    g32p_supplierForest_actual_036136

def g32p_supplierForest_node_123966 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_123966 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123966 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_109210 := by
  decide +kernel

theorem g32p_supplierForest_actual_123966 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123966) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_123966
    g32p_supplierForest_actual_109210

def g32p_supplierForest_node_123993 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_123993 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123993 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153236 := by
  decide +kernel

theorem g32p_supplierForest_actual_123993 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123993) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_123993
    g32p_supplierForest_actual_153236

def g32p_supplierForest_node_124006 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_124006 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124006 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122286 := by
  decide +kernel

theorem g32p_supplierForest_actual_124006 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124006) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 1 g32p_supplierForest_edge_124006
    g32p_supplierForest_actual_122286

def g32p_supplierForest_node_124009 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_124009 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124009 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153248 := by
  decide +kernel

theorem g32p_supplierForest_actual_124009 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124009) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_124009
    g32p_supplierForest_actual_153248

def g32p_supplierForest_node_124029 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_124029 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124029 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_123834 := by
  decide +kernel

theorem g32p_supplierForest_actual_124029 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124029) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_124029
    g32p_supplierForest_actual_123834

def g32p_supplierForest_node_124069 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_124069 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124069 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127571 := by
  decide +kernel

theorem g32p_supplierForest_actual_124069 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124069) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_124069
    g32p_supplierForest_actual_127571

def g32p_supplierForest_node_124086 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_124086 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124086 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_037007 := by
  decide +kernel

theorem g32p_supplierForest_actual_124086 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124086) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_124086
    g32p_supplierForest_actual_037007

def g32p_supplierForest_node_124133 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124133 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124133 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_104483 := by
  decide +kernel

theorem g32p_supplierForest_actual_124133 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124133) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_124133
    g32p_supplierForest_actual_104483

def g32p_supplierForest_node_124149 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_124149 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124149 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_114284 := by
  decide +kernel

theorem g32p_supplierForest_actual_124149 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124149) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_124149
    g32p_supplierForest_actual_114284

def g32p_supplierForest_node_124151 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_124151 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124151 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122409 := by
  decide +kernel

theorem g32p_supplierForest_actual_124151 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124151) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_124151
    g32p_supplierForest_actual_122409

def g32p_supplierForest_node_124168 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124168 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124168 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_036822 := by
  decide +kernel

theorem g32p_supplierForest_actual_124168 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124168) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_124168
    g32p_supplierForest_actual_036822

def g32p_supplierForest_node_124173 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_124173 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124173 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122365 := by
  decide +kernel

theorem g32p_supplierForest_actual_124173 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124173) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_124173
    g32p_supplierForest_actual_122365

def g32p_supplierForest_node_124183 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_124183 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124183 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_123568 := by
  decide +kernel

theorem g32p_supplierForest_actual_124183 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124183) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_124183
    g32p_supplierForest_actual_123568

def g32p_supplierForest_node_124198 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124198 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124198 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043873 := by
  decide +kernel

theorem g32p_supplierForest_actual_124198 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124198) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_124198
    g32p_supplierForest_actual_043873

def g32p_supplierForest_node_124202 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124202 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124202 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118501 := by
  decide +kernel

theorem g32p_supplierForest_actual_124202 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124202) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_124202
    g32p_supplierForest_actual_118501

def g32p_supplierForest_node_124231 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_124231 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124231 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153047 := by
  decide +kernel

theorem g32p_supplierForest_actual_124231 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124231) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 0 g32p_supplierForest_edge_124231
    g32p_supplierForest_actual_153047

def g32p_supplierForest_node_124285 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_124285 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124285 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_103294 := by
  decide +kernel

theorem g32p_supplierForest_actual_124285 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124285) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_124285
    g32p_supplierForest_actual_103294

def g32p_supplierForest_node_124290 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_124290 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124290 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037617 := by
  decide +kernel

theorem g32p_supplierForest_actual_124290 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124290) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_124290
    g32p_supplierForest_actual_037617

def g32p_supplierForest_node_124306 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_124306 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124306 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153365 := by
  decide +kernel

theorem g32p_supplierForest_actual_124306 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124306) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 0 g32p_supplierForest_edge_124306
    g32p_supplierForest_actual_153365

def g32p_supplierForest_node_124353 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_124353 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124353 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_107984 := by
  decide +kernel

theorem g32p_supplierForest_actual_124353 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124353) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 0 g32p_supplierForest_edge_124353
    g32p_supplierForest_actual_107984

def g32p_supplierForest_node_124378 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_124378 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124378 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102143 := by
  decide +kernel

theorem g32p_supplierForest_actual_124378 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124378) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_124378
    g32p_supplierForest_actual_102143

def g32p_supplierForest_node_124423 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_124423 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124423 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_112035 := by
  decide +kernel

theorem g32p_supplierForest_actual_124423 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124423) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_124423
    g32p_supplierForest_actual_112035

def g32p_supplierForest_node_124457 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_124457 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124457 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_124444 := by
  decide +kernel

theorem g32p_supplierForest_actual_124457 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124457) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_124457
    g32p_supplierForest_actual_124444

def g32p_supplierForest_node_124468 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_124468 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124468 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_042075 := by
  decide +kernel

theorem g32p_supplierForest_actual_124468 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124468) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 1 g32p_supplierForest_edge_124468
    g32p_supplierForest_actual_042075

def g32p_supplierForest_node_124475 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_124475 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124475 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122965 := by
  decide +kernel

theorem g32p_supplierForest_actual_124475 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124475) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_124475
    g32p_supplierForest_actual_122965

def g32p_supplierForest_node_124476 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124476 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124476 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_105226 := by
  decide +kernel

theorem g32p_supplierForest_actual_124476 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124476) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_124476
    g32p_supplierForest_actual_105226

def g32p_supplierForest_node_124480 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_124480 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124480 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_125220 := by
  decide +kernel

theorem g32p_supplierForest_actual_124480 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124480) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 1 g32p_supplierForest_edge_124480
    g32p_supplierForest_actual_125220

def g32p_supplierForest_node_124485 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124485 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124485 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_041904 := by
  decide +kernel

theorem g32p_supplierForest_actual_124485 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124485) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 1 g32p_supplierForest_edge_124485
    g32p_supplierForest_actual_041904

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_072 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_083617 else g32p_supplierForest_node_083651) else (if i.val < 3 then g32p_supplierForest_node_083679 else g32p_supplierForest_node_083683)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_083691 else g32p_supplierForest_node_083717) else (if i.val < 7 then g32p_supplierForest_node_083727 else g32p_supplierForest_node_083729))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_083743 else g32p_supplierForest_node_083753) else (if i.val < 11 then g32p_supplierForest_node_083770 else g32p_supplierForest_node_083787)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_083794 else g32p_supplierForest_node_083820) else (if i.val < 15 then g32p_supplierForest_node_083839 else g32p_supplierForest_node_083857)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_083859 else g32p_supplierForest_node_083863) else (if i.val < 19 then g32p_supplierForest_node_083908 else g32p_supplierForest_node_083927)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_083964 else g32p_supplierForest_node_083979) else (if i.val < 23 then g32p_supplierForest_node_083992 else g32p_supplierForest_node_083995))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_084056 else g32p_supplierForest_node_084066) else (if i.val < 27 then g32p_supplierForest_node_084117 else g32p_supplierForest_node_084148)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_084149 else g32p_supplierForest_node_084204) else (if i.val < 31 then g32p_supplierForest_node_084210 else g32p_supplierForest_node_084217))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_084269 else g32p_supplierForest_node_084273) else (if i.val < 35 then g32p_supplierForest_node_084279 else g32p_supplierForest_node_084280)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_084328 else g32p_supplierForest_node_084332) else (if i.val < 39 then g32p_supplierForest_node_084334 else g32p_supplierForest_node_084342))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_084353 else g32p_supplierForest_node_084371) else (if i.val < 43 then g32p_supplierForest_node_084427 else g32p_supplierForest_node_084457)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_084521 else g32p_supplierForest_node_084522) else (if i.val < 47 then g32p_supplierForest_node_084525 else g32p_supplierForest_node_084527)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_084531 else g32p_supplierForest_node_084545) else (if i.val < 51 then g32p_supplierForest_node_084622 else g32p_supplierForest_node_084628)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_084632 else g32p_supplierForest_node_084635) else (if i.val < 55 then g32p_supplierForest_node_084642 else g32p_supplierForest_node_084650))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_084677 else g32p_supplierForest_node_084679) else (if i.val < 59 then g32p_supplierForest_node_084713 else g32p_supplierForest_node_084724)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_084736 else g32p_supplierForest_node_084741) else (if i.val < 63 then g32p_supplierForest_node_084751 else g32p_supplierForest_node_084755)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_084758 else g32p_supplierForest_node_084831) else (if i.val < 67 then g32p_supplierForest_node_084838 else g32p_supplierForest_node_084852)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_084857 else g32p_supplierForest_node_084892) else (if i.val < 71 then g32p_supplierForest_node_084903 else g32p_supplierForest_node_084905))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_084908 else g32p_supplierForest_node_084916) else (if i.val < 75 then g32p_supplierForest_node_084998 else g32p_supplierForest_node_085061)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_085081 else g32p_supplierForest_node_085093) else (if i.val < 79 then g32p_supplierForest_node_085097 else g32p_supplierForest_node_085098)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_085100 else g32p_supplierForest_node_085134) else (if i.val < 83 then g32p_supplierForest_node_085138 else g32p_supplierForest_node_085153)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_085166 else g32p_supplierForest_node_085167) else (if i.val < 87 then g32p_supplierForest_node_085173 else g32p_supplierForest_node_085176))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_085184 else g32p_supplierForest_node_085198) else (if i.val < 91 then g32p_supplierForest_node_085215 else g32p_supplierForest_node_085233)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_085240 else g32p_supplierForest_node_085241) else (if i.val < 95 then g32p_supplierForest_node_085245 else g32p_supplierForest_node_085265))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_085280 else g32p_supplierForest_node_085322) else (if i.val < 99 then g32p_supplierForest_node_085381 else g32p_supplierForest_node_085401)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_085421 else g32p_supplierForest_node_085439) else (if i.val < 103 then g32p_supplierForest_node_085443 else g32p_supplierForest_node_085456))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_085508 else g32p_supplierForest_node_085540) else (if i.val < 107 then g32p_supplierForest_node_085546 else g32p_supplierForest_node_085565)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_085570 else g32p_supplierForest_node_085583) else (if i.val < 111 then g32p_supplierForest_node_085612 else g32p_supplierForest_node_085637)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_085650 else g32p_supplierForest_node_085669) else (if i.val < 115 then g32p_supplierForest_node_085677 else g32p_supplierForest_node_085702)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_085706 else g32p_supplierForest_node_085739) else (if i.val < 119 then g32p_supplierForest_node_085745 else g32p_supplierForest_node_085746))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_085793 else g32p_supplierForest_node_085807) else (if i.val < 123 then g32p_supplierForest_node_085818 else g32p_supplierForest_node_085830)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_085835 else g32p_supplierForest_node_085895) else (if i.val < 127 then g32p_supplierForest_node_085897 else g32p_supplierForest_node_085898))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_085900 else g32p_supplierForest_node_085911) else (if i.val < 131 then g32p_supplierForest_node_085924 else g32p_supplierForest_node_085925)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_085930 else g32p_supplierForest_node_085941) else (if i.val < 135 then g32p_supplierForest_node_085950 else g32p_supplierForest_node_085964))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_085965 else g32p_supplierForest_node_085969) else (if i.val < 139 then g32p_supplierForest_node_085970 else g32p_supplierForest_node_085974)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_086039 else g32p_supplierForest_node_086047) else (if i.val < 143 then g32p_supplierForest_node_086077 else g32p_supplierForest_node_086120)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_086139 else g32p_supplierForest_node_086174) else (if i.val < 147 then g32p_supplierForest_node_086175 else g32p_supplierForest_node_086191)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_086198 else g32p_supplierForest_node_086228) else (if i.val < 151 then g32p_supplierForest_node_086258 else g32p_supplierForest_node_086292))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_086345 else g32p_supplierForest_node_086367) else (if i.val < 155 then g32p_supplierForest_node_086376 else g32p_supplierForest_node_086381)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_086407 else g32p_supplierForest_node_086420) else (if i.val < 159 then g32p_supplierForest_node_086469 else g32p_supplierForest_node_086473))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_086482 else g32p_supplierForest_node_086501) else (if i.val < 163 then g32p_supplierForest_node_086541 else g32p_supplierForest_node_086548)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_086561 else g32p_supplierForest_node_086573) else (if i.val < 167 then g32p_supplierForest_node_086583 else g32p_supplierForest_node_086602))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_086638 else g32p_supplierForest_node_086696) else (if i.val < 171 then g32p_supplierForest_node_086725 else g32p_supplierForest_node_086737)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_086749 else g32p_supplierForest_node_086750) else (if i.val < 175 then g32p_supplierForest_node_086751 else g32p_supplierForest_node_086756)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_086795 else g32p_supplierForest_node_086799) else (if i.val < 179 then g32p_supplierForest_node_086828 else g32p_supplierForest_node_086874)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_086887 else g32p_supplierForest_node_086906) else (if i.val < 183 then g32p_supplierForest_node_086923 else g32p_supplierForest_node_086952))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_086957 else g32p_supplierForest_node_086978) else (if i.val < 187 then g32p_supplierForest_node_086981 else g32p_supplierForest_node_087018)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_087038 else g32p_supplierForest_node_087042) else (if i.val < 191 then g32p_supplierForest_node_087050 else g32p_supplierForest_node_087119)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_087148 else g32p_supplierForest_node_087164) else (if i.val < 195 then g32p_supplierForest_node_087204 else g32p_supplierForest_node_087215)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_087266 else g32p_supplierForest_node_087270) else (if i.val < 199 then g32p_supplierForest_node_087307 else g32p_supplierForest_node_087308))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_087311 else g32p_supplierForest_node_087316) else (if i.val < 203 then g32p_supplierForest_node_087356 else g32p_supplierForest_node_087382)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_087384 else g32p_supplierForest_node_087438) else (if i.val < 207 then g32p_supplierForest_node_087457 else g32p_supplierForest_node_087460)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_087476 else g32p_supplierForest_node_087500) else (if i.val < 211 then g32p_supplierForest_node_087529 else g32p_supplierForest_node_087563)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_087603 else g32p_supplierForest_node_087628) else (if i.val < 215 then g32p_supplierForest_node_087643 else g32p_supplierForest_node_087655))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_087676 else g32p_supplierForest_node_087680) else (if i.val < 219 then g32p_supplierForest_node_087726 else g32p_supplierForest_node_087732)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_087738 else g32p_supplierForest_node_087754) else (if i.val < 223 then g32p_supplierForest_node_087757 else g32p_supplierForest_node_087794))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_087800 else g32p_supplierForest_node_087807) else (if i.val < 227 then g32p_supplierForest_node_087846 else g32p_supplierForest_node_087868)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_087893 else g32p_supplierForest_node_087917) else (if i.val < 231 then g32p_supplierForest_node_087927 else g32p_supplierForest_node_087971))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_087972 else g32p_supplierForest_node_088031) else (if i.val < 235 then g32p_supplierForest_node_088042 else g32p_supplierForest_node_088046)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_088052 else g32p_supplierForest_node_088055) else (if i.val < 239 then g32p_supplierForest_node_088056 else g32p_supplierForest_node_088108)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_088155 else g32p_supplierForest_node_088167) else (if i.val < 243 then g32p_supplierForest_node_088190 else g32p_supplierForest_node_088230)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_088255 else g32p_supplierForest_node_088264) else (if i.val < 247 then g32p_supplierForest_node_088274 else g32p_supplierForest_node_088292))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_088309 else g32p_supplierForest_node_088310) else (if i.val < 251 then g32p_supplierForest_node_088317 else g32p_supplierForest_node_088347)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_088359 else g32p_supplierForest_node_088374) else (if i.val < 255 then g32p_supplierForest_node_088391 else g32p_supplierForest_node_088402))))))))

def g32p_supplierForest_classes_072 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 49 else 49) else (if i.val < 3 then 49 else 84)) else (if i.val < 6 then (if i.val < 5 then 49 else 46) else (if i.val < 7 then 46 else 46))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 25 else 50) else (if i.val < 11 then 55 else 46)) else (if i.val < 14 then (if i.val < 13 then 46 else 49) else (if i.val < 15 then 13 else 46)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 13 else 54) else (if i.val < 19 then 46 else 12)) else (if i.val < 22 then (if i.val < 21 then 13 else 26) else (if i.val < 23 then 46 else 46))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 82 else 50) else (if i.val < 27 then 49 else 49)) else (if i.val < 30 then (if i.val < 29 then 46 else 54) else (if i.val < 31 then 46 else 46))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 50 else 49) else (if i.val < 35 then 82 else 84)) else (if i.val < 38 then (if i.val < 37 then 46 else 84) else (if i.val < 39 then 45 else 53))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 26 else 55) else (if i.val < 43 then 49 else 13)) else (if i.val < 46 then (if i.val < 45 then 50 else 11) else (if i.val < 47 then 85 else 50)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 83 else 53) else (if i.val < 51 then 49 else 9)) else (if i.val < 54 then (if i.val < 53 then 49 else 46) else (if i.val < 55 then 49 else 49))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 53 else 49) else (if i.val < 59 then 49 else 26)) else (if i.val < 62 then (if i.val < 61 then 26 else 50) else (if i.val < 63 then 49 else 52)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 50 else 10) else (if i.val < 67 then 50 else 46)) else (if i.val < 70 then (if i.val < 69 then 49 else 27) else (if i.val < 71 then 50 else 49))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 49 else 25) else (if i.val < 75 then 46 else 47)) else (if i.val < 78 then (if i.val < 77 then 84 else 47) else (if i.val < 79 then 56 else 81)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 47 else 46) else (if i.val < 83 then 48 else 46)) else (if i.val < 86 then (if i.val < 85 then 48 else 27) else (if i.val < 87 then 82 else 84))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 45 else 53) else (if i.val < 91 then 47 else 13)) else (if i.val < 94 then (if i.val < 93 then 45 else 46) else (if i.val < 95 then 84 else 49))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 49 else 46) else (if i.val < 99 then 11 else 47)) else (if i.val < 102 then (if i.val < 101 then 46 else 52) else (if i.val < 103 then 45 else 46))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 13 else 46) else (if i.val < 107 then 46 else 80)) else (if i.val < 110 then (if i.val < 109 then 27 else 55) else (if i.val < 111 then 46 else 26)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 46 else 8) else (if i.val < 115 then 84 else 84)) else (if i.val < 118 then (if i.val < 117 then 80 else 46) else (if i.val < 119 then 52 else 54))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 46 else 86) else (if i.val < 123 then 86 else 25)) else (if i.val < 126 then (if i.val < 125 then 45 else 48) else (if i.val < 127 then 46 else 50))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 12 else 45) else (if i.val < 131 then 47 else 49)) else (if i.val < 134 then (if i.val < 133 then 53 else 50) else (if i.val < 135 then 50 else 49))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 82 else 46) else (if i.val < 139 then 46 else 49)) else (if i.val < 142 then (if i.val < 141 then 26 else 46) else (if i.val < 143 then 80 else 52)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 46 else 13) else (if i.val < 147 then 45 else 50)) else (if i.val < 150 then (if i.val < 149 then 49 else 49) else (if i.val < 151 then 55 else 52))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 48 else 25) else (if i.val < 155 then 13 else 13)) else (if i.val < 158 then (if i.val < 157 then 49 else 46) else (if i.val < 159 then 26 else 83))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 25 else 26) else (if i.val < 163 then 26 else 84)) else (if i.val < 166 then (if i.val < 165 then 50 else 56) else (if i.val < 167 then 45 else 49))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 49 else 25) else (if i.val < 171 then 45 else 49)) else (if i.val < 174 then (if i.val < 173 then 50 else 13) else (if i.val < 175 then 25 else 49)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 13 else 55) else (if i.val < 179 then 45 else 50)) else (if i.val < 182 then (if i.val < 181 then 46 else 26) else (if i.val < 183 then 46 else 86))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 25 else 47) else (if i.val < 187 then 56 else 46)) else (if i.val < 190 then (if i.val < 189 then 48 else 47) else (if i.val < 191 then 49 else 84)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 80 else 52) else (if i.val < 195 then 50 else 13)) else (if i.val < 198 then (if i.val < 197 then 52 else 26) else (if i.val < 199 then 50 else 53))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 53 else 47) else (if i.val < 203 then 49 else 48)) else (if i.val < 206 then (if i.val < 205 then 49 else 46) else (if i.val < 207 then 86 else 86)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 13 else 53) else (if i.val < 211 then 53 else 26)) else (if i.val < 214 then (if i.val < 213 then 56 else 47) else (if i.val < 215 then 46 else 48))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 47 else 47) else (if i.val < 219 then 46 else 46)) else (if i.val < 222 then (if i.val < 221 then 46 else 48) else (if i.val < 223 then 47 else 53))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 46 else 55) else (if i.val < 227 then 46 else 49)) else (if i.val < 230 then (if i.val < 229 then 46 else 13) else (if i.val < 231 then 49 else 26))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 49 else 49) else (if i.val < 235 then 49 else 11)) else (if i.val < 238 then (if i.val < 237 then 46 else 12) else (if i.val < 239 then 84 else 26)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 46 else 49) else (if i.val < 243 then 46 else 13)) else (if i.val < 246 then (if i.val < 245 then 13 else 50) else (if i.val < 247 then 47 else 25))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 49 else 49) else (if i.val < 251 then 9 else 56)) else (if i.val < 254 then (if i.val < 253 then 50 else 46) else (if i.val < 255 then 46 else 51))))))))

theorem g32p_supplierForest_actual_072 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_072 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_072 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_083617
  · exact g32p_supplierForest_actual_083651
  · exact g32p_supplierForest_actual_083679
  · exact g32p_supplierForest_actual_083683
  · exact g32p_supplierForest_actual_083691
  · exact g32p_supplierForest_actual_083717
  · exact g32p_supplierForest_actual_083727
  · exact g32p_supplierForest_actual_083729
  · exact g32p_supplierForest_actual_083743
  · exact g32p_supplierForest_actual_083753
  · exact g32p_supplierForest_actual_083770
  · exact g32p_supplierForest_actual_083787
  · exact g32p_supplierForest_actual_083794
  · exact g32p_supplierForest_actual_083820
  · exact g32p_supplierForest_actual_083839
  · exact g32p_supplierForest_actual_083857
  · exact g32p_supplierForest_actual_083859
  · exact g32p_supplierForest_actual_083863
  · exact g32p_supplierForest_actual_083908
  · exact g32p_supplierForest_actual_083927
  · exact g32p_supplierForest_actual_083964
  · exact g32p_supplierForest_actual_083979
  · exact g32p_supplierForest_actual_083992
  · exact g32p_supplierForest_actual_083995
  · exact g32p_supplierForest_actual_084056
  · exact g32p_supplierForest_actual_084066
  · exact g32p_supplierForest_actual_084117
  · exact g32p_supplierForest_actual_084148
  · exact g32p_supplierForest_actual_084149
  · exact g32p_supplierForest_actual_084204
  · exact g32p_supplierForest_actual_084210
  · exact g32p_supplierForest_actual_084217
  · exact g32p_supplierForest_actual_084269
  · exact g32p_supplierForest_actual_084273
  · exact g32p_supplierForest_actual_084279
  · exact g32p_supplierForest_actual_084280
  · exact g32p_supplierForest_actual_084328
  · exact g32p_supplierForest_actual_084332
  · exact g32p_supplierForest_actual_084334
  · exact g32p_supplierForest_actual_084342
  · exact g32p_supplierForest_actual_084353
  · exact g32p_supplierForest_actual_084371
  · exact g32p_supplierForest_actual_084427
  · exact g32p_supplierForest_actual_084457
  · exact g32p_supplierForest_actual_084521
  · exact g32p_supplierForest_actual_084522
  · exact g32p_supplierForest_actual_084525
  · exact g32p_supplierForest_actual_084527
  · exact g32p_supplierForest_actual_084531
  · exact g32p_supplierForest_actual_084545
  · exact g32p_supplierForest_actual_084622
  · exact g32p_supplierForest_actual_084628
  · exact g32p_supplierForest_actual_084632
  · exact g32p_supplierForest_actual_084635
  · exact g32p_supplierForest_actual_084642
  · exact g32p_supplierForest_actual_084650
  · exact g32p_supplierForest_actual_084677
  · exact g32p_supplierForest_actual_084679
  · exact g32p_supplierForest_actual_084713
  · exact g32p_supplierForest_actual_084724
  · exact g32p_supplierForest_actual_084736
  · exact g32p_supplierForest_actual_084741
  · exact g32p_supplierForest_actual_084751
  · exact g32p_supplierForest_actual_084755
  · exact g32p_supplierForest_actual_084758
  · exact g32p_supplierForest_actual_084831
  · exact g32p_supplierForest_actual_084838
  · exact g32p_supplierForest_actual_084852
  · exact g32p_supplierForest_actual_084857
  · exact g32p_supplierForest_actual_084892
  · exact g32p_supplierForest_actual_084903
  · exact g32p_supplierForest_actual_084905
  · exact g32p_supplierForest_actual_084908
  · exact g32p_supplierForest_actual_084916
  · exact g32p_supplierForest_actual_084998
  · exact g32p_supplierForest_actual_085061
  · exact g32p_supplierForest_actual_085081
  · exact g32p_supplierForest_actual_085093
  · exact g32p_supplierForest_actual_085097
  · exact g32p_supplierForest_actual_085098
  · exact g32p_supplierForest_actual_085100
  · exact g32p_supplierForest_actual_085134
  · exact g32p_supplierForest_actual_085138
  · exact g32p_supplierForest_actual_085153
  · exact g32p_supplierForest_actual_085166
  · exact g32p_supplierForest_actual_085167
  · exact g32p_supplierForest_actual_085173
  · exact g32p_supplierForest_actual_085176
  · exact g32p_supplierForest_actual_085184
  · exact g32p_supplierForest_actual_085198
  · exact g32p_supplierForest_actual_085215
  · exact g32p_supplierForest_actual_085233
  · exact g32p_supplierForest_actual_085240
  · exact g32p_supplierForest_actual_085241
  · exact g32p_supplierForest_actual_085245
  · exact g32p_supplierForest_actual_085265
  · exact g32p_supplierForest_actual_085280
  · exact g32p_supplierForest_actual_085322
  · exact g32p_supplierForest_actual_085381
  · exact g32p_supplierForest_actual_085401
  · exact g32p_supplierForest_actual_085421
  · exact g32p_supplierForest_actual_085439
  · exact g32p_supplierForest_actual_085443
  · exact g32p_supplierForest_actual_085456
  · exact g32p_supplierForest_actual_085508
  · exact g32p_supplierForest_actual_085540
  · exact g32p_supplierForest_actual_085546
  · exact g32p_supplierForest_actual_085565
  · exact g32p_supplierForest_actual_085570
  · exact g32p_supplierForest_actual_085583
  · exact g32p_supplierForest_actual_085612
  · exact g32p_supplierForest_actual_085637
  · exact g32p_supplierForest_actual_085650
  · exact g32p_supplierForest_actual_085669
  · exact g32p_supplierForest_actual_085677
  · exact g32p_supplierForest_actual_085702
  · exact g32p_supplierForest_actual_085706
  · exact g32p_supplierForest_actual_085739
  · exact g32p_supplierForest_actual_085745
  · exact g32p_supplierForest_actual_085746
  · exact g32p_supplierForest_actual_085793
  · exact g32p_supplierForest_actual_085807
  · exact g32p_supplierForest_actual_085818
  · exact g32p_supplierForest_actual_085830
  · exact g32p_supplierForest_actual_085835
  · exact g32p_supplierForest_actual_085895
  · exact g32p_supplierForest_actual_085897
  · exact g32p_supplierForest_actual_085898
  · exact g32p_supplierForest_actual_085900
  · exact g32p_supplierForest_actual_085911
  · exact g32p_supplierForest_actual_085924
  · exact g32p_supplierForest_actual_085925
  · exact g32p_supplierForest_actual_085930
  · exact g32p_supplierForest_actual_085941
  · exact g32p_supplierForest_actual_085950
  · exact g32p_supplierForest_actual_085964
  · exact g32p_supplierForest_actual_085965
  · exact g32p_supplierForest_actual_085969
  · exact g32p_supplierForest_actual_085970
  · exact g32p_supplierForest_actual_085974
  · exact g32p_supplierForest_actual_086039
  · exact g32p_supplierForest_actual_086047
  · exact g32p_supplierForest_actual_086077
  · exact g32p_supplierForest_actual_086120
  · exact g32p_supplierForest_actual_086139
  · exact g32p_supplierForest_actual_086174
  · exact g32p_supplierForest_actual_086175
  · exact g32p_supplierForest_actual_086191
  · exact g32p_supplierForest_actual_086198
  · exact g32p_supplierForest_actual_086228
  · exact g32p_supplierForest_actual_086258
  · exact g32p_supplierForest_actual_086292
  · exact g32p_supplierForest_actual_086345
  · exact g32p_supplierForest_actual_086367
  · exact g32p_supplierForest_actual_086376
  · exact g32p_supplierForest_actual_086381
  · exact g32p_supplierForest_actual_086407
  · exact g32p_supplierForest_actual_086420
  · exact g32p_supplierForest_actual_086469
  · exact g32p_supplierForest_actual_086473
  · exact g32p_supplierForest_actual_086482
  · exact g32p_supplierForest_actual_086501
  · exact g32p_supplierForest_actual_086541
  · exact g32p_supplierForest_actual_086548
  · exact g32p_supplierForest_actual_086561
  · exact g32p_supplierForest_actual_086573
  · exact g32p_supplierForest_actual_086583
  · exact g32p_supplierForest_actual_086602
  · exact g32p_supplierForest_actual_086638
  · exact g32p_supplierForest_actual_086696
  · exact g32p_supplierForest_actual_086725
  · exact g32p_supplierForest_actual_086737
  · exact g32p_supplierForest_actual_086749
  · exact g32p_supplierForest_actual_086750
  · exact g32p_supplierForest_actual_086751
  · exact g32p_supplierForest_actual_086756
  · exact g32p_supplierForest_actual_086795
  · exact g32p_supplierForest_actual_086799
  · exact g32p_supplierForest_actual_086828
  · exact g32p_supplierForest_actual_086874
  · exact g32p_supplierForest_actual_086887
  · exact g32p_supplierForest_actual_086906
  · exact g32p_supplierForest_actual_086923
  · exact g32p_supplierForest_actual_086952
  · exact g32p_supplierForest_actual_086957
  · exact g32p_supplierForest_actual_086978
  · exact g32p_supplierForest_actual_086981
  · exact g32p_supplierForest_actual_087018
  · exact g32p_supplierForest_actual_087038
  · exact g32p_supplierForest_actual_087042
  · exact g32p_supplierForest_actual_087050
  · exact g32p_supplierForest_actual_087119
  · exact g32p_supplierForest_actual_087148
  · exact g32p_supplierForest_actual_087164
  · exact g32p_supplierForest_actual_087204
  · exact g32p_supplierForest_actual_087215
  · exact g32p_supplierForest_actual_087266
  · exact g32p_supplierForest_actual_087270
  · exact g32p_supplierForest_actual_087307
  · exact g32p_supplierForest_actual_087308
  · exact g32p_supplierForest_actual_087311
  · exact g32p_supplierForest_actual_087316
  · exact g32p_supplierForest_actual_087356
  · exact g32p_supplierForest_actual_087382
  · exact g32p_supplierForest_actual_087384
  · exact g32p_supplierForest_actual_087438
  · exact g32p_supplierForest_actual_087457
  · exact g32p_supplierForest_actual_087460
  · exact g32p_supplierForest_actual_087476
  · exact g32p_supplierForest_actual_087500
  · exact g32p_supplierForest_actual_087529
  · exact g32p_supplierForest_actual_087563
  · exact g32p_supplierForest_actual_087603
  · exact g32p_supplierForest_actual_087628
  · exact g32p_supplierForest_actual_087643
  · exact g32p_supplierForest_actual_087655
  · exact g32p_supplierForest_actual_087676
  · exact g32p_supplierForest_actual_087680
  · exact g32p_supplierForest_actual_087726
  · exact g32p_supplierForest_actual_087732
  · exact g32p_supplierForest_actual_087738
  · exact g32p_supplierForest_actual_087754
  · exact g32p_supplierForest_actual_087757
  · exact g32p_supplierForest_actual_087794
  · exact g32p_supplierForest_actual_087800
  · exact g32p_supplierForest_actual_087807
  · exact g32p_supplierForest_actual_087846
  · exact g32p_supplierForest_actual_087868
  · exact g32p_supplierForest_actual_087893
  · exact g32p_supplierForest_actual_087917
  · exact g32p_supplierForest_actual_087927
  · exact g32p_supplierForest_actual_087971
  · exact g32p_supplierForest_actual_087972
  · exact g32p_supplierForest_actual_088031
  · exact g32p_supplierForest_actual_088042
  · exact g32p_supplierForest_actual_088046
  · exact g32p_supplierForest_actual_088052
  · exact g32p_supplierForest_actual_088055
  · exact g32p_supplierForest_actual_088056
  · exact g32p_supplierForest_actual_088108
  · exact g32p_supplierForest_actual_088155
  · exact g32p_supplierForest_actual_088167
  · exact g32p_supplierForest_actual_088190
  · exact g32p_supplierForest_actual_088230
  · exact g32p_supplierForest_actual_088255
  · exact g32p_supplierForest_actual_088264
  · exact g32p_supplierForest_actual_088274
  · exact g32p_supplierForest_actual_088292
  · exact g32p_supplierForest_actual_088309
  · exact g32p_supplierForest_actual_088310
  · exact g32p_supplierForest_actual_088317
  · exact g32p_supplierForest_actual_088347
  · exact g32p_supplierForest_actual_088359
  · exact g32p_supplierForest_actual_088374
  · exact g32p_supplierForest_actual_088391
  · exact g32p_supplierForest_actual_088402

def g32p_supplierForest_nodes_073 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_088424 else g32p_supplierForest_node_088430) else (if i.val < 3 then g32p_supplierForest_node_088431 else g32p_supplierForest_node_088480)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_088485 else g32p_supplierForest_node_088517) else (if i.val < 7 then g32p_supplierForest_node_088576 else g32p_supplierForest_node_088580))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_088616 else g32p_supplierForest_node_088617) else (if i.val < 11 then g32p_supplierForest_node_088633 else g32p_supplierForest_node_088636)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_088641 else g32p_supplierForest_node_088654) else (if i.val < 15 then g32p_supplierForest_node_088665 else g32p_supplierForest_node_088697)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_088715 else g32p_supplierForest_node_088731) else (if i.val < 19 then g32p_supplierForest_node_088741 else g32p_supplierForest_node_088752)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_088769 else g32p_supplierForest_node_088778) else (if i.val < 23 then g32p_supplierForest_node_088793 else g32p_supplierForest_node_088846))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_088866 else g32p_supplierForest_node_088877) else (if i.val < 27 then g32p_supplierForest_node_088896 else g32p_supplierForest_node_088899)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_088966 else g32p_supplierForest_node_088987) else (if i.val < 31 then g32p_supplierForest_node_089065 else g32p_supplierForest_node_089067))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_089085 else g32p_supplierForest_node_089108) else (if i.val < 35 then g32p_supplierForest_node_089124 else g32p_supplierForest_node_089138)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_089148 else g32p_supplierForest_node_089178) else (if i.val < 39 then g32p_supplierForest_node_089179 else g32p_supplierForest_node_089183))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_089255 else g32p_supplierForest_node_089284) else (if i.val < 43 then g32p_supplierForest_node_089363 else g32p_supplierForest_node_089364)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_089382 else g32p_supplierForest_node_089389) else (if i.val < 47 then g32p_supplierForest_node_089415 else g32p_supplierForest_node_089423)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_089437 else g32p_supplierForest_node_089447) else (if i.val < 51 then g32p_supplierForest_node_089455 else g32p_supplierForest_node_089472)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_089522 else g32p_supplierForest_node_089528) else (if i.val < 55 then g32p_supplierForest_node_089535 else g32p_supplierForest_node_089540))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_089596 else g32p_supplierForest_node_089629) else (if i.val < 59 then g32p_supplierForest_node_089657 else g32p_supplierForest_node_089708)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_089721 else g32p_supplierForest_node_089725) else (if i.val < 63 then g32p_supplierForest_node_089732 else g32p_supplierForest_node_089801)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_089814 else g32p_supplierForest_node_089854) else (if i.val < 67 then g32p_supplierForest_node_089888 else g32p_supplierForest_node_089922)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_089929 else g32p_supplierForest_node_089941) else (if i.val < 71 then g32p_supplierForest_node_089985 else g32p_supplierForest_node_089997))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_090023 else g32p_supplierForest_node_090036) else (if i.val < 75 then g32p_supplierForest_node_090060 else g32p_supplierForest_node_090115)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_090181 else g32p_supplierForest_node_090190) else (if i.val < 79 then g32p_supplierForest_node_090193 else g32p_supplierForest_node_090202)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_090238 else g32p_supplierForest_node_090277) else (if i.val < 83 then g32p_supplierForest_node_090334 else g32p_supplierForest_node_090360)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_090383 else g32p_supplierForest_node_090424) else (if i.val < 87 then g32p_supplierForest_node_090457 else g32p_supplierForest_node_090477))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_090493 else g32p_supplierForest_node_090505) else (if i.val < 91 then g32p_supplierForest_node_090555 else g32p_supplierForest_node_090557)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_090559 else g32p_supplierForest_node_090564) else (if i.val < 95 then g32p_supplierForest_node_090578 else g32p_supplierForest_node_090602))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_090647 else g32p_supplierForest_node_090722) else (if i.val < 99 then g32p_supplierForest_node_090726 else g32p_supplierForest_node_090763)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_090766 else g32p_supplierForest_node_090775) else (if i.val < 103 then g32p_supplierForest_node_090794 else g32p_supplierForest_node_090796))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_090802 else g32p_supplierForest_node_090807) else (if i.val < 107 then g32p_supplierForest_node_090819 else g32p_supplierForest_node_090826)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_090836 else g32p_supplierForest_node_090857) else (if i.val < 111 then g32p_supplierForest_node_090874 else g32p_supplierForest_node_090884)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_090901 else g32p_supplierForest_node_090939) else (if i.val < 115 then g32p_supplierForest_node_090991 else g32p_supplierForest_node_091007)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_091021 else g32p_supplierForest_node_091027) else (if i.val < 119 then g32p_supplierForest_node_091028 else g32p_supplierForest_node_091030))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_091051 else g32p_supplierForest_node_091059) else (if i.val < 123 then g32p_supplierForest_node_091079 else g32p_supplierForest_node_091094)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_091107 else g32p_supplierForest_node_091125) else (if i.val < 127 then g32p_supplierForest_node_091151 else g32p_supplierForest_node_091157))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_091179 else g32p_supplierForest_node_091181) else (if i.val < 131 then g32p_supplierForest_node_091232 else g32p_supplierForest_node_091241)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_091339 else g32p_supplierForest_node_091346) else (if i.val < 135 then g32p_supplierForest_node_091358 else g32p_supplierForest_node_091379))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_091401 else g32p_supplierForest_node_091456) else (if i.val < 139 then g32p_supplierForest_node_091473 else g32p_supplierForest_node_091479)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_091482 else g32p_supplierForest_node_091486) else (if i.val < 143 then g32p_supplierForest_node_091526 else g32p_supplierForest_node_091542)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_091571 else g32p_supplierForest_node_091594) else (if i.val < 147 then g32p_supplierForest_node_091627 else g32p_supplierForest_node_091642)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_091643 else g32p_supplierForest_node_091650) else (if i.val < 151 then g32p_supplierForest_node_091713 else g32p_supplierForest_node_091742))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_091766 else g32p_supplierForest_node_091789) else (if i.val < 155 then g32p_supplierForest_node_091794 else g32p_supplierForest_node_091795)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_091888 else g32p_supplierForest_node_091926) else (if i.val < 159 then g32p_supplierForest_node_091932 else g32p_supplierForest_node_091938))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_091953 else g32p_supplierForest_node_091960) else (if i.val < 163 then g32p_supplierForest_node_091973 else g32p_supplierForest_node_091978)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_092001 else g32p_supplierForest_node_092042) else (if i.val < 167 then g32p_supplierForest_node_092044 else g32p_supplierForest_node_092056))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_092060 else g32p_supplierForest_node_092063) else (if i.val < 171 then g32p_supplierForest_node_092119 else g32p_supplierForest_node_092147)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_092172 else g32p_supplierForest_node_092199) else (if i.val < 175 then g32p_supplierForest_node_092233 else g32p_supplierForest_node_092234)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_092251 else g32p_supplierForest_node_092298) else (if i.val < 179 then g32p_supplierForest_node_092302 else g32p_supplierForest_node_092372)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_092414 else g32p_supplierForest_node_092423) else (if i.val < 183 then g32p_supplierForest_node_092435 else g32p_supplierForest_node_092475))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_092488 else g32p_supplierForest_node_092539) else (if i.val < 187 then g32p_supplierForest_node_092551 else g32p_supplierForest_node_092559)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_092578 else g32p_supplierForest_node_092606) else (if i.val < 191 then g32p_supplierForest_node_092618 else g32p_supplierForest_node_092642)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_092657 else g32p_supplierForest_node_092667) else (if i.val < 195 then g32p_supplierForest_node_092694 else g32p_supplierForest_node_092696)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_092698 else g32p_supplierForest_node_092766) else (if i.val < 199 then g32p_supplierForest_node_092789 else g32p_supplierForest_node_092812))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_092815 else g32p_supplierForest_node_092823) else (if i.val < 203 then g32p_supplierForest_node_092834 else g32p_supplierForest_node_092837)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_092852 else g32p_supplierForest_node_092867) else (if i.val < 207 then g32p_supplierForest_node_092890 else g32p_supplierForest_node_092926)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_092934 else g32p_supplierForest_node_092999) else (if i.val < 211 then g32p_supplierForest_node_093000 else g32p_supplierForest_node_093001)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_093020 else g32p_supplierForest_node_093025) else (if i.val < 215 then g32p_supplierForest_node_093035 else g32p_supplierForest_node_093040))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_093042 else g32p_supplierForest_node_093082) else (if i.val < 219 then g32p_supplierForest_node_093101 else g32p_supplierForest_node_093116)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_093128 else g32p_supplierForest_node_093131) else (if i.val < 223 then g32p_supplierForest_node_093136 else g32p_supplierForest_node_093145))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_093149 else g32p_supplierForest_node_093160) else (if i.val < 227 then g32p_supplierForest_node_093177 else g32p_supplierForest_node_093200)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_093225 else g32p_supplierForest_node_093264) else (if i.val < 231 then g32p_supplierForest_node_093272 else g32p_supplierForest_node_093288))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_093293 else g32p_supplierForest_node_093300) else (if i.val < 235 then g32p_supplierForest_node_093301 else g32p_supplierForest_node_093303)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_093305 else g32p_supplierForest_node_093325) else (if i.val < 239 then g32p_supplierForest_node_093327 else g32p_supplierForest_node_093350)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_093371 else g32p_supplierForest_node_093379) else (if i.val < 243 then g32p_supplierForest_node_093423 else g32p_supplierForest_node_093452)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_093468 else g32p_supplierForest_node_093517) else (if i.val < 247 then g32p_supplierForest_node_093530 else g32p_supplierForest_node_093535))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_093556 else g32p_supplierForest_node_093563) else (if i.val < 251 then g32p_supplierForest_node_093587 else g32p_supplierForest_node_093595)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_093629 else g32p_supplierForest_node_093637) else (if i.val < 255 then g32p_supplierForest_node_093713 else g32p_supplierForest_node_093727))))))))

def g32p_supplierForest_classes_073 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 82 else 12) else (if i.val < 3 then 46 else 46)) else (if i.val < 6 then (if i.val < 5 then 46 else 56) else (if i.val < 7 then 46 else 84))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 80 else 46) else (if i.val < 11 then 53 else 49)) else (if i.val < 14 then (if i.val < 13 then 26 else 55) else (if i.val < 15 then 50 else 49)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 46 else 46) else (if i.val < 19 then 46 else 26)) else (if i.val < 22 then (if i.val < 21 then 82 else 45) else (if i.val < 23 then 46 else 80))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 45 else 46) else (if i.val < 27 then 83 else 82)) else (if i.val < 30 then (if i.val < 29 then 84 else 27) else (if i.val < 31 then 80 else 46))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 84 else 46) else (if i.val < 35 then 49 else 55)) else (if i.val < 38 then (if i.val < 37 then 47 else 47) else (if i.val < 39 then 83 else 55))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 46 else 56) else (if i.val < 43 then 53 else 47)) else (if i.val < 46 then (if i.val < 45 then 81 else 49) else (if i.val < 47 then 50 else 26)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 49 else 47) else (if i.val < 51 then 47 else 46)) else (if i.val < 54 then (if i.val < 53 then 13 else 47) else (if i.val < 55 then 55 else 50))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 26 else 27) else (if i.val < 59 then 50 else 46)) else (if i.val < 62 then (if i.val < 61 then 46 else 45) else (if i.val < 63 then 84 else 50)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 48 else 47) else (if i.val < 67 then 86 else 49)) else (if i.val < 70 then (if i.val < 69 then 46 else 13) else (if i.val < 71 then 26 else 13))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 25 else 46) else (if i.val < 75 then 45 else 52)) else (if i.val < 78 then (if i.val < 77 then 26 else 83) else (if i.val < 79 then 11 else 26)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 26 else 49) else (if i.val < 83 then 13 else 54)) else (if i.val < 86 then (if i.val < 85 then 53 else 26) else (if i.val < 87 then 46 else 46))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 86 else 26) else (if i.val < 91 then 80 else 86)) else (if i.val < 94 then (if i.val < 93 then 46 else 46) else (if i.val < 95 then 46 else 82))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 13 else 26) else (if i.val < 99 then 49 else 50)) else (if i.val < 102 then (if i.val < 101 then 50 else 49) else (if i.val < 103 then 55 else 54))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 83 else 83) else (if i.val < 107 then 26 else 25)) else (if i.val < 110 then (if i.val < 109 then 82 else 13) else (if i.val < 111 then 26 else 85)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 55 else 9) else (if i.val < 115 then 46 else 84)) else (if i.val < 118 then (if i.val < 117 then 47 else 49) else (if i.val < 119 then 49 else 50))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 46 else 84) else (if i.val < 123 then 50 else 53)) else (if i.val < 126 then (if i.val < 125 then 49 else 27) else (if i.val < 127 then 52 else 47))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 50 else 26) else (if i.val < 131 then 49 else 45)) else (if i.val < 134 then (if i.val < 133 then 9 else 47) else (if i.val < 135 then 27 else 46))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 49 else 25) else (if i.val < 139 then 49 else 56)) else (if i.val < 142 then (if i.val < 141 then 49 else 47) else (if i.val < 143 then 49 else 50)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 47 else 50) else (if i.val < 147 then 86 else 13)) else (if i.val < 150 then (if i.val < 149 then 49 else 50) else (if i.val < 151 then 84 else 82))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 46 else 12) else (if i.val < 155 then 13 else 47)) else (if i.val < 158 then (if i.val < 157 then 49 else 13) else (if i.val < 159 then 13 else 50))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 56 else 47) else (if i.val < 163 then 50 else 49)) else (if i.val < 166 then (if i.val < 165 then 46 else 80) else (if i.val < 167 then 49 else 47))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 50 else 9) else (if i.val < 171 then 46 else 80)) else (if i.val < 174 then (if i.val < 173 then 26 else 46) else (if i.val < 175 then 50 else 49)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 49 else 9) else (if i.val < 179 then 85 else 80)) else (if i.val < 182 then (if i.val < 181 then 49 else 48) else (if i.val < 183 then 55 else 49))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 49 else 49) else (if i.val < 187 then 9 else 46)) else (if i.val < 190 then (if i.val < 189 then 9 else 52) else (if i.val < 191 then 46 else 25)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 46 else 25) else (if i.val < 195 then 49 else 25)) else (if i.val < 198 then (if i.val < 197 then 46 else 49) else (if i.val < 199 then 49 else 49))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 47 else 55) else (if i.val < 203 then 47 else 55)) else (if i.val < 206 then (if i.val < 205 then 49 else 47) else (if i.val < 207 then 47 else 49)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 49 else 45) else (if i.val < 211 then 45 else 55)) else (if i.val < 214 then (if i.val < 213 then 13 else 47) else (if i.val < 215 then 25 else 84))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 46 else 46) else (if i.val < 219 then 84 else 11)) else (if i.val < 222 then (if i.val < 221 then 53 else 25) else (if i.val < 223 then 56 else 52))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 46 else 45) else (if i.val < 227 then 49 else 53)) else (if i.val < 230 then (if i.val < 229 then 46 else 49) else (if i.val < 231 then 49 else 13))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 49 else 46) else (if i.val < 235 then 45 else 46)) else (if i.val < 238 then (if i.val < 237 then 86 else 9) else (if i.val < 239 then 80 else 26)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 46 else 49) else (if i.val < 243 then 46 else 49)) else (if i.val < 246 then (if i.val < 245 then 13 else 26) else (if i.val < 247 then 47 else 46))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 47 else 52) else (if i.val < 251 then 13 else 47)) else (if i.val < 254 then (if i.val < 253 then 82 else 26) else (if i.val < 255 then 13 else 50))))))))

theorem g32p_supplierForest_actual_073 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_073 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_073 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_088424
  · exact g32p_supplierForest_actual_088430
  · exact g32p_supplierForest_actual_088431
  · exact g32p_supplierForest_actual_088480
  · exact g32p_supplierForest_actual_088485
  · exact g32p_supplierForest_actual_088517
  · exact g32p_supplierForest_actual_088576
  · exact g32p_supplierForest_actual_088580
  · exact g32p_supplierForest_actual_088616
  · exact g32p_supplierForest_actual_088617
  · exact g32p_supplierForest_actual_088633
  · exact g32p_supplierForest_actual_088636
  · exact g32p_supplierForest_actual_088641
  · exact g32p_supplierForest_actual_088654
  · exact g32p_supplierForest_actual_088665
  · exact g32p_supplierForest_actual_088697
  · exact g32p_supplierForest_actual_088715
  · exact g32p_supplierForest_actual_088731
  · exact g32p_supplierForest_actual_088741
  · exact g32p_supplierForest_actual_088752
  · exact g32p_supplierForest_actual_088769
  · exact g32p_supplierForest_actual_088778
  · exact g32p_supplierForest_actual_088793
  · exact g32p_supplierForest_actual_088846
  · exact g32p_supplierForest_actual_088866
  · exact g32p_supplierForest_actual_088877
  · exact g32p_supplierForest_actual_088896
  · exact g32p_supplierForest_actual_088899
  · exact g32p_supplierForest_actual_088966
  · exact g32p_supplierForest_actual_088987
  · exact g32p_supplierForest_actual_089065
  · exact g32p_supplierForest_actual_089067
  · exact g32p_supplierForest_actual_089085
  · exact g32p_supplierForest_actual_089108
  · exact g32p_supplierForest_actual_089124
  · exact g32p_supplierForest_actual_089138
  · exact g32p_supplierForest_actual_089148
  · exact g32p_supplierForest_actual_089178
  · exact g32p_supplierForest_actual_089179
  · exact g32p_supplierForest_actual_089183
  · exact g32p_supplierForest_actual_089255
  · exact g32p_supplierForest_actual_089284
  · exact g32p_supplierForest_actual_089363
  · exact g32p_supplierForest_actual_089364
  · exact g32p_supplierForest_actual_089382
  · exact g32p_supplierForest_actual_089389
  · exact g32p_supplierForest_actual_089415
  · exact g32p_supplierForest_actual_089423
  · exact g32p_supplierForest_actual_089437
  · exact g32p_supplierForest_actual_089447
  · exact g32p_supplierForest_actual_089455
  · exact g32p_supplierForest_actual_089472
  · exact g32p_supplierForest_actual_089522
  · exact g32p_supplierForest_actual_089528
  · exact g32p_supplierForest_actual_089535
  · exact g32p_supplierForest_actual_089540
  · exact g32p_supplierForest_actual_089596
  · exact g32p_supplierForest_actual_089629
  · exact g32p_supplierForest_actual_089657
  · exact g32p_supplierForest_actual_089708
  · exact g32p_supplierForest_actual_089721
  · exact g32p_supplierForest_actual_089725
  · exact g32p_supplierForest_actual_089732
  · exact g32p_supplierForest_actual_089801
  · exact g32p_supplierForest_actual_089814
  · exact g32p_supplierForest_actual_089854
  · exact g32p_supplierForest_actual_089888
  · exact g32p_supplierForest_actual_089922
  · exact g32p_supplierForest_actual_089929
  · exact g32p_supplierForest_actual_089941
  · exact g32p_supplierForest_actual_089985
  · exact g32p_supplierForest_actual_089997
  · exact g32p_supplierForest_actual_090023
  · exact g32p_supplierForest_actual_090036
  · exact g32p_supplierForest_actual_090060
  · exact g32p_supplierForest_actual_090115
  · exact g32p_supplierForest_actual_090181
  · exact g32p_supplierForest_actual_090190
  · exact g32p_supplierForest_actual_090193
  · exact g32p_supplierForest_actual_090202
  · exact g32p_supplierForest_actual_090238
  · exact g32p_supplierForest_actual_090277
  · exact g32p_supplierForest_actual_090334
  · exact g32p_supplierForest_actual_090360
  · exact g32p_supplierForest_actual_090383
  · exact g32p_supplierForest_actual_090424
  · exact g32p_supplierForest_actual_090457
  · exact g32p_supplierForest_actual_090477
  · exact g32p_supplierForest_actual_090493
  · exact g32p_supplierForest_actual_090505
  · exact g32p_supplierForest_actual_090555
  · exact g32p_supplierForest_actual_090557
  · exact g32p_supplierForest_actual_090559
  · exact g32p_supplierForest_actual_090564
  · exact g32p_supplierForest_actual_090578
  · exact g32p_supplierForest_actual_090602
  · exact g32p_supplierForest_actual_090647
  · exact g32p_supplierForest_actual_090722
  · exact g32p_supplierForest_actual_090726
  · exact g32p_supplierForest_actual_090763
  · exact g32p_supplierForest_actual_090766
  · exact g32p_supplierForest_actual_090775
  · exact g32p_supplierForest_actual_090794
  · exact g32p_supplierForest_actual_090796
  · exact g32p_supplierForest_actual_090802
  · exact g32p_supplierForest_actual_090807
  · exact g32p_supplierForest_actual_090819
  · exact g32p_supplierForest_actual_090826
  · exact g32p_supplierForest_actual_090836
  · exact g32p_supplierForest_actual_090857
  · exact g32p_supplierForest_actual_090874
  · exact g32p_supplierForest_actual_090884
  · exact g32p_supplierForest_actual_090901
  · exact g32p_supplierForest_actual_090939
  · exact g32p_supplierForest_actual_090991
  · exact g32p_supplierForest_actual_091007
  · exact g32p_supplierForest_actual_091021
  · exact g32p_supplierForest_actual_091027
  · exact g32p_supplierForest_actual_091028
  · exact g32p_supplierForest_actual_091030
  · exact g32p_supplierForest_actual_091051
  · exact g32p_supplierForest_actual_091059
  · exact g32p_supplierForest_actual_091079
  · exact g32p_supplierForest_actual_091094
  · exact g32p_supplierForest_actual_091107
  · exact g32p_supplierForest_actual_091125
  · exact g32p_supplierForest_actual_091151
  · exact g32p_supplierForest_actual_091157
  · exact g32p_supplierForest_actual_091179
  · exact g32p_supplierForest_actual_091181
  · exact g32p_supplierForest_actual_091232
  · exact g32p_supplierForest_actual_091241
  · exact g32p_supplierForest_actual_091339
  · exact g32p_supplierForest_actual_091346
  · exact g32p_supplierForest_actual_091358
  · exact g32p_supplierForest_actual_091379
  · exact g32p_supplierForest_actual_091401
  · exact g32p_supplierForest_actual_091456
  · exact g32p_supplierForest_actual_091473
  · exact g32p_supplierForest_actual_091479
  · exact g32p_supplierForest_actual_091482
  · exact g32p_supplierForest_actual_091486
  · exact g32p_supplierForest_actual_091526
  · exact g32p_supplierForest_actual_091542
  · exact g32p_supplierForest_actual_091571
  · exact g32p_supplierForest_actual_091594
  · exact g32p_supplierForest_actual_091627
  · exact g32p_supplierForest_actual_091642
  · exact g32p_supplierForest_actual_091643
  · exact g32p_supplierForest_actual_091650
  · exact g32p_supplierForest_actual_091713
  · exact g32p_supplierForest_actual_091742
  · exact g32p_supplierForest_actual_091766
  · exact g32p_supplierForest_actual_091789
  · exact g32p_supplierForest_actual_091794
  · exact g32p_supplierForest_actual_091795
  · exact g32p_supplierForest_actual_091888
  · exact g32p_supplierForest_actual_091926
  · exact g32p_supplierForest_actual_091932
  · exact g32p_supplierForest_actual_091938
  · exact g32p_supplierForest_actual_091953
  · exact g32p_supplierForest_actual_091960
  · exact g32p_supplierForest_actual_091973
  · exact g32p_supplierForest_actual_091978
  · exact g32p_supplierForest_actual_092001
  · exact g32p_supplierForest_actual_092042
  · exact g32p_supplierForest_actual_092044
  · exact g32p_supplierForest_actual_092056
  · exact g32p_supplierForest_actual_092060
  · exact g32p_supplierForest_actual_092063
  · exact g32p_supplierForest_actual_092119
  · exact g32p_supplierForest_actual_092147
  · exact g32p_supplierForest_actual_092172
  · exact g32p_supplierForest_actual_092199
  · exact g32p_supplierForest_actual_092233
  · exact g32p_supplierForest_actual_092234
  · exact g32p_supplierForest_actual_092251
  · exact g32p_supplierForest_actual_092298
  · exact g32p_supplierForest_actual_092302
  · exact g32p_supplierForest_actual_092372
  · exact g32p_supplierForest_actual_092414
  · exact g32p_supplierForest_actual_092423
  · exact g32p_supplierForest_actual_092435
  · exact g32p_supplierForest_actual_092475
  · exact g32p_supplierForest_actual_092488
  · exact g32p_supplierForest_actual_092539
  · exact g32p_supplierForest_actual_092551
  · exact g32p_supplierForest_actual_092559
  · exact g32p_supplierForest_actual_092578
  · exact g32p_supplierForest_actual_092606
  · exact g32p_supplierForest_actual_092618
  · exact g32p_supplierForest_actual_092642
  · exact g32p_supplierForest_actual_092657
  · exact g32p_supplierForest_actual_092667
  · exact g32p_supplierForest_actual_092694
  · exact g32p_supplierForest_actual_092696
  · exact g32p_supplierForest_actual_092698
  · exact g32p_supplierForest_actual_092766
  · exact g32p_supplierForest_actual_092789
  · exact g32p_supplierForest_actual_092812
  · exact g32p_supplierForest_actual_092815
  · exact g32p_supplierForest_actual_092823
  · exact g32p_supplierForest_actual_092834
  · exact g32p_supplierForest_actual_092837
  · exact g32p_supplierForest_actual_092852
  · exact g32p_supplierForest_actual_092867
  · exact g32p_supplierForest_actual_092890
  · exact g32p_supplierForest_actual_092926
  · exact g32p_supplierForest_actual_092934
  · exact g32p_supplierForest_actual_092999
  · exact g32p_supplierForest_actual_093000
  · exact g32p_supplierForest_actual_093001
  · exact g32p_supplierForest_actual_093020
  · exact g32p_supplierForest_actual_093025
  · exact g32p_supplierForest_actual_093035
  · exact g32p_supplierForest_actual_093040
  · exact g32p_supplierForest_actual_093042
  · exact g32p_supplierForest_actual_093082
  · exact g32p_supplierForest_actual_093101
  · exact g32p_supplierForest_actual_093116
  · exact g32p_supplierForest_actual_093128
  · exact g32p_supplierForest_actual_093131
  · exact g32p_supplierForest_actual_093136
  · exact g32p_supplierForest_actual_093145
  · exact g32p_supplierForest_actual_093149
  · exact g32p_supplierForest_actual_093160
  · exact g32p_supplierForest_actual_093177
  · exact g32p_supplierForest_actual_093200
  · exact g32p_supplierForest_actual_093225
  · exact g32p_supplierForest_actual_093264
  · exact g32p_supplierForest_actual_093272
  · exact g32p_supplierForest_actual_093288
  · exact g32p_supplierForest_actual_093293
  · exact g32p_supplierForest_actual_093300
  · exact g32p_supplierForest_actual_093301
  · exact g32p_supplierForest_actual_093303
  · exact g32p_supplierForest_actual_093305
  · exact g32p_supplierForest_actual_093325
  · exact g32p_supplierForest_actual_093327
  · exact g32p_supplierForest_actual_093350
  · exact g32p_supplierForest_actual_093371
  · exact g32p_supplierForest_actual_093379
  · exact g32p_supplierForest_actual_093423
  · exact g32p_supplierForest_actual_093452
  · exact g32p_supplierForest_actual_093468
  · exact g32p_supplierForest_actual_093517
  · exact g32p_supplierForest_actual_093530
  · exact g32p_supplierForest_actual_093535
  · exact g32p_supplierForest_actual_093556
  · exact g32p_supplierForest_actual_093563
  · exact g32p_supplierForest_actual_093587
  · exact g32p_supplierForest_actual_093595
  · exact g32p_supplierForest_actual_093629
  · exact g32p_supplierForest_actual_093637
  · exact g32p_supplierForest_actual_093713
  · exact g32p_supplierForest_actual_093727

def g32p_supplierForest_nodes_074 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_093757 else g32p_supplierForest_node_093824) else (if i.val < 3 then g32p_supplierForest_node_093840 else g32p_supplierForest_node_093884)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_093894 else g32p_supplierForest_node_093904) else (if i.val < 7 then g32p_supplierForest_node_093918 else g32p_supplierForest_node_093927))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_093936 else g32p_supplierForest_node_093937) else (if i.val < 11 then g32p_supplierForest_node_093938 else g32p_supplierForest_node_093945)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_093952 else g32p_supplierForest_node_093954) else (if i.val < 15 then g32p_supplierForest_node_093962 else g32p_supplierForest_node_093964)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_093966 else g32p_supplierForest_node_093972) else (if i.val < 19 then g32p_supplierForest_node_093985 else g32p_supplierForest_node_093987)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_094022 else g32p_supplierForest_node_094032) else (if i.val < 23 then g32p_supplierForest_node_094053 else g32p_supplierForest_node_094116))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_094131 else g32p_supplierForest_node_094178) else (if i.val < 27 then g32p_supplierForest_node_094182 else g32p_supplierForest_node_094257)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_094261 else g32p_supplierForest_node_094263) else (if i.val < 31 then g32p_supplierForest_node_094265 else g32p_supplierForest_node_094279))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_094299 else g32p_supplierForest_node_094304) else (if i.val < 35 then g32p_supplierForest_node_094326 else g32p_supplierForest_node_094357)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_094373 else g32p_supplierForest_node_094395) else (if i.val < 39 then g32p_supplierForest_node_094411 else g32p_supplierForest_node_094480))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_094497 else g32p_supplierForest_node_094511) else (if i.val < 43 then g32p_supplierForest_node_094512 else g32p_supplierForest_node_094534)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_094556 else g32p_supplierForest_node_094561) else (if i.val < 47 then g32p_supplierForest_node_094615 else g32p_supplierForest_node_094664)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_094666 else g32p_supplierForest_node_094688) else (if i.val < 51 then g32p_supplierForest_node_094696 else g32p_supplierForest_node_094703)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_094711 else g32p_supplierForest_node_094733) else (if i.val < 55 then g32p_supplierForest_node_094739 else g32p_supplierForest_node_094742))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_094804 else g32p_supplierForest_node_094823) else (if i.val < 59 then g32p_supplierForest_node_094828 else g32p_supplierForest_node_094830)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_094832 else g32p_supplierForest_node_094862) else (if i.val < 63 then g32p_supplierForest_node_094864 else g32p_supplierForest_node_094879)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_094904 else g32p_supplierForest_node_094905) else (if i.val < 67 then g32p_supplierForest_node_094909 else g32p_supplierForest_node_094964)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_094973 else g32p_supplierForest_node_094996) else (if i.val < 71 then g32p_supplierForest_node_094999 else g32p_supplierForest_node_095014))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_095027 else g32p_supplierForest_node_095035) else (if i.val < 75 then g32p_supplierForest_node_095064 else g32p_supplierForest_node_095068)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_095108 else g32p_supplierForest_node_095150) else (if i.val < 79 then g32p_supplierForest_node_095156 else g32p_supplierForest_node_095174)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_095189 else g32p_supplierForest_node_095197) else (if i.val < 83 then g32p_supplierForest_node_095200 else g32p_supplierForest_node_095210)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_095213 else g32p_supplierForest_node_095246) else (if i.val < 87 then g32p_supplierForest_node_095259 else g32p_supplierForest_node_095260))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_095284 else g32p_supplierForest_node_095329) else (if i.val < 91 then g32p_supplierForest_node_095354 else g32p_supplierForest_node_095358)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_095367 else g32p_supplierForest_node_095383) else (if i.val < 95 then g32p_supplierForest_node_095411 else g32p_supplierForest_node_095434))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_095447 else g32p_supplierForest_node_095448) else (if i.val < 99 then g32p_supplierForest_node_095472 else g32p_supplierForest_node_095475)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_095549 else g32p_supplierForest_node_095565) else (if i.val < 103 then g32p_supplierForest_node_095583 else g32p_supplierForest_node_095615))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_095625 else g32p_supplierForest_node_095634) else (if i.val < 107 then g32p_supplierForest_node_095641 else g32p_supplierForest_node_095769)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_095806 else g32p_supplierForest_node_095899) else (if i.val < 111 then g32p_supplierForest_node_095904 else g32p_supplierForest_node_095953)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_095973 else g32p_supplierForest_node_096028) else (if i.val < 115 then g32p_supplierForest_node_096060 else g32p_supplierForest_node_096072)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_096084 else g32p_supplierForest_node_096100) else (if i.val < 119 then g32p_supplierForest_node_096125 else g32p_supplierForest_node_096147))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_096162 else g32p_supplierForest_node_096187) else (if i.val < 123 then g32p_supplierForest_node_096200 else g32p_supplierForest_node_096205)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_096211 else g32p_supplierForest_node_096221) else (if i.val < 127 then g32p_supplierForest_node_096231 else g32p_supplierForest_node_096257))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_096272 else g32p_supplierForest_node_096297) else (if i.val < 131 then g32p_supplierForest_node_096321 else g32p_supplierForest_node_096324)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_096328 else g32p_supplierForest_node_096339) else (if i.val < 135 then g32p_supplierForest_node_096341 else g32p_supplierForest_node_096350))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_096399 else g32p_supplierForest_node_096445) else (if i.val < 139 then g32p_supplierForest_node_096462 else g32p_supplierForest_node_096526)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_096527 else g32p_supplierForest_node_096553) else (if i.val < 143 then g32p_supplierForest_node_096591 else g32p_supplierForest_node_096604)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_096618 else g32p_supplierForest_node_096659) else (if i.val < 147 then g32p_supplierForest_node_096670 else g32p_supplierForest_node_096682)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_096743 else g32p_supplierForest_node_096753) else (if i.val < 151 then g32p_supplierForest_node_096764 else g32p_supplierForest_node_096809))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_096812 else g32p_supplierForest_node_096830) else (if i.val < 155 then g32p_supplierForest_node_096883 else g32p_supplierForest_node_096887)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_096920 else g32p_supplierForest_node_096929) else (if i.val < 159 then g32p_supplierForest_node_097006 else g32p_supplierForest_node_097037))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_097050 else g32p_supplierForest_node_097066) else (if i.val < 163 then g32p_supplierForest_node_097082 else g32p_supplierForest_node_097113)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_097127 else g32p_supplierForest_node_097212) else (if i.val < 167 then g32p_supplierForest_node_097322 else g32p_supplierForest_node_097342))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_097347 else g32p_supplierForest_node_097361) else (if i.val < 171 then g32p_supplierForest_node_097375 else g32p_supplierForest_node_097381)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_097403 else g32p_supplierForest_node_097422) else (if i.val < 175 then g32p_supplierForest_node_097437 else g32p_supplierForest_node_097462)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_097478 else g32p_supplierForest_node_097496) else (if i.val < 179 then g32p_supplierForest_node_097517 else g32p_supplierForest_node_097526)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_097533 else g32p_supplierForest_node_097580) else (if i.val < 183 then g32p_supplierForest_node_097583 else g32p_supplierForest_node_097595))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_097598 else g32p_supplierForest_node_097599) else (if i.val < 187 then g32p_supplierForest_node_097617 else g32p_supplierForest_node_097620)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_097648 else g32p_supplierForest_node_097674) else (if i.val < 191 then g32p_supplierForest_node_097681 else g32p_supplierForest_node_097754)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_097761 else g32p_supplierForest_node_097774) else (if i.val < 195 then g32p_supplierForest_node_097778 else g32p_supplierForest_node_097797)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_097812 else g32p_supplierForest_node_097858) else (if i.val < 199 then g32p_supplierForest_node_097861 else g32p_supplierForest_node_097985))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_097998 else g32p_supplierForest_node_098054) else (if i.val < 203 then g32p_supplierForest_node_098092 else g32p_supplierForest_node_098119)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_098143 else g32p_supplierForest_node_098144) else (if i.val < 207 then g32p_supplierForest_node_098154 else g32p_supplierForest_node_098162)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_098175 else g32p_supplierForest_node_098187) else (if i.val < 211 then g32p_supplierForest_node_098188 else g32p_supplierForest_node_098193)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_098218 else g32p_supplierForest_node_098306) else (if i.val < 215 then g32p_supplierForest_node_098418 else g32p_supplierForest_node_098423))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_098438 else g32p_supplierForest_node_098444) else (if i.val < 219 then g32p_supplierForest_node_098451 else g32p_supplierForest_node_098453)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_098458 else g32p_supplierForest_node_098461) else (if i.val < 223 then g32p_supplierForest_node_098472 else g32p_supplierForest_node_098483))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_098532 else g32p_supplierForest_node_098569) else (if i.val < 227 then g32p_supplierForest_node_098575 else g32p_supplierForest_node_098584)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_098589 else g32p_supplierForest_node_098590) else (if i.val < 231 then g32p_supplierForest_node_098593 else g32p_supplierForest_node_098608))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_098620 else g32p_supplierForest_node_098623) else (if i.val < 235 then g32p_supplierForest_node_098685 else g32p_supplierForest_node_098721)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_098729 else g32p_supplierForest_node_098777) else (if i.val < 239 then g32p_supplierForest_node_098830 else g32p_supplierForest_node_098832)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_098862 else g32p_supplierForest_node_098864) else (if i.val < 243 then g32p_supplierForest_node_098889 else g32p_supplierForest_node_098900)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_098904 else g32p_supplierForest_node_098923) else (if i.val < 247 then g32p_supplierForest_node_098948 else g32p_supplierForest_node_098949))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_098966 else g32p_supplierForest_node_098984) else (if i.val < 251 then g32p_supplierForest_node_098988 else g32p_supplierForest_node_098998)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_099015 else g32p_supplierForest_node_099021) else (if i.val < 255 then g32p_supplierForest_node_099063 else g32p_supplierForest_node_099067))))))))

def g32p_supplierForest_classes_074 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 46 else 49) else (if i.val < 3 then 46 else 46)) else (if i.val < 6 then (if i.val < 5 then 53 else 56) else (if i.val < 7 then 50 else 46))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 53 else 80) else (if i.val < 11 then 46 else 47)) else (if i.val < 14 then (if i.val < 13 then 47 else 84) else (if i.val < 15 then 11 else 49)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 49 else 46) else (if i.val < 19 then 49 else 47)) else (if i.val < 22 then (if i.val < 21 then 46 else 54) else (if i.val < 23 then 26 else 81))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 46 else 54) else (if i.val < 27 then 52 else 55)) else (if i.val < 30 then (if i.val < 29 then 84 else 46) else (if i.val < 31 then 48 else 80))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 55 else 80) else (if i.val < 35 then 50 else 49)) else (if i.val < 38 then (if i.val < 37 then 46 else 49) else (if i.val < 39 then 46 else 49))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 49 else 46) else (if i.val < 43 then 53 else 84)) else (if i.val < 46 then (if i.val < 45 then 45 else 25) else (if i.val < 47 then 46 else 49)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 13 else 26) else (if i.val < 51 then 25 else 86)) else (if i.val < 54 then (if i.val < 53 then 8 else 25) else (if i.val < 55 then 50 else 25))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 49 else 84) else (if i.val < 59 then 13 else 49)) else (if i.val < 62 then (if i.val < 61 then 26 else 49) else (if i.val < 63 then 46 else 26)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 47 else 81) else (if i.val < 67 then 47 else 55)) else (if i.val < 70 then (if i.val < 69 then 11 else 11) else (if i.val < 71 then 25 else 84))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 46 else 25) else (if i.val < 75 then 54 else 46)) else (if i.val < 78 then (if i.val < 77 then 25 else 25) else (if i.val < 79 then 53 else 86)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 27 else 50) else (if i.val < 83 then 46 else 56)) else (if i.val < 86 then (if i.val < 85 then 56 else 49) else (if i.val < 87 then 46 else 11))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 9 else 26) else (if i.val < 91 then 50 else 82)) else (if i.val < 94 then (if i.val < 93 then 13 else 45) else (if i.val < 95 then 49 else 27))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 49 else 25) else (if i.val < 99 then 52 else 47)) else (if i.val < 102 then (if i.val < 101 then 49 else 50) else (if i.val < 103 then 86 else 46))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 46 else 13) else (if i.val < 107 then 56 else 26)) else (if i.val < 110 then (if i.val < 109 then 49 else 26) else (if i.val < 111 then 46 else 26)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 46 else 54) else (if i.val < 115 then 12 else 84)) else (if i.val < 118 then (if i.val < 117 then 49 else 85) else (if i.val < 119 then 47 else 46))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 84 else 83) else (if i.val < 123 then 46 else 46)) else (if i.val < 126 then (if i.val < 125 then 84 else 26) else (if i.val < 127 then 46 else 26))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 49 else 53) else (if i.val < 131 then 52 else 46)) else (if i.val < 134 then (if i.val < 133 then 45 else 45) else (if i.val < 135 then 9 else 50))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 25 else 52) else (if i.val < 139 then 86 else 46)) else (if i.val < 142 then (if i.val < 141 then 26 else 84) else (if i.val < 143 then 53 else 26)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 84 else 26) else (if i.val < 147 then 26 else 84)) else (if i.val < 150 then (if i.val < 149 then 50 else 49) else (if i.val < 151 then 46 else 49))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 53 else 25) else (if i.val < 155 then 81 else 49)) else (if i.val < 158 then (if i.val < 157 then 50 else 46) else (if i.val < 159 then 80 else 46))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 49 else 55) else (if i.val < 163 then 46 else 47)) else (if i.val < 166 then (if i.val < 165 then 56 else 53) else (if i.val < 167 then 26 else 26))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 53 else 46) else (if i.val < 171 then 26 else 49)) else (if i.val < 174 then (if i.val < 173 then 13 else 54) else (if i.val < 175 then 49 else 49)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 49 else 46) else (if i.val < 179 then 45 else 47)) else (if i.val < 182 then (if i.val < 181 then 25 else 49) else (if i.val < 183 then 54 else 12))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 13 else 50) else (if i.val < 187 then 81 else 80)) else (if i.val < 190 then (if i.val < 189 then 49 else 86) else (if i.val < 191 then 50 else 47)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 9 else 86) else (if i.val < 195 then 49 else 49)) else (if i.val < 198 then (if i.val < 197 then 26 else 49) else (if i.val < 199 then 26 else 83))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 50 else 26) else (if i.val < 203 then 55 else 46)) else (if i.val < 206 then (if i.val < 205 then 27 else 80) else (if i.val < 207 then 55 else 48)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 46 else 49) else (if i.val < 211 then 51 else 49)) else (if i.val < 214 then (if i.val < 213 then 52 else 55) else (if i.val < 215 then 55 else 49))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 50 else 49) else (if i.val < 219 then 49 else 55)) else (if i.val < 222 then (if i.val < 221 then 53 else 47) else (if i.val < 223 then 49 else 54))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 86 else 46) else (if i.val < 227 then 46 else 55)) else (if i.val < 230 then (if i.val < 229 then 81 else 53) else (if i.val < 231 then 55 else 85))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 26 else 46) else (if i.val < 235 then 47 else 49)) else (if i.val < 238 then (if i.val < 237 then 49 else 54) else (if i.val < 239 then 49 else 80)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 56 else 47) else (if i.val < 243 then 85 else 46)) else (if i.val < 246 then (if i.val < 245 then 84 else 25) else (if i.val < 247 then 55 else 49))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 84 else 47) else (if i.val < 251 then 25 else 49)) else (if i.val < 254 then (if i.val < 253 then 25 else 53) else (if i.val < 255 then 53 else 50))))))))

theorem g32p_supplierForest_actual_074 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_074 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_074 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_093757
  · exact g32p_supplierForest_actual_093824
  · exact g32p_supplierForest_actual_093840
  · exact g32p_supplierForest_actual_093884
  · exact g32p_supplierForest_actual_093894
  · exact g32p_supplierForest_actual_093904
  · exact g32p_supplierForest_actual_093918
  · exact g32p_supplierForest_actual_093927
  · exact g32p_supplierForest_actual_093936
  · exact g32p_supplierForest_actual_093937
  · exact g32p_supplierForest_actual_093938
  · exact g32p_supplierForest_actual_093945
  · exact g32p_supplierForest_actual_093952
  · exact g32p_supplierForest_actual_093954
  · exact g32p_supplierForest_actual_093962
  · exact g32p_supplierForest_actual_093964
  · exact g32p_supplierForest_actual_093966
  · exact g32p_supplierForest_actual_093972
  · exact g32p_supplierForest_actual_093985
  · exact g32p_supplierForest_actual_093987
  · exact g32p_supplierForest_actual_094022
  · exact g32p_supplierForest_actual_094032
  · exact g32p_supplierForest_actual_094053
  · exact g32p_supplierForest_actual_094116
  · exact g32p_supplierForest_actual_094131
  · exact g32p_supplierForest_actual_094178
  · exact g32p_supplierForest_actual_094182
  · exact g32p_supplierForest_actual_094257
  · exact g32p_supplierForest_actual_094261
  · exact g32p_supplierForest_actual_094263
  · exact g32p_supplierForest_actual_094265
  · exact g32p_supplierForest_actual_094279
  · exact g32p_supplierForest_actual_094299
  · exact g32p_supplierForest_actual_094304
  · exact g32p_supplierForest_actual_094326
  · exact g32p_supplierForest_actual_094357
  · exact g32p_supplierForest_actual_094373
  · exact g32p_supplierForest_actual_094395
  · exact g32p_supplierForest_actual_094411
  · exact g32p_supplierForest_actual_094480
  · exact g32p_supplierForest_actual_094497
  · exact g32p_supplierForest_actual_094511
  · exact g32p_supplierForest_actual_094512
  · exact g32p_supplierForest_actual_094534
  · exact g32p_supplierForest_actual_094556
  · exact g32p_supplierForest_actual_094561
  · exact g32p_supplierForest_actual_094615
  · exact g32p_supplierForest_actual_094664
  · exact g32p_supplierForest_actual_094666
  · exact g32p_supplierForest_actual_094688
  · exact g32p_supplierForest_actual_094696
  · exact g32p_supplierForest_actual_094703
  · exact g32p_supplierForest_actual_094711
  · exact g32p_supplierForest_actual_094733
  · exact g32p_supplierForest_actual_094739
  · exact g32p_supplierForest_actual_094742
  · exact g32p_supplierForest_actual_094804
  · exact g32p_supplierForest_actual_094823
  · exact g32p_supplierForest_actual_094828
  · exact g32p_supplierForest_actual_094830
  · exact g32p_supplierForest_actual_094832
  · exact g32p_supplierForest_actual_094862
  · exact g32p_supplierForest_actual_094864
  · exact g32p_supplierForest_actual_094879
  · exact g32p_supplierForest_actual_094904
  · exact g32p_supplierForest_actual_094905
  · exact g32p_supplierForest_actual_094909
  · exact g32p_supplierForest_actual_094964
  · exact g32p_supplierForest_actual_094973
  · exact g32p_supplierForest_actual_094996
  · exact g32p_supplierForest_actual_094999
  · exact g32p_supplierForest_actual_095014
  · exact g32p_supplierForest_actual_095027
  · exact g32p_supplierForest_actual_095035
  · exact g32p_supplierForest_actual_095064
  · exact g32p_supplierForest_actual_095068
  · exact g32p_supplierForest_actual_095108
  · exact g32p_supplierForest_actual_095150
  · exact g32p_supplierForest_actual_095156
  · exact g32p_supplierForest_actual_095174
  · exact g32p_supplierForest_actual_095189
  · exact g32p_supplierForest_actual_095197
  · exact g32p_supplierForest_actual_095200
  · exact g32p_supplierForest_actual_095210
  · exact g32p_supplierForest_actual_095213
  · exact g32p_supplierForest_actual_095246
  · exact g32p_supplierForest_actual_095259
  · exact g32p_supplierForest_actual_095260
  · exact g32p_supplierForest_actual_095284
  · exact g32p_supplierForest_actual_095329
  · exact g32p_supplierForest_actual_095354
  · exact g32p_supplierForest_actual_095358
  · exact g32p_supplierForest_actual_095367
  · exact g32p_supplierForest_actual_095383
  · exact g32p_supplierForest_actual_095411
  · exact g32p_supplierForest_actual_095434
  · exact g32p_supplierForest_actual_095447
  · exact g32p_supplierForest_actual_095448
  · exact g32p_supplierForest_actual_095472
  · exact g32p_supplierForest_actual_095475
  · exact g32p_supplierForest_actual_095549
  · exact g32p_supplierForest_actual_095565
  · exact g32p_supplierForest_actual_095583
  · exact g32p_supplierForest_actual_095615
  · exact g32p_supplierForest_actual_095625
  · exact g32p_supplierForest_actual_095634
  · exact g32p_supplierForest_actual_095641
  · exact g32p_supplierForest_actual_095769
  · exact g32p_supplierForest_actual_095806
  · exact g32p_supplierForest_actual_095899
  · exact g32p_supplierForest_actual_095904
  · exact g32p_supplierForest_actual_095953
  · exact g32p_supplierForest_actual_095973
  · exact g32p_supplierForest_actual_096028
  · exact g32p_supplierForest_actual_096060
  · exact g32p_supplierForest_actual_096072
  · exact g32p_supplierForest_actual_096084
  · exact g32p_supplierForest_actual_096100
  · exact g32p_supplierForest_actual_096125
  · exact g32p_supplierForest_actual_096147
  · exact g32p_supplierForest_actual_096162
  · exact g32p_supplierForest_actual_096187
  · exact g32p_supplierForest_actual_096200
  · exact g32p_supplierForest_actual_096205
  · exact g32p_supplierForest_actual_096211
  · exact g32p_supplierForest_actual_096221
  · exact g32p_supplierForest_actual_096231
  · exact g32p_supplierForest_actual_096257
  · exact g32p_supplierForest_actual_096272
  · exact g32p_supplierForest_actual_096297
  · exact g32p_supplierForest_actual_096321
  · exact g32p_supplierForest_actual_096324
  · exact g32p_supplierForest_actual_096328
  · exact g32p_supplierForest_actual_096339
  · exact g32p_supplierForest_actual_096341
  · exact g32p_supplierForest_actual_096350
  · exact g32p_supplierForest_actual_096399
  · exact g32p_supplierForest_actual_096445
  · exact g32p_supplierForest_actual_096462
  · exact g32p_supplierForest_actual_096526
  · exact g32p_supplierForest_actual_096527
  · exact g32p_supplierForest_actual_096553
  · exact g32p_supplierForest_actual_096591
  · exact g32p_supplierForest_actual_096604
  · exact g32p_supplierForest_actual_096618
  · exact g32p_supplierForest_actual_096659
  · exact g32p_supplierForest_actual_096670
  · exact g32p_supplierForest_actual_096682
  · exact g32p_supplierForest_actual_096743
  · exact g32p_supplierForest_actual_096753
  · exact g32p_supplierForest_actual_096764
  · exact g32p_supplierForest_actual_096809
  · exact g32p_supplierForest_actual_096812
  · exact g32p_supplierForest_actual_096830
  · exact g32p_supplierForest_actual_096883
  · exact g32p_supplierForest_actual_096887
  · exact g32p_supplierForest_actual_096920
  · exact g32p_supplierForest_actual_096929
  · exact g32p_supplierForest_actual_097006
  · exact g32p_supplierForest_actual_097037
  · exact g32p_supplierForest_actual_097050
  · exact g32p_supplierForest_actual_097066
  · exact g32p_supplierForest_actual_097082
  · exact g32p_supplierForest_actual_097113
  · exact g32p_supplierForest_actual_097127
  · exact g32p_supplierForest_actual_097212
  · exact g32p_supplierForest_actual_097322
  · exact g32p_supplierForest_actual_097342
  · exact g32p_supplierForest_actual_097347
  · exact g32p_supplierForest_actual_097361
  · exact g32p_supplierForest_actual_097375
  · exact g32p_supplierForest_actual_097381
  · exact g32p_supplierForest_actual_097403
  · exact g32p_supplierForest_actual_097422
  · exact g32p_supplierForest_actual_097437
  · exact g32p_supplierForest_actual_097462
  · exact g32p_supplierForest_actual_097478
  · exact g32p_supplierForest_actual_097496
  · exact g32p_supplierForest_actual_097517
  · exact g32p_supplierForest_actual_097526
  · exact g32p_supplierForest_actual_097533
  · exact g32p_supplierForest_actual_097580
  · exact g32p_supplierForest_actual_097583
  · exact g32p_supplierForest_actual_097595
  · exact g32p_supplierForest_actual_097598
  · exact g32p_supplierForest_actual_097599
  · exact g32p_supplierForest_actual_097617
  · exact g32p_supplierForest_actual_097620
  · exact g32p_supplierForest_actual_097648
  · exact g32p_supplierForest_actual_097674
  · exact g32p_supplierForest_actual_097681
  · exact g32p_supplierForest_actual_097754
  · exact g32p_supplierForest_actual_097761
  · exact g32p_supplierForest_actual_097774
  · exact g32p_supplierForest_actual_097778
  · exact g32p_supplierForest_actual_097797
  · exact g32p_supplierForest_actual_097812
  · exact g32p_supplierForest_actual_097858
  · exact g32p_supplierForest_actual_097861
  · exact g32p_supplierForest_actual_097985
  · exact g32p_supplierForest_actual_097998
  · exact g32p_supplierForest_actual_098054
  · exact g32p_supplierForest_actual_098092
  · exact g32p_supplierForest_actual_098119
  · exact g32p_supplierForest_actual_098143
  · exact g32p_supplierForest_actual_098144
  · exact g32p_supplierForest_actual_098154
  · exact g32p_supplierForest_actual_098162
  · exact g32p_supplierForest_actual_098175
  · exact g32p_supplierForest_actual_098187
  · exact g32p_supplierForest_actual_098188
  · exact g32p_supplierForest_actual_098193
  · exact g32p_supplierForest_actual_098218
  · exact g32p_supplierForest_actual_098306
  · exact g32p_supplierForest_actual_098418
  · exact g32p_supplierForest_actual_098423
  · exact g32p_supplierForest_actual_098438
  · exact g32p_supplierForest_actual_098444
  · exact g32p_supplierForest_actual_098451
  · exact g32p_supplierForest_actual_098453
  · exact g32p_supplierForest_actual_098458
  · exact g32p_supplierForest_actual_098461
  · exact g32p_supplierForest_actual_098472
  · exact g32p_supplierForest_actual_098483
  · exact g32p_supplierForest_actual_098532
  · exact g32p_supplierForest_actual_098569
  · exact g32p_supplierForest_actual_098575
  · exact g32p_supplierForest_actual_098584
  · exact g32p_supplierForest_actual_098589
  · exact g32p_supplierForest_actual_098590
  · exact g32p_supplierForest_actual_098593
  · exact g32p_supplierForest_actual_098608
  · exact g32p_supplierForest_actual_098620
  · exact g32p_supplierForest_actual_098623
  · exact g32p_supplierForest_actual_098685
  · exact g32p_supplierForest_actual_098721
  · exact g32p_supplierForest_actual_098729
  · exact g32p_supplierForest_actual_098777
  · exact g32p_supplierForest_actual_098830
  · exact g32p_supplierForest_actual_098832
  · exact g32p_supplierForest_actual_098862
  · exact g32p_supplierForest_actual_098864
  · exact g32p_supplierForest_actual_098889
  · exact g32p_supplierForest_actual_098900
  · exact g32p_supplierForest_actual_098904
  · exact g32p_supplierForest_actual_098923
  · exact g32p_supplierForest_actual_098948
  · exact g32p_supplierForest_actual_098949
  · exact g32p_supplierForest_actual_098966
  · exact g32p_supplierForest_actual_098984
  · exact g32p_supplierForest_actual_098988
  · exact g32p_supplierForest_actual_098998
  · exact g32p_supplierForest_actual_099015
  · exact g32p_supplierForest_actual_099021
  · exact g32p_supplierForest_actual_099063
  · exact g32p_supplierForest_actual_099067

def g32p_supplierForest_nodes_075 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_099120 else g32p_supplierForest_node_099126) else (if i.val < 3 then g32p_supplierForest_node_099129 else g32p_supplierForest_node_099133)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_099142 else g32p_supplierForest_node_099210) else (if i.val < 7 then g32p_supplierForest_node_099239 else g32p_supplierForest_node_099247))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_099338 else g32p_supplierForest_node_099376) else (if i.val < 11 then g32p_supplierForest_node_099397 else g32p_supplierForest_node_099423)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_099440 else g32p_supplierForest_node_099445) else (if i.val < 15 then g32p_supplierForest_node_099463 else g32p_supplierForest_node_099471)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_099478 else g32p_supplierForest_node_099507) else (if i.val < 19 then g32p_supplierForest_node_099516 else g32p_supplierForest_node_099523)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_099531 else g32p_supplierForest_node_099547) else (if i.val < 23 then g32p_supplierForest_node_099579 else g32p_supplierForest_node_099603))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_099612 else g32p_supplierForest_node_099617) else (if i.val < 27 then g32p_supplierForest_node_099627 else g32p_supplierForest_node_099644)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_099654 else g32p_supplierForest_node_099656) else (if i.val < 31 then g32p_supplierForest_node_099669 else g32p_supplierForest_node_099690))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_099699 else g32p_supplierForest_node_099702) else (if i.val < 35 then g32p_supplierForest_node_099719 else g32p_supplierForest_node_099735)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_099750 else g32p_supplierForest_node_099772) else (if i.val < 39 then g32p_supplierForest_node_099835 else g32p_supplierForest_node_099844))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_099849 else g32p_supplierForest_node_099850) else (if i.val < 43 then g32p_supplierForest_node_099878 else g32p_supplierForest_node_099912)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_099939 else g32p_supplierForest_node_099980) else (if i.val < 47 then g32p_supplierForest_node_100030 else g32p_supplierForest_node_100041)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_100042 else g32p_supplierForest_node_100101) else (if i.val < 51 then g32p_supplierForest_node_100115 else g32p_supplierForest_node_100122)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_100130 else g32p_supplierForest_node_100136) else (if i.val < 55 then g32p_supplierForest_node_100159 else g32p_supplierForest_node_100227))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_100234 else g32p_supplierForest_node_100257) else (if i.val < 59 then g32p_supplierForest_node_100260 else g32p_supplierForest_node_100266)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_100294 else g32p_supplierForest_node_100298) else (if i.val < 63 then g32p_supplierForest_node_100325 else g32p_supplierForest_node_100341)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_100370 else g32p_supplierForest_node_100395) else (if i.val < 67 then g32p_supplierForest_node_100402 else g32p_supplierForest_node_100403)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_100441 else g32p_supplierForest_node_100454) else (if i.val < 71 then g32p_supplierForest_node_100463 else g32p_supplierForest_node_100475))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_100497 else g32p_supplierForest_node_100500) else (if i.val < 75 then g32p_supplierForest_node_100501 else g32p_supplierForest_node_100506)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_100513 else g32p_supplierForest_node_100529) else (if i.val < 79 then g32p_supplierForest_node_100542 else g32p_supplierForest_node_100592)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_100597 else g32p_supplierForest_node_100601) else (if i.val < 83 then g32p_supplierForest_node_100602 else g32p_supplierForest_node_100640)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_100644 else g32p_supplierForest_node_100646) else (if i.val < 87 then g32p_supplierForest_node_100650 else g32p_supplierForest_node_100659))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_100681 else g32p_supplierForest_node_100688) else (if i.val < 91 then g32p_supplierForest_node_100707 else g32p_supplierForest_node_100725)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_100735 else g32p_supplierForest_node_100758) else (if i.val < 95 then g32p_supplierForest_node_100795 else g32p_supplierForest_node_100834))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_100838 else g32p_supplierForest_node_100894) else (if i.val < 99 then g32p_supplierForest_node_100913 else g32p_supplierForest_node_100940)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_100949 else g32p_supplierForest_node_100967) else (if i.val < 103 then g32p_supplierForest_node_100980 else g32p_supplierForest_node_100981))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_100990 else g32p_supplierForest_node_100994) else (if i.val < 107 then g32p_supplierForest_node_101004 else g32p_supplierForest_node_101029)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_101041 else g32p_supplierForest_node_101043) else (if i.val < 111 then g32p_supplierForest_node_101047 else g32p_supplierForest_node_101066)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_101099 else g32p_supplierForest_node_101141) else (if i.val < 115 then g32p_supplierForest_node_101175 else g32p_supplierForest_node_101191)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_101258 else g32p_supplierForest_node_101267) else (if i.val < 119 then g32p_supplierForest_node_101291 else g32p_supplierForest_node_101334))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_101347 else g32p_supplierForest_node_101363) else (if i.val < 123 then g32p_supplierForest_node_101367 else g32p_supplierForest_node_101432)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_101448 else g32p_supplierForest_node_101468) else (if i.val < 127 then g32p_supplierForest_node_101485 else g32p_supplierForest_node_101511))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_101544 else g32p_supplierForest_node_101553) else (if i.val < 131 then g32p_supplierForest_node_101555 else g32p_supplierForest_node_101556)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_101567 else g32p_supplierForest_node_101581) else (if i.val < 135 then g32p_supplierForest_node_101621 else g32p_supplierForest_node_101642))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_101666 else g32p_supplierForest_node_101674) else (if i.val < 139 then g32p_supplierForest_node_101709 else g32p_supplierForest_node_101769)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_101795 else g32p_supplierForest_node_101796) else (if i.val < 143 then g32p_supplierForest_node_101819 else g32p_supplierForest_node_101844)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_101869 else g32p_supplierForest_node_101871) else (if i.val < 147 then g32p_supplierForest_node_101890 else g32p_supplierForest_node_101908)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_101922 else g32p_supplierForest_node_101924) else (if i.val < 151 then g32p_supplierForest_node_101937 else g32p_supplierForest_node_101961))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_101998 else g32p_supplierForest_node_102001) else (if i.val < 155 then g32p_supplierForest_node_102013 else g32p_supplierForest_node_102051)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_102057 else g32p_supplierForest_node_102069) else (if i.val < 159 then g32p_supplierForest_node_102089 else g32p_supplierForest_node_102116))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_102167 else g32p_supplierForest_node_102171) else (if i.val < 163 then g32p_supplierForest_node_102174 else g32p_supplierForest_node_102183)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_102184 else g32p_supplierForest_node_102188) else (if i.val < 167 then g32p_supplierForest_node_102220 else g32p_supplierForest_node_102230))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_102233 else g32p_supplierForest_node_102246) else (if i.val < 171 then g32p_supplierForest_node_102268 else g32p_supplierForest_node_102289)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_102295 else g32p_supplierForest_node_102297) else (if i.val < 175 then g32p_supplierForest_node_102300 else g32p_supplierForest_node_102313)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_102319 else g32p_supplierForest_node_102355) else (if i.val < 179 then g32p_supplierForest_node_102366 else g32p_supplierForest_node_102380)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_102414 else g32p_supplierForest_node_102448) else (if i.val < 183 then g32p_supplierForest_node_102449 else g32p_supplierForest_node_102458))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_102468 else g32p_supplierForest_node_102473) else (if i.val < 187 then g32p_supplierForest_node_102479 else g32p_supplierForest_node_102494)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_102495 else g32p_supplierForest_node_102505) else (if i.val < 191 then g32p_supplierForest_node_102516 else g32p_supplierForest_node_102517)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_102532 else g32p_supplierForest_node_102548) else (if i.val < 195 then g32p_supplierForest_node_102559 else g32p_supplierForest_node_102588)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_102608 else g32p_supplierForest_node_102617) else (if i.val < 199 then g32p_supplierForest_node_102620 else g32p_supplierForest_node_102626))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_102650 else g32p_supplierForest_node_102669) else (if i.val < 203 then g32p_supplierForest_node_102703 else g32p_supplierForest_node_102717)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_102729 else g32p_supplierForest_node_102739) else (if i.val < 207 then g32p_supplierForest_node_102747 else g32p_supplierForest_node_102761)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_102783 else g32p_supplierForest_node_102788) else (if i.val < 211 then g32p_supplierForest_node_102802 else g32p_supplierForest_node_102813)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_102815 else g32p_supplierForest_node_102821) else (if i.val < 215 then g32p_supplierForest_node_102841 else g32p_supplierForest_node_102851))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_102853 else g32p_supplierForest_node_102917) else (if i.val < 219 then g32p_supplierForest_node_102974 else g32p_supplierForest_node_102982)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_103011 else g32p_supplierForest_node_103017) else (if i.val < 223 then g32p_supplierForest_node_103038 else g32p_supplierForest_node_103047))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_103079 else g32p_supplierForest_node_103094) else (if i.val < 227 then g32p_supplierForest_node_103100 else g32p_supplierForest_node_103104)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_103110 else g32p_supplierForest_node_103112) else (if i.val < 231 then g32p_supplierForest_node_103130 else g32p_supplierForest_node_103140))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_103190 else g32p_supplierForest_node_103193) else (if i.val < 235 then g32p_supplierForest_node_103197 else g32p_supplierForest_node_103254)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_103271 else g32p_supplierForest_node_103299) else (if i.val < 239 then g32p_supplierForest_node_103323 else g32p_supplierForest_node_103331)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_103336 else g32p_supplierForest_node_103350) else (if i.val < 243 then g32p_supplierForest_node_103352 else g32p_supplierForest_node_103367)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_103386 else g32p_supplierForest_node_103412) else (if i.val < 247 then g32p_supplierForest_node_103419 else g32p_supplierForest_node_103434))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_103449 else g32p_supplierForest_node_103463) else (if i.val < 251 then g32p_supplierForest_node_103494 else g32p_supplierForest_node_103506)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_103524 else g32p_supplierForest_node_103525) else (if i.val < 255 then g32p_supplierForest_node_103527 else g32p_supplierForest_node_103541))))))))

def g32p_supplierForest_classes_075 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 13 else 54) else (if i.val < 3 then 46 else 54)) else (if i.val < 6 then (if i.val < 5 then 25 else 55) else (if i.val < 7 then 50 else 25))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 13 else 80) else (if i.val < 11 then 47 else 25)) else (if i.val < 14 then (if i.val < 13 then 13 else 46) else (if i.val < 15 then 80 else 25)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 46 else 25) else (if i.val < 19 then 54 else 50)) else (if i.val < 22 then (if i.val < 21 then 25 else 80) else (if i.val < 23 then 46 else 80))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 47) else (if i.val < 27 then 52 else 13)) else (if i.val < 30 then (if i.val < 29 then 49 else 45) else (if i.val < 31 then 55 else 47))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 48 else 48) else (if i.val < 35 then 49 else 26)) else (if i.val < 38 then (if i.val < 37 then 25 else 47) else (if i.val < 39 then 84 else 50))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 45 else 12) else (if i.val < 43 then 54 else 25)) else (if i.val < 46 then (if i.val < 45 then 46 else 82) else (if i.val < 47 then 54 else 56)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 56 else 80) else (if i.val < 51 then 25 else 46)) else (if i.val < 54 then (if i.val < 53 then 86 else 49) else (if i.val < 55 then 47 else 46))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 9 else 46) else (if i.val < 59 then 47 else 26)) else (if i.val < 62 then (if i.val < 61 then 49 else 46) else (if i.val < 63 then 49 else 46)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 46 else 54) else (if i.val < 67 then 46 else 25)) else (if i.val < 70 then (if i.val < 69 then 49 else 56) else (if i.val < 71 then 49 else 26))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 54 else 13) else (if i.val < 75 then 50 else 13)) else (if i.val < 78 then (if i.val < 77 then 49 else 49) else (if i.val < 79 then 50 else 47)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 47 else 46) else (if i.val < 83 then 55 else 46)) else (if i.val < 86 then (if i.val < 85 then 80 else 86) else (if i.val < 87 then 25 else 55))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 49 else 49) else (if i.val < 91 then 26 else 55)) else (if i.val < 94 then (if i.val < 93 then 49 else 55) else (if i.val < 95 then 50 else 54))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 86 else 85) else (if i.val < 99 then 13 else 55)) else (if i.val < 102 then (if i.val < 101 then 55 else 49) else (if i.val < 103 then 49 else 55))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 13 else 80) else (if i.val < 107 then 11 else 46)) else (if i.val < 110 then (if i.val < 109 then 83 else 84) else (if i.val < 111 then 80 else 25)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 25 else 47) else (if i.val < 115 then 13 else 49)) else (if i.val < 118 then (if i.val < 117 then 80 else 46) else (if i.val < 119 then 47 else 47))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 46 else 80) else (if i.val < 123 then 55 else 52)) else (if i.val < 126 then (if i.val < 125 then 11 else 81) else (if i.val < 127 then 86 else 52))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 49 else 53) else (if i.val < 131 then 26 else 13)) else (if i.val < 134 then (if i.val < 133 then 55 else 26) else (if i.val < 135 then 46 else 86))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 80 else 80) else (if i.val < 139 then 11 else 49)) else (if i.val < 142 then (if i.val < 141 then 86 else 49) else (if i.val < 143 then 56 else 53)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 54 else 53) else (if i.val < 147 then 13 else 60)) else (if i.val < 150 then (if i.val < 149 then 57 else 30) else (if i.val < 151 then 66 else 63))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 60 else 57) else (if i.val < 155 then 34 else 30)) else (if i.val < 158 then (if i.val < 157 then 57 else 64) else (if i.val < 159 then 58 else 16))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 59 else 59) else (if i.val < 163 then 66 else 66)) else (if i.val < 166 then (if i.val < 165 then 57 else 57) else (if i.val < 167 then 15 else 15))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 58 else 60) else (if i.val < 171 then 36 else 30)) else (if i.val < 174 then (if i.val < 173 then 64 else 63) else (if i.val < 175 then 4 else 64)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 57 else 57) else (if i.val < 179 then 63 else 61)) else (if i.val < 182 then (if i.val < 181 then 58 else 57) else (if i.val < 183 then 36 else 63))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 59 else 30) else (if i.val < 187 then 30 else 30)) else (if i.val < 190 then (if i.val < 189 then 30 else 30) else (if i.val < 191 then 30 else 30)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 15 else 59) else (if i.val < 195 then 60 else 30)) else (if i.val < 198 then (if i.val < 197 then 29 else 57) else (if i.val < 199 then 30 else 29))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 57 else 59) else (if i.val < 203 then 30 else 16)) else (if i.val < 206 then (if i.val < 205 then 15 else 57) else (if i.val < 207 then 33 else 57)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 29 else 29) else (if i.val < 211 then 57 else 30)) else (if i.val < 214 then (if i.val < 213 then 29 else 30) else (if i.val < 215 then 66 else 60))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 57 else 58) else (if i.val < 219 then 17 else 16)) else (if i.val < 222 then (if i.val < 221 then 36 else 17) else (if i.val < 223 then 30 else 16))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 57 else 57) else (if i.val < 227 then 59 else 34)) else (if i.val < 230 then (if i.val < 229 then 30 else 59) else (if i.val < 231 then 16 else 57))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 60 else 64) else (if i.val < 235 then 34 else 57)) else (if i.val < 238 then (if i.val < 237 then 30 else 58) else (if i.val < 239 then 57 else 57)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 57 else 29) else (if i.val < 243 then 33 else 58)) else (if i.val < 246 then (if i.val < 245 then 63 else 30) else (if i.val < 247 then 59 else 29))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 59 else 30) else (if i.val < 251 then 30 else 66)) else (if i.val < 254 then (if i.val < 253 then 30 else 61) else (if i.val < 255 then 29 else 66))))))))

theorem g32p_supplierForest_actual_075 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_075 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_075 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_099120
  · exact g32p_supplierForest_actual_099126
  · exact g32p_supplierForest_actual_099129
  · exact g32p_supplierForest_actual_099133
  · exact g32p_supplierForest_actual_099142
  · exact g32p_supplierForest_actual_099210
  · exact g32p_supplierForest_actual_099239
  · exact g32p_supplierForest_actual_099247
  · exact g32p_supplierForest_actual_099338
  · exact g32p_supplierForest_actual_099376
  · exact g32p_supplierForest_actual_099397
  · exact g32p_supplierForest_actual_099423
  · exact g32p_supplierForest_actual_099440
  · exact g32p_supplierForest_actual_099445
  · exact g32p_supplierForest_actual_099463
  · exact g32p_supplierForest_actual_099471
  · exact g32p_supplierForest_actual_099478
  · exact g32p_supplierForest_actual_099507
  · exact g32p_supplierForest_actual_099516
  · exact g32p_supplierForest_actual_099523
  · exact g32p_supplierForest_actual_099531
  · exact g32p_supplierForest_actual_099547
  · exact g32p_supplierForest_actual_099579
  · exact g32p_supplierForest_actual_099603
  · exact g32p_supplierForest_actual_099612
  · exact g32p_supplierForest_actual_099617
  · exact g32p_supplierForest_actual_099627
  · exact g32p_supplierForest_actual_099644
  · exact g32p_supplierForest_actual_099654
  · exact g32p_supplierForest_actual_099656
  · exact g32p_supplierForest_actual_099669
  · exact g32p_supplierForest_actual_099690
  · exact g32p_supplierForest_actual_099699
  · exact g32p_supplierForest_actual_099702
  · exact g32p_supplierForest_actual_099719
  · exact g32p_supplierForest_actual_099735
  · exact g32p_supplierForest_actual_099750
  · exact g32p_supplierForest_actual_099772
  · exact g32p_supplierForest_actual_099835
  · exact g32p_supplierForest_actual_099844
  · exact g32p_supplierForest_actual_099849
  · exact g32p_supplierForest_actual_099850
  · exact g32p_supplierForest_actual_099878
  · exact g32p_supplierForest_actual_099912
  · exact g32p_supplierForest_actual_099939
  · exact g32p_supplierForest_actual_099980
  · exact g32p_supplierForest_actual_100030
  · exact g32p_supplierForest_actual_100041
  · exact g32p_supplierForest_actual_100042
  · exact g32p_supplierForest_actual_100101
  · exact g32p_supplierForest_actual_100115
  · exact g32p_supplierForest_actual_100122
  · exact g32p_supplierForest_actual_100130
  · exact g32p_supplierForest_actual_100136
  · exact g32p_supplierForest_actual_100159
  · exact g32p_supplierForest_actual_100227
  · exact g32p_supplierForest_actual_100234
  · exact g32p_supplierForest_actual_100257
  · exact g32p_supplierForest_actual_100260
  · exact g32p_supplierForest_actual_100266
  · exact g32p_supplierForest_actual_100294
  · exact g32p_supplierForest_actual_100298
  · exact g32p_supplierForest_actual_100325
  · exact g32p_supplierForest_actual_100341
  · exact g32p_supplierForest_actual_100370
  · exact g32p_supplierForest_actual_100395
  · exact g32p_supplierForest_actual_100402
  · exact g32p_supplierForest_actual_100403
  · exact g32p_supplierForest_actual_100441
  · exact g32p_supplierForest_actual_100454
  · exact g32p_supplierForest_actual_100463
  · exact g32p_supplierForest_actual_100475
  · exact g32p_supplierForest_actual_100497
  · exact g32p_supplierForest_actual_100500
  · exact g32p_supplierForest_actual_100501
  · exact g32p_supplierForest_actual_100506
  · exact g32p_supplierForest_actual_100513
  · exact g32p_supplierForest_actual_100529
  · exact g32p_supplierForest_actual_100542
  · exact g32p_supplierForest_actual_100592
  · exact g32p_supplierForest_actual_100597
  · exact g32p_supplierForest_actual_100601
  · exact g32p_supplierForest_actual_100602
  · exact g32p_supplierForest_actual_100640
  · exact g32p_supplierForest_actual_100644
  · exact g32p_supplierForest_actual_100646
  · exact g32p_supplierForest_actual_100650
  · exact g32p_supplierForest_actual_100659
  · exact g32p_supplierForest_actual_100681
  · exact g32p_supplierForest_actual_100688
  · exact g32p_supplierForest_actual_100707
  · exact g32p_supplierForest_actual_100725
  · exact g32p_supplierForest_actual_100735
  · exact g32p_supplierForest_actual_100758
  · exact g32p_supplierForest_actual_100795
  · exact g32p_supplierForest_actual_100834
  · exact g32p_supplierForest_actual_100838
  · exact g32p_supplierForest_actual_100894
  · exact g32p_supplierForest_actual_100913
  · exact g32p_supplierForest_actual_100940
  · exact g32p_supplierForest_actual_100949
  · exact g32p_supplierForest_actual_100967
  · exact g32p_supplierForest_actual_100980
  · exact g32p_supplierForest_actual_100981
  · exact g32p_supplierForest_actual_100990
  · exact g32p_supplierForest_actual_100994
  · exact g32p_supplierForest_actual_101004
  · exact g32p_supplierForest_actual_101029
  · exact g32p_supplierForest_actual_101041
  · exact g32p_supplierForest_actual_101043
  · exact g32p_supplierForest_actual_101047
  · exact g32p_supplierForest_actual_101066
  · exact g32p_supplierForest_actual_101099
  · exact g32p_supplierForest_actual_101141
  · exact g32p_supplierForest_actual_101175
  · exact g32p_supplierForest_actual_101191
  · exact g32p_supplierForest_actual_101258
  · exact g32p_supplierForest_actual_101267
  · exact g32p_supplierForest_actual_101291
  · exact g32p_supplierForest_actual_101334
  · exact g32p_supplierForest_actual_101347
  · exact g32p_supplierForest_actual_101363
  · exact g32p_supplierForest_actual_101367
  · exact g32p_supplierForest_actual_101432
  · exact g32p_supplierForest_actual_101448
  · exact g32p_supplierForest_actual_101468
  · exact g32p_supplierForest_actual_101485
  · exact g32p_supplierForest_actual_101511
  · exact g32p_supplierForest_actual_101544
  · exact g32p_supplierForest_actual_101553
  · exact g32p_supplierForest_actual_101555
  · exact g32p_supplierForest_actual_101556
  · exact g32p_supplierForest_actual_101567
  · exact g32p_supplierForest_actual_101581
  · exact g32p_supplierForest_actual_101621
  · exact g32p_supplierForest_actual_101642
  · exact g32p_supplierForest_actual_101666
  · exact g32p_supplierForest_actual_101674
  · exact g32p_supplierForest_actual_101709
  · exact g32p_supplierForest_actual_101769
  · exact g32p_supplierForest_actual_101795
  · exact g32p_supplierForest_actual_101796
  · exact g32p_supplierForest_actual_101819
  · exact g32p_supplierForest_actual_101844
  · exact g32p_supplierForest_actual_101869
  · exact g32p_supplierForest_actual_101871
  · exact g32p_supplierForest_actual_101890
  · exact g32p_supplierForest_actual_101908
  · exact g32p_supplierForest_actual_101922
  · exact g32p_supplierForest_actual_101924
  · exact g32p_supplierForest_actual_101937
  · exact g32p_supplierForest_actual_101961
  · exact g32p_supplierForest_actual_101998
  · exact g32p_supplierForest_actual_102001
  · exact g32p_supplierForest_actual_102013
  · exact g32p_supplierForest_actual_102051
  · exact g32p_supplierForest_actual_102057
  · exact g32p_supplierForest_actual_102069
  · exact g32p_supplierForest_actual_102089
  · exact g32p_supplierForest_actual_102116
  · exact g32p_supplierForest_actual_102167
  · exact g32p_supplierForest_actual_102171
  · exact g32p_supplierForest_actual_102174
  · exact g32p_supplierForest_actual_102183
  · exact g32p_supplierForest_actual_102184
  · exact g32p_supplierForest_actual_102188
  · exact g32p_supplierForest_actual_102220
  · exact g32p_supplierForest_actual_102230
  · exact g32p_supplierForest_actual_102233
  · exact g32p_supplierForest_actual_102246
  · exact g32p_supplierForest_actual_102268
  · exact g32p_supplierForest_actual_102289
  · exact g32p_supplierForest_actual_102295
  · exact g32p_supplierForest_actual_102297
  · exact g32p_supplierForest_actual_102300
  · exact g32p_supplierForest_actual_102313
  · exact g32p_supplierForest_actual_102319
  · exact g32p_supplierForest_actual_102355
  · exact g32p_supplierForest_actual_102366
  · exact g32p_supplierForest_actual_102380
  · exact g32p_supplierForest_actual_102414
  · exact g32p_supplierForest_actual_102448
  · exact g32p_supplierForest_actual_102449
  · exact g32p_supplierForest_actual_102458
  · exact g32p_supplierForest_actual_102468
  · exact g32p_supplierForest_actual_102473
  · exact g32p_supplierForest_actual_102479
  · exact g32p_supplierForest_actual_102494
  · exact g32p_supplierForest_actual_102495
  · exact g32p_supplierForest_actual_102505
  · exact g32p_supplierForest_actual_102516
  · exact g32p_supplierForest_actual_102517
  · exact g32p_supplierForest_actual_102532
  · exact g32p_supplierForest_actual_102548
  · exact g32p_supplierForest_actual_102559
  · exact g32p_supplierForest_actual_102588
  · exact g32p_supplierForest_actual_102608
  · exact g32p_supplierForest_actual_102617
  · exact g32p_supplierForest_actual_102620
  · exact g32p_supplierForest_actual_102626
  · exact g32p_supplierForest_actual_102650
  · exact g32p_supplierForest_actual_102669
  · exact g32p_supplierForest_actual_102703
  · exact g32p_supplierForest_actual_102717
  · exact g32p_supplierForest_actual_102729
  · exact g32p_supplierForest_actual_102739
  · exact g32p_supplierForest_actual_102747
  · exact g32p_supplierForest_actual_102761
  · exact g32p_supplierForest_actual_102783
  · exact g32p_supplierForest_actual_102788
  · exact g32p_supplierForest_actual_102802
  · exact g32p_supplierForest_actual_102813
  · exact g32p_supplierForest_actual_102815
  · exact g32p_supplierForest_actual_102821
  · exact g32p_supplierForest_actual_102841
  · exact g32p_supplierForest_actual_102851
  · exact g32p_supplierForest_actual_102853
  · exact g32p_supplierForest_actual_102917
  · exact g32p_supplierForest_actual_102974
  · exact g32p_supplierForest_actual_102982
  · exact g32p_supplierForest_actual_103011
  · exact g32p_supplierForest_actual_103017
  · exact g32p_supplierForest_actual_103038
  · exact g32p_supplierForest_actual_103047
  · exact g32p_supplierForest_actual_103079
  · exact g32p_supplierForest_actual_103094
  · exact g32p_supplierForest_actual_103100
  · exact g32p_supplierForest_actual_103104
  · exact g32p_supplierForest_actual_103110
  · exact g32p_supplierForest_actual_103112
  · exact g32p_supplierForest_actual_103130
  · exact g32p_supplierForest_actual_103140
  · exact g32p_supplierForest_actual_103190
  · exact g32p_supplierForest_actual_103193
  · exact g32p_supplierForest_actual_103197
  · exact g32p_supplierForest_actual_103254
  · exact g32p_supplierForest_actual_103271
  · exact g32p_supplierForest_actual_103299
  · exact g32p_supplierForest_actual_103323
  · exact g32p_supplierForest_actual_103331
  · exact g32p_supplierForest_actual_103336
  · exact g32p_supplierForest_actual_103350
  · exact g32p_supplierForest_actual_103352
  · exact g32p_supplierForest_actual_103367
  · exact g32p_supplierForest_actual_103386
  · exact g32p_supplierForest_actual_103412
  · exact g32p_supplierForest_actual_103419
  · exact g32p_supplierForest_actual_103434
  · exact g32p_supplierForest_actual_103449
  · exact g32p_supplierForest_actual_103463
  · exact g32p_supplierForest_actual_103494
  · exact g32p_supplierForest_actual_103506
  · exact g32p_supplierForest_actual_103524
  · exact g32p_supplierForest_actual_103525
  · exact g32p_supplierForest_actual_103527
  · exact g32p_supplierForest_actual_103541

def g32p_supplierForest_nodes_076 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_103564 else g32p_supplierForest_node_103576) else (if i.val < 3 then g32p_supplierForest_node_103588 else g32p_supplierForest_node_103592)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_103653 else g32p_supplierForest_node_103659) else (if i.val < 7 then g32p_supplierForest_node_103682 else g32p_supplierForest_node_103708))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_103714 else g32p_supplierForest_node_103722) else (if i.val < 11 then g32p_supplierForest_node_103724 else g32p_supplierForest_node_103727)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_103729 else g32p_supplierForest_node_103740) else (if i.val < 15 then g32p_supplierForest_node_103744 else g32p_supplierForest_node_103753)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_103775 else g32p_supplierForest_node_103834) else (if i.val < 19 then g32p_supplierForest_node_103855 else g32p_supplierForest_node_103875)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_103877 else g32p_supplierForest_node_103932) else (if i.val < 23 then g32p_supplierForest_node_103960 else g32p_supplierForest_node_103992))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_104000 else g32p_supplierForest_node_104021) else (if i.val < 27 then g32p_supplierForest_node_104035 else g32p_supplierForest_node_104058)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_104070 else g32p_supplierForest_node_104076) else (if i.val < 31 then g32p_supplierForest_node_104087 else g32p_supplierForest_node_104096))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_104097 else g32p_supplierForest_node_104107) else (if i.val < 35 then g32p_supplierForest_node_104108 else g32p_supplierForest_node_104126)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_104138 else g32p_supplierForest_node_104142) else (if i.val < 39 then g32p_supplierForest_node_104152 else g32p_supplierForest_node_104155))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_104166 else g32p_supplierForest_node_104181) else (if i.val < 43 then g32p_supplierForest_node_104187 else g32p_supplierForest_node_104217)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_104218 else g32p_supplierForest_node_104255) else (if i.val < 47 then g32p_supplierForest_node_104270 else g32p_supplierForest_node_104275)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_104276 else g32p_supplierForest_node_104278) else (if i.val < 51 then g32p_supplierForest_node_104298 else g32p_supplierForest_node_104309)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_104311 else g32p_supplierForest_node_104314) else (if i.val < 55 then g32p_supplierForest_node_104334 else g32p_supplierForest_node_104353))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_104372 else g32p_supplierForest_node_104377) else (if i.val < 59 then g32p_supplierForest_node_104411 else g32p_supplierForest_node_104442)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_104474 else g32p_supplierForest_node_104511) else (if i.val < 63 then g32p_supplierForest_node_104526 else g32p_supplierForest_node_104537)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_104546 else g32p_supplierForest_node_104548) else (if i.val < 67 then g32p_supplierForest_node_104550 else g32p_supplierForest_node_104574)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_104578 else g32p_supplierForest_node_104585) else (if i.val < 71 then g32p_supplierForest_node_104595 else g32p_supplierForest_node_104617))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_104638 else g32p_supplierForest_node_104661) else (if i.val < 75 then g32p_supplierForest_node_104688 else g32p_supplierForest_node_104693)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_104699 else g32p_supplierForest_node_104718) else (if i.val < 79 then g32p_supplierForest_node_104734 else g32p_supplierForest_node_104751)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_104752 else g32p_supplierForest_node_104831) else (if i.val < 83 then g32p_supplierForest_node_104852 else g32p_supplierForest_node_104872)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_104873 else g32p_supplierForest_node_104882) else (if i.val < 87 then g32p_supplierForest_node_104905 else g32p_supplierForest_node_104907))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_104913 else g32p_supplierForest_node_105014) else (if i.val < 91 then g32p_supplierForest_node_105035 else g32p_supplierForest_node_105047)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_105064 else g32p_supplierForest_node_105068) else (if i.val < 95 then g32p_supplierForest_node_105090 else g32p_supplierForest_node_105091))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_105092 else g32p_supplierForest_node_105096) else (if i.val < 99 then g32p_supplierForest_node_105121 else g32p_supplierForest_node_105150)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_105192 else g32p_supplierForest_node_105215) else (if i.val < 103 then g32p_supplierForest_node_105224 else g32p_supplierForest_node_105238))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_105250 else g32p_supplierForest_node_105254) else (if i.val < 107 then g32p_supplierForest_node_105260 else g32p_supplierForest_node_105279)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_105293 else g32p_supplierForest_node_105310) else (if i.val < 111 then g32p_supplierForest_node_105319 else g32p_supplierForest_node_105328)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_105408 else g32p_supplierForest_node_105438) else (if i.val < 115 then g32p_supplierForest_node_105447 else g32p_supplierForest_node_105486)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_105489 else g32p_supplierForest_node_105540) else (if i.val < 119 then g32p_supplierForest_node_105578 else g32p_supplierForest_node_105608))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_105616 else g32p_supplierForest_node_105627) else (if i.val < 123 then g32p_supplierForest_node_105698 else g32p_supplierForest_node_105704)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_105747 else g32p_supplierForest_node_105781) else (if i.val < 127 then g32p_supplierForest_node_105786 else g32p_supplierForest_node_105807))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_105815 else g32p_supplierForest_node_105855) else (if i.val < 131 then g32p_supplierForest_node_105876 else g32p_supplierForest_node_105881)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_105885 else g32p_supplierForest_node_105892) else (if i.val < 135 then g32p_supplierForest_node_105912 else g32p_supplierForest_node_105927))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_105933 else g32p_supplierForest_node_105959) else (if i.val < 139 then g32p_supplierForest_node_105960 else g32p_supplierForest_node_105981)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_106018 else g32p_supplierForest_node_106021) else (if i.val < 143 then g32p_supplierForest_node_106024 else g32p_supplierForest_node_106042)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_106054 else g32p_supplierForest_node_106069) else (if i.val < 147 then g32p_supplierForest_node_106102 else g32p_supplierForest_node_106117)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_106154 else g32p_supplierForest_node_106177) else (if i.val < 151 then g32p_supplierForest_node_106181 else g32p_supplierForest_node_106190))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_106193 else g32p_supplierForest_node_106203) else (if i.val < 155 then g32p_supplierForest_node_106205 else g32p_supplierForest_node_106212)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_106240 else g32p_supplierForest_node_106242) else (if i.val < 159 then g32p_supplierForest_node_106247 else g32p_supplierForest_node_106260))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_106290 else g32p_supplierForest_node_106314) else (if i.val < 163 then g32p_supplierForest_node_106319 else g32p_supplierForest_node_106335)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_106344 else g32p_supplierForest_node_106347) else (if i.val < 167 then g32p_supplierForest_node_106349 else g32p_supplierForest_node_106360))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_106389 else g32p_supplierForest_node_106392) else (if i.val < 171 then g32p_supplierForest_node_106401 else g32p_supplierForest_node_106409)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_106416 else g32p_supplierForest_node_106426) else (if i.val < 175 then g32p_supplierForest_node_106441 else g32p_supplierForest_node_106458)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_106459 else g32p_supplierForest_node_106473) else (if i.val < 179 then g32p_supplierForest_node_106483 else g32p_supplierForest_node_106497)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_106529 else g32p_supplierForest_node_106550) else (if i.val < 183 then g32p_supplierForest_node_106558 else g32p_supplierForest_node_106588))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_106599 else g32p_supplierForest_node_106612) else (if i.val < 187 then g32p_supplierForest_node_106615 else g32p_supplierForest_node_106627)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_106681 else g32p_supplierForest_node_106688) else (if i.val < 191 then g32p_supplierForest_node_106712 else g32p_supplierForest_node_106740)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_106743 else g32p_supplierForest_node_106757) else (if i.val < 195 then g32p_supplierForest_node_106761 else g32p_supplierForest_node_106778)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_106812 else g32p_supplierForest_node_106888) else (if i.val < 199 then g32p_supplierForest_node_106937 else g32p_supplierForest_node_106941))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_106949 else g32p_supplierForest_node_106953) else (if i.val < 203 then g32p_supplierForest_node_106980 else g32p_supplierForest_node_106996)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_107056 else g32p_supplierForest_node_107081) else (if i.val < 207 then g32p_supplierForest_node_107084 else g32p_supplierForest_node_107116)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_107147 else g32p_supplierForest_node_107192) else (if i.val < 211 then g32p_supplierForest_node_107196 else g32p_supplierForest_node_107207)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_107220 else g32p_supplierForest_node_107225) else (if i.val < 215 then g32p_supplierForest_node_107260 else g32p_supplierForest_node_107287))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_107310 else g32p_supplierForest_node_107312) else (if i.val < 219 then g32p_supplierForest_node_107339 else g32p_supplierForest_node_107350)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_107354 else g32p_supplierForest_node_107365) else (if i.val < 223 then g32p_supplierForest_node_107369 else g32p_supplierForest_node_107434))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_107447 else g32p_supplierForest_node_107449) else (if i.val < 227 then g32p_supplierForest_node_107475 else g32p_supplierForest_node_107480)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_107556 else g32p_supplierForest_node_107568) else (if i.val < 231 then g32p_supplierForest_node_107586 else g32p_supplierForest_node_107591))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_107594 else g32p_supplierForest_node_107612) else (if i.val < 235 then g32p_supplierForest_node_107633 else g32p_supplierForest_node_107634)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_107665 else g32p_supplierForest_node_107732) else (if i.val < 239 then g32p_supplierForest_node_107742 else g32p_supplierForest_node_107760)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_107811 else g32p_supplierForest_node_107816) else (if i.val < 243 then g32p_supplierForest_node_107823 else g32p_supplierForest_node_107862)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_107889 else g32p_supplierForest_node_107891) else (if i.val < 247 then g32p_supplierForest_node_107915 else g32p_supplierForest_node_107938))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_108012 else g32p_supplierForest_node_108017) else (if i.val < 251 then g32p_supplierForest_node_108022 else g32p_supplierForest_node_108029)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_108037 else g32p_supplierForest_node_108066) else (if i.val < 255 then g32p_supplierForest_node_108070 else g32p_supplierForest_node_108095))))))))

def g32p_supplierForest_classes_076 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 30 else 36) else (if i.val < 3 then 57 else 63)) else (if i.val < 6 then (if i.val < 5 then 58 else 30) else (if i.val < 7 then 59 else 17))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 62 else 34) else (if i.val < 11 then 36 else 16)) else (if i.val < 14 then (if i.val < 13 then 57 else 30) else (if i.val < 15 then 30 else 66)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 34 else 57) else (if i.val < 19 then 61 else 57)) else (if i.val < 22 then (if i.val < 21 then 57 else 60) else (if i.val < 23 then 16 else 60))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 59 else 66) else (if i.val < 27 then 29 else 29)) else (if i.val < 30 then (if i.val < 29 then 58 else 60) else (if i.val < 31 then 17 else 59))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 60 else 62) else (if i.val < 35 then 57 else 59)) else (if i.val < 38 then (if i.val < 37 then 15 else 60) else (if i.val < 39 then 15 else 58))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 29 else 30) else (if i.val < 43 then 30 else 34)) else (if i.val < 46 then (if i.val < 45 then 14 else 57) else (if i.val < 47 then 64 else 57)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 57 else 33) else (if i.val < 51 then 33 else 59)) else (if i.val < 54 then (if i.val < 53 then 16 else 57) else (if i.val < 55 then 30 else 30))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 15 else 14) else (if i.val < 59 then 30 else 33)) else (if i.val < 62 then (if i.val < 61 then 16 else 15) else (if i.val < 63 then 57 else 16)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 30 else 16) else (if i.val < 67 then 14 else 61)) else (if i.val < 70 then (if i.val < 69 then 60 else 29) else (if i.val < 71 then 16 else 36))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 15 else 59) else (if i.val < 75 then 59 else 59)) else (if i.val < 78 then (if i.val < 77 then 17 else 60) else (if i.val < 79 then 63 else 63)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 59 else 33) else (if i.val < 83 then 60 else 16)) else (if i.val < 86 then (if i.val < 85 then 34 else 57) else (if i.val < 87 then 29 else 60))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 16 else 15) else (if i.val < 91 then 58 else 30)) else (if i.val < 94 then (if i.val < 93 then 33 else 30) else (if i.val < 95 then 57 else 34))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 36 else 59) else (if i.val < 99 then 57 else 34)) else (if i.val < 102 then (if i.val < 101 then 60 else 58) else (if i.val < 103 then 4 else 17))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 34 else 58) else (if i.val < 107 then 61 else 59)) else (if i.val < 110 then (if i.val < 109 then 65 else 29) else (if i.val < 111 then 30 else 60)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 58 else 33) else (if i.val < 115 then 15 else 60)) else (if i.val < 118 then (if i.val < 117 then 60 else 30) else (if i.val < 119 then 30 else 30))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 59 else 57) else (if i.val < 123 then 58 else 60)) else (if i.val < 126 then (if i.val < 125 then 15 else 63) else (if i.val < 127 then 60 else 57))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 15 else 57) else (if i.val < 131 then 30 else 32)) else (if i.val < 134 then (if i.val < 133 then 63 else 63) else (if i.val < 135 then 29 else 34))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 29 else 29) else (if i.val < 139 then 30 else 35)) else (if i.val < 142 then (if i.val < 141 then 33 else 29) else (if i.val < 143 then 57 else 62)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 34 else 29) else (if i.val < 147 then 33 else 58)) else (if i.val < 150 then (if i.val < 149 then 33 else 57) else (if i.val < 151 then 29 else 57))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 15 else 16) else (if i.val < 155 then 33 else 60)) else (if i.val < 158 then (if i.val < 157 then 30 else 34) else (if i.val < 159 then 35 else 92))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 35 else 29) else (if i.val < 163 then 15 else 16)) else (if i.val < 166 then (if i.val < 165 then 57 else 59) else (if i.val < 167 then 59 else 30))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 16 else 36) else (if i.val < 171 then 66 else 29)) else (if i.val < 174 then (if i.val < 173 then 36 else 61) else (if i.val < 175 then 58 else 29)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 60 else 17) else (if i.val < 179 then 16 else 57)) else (if i.val < 182 then (if i.val < 181 then 36 else 34) else (if i.val < 183 then 57 else 17))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 66 else 29) else (if i.val < 187 then 57 else 34)) else (if i.val < 190 then (if i.val < 189 then 30 else 60) else (if i.val < 191 then 35 else 59)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 57 else 17) else (if i.val < 195 then 66 else 66)) else (if i.val < 198 then (if i.val < 197 then 29 else 57) else (if i.val < 199 then 60 else 57))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 15 else 14) else (if i.val < 203 then 33 else 60)) else (if i.val < 206 then (if i.val < 205 then 60 else 58) else (if i.val < 207 then 60 else 34)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 57 else 63) else (if i.val < 211 then 29 else 36)) else (if i.val < 214 then (if i.val < 213 then 34 else 57) else (if i.val < 215 then 66 else 30))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 15 else 63) else (if i.val < 219 then 61 else 59)) else (if i.val < 222 then (if i.val < 221 then 57 else 15) else (if i.val < 223 then 61 else 60))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 57 else 57) else (if i.val < 227 then 60 else 30)) else (if i.val < 230 then (if i.val < 229 then 16 else 58) else (if i.val < 231 then 29 else 59))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 57 else 30) else (if i.val < 235 then 30 else 30)) else (if i.val < 238 then (if i.val < 237 then 29 else 57) else (if i.val < 239 then 63 else 60)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 36 else 66) else (if i.val < 243 then 60 else 62)) else (if i.val < 246 then (if i.val < 245 then 59 else 63) else (if i.val < 247 then 59 else 92))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 16 else 59) else (if i.val < 251 then 30 else 66)) else (if i.val < 254 then (if i.val < 253 then 57 else 66) else (if i.val < 255 then 30 else 63))))))))

theorem g32p_supplierForest_actual_076 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_076 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_076 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_103564
  · exact g32p_supplierForest_actual_103576
  · exact g32p_supplierForest_actual_103588
  · exact g32p_supplierForest_actual_103592
  · exact g32p_supplierForest_actual_103653
  · exact g32p_supplierForest_actual_103659
  · exact g32p_supplierForest_actual_103682
  · exact g32p_supplierForest_actual_103708
  · exact g32p_supplierForest_actual_103714
  · exact g32p_supplierForest_actual_103722
  · exact g32p_supplierForest_actual_103724
  · exact g32p_supplierForest_actual_103727
  · exact g32p_supplierForest_actual_103729
  · exact g32p_supplierForest_actual_103740
  · exact g32p_supplierForest_actual_103744
  · exact g32p_supplierForest_actual_103753
  · exact g32p_supplierForest_actual_103775
  · exact g32p_supplierForest_actual_103834
  · exact g32p_supplierForest_actual_103855
  · exact g32p_supplierForest_actual_103875
  · exact g32p_supplierForest_actual_103877
  · exact g32p_supplierForest_actual_103932
  · exact g32p_supplierForest_actual_103960
  · exact g32p_supplierForest_actual_103992
  · exact g32p_supplierForest_actual_104000
  · exact g32p_supplierForest_actual_104021
  · exact g32p_supplierForest_actual_104035
  · exact g32p_supplierForest_actual_104058
  · exact g32p_supplierForest_actual_104070
  · exact g32p_supplierForest_actual_104076
  · exact g32p_supplierForest_actual_104087
  · exact g32p_supplierForest_actual_104096
  · exact g32p_supplierForest_actual_104097
  · exact g32p_supplierForest_actual_104107
  · exact g32p_supplierForest_actual_104108
  · exact g32p_supplierForest_actual_104126
  · exact g32p_supplierForest_actual_104138
  · exact g32p_supplierForest_actual_104142
  · exact g32p_supplierForest_actual_104152
  · exact g32p_supplierForest_actual_104155
  · exact g32p_supplierForest_actual_104166
  · exact g32p_supplierForest_actual_104181
  · exact g32p_supplierForest_actual_104187
  · exact g32p_supplierForest_actual_104217
  · exact g32p_supplierForest_actual_104218
  · exact g32p_supplierForest_actual_104255
  · exact g32p_supplierForest_actual_104270
  · exact g32p_supplierForest_actual_104275
  · exact g32p_supplierForest_actual_104276
  · exact g32p_supplierForest_actual_104278
  · exact g32p_supplierForest_actual_104298
  · exact g32p_supplierForest_actual_104309
  · exact g32p_supplierForest_actual_104311
  · exact g32p_supplierForest_actual_104314
  · exact g32p_supplierForest_actual_104334
  · exact g32p_supplierForest_actual_104353
  · exact g32p_supplierForest_actual_104372
  · exact g32p_supplierForest_actual_104377
  · exact g32p_supplierForest_actual_104411
  · exact g32p_supplierForest_actual_104442
  · exact g32p_supplierForest_actual_104474
  · exact g32p_supplierForest_actual_104511
  · exact g32p_supplierForest_actual_104526
  · exact g32p_supplierForest_actual_104537
  · exact g32p_supplierForest_actual_104546
  · exact g32p_supplierForest_actual_104548
  · exact g32p_supplierForest_actual_104550
  · exact g32p_supplierForest_actual_104574
  · exact g32p_supplierForest_actual_104578
  · exact g32p_supplierForest_actual_104585
  · exact g32p_supplierForest_actual_104595
  · exact g32p_supplierForest_actual_104617
  · exact g32p_supplierForest_actual_104638
  · exact g32p_supplierForest_actual_104661
  · exact g32p_supplierForest_actual_104688
  · exact g32p_supplierForest_actual_104693
  · exact g32p_supplierForest_actual_104699
  · exact g32p_supplierForest_actual_104718
  · exact g32p_supplierForest_actual_104734
  · exact g32p_supplierForest_actual_104751
  · exact g32p_supplierForest_actual_104752
  · exact g32p_supplierForest_actual_104831
  · exact g32p_supplierForest_actual_104852
  · exact g32p_supplierForest_actual_104872
  · exact g32p_supplierForest_actual_104873
  · exact g32p_supplierForest_actual_104882
  · exact g32p_supplierForest_actual_104905
  · exact g32p_supplierForest_actual_104907
  · exact g32p_supplierForest_actual_104913
  · exact g32p_supplierForest_actual_105014
  · exact g32p_supplierForest_actual_105035
  · exact g32p_supplierForest_actual_105047
  · exact g32p_supplierForest_actual_105064
  · exact g32p_supplierForest_actual_105068
  · exact g32p_supplierForest_actual_105090
  · exact g32p_supplierForest_actual_105091
  · exact g32p_supplierForest_actual_105092
  · exact g32p_supplierForest_actual_105096
  · exact g32p_supplierForest_actual_105121
  · exact g32p_supplierForest_actual_105150
  · exact g32p_supplierForest_actual_105192
  · exact g32p_supplierForest_actual_105215
  · exact g32p_supplierForest_actual_105224
  · exact g32p_supplierForest_actual_105238
  · exact g32p_supplierForest_actual_105250
  · exact g32p_supplierForest_actual_105254
  · exact g32p_supplierForest_actual_105260
  · exact g32p_supplierForest_actual_105279
  · exact g32p_supplierForest_actual_105293
  · exact g32p_supplierForest_actual_105310
  · exact g32p_supplierForest_actual_105319
  · exact g32p_supplierForest_actual_105328
  · exact g32p_supplierForest_actual_105408
  · exact g32p_supplierForest_actual_105438
  · exact g32p_supplierForest_actual_105447
  · exact g32p_supplierForest_actual_105486
  · exact g32p_supplierForest_actual_105489
  · exact g32p_supplierForest_actual_105540
  · exact g32p_supplierForest_actual_105578
  · exact g32p_supplierForest_actual_105608
  · exact g32p_supplierForest_actual_105616
  · exact g32p_supplierForest_actual_105627
  · exact g32p_supplierForest_actual_105698
  · exact g32p_supplierForest_actual_105704
  · exact g32p_supplierForest_actual_105747
  · exact g32p_supplierForest_actual_105781
  · exact g32p_supplierForest_actual_105786
  · exact g32p_supplierForest_actual_105807
  · exact g32p_supplierForest_actual_105815
  · exact g32p_supplierForest_actual_105855
  · exact g32p_supplierForest_actual_105876
  · exact g32p_supplierForest_actual_105881
  · exact g32p_supplierForest_actual_105885
  · exact g32p_supplierForest_actual_105892
  · exact g32p_supplierForest_actual_105912
  · exact g32p_supplierForest_actual_105927
  · exact g32p_supplierForest_actual_105933
  · exact g32p_supplierForest_actual_105959
  · exact g32p_supplierForest_actual_105960
  · exact g32p_supplierForest_actual_105981
  · exact g32p_supplierForest_actual_106018
  · exact g32p_supplierForest_actual_106021
  · exact g32p_supplierForest_actual_106024
  · exact g32p_supplierForest_actual_106042
  · exact g32p_supplierForest_actual_106054
  · exact g32p_supplierForest_actual_106069
  · exact g32p_supplierForest_actual_106102
  · exact g32p_supplierForest_actual_106117
  · exact g32p_supplierForest_actual_106154
  · exact g32p_supplierForest_actual_106177
  · exact g32p_supplierForest_actual_106181
  · exact g32p_supplierForest_actual_106190
  · exact g32p_supplierForest_actual_106193
  · exact g32p_supplierForest_actual_106203
  · exact g32p_supplierForest_actual_106205
  · exact g32p_supplierForest_actual_106212
  · exact g32p_supplierForest_actual_106240
  · exact g32p_supplierForest_actual_106242
  · exact g32p_supplierForest_actual_106247
  · exact g32p_supplierForest_actual_106260
  · exact g32p_supplierForest_actual_106290
  · exact g32p_supplierForest_actual_106314
  · exact g32p_supplierForest_actual_106319
  · exact g32p_supplierForest_actual_106335
  · exact g32p_supplierForest_actual_106344
  · exact g32p_supplierForest_actual_106347
  · exact g32p_supplierForest_actual_106349
  · exact g32p_supplierForest_actual_106360
  · exact g32p_supplierForest_actual_106389
  · exact g32p_supplierForest_actual_106392
  · exact g32p_supplierForest_actual_106401
  · exact g32p_supplierForest_actual_106409
  · exact g32p_supplierForest_actual_106416
  · exact g32p_supplierForest_actual_106426
  · exact g32p_supplierForest_actual_106441
  · exact g32p_supplierForest_actual_106458
  · exact g32p_supplierForest_actual_106459
  · exact g32p_supplierForest_actual_106473
  · exact g32p_supplierForest_actual_106483
  · exact g32p_supplierForest_actual_106497
  · exact g32p_supplierForest_actual_106529
  · exact g32p_supplierForest_actual_106550
  · exact g32p_supplierForest_actual_106558
  · exact g32p_supplierForest_actual_106588
  · exact g32p_supplierForest_actual_106599
  · exact g32p_supplierForest_actual_106612
  · exact g32p_supplierForest_actual_106615
  · exact g32p_supplierForest_actual_106627
  · exact g32p_supplierForest_actual_106681
  · exact g32p_supplierForest_actual_106688
  · exact g32p_supplierForest_actual_106712
  · exact g32p_supplierForest_actual_106740
  · exact g32p_supplierForest_actual_106743
  · exact g32p_supplierForest_actual_106757
  · exact g32p_supplierForest_actual_106761
  · exact g32p_supplierForest_actual_106778
  · exact g32p_supplierForest_actual_106812
  · exact g32p_supplierForest_actual_106888
  · exact g32p_supplierForest_actual_106937
  · exact g32p_supplierForest_actual_106941
  · exact g32p_supplierForest_actual_106949
  · exact g32p_supplierForest_actual_106953
  · exact g32p_supplierForest_actual_106980
  · exact g32p_supplierForest_actual_106996
  · exact g32p_supplierForest_actual_107056
  · exact g32p_supplierForest_actual_107081
  · exact g32p_supplierForest_actual_107084
  · exact g32p_supplierForest_actual_107116
  · exact g32p_supplierForest_actual_107147
  · exact g32p_supplierForest_actual_107192
  · exact g32p_supplierForest_actual_107196
  · exact g32p_supplierForest_actual_107207
  · exact g32p_supplierForest_actual_107220
  · exact g32p_supplierForest_actual_107225
  · exact g32p_supplierForest_actual_107260
  · exact g32p_supplierForest_actual_107287
  · exact g32p_supplierForest_actual_107310
  · exact g32p_supplierForest_actual_107312
  · exact g32p_supplierForest_actual_107339
  · exact g32p_supplierForest_actual_107350
  · exact g32p_supplierForest_actual_107354
  · exact g32p_supplierForest_actual_107365
  · exact g32p_supplierForest_actual_107369
  · exact g32p_supplierForest_actual_107434
  · exact g32p_supplierForest_actual_107447
  · exact g32p_supplierForest_actual_107449
  · exact g32p_supplierForest_actual_107475
  · exact g32p_supplierForest_actual_107480
  · exact g32p_supplierForest_actual_107556
  · exact g32p_supplierForest_actual_107568
  · exact g32p_supplierForest_actual_107586
  · exact g32p_supplierForest_actual_107591
  · exact g32p_supplierForest_actual_107594
  · exact g32p_supplierForest_actual_107612
  · exact g32p_supplierForest_actual_107633
  · exact g32p_supplierForest_actual_107634
  · exact g32p_supplierForest_actual_107665
  · exact g32p_supplierForest_actual_107732
  · exact g32p_supplierForest_actual_107742
  · exact g32p_supplierForest_actual_107760
  · exact g32p_supplierForest_actual_107811
  · exact g32p_supplierForest_actual_107816
  · exact g32p_supplierForest_actual_107823
  · exact g32p_supplierForest_actual_107862
  · exact g32p_supplierForest_actual_107889
  · exact g32p_supplierForest_actual_107891
  · exact g32p_supplierForest_actual_107915
  · exact g32p_supplierForest_actual_107938
  · exact g32p_supplierForest_actual_108012
  · exact g32p_supplierForest_actual_108017
  · exact g32p_supplierForest_actual_108022
  · exact g32p_supplierForest_actual_108029
  · exact g32p_supplierForest_actual_108037
  · exact g32p_supplierForest_actual_108066
  · exact g32p_supplierForest_actual_108070
  · exact g32p_supplierForest_actual_108095

def g32p_supplierForest_nodes_077 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_108117 else g32p_supplierForest_node_108135) else (if i.val < 3 then g32p_supplierForest_node_108176 else g32p_supplierForest_node_108321)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_108330 else g32p_supplierForest_node_108344) else (if i.val < 7 then g32p_supplierForest_node_108383 else g32p_supplierForest_node_108405))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_108409 else g32p_supplierForest_node_108471) else (if i.val < 11 then g32p_supplierForest_node_108507 else g32p_supplierForest_node_108510)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_108520 else g32p_supplierForest_node_108523) else (if i.val < 15 then g32p_supplierForest_node_108528 else g32p_supplierForest_node_108531)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_108545 else g32p_supplierForest_node_108560) else (if i.val < 19 then g32p_supplierForest_node_108606 else g32p_supplierForest_node_108617)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_108623 else g32p_supplierForest_node_108635) else (if i.val < 23 then g32p_supplierForest_node_108638 else g32p_supplierForest_node_108640))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_108641 else g32p_supplierForest_node_108692) else (if i.val < 27 then g32p_supplierForest_node_108696 else g32p_supplierForest_node_108720)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_108750 else g32p_supplierForest_node_108780) else (if i.val < 31 then g32p_supplierForest_node_108783 else g32p_supplierForest_node_108787))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_108789 else g32p_supplierForest_node_108821) else (if i.val < 35 then g32p_supplierForest_node_108837 else g32p_supplierForest_node_108840)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_108858 else g32p_supplierForest_node_108866) else (if i.val < 39 then g32p_supplierForest_node_108884 else g32p_supplierForest_node_108885))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_108899 else g32p_supplierForest_node_108925) else (if i.val < 43 then g32p_supplierForest_node_108954 else g32p_supplierForest_node_108963)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_108991 else g32p_supplierForest_node_109010) else (if i.val < 47 then g32p_supplierForest_node_109063 else g32p_supplierForest_node_109064)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_109068 else g32p_supplierForest_node_109082) else (if i.val < 51 then g32p_supplierForest_node_109106 else g32p_supplierForest_node_109109)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_109156 else g32p_supplierForest_node_109166) else (if i.val < 55 then g32p_supplierForest_node_109172 else g32p_supplierForest_node_109174))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_109176 else g32p_supplierForest_node_109178) else (if i.val < 59 then g32p_supplierForest_node_109179 else g32p_supplierForest_node_109187)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_109214 else g32p_supplierForest_node_109267) else (if i.val < 63 then g32p_supplierForest_node_109345 else g32p_supplierForest_node_109356)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_109366 else g32p_supplierForest_node_109416) else (if i.val < 67 then g32p_supplierForest_node_109438 else g32p_supplierForest_node_109469)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_109479 else g32p_supplierForest_node_109500) else (if i.val < 71 then g32p_supplierForest_node_109579 else g32p_supplierForest_node_109614))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_109615 else g32p_supplierForest_node_109631) else (if i.val < 75 then g32p_supplierForest_node_109634 else g32p_supplierForest_node_109639)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_109648 else g32p_supplierForest_node_109675) else (if i.val < 79 then g32p_supplierForest_node_109683 else g32p_supplierForest_node_109685)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_109696 else g32p_supplierForest_node_109721) else (if i.val < 83 then g32p_supplierForest_node_109731 else g32p_supplierForest_node_109782)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_109783 else g32p_supplierForest_node_109800) else (if i.val < 87 then g32p_supplierForest_node_109930 else g32p_supplierForest_node_109934))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_109949 else g32p_supplierForest_node_109990) else (if i.val < 91 then g32p_supplierForest_node_109991 else g32p_supplierForest_node_110008)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_110021 else g32p_supplierForest_node_110026) else (if i.val < 95 then g32p_supplierForest_node_110032 else g32p_supplierForest_node_110055))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_110058 else g32p_supplierForest_node_110091) else (if i.val < 99 then g32p_supplierForest_node_110103 else g32p_supplierForest_node_110134)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_110169 else g32p_supplierForest_node_110201) else (if i.val < 103 then g32p_supplierForest_node_110238 else g32p_supplierForest_node_110245))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_110271 else g32p_supplierForest_node_110272) else (if i.val < 107 then g32p_supplierForest_node_110306 else g32p_supplierForest_node_110310)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_110329 else g32p_supplierForest_node_110398) else (if i.val < 111 then g32p_supplierForest_node_110403 else g32p_supplierForest_node_110409)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_110436 else g32p_supplierForest_node_110501) else (if i.val < 115 then g32p_supplierForest_node_110537 else g32p_supplierForest_node_110584)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_110601 else g32p_supplierForest_node_110613) else (if i.val < 119 then g32p_supplierForest_node_110617 else g32p_supplierForest_node_110672))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_110690 else g32p_supplierForest_node_110732) else (if i.val < 123 then g32p_supplierForest_node_110734 else g32p_supplierForest_node_110751)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_110802 else g32p_supplierForest_node_110859) else (if i.val < 127 then g32p_supplierForest_node_110892 else g32p_supplierForest_node_110949))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_110959 else g32p_supplierForest_node_110964) else (if i.val < 131 then g32p_supplierForest_node_111009 else g32p_supplierForest_node_111038)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_111043 else g32p_supplierForest_node_111111) else (if i.val < 135 then g32p_supplierForest_node_111141 else g32p_supplierForest_node_111146))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_111175 else g32p_supplierForest_node_111191) else (if i.val < 139 then g32p_supplierForest_node_111201 else g32p_supplierForest_node_111225)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_111226 else g32p_supplierForest_node_111230) else (if i.val < 143 then g32p_supplierForest_node_111238 else g32p_supplierForest_node_111249)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_111265 else g32p_supplierForest_node_111274) else (if i.val < 147 then g32p_supplierForest_node_111297 else g32p_supplierForest_node_111306)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_111309 else g32p_supplierForest_node_111319) else (if i.val < 151 then g32p_supplierForest_node_111320 else g32p_supplierForest_node_111372))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_111375 else g32p_supplierForest_node_111419) else (if i.val < 155 then g32p_supplierForest_node_111443 else g32p_supplierForest_node_111481)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_111482 else g32p_supplierForest_node_111511) else (if i.val < 159 then g32p_supplierForest_node_111531 else g32p_supplierForest_node_111539))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_111606 else g32p_supplierForest_node_111655) else (if i.val < 163 then g32p_supplierForest_node_111713 else g32p_supplierForest_node_111714)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_111730 else g32p_supplierForest_node_111740) else (if i.val < 167 then g32p_supplierForest_node_111768 else g32p_supplierForest_node_111789))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_111857 else g32p_supplierForest_node_111897) else (if i.val < 171 then g32p_supplierForest_node_111907 else g32p_supplierForest_node_111928)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_111946 else g32p_supplierForest_node_111972) else (if i.val < 175 then g32p_supplierForest_node_111979 else g32p_supplierForest_node_111991)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_112006 else g32p_supplierForest_node_112039) else (if i.val < 179 then g32p_supplierForest_node_112098 else g32p_supplierForest_node_112118)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_112127 else g32p_supplierForest_node_112138) else (if i.val < 183 then g32p_supplierForest_node_112146 else g32p_supplierForest_node_112148))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_112172 else g32p_supplierForest_node_112181) else (if i.val < 187 then g32p_supplierForest_node_112206 else g32p_supplierForest_node_112246)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_112267 else g32p_supplierForest_node_112271) else (if i.val < 191 then g32p_supplierForest_node_112284 else g32p_supplierForest_node_112285)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_112300 else g32p_supplierForest_node_112307) else (if i.val < 195 then g32p_supplierForest_node_112338 else g32p_supplierForest_node_112343)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_112426 else g32p_supplierForest_node_112432) else (if i.val < 199 then g32p_supplierForest_node_112443 else g32p_supplierForest_node_112450))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_112552 else g32p_supplierForest_node_112554) else (if i.val < 203 then g32p_supplierForest_node_112558 else g32p_supplierForest_node_112622)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_112694 else g32p_supplierForest_node_112699) else (if i.val < 207 then g32p_supplierForest_node_112719 else g32p_supplierForest_node_112738)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_112777 else g32p_supplierForest_node_112780) else (if i.val < 211 then g32p_supplierForest_node_112790 else g32p_supplierForest_node_112794)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_112824 else g32p_supplierForest_node_112875) else (if i.val < 215 then g32p_supplierForest_node_112886 else g32p_supplierForest_node_112899))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_112900 else g32p_supplierForest_node_112901) else (if i.val < 219 then g32p_supplierForest_node_112904 else g32p_supplierForest_node_112911)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_112928 else g32p_supplierForest_node_112937) else (if i.val < 223 then g32p_supplierForest_node_112993 else g32p_supplierForest_node_112994))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_113013 else g32p_supplierForest_node_113018) else (if i.val < 227 then g32p_supplierForest_node_113042 else g32p_supplierForest_node_113048)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_113071 else g32p_supplierForest_node_113081) else (if i.val < 231 then g32p_supplierForest_node_113084 else g32p_supplierForest_node_113092))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_113096 else g32p_supplierForest_node_113104) else (if i.val < 235 then g32p_supplierForest_node_113114 else g32p_supplierForest_node_113165)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_113177 else g32p_supplierForest_node_113196) else (if i.val < 239 then g32p_supplierForest_node_113205 else g32p_supplierForest_node_113221)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_113231 else g32p_supplierForest_node_113269) else (if i.val < 243 then g32p_supplierForest_node_113274 else g32p_supplierForest_node_113297)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_113304 else g32p_supplierForest_node_113319) else (if i.val < 247 then g32p_supplierForest_node_113323 else g32p_supplierForest_node_113327))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_113360 else g32p_supplierForest_node_113400) else (if i.val < 251 then g32p_supplierForest_node_113408 else g32p_supplierForest_node_113413)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_113418 else g32p_supplierForest_node_113434) else (if i.val < 255 then g32p_supplierForest_node_113446 else g32p_supplierForest_node_113481))))))))

def g32p_supplierForest_classes_077 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 57) else (if i.val < 3 then 60 else 14)) else (if i.val < 6 then (if i.val < 5 then 57 else 60) else (if i.val < 7 then 59 else 57))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 59 else 91) else (if i.val < 11 then 15 else 58)) else (if i.val < 14 then (if i.val < 13 then 15 else 57) else (if i.val < 15 then 60 else 29)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 57 else 15) else (if i.val < 19 then 17 else 60)) else (if i.val < 22 then (if i.val < 21 then 34 else 57) else (if i.val < 23 then 30 else 33))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 66 else 35) else (if i.val < 27 then 60 else 64)) else (if i.val < 30 then (if i.val < 29 then 62 else 64) else (if i.val < 31 then 30 else 16))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 57 else 66) else (if i.val < 35 then 30 else 57)) else (if i.val < 38 then (if i.val < 37 then 63 else 29) else (if i.val < 39 then 30 else 30))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 57 else 29) else (if i.val < 43 then 16 else 30)) else (if i.val < 46 then (if i.val < 45 then 66 else 34) else (if i.val < 47 then 60 else 59)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 59 else 57) else (if i.val < 51 then 66 else 57)) else (if i.val < 54 then (if i.val < 53 then 59 else 57) else (if i.val < 55 then 61 else 60))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 57 else 57) else (if i.val < 59 then 57 else 30)) else (if i.val < 62 then (if i.val < 61 then 60 else 30) else (if i.val < 63 then 29 else 36)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 57 else 29) else (if i.val < 67 then 63 else 57)) else (if i.val < 70 then (if i.val < 69 then 16 else 29) else (if i.val < 71 then 15 else 60))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 57 else 57) else (if i.val < 75 then 60 else 91)) else (if i.val < 78 then (if i.val < 77 then 29 else 60) else (if i.val < 79 then 61 else 30)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 57 else 60) else (if i.val < 83 then 63 else 16)) else (if i.val < 86 then (if i.val < 85 then 36 else 36) else (if i.val < 87 then 30 else 57))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 57 else 57) else (if i.val < 91 then 29 else 59)) else (if i.val < 94 then (if i.val < 93 then 29 else 36) else (if i.val < 95 then 57 else 16))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 36 else 29) else (if i.val < 99 then 30 else 33)) else (if i.val < 102 then (if i.val < 101 then 29 else 62) else (if i.val < 103 then 30 else 29))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 60 else 66) else (if i.val < 107 then 29 else 66)) else (if i.val < 110 then (if i.val < 109 then 66 else 59) else (if i.val < 111 then 60 else 57)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 57 else 16) else (if i.val < 115 then 57 else 29)) else (if i.val < 118 then (if i.val < 117 then 34 else 30) else (if i.val < 119 then 34 else 15))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 15 else 63) else (if i.val < 123 then 66 else 66)) else (if i.val < 126 then (if i.val < 125 then 34 else 66) else (if i.val < 127 then 29 else 16))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 36 else 60) else (if i.val < 131 then 34 else 57)) else (if i.val < 134 then (if i.val < 133 then 29 else 34) else (if i.val < 135 then 29 else 57))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 30 else 30) else (if i.val < 139 then 58 else 57)) else (if i.val < 142 then (if i.val < 141 then 58 else 57) else (if i.val < 143 then 17 else 62)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 33 else 59) else (if i.val < 147 then 29 else 29)) else (if i.val < 150 then (if i.val < 149 then 58 else 30) else (if i.val < 151 then 58 else 57))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 30 else 62) else (if i.val < 155 then 90 else 29)) else (if i.val < 158 then (if i.val < 157 then 57 else 58) else (if i.val < 159 then 30 else 30))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 66 else 66) else (if i.val < 163 then 61 else 57)) else (if i.val < 166 then (if i.val < 165 then 14 else 59) else (if i.val < 167 then 16 else 57))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 57 else 30) else (if i.val < 171 then 34 else 29)) else (if i.val < 174 then (if i.val < 173 then 30 else 30) else (if i.val < 175 then 60 else 59)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 57 else 60) else (if i.val < 179 then 66 else 30)) else (if i.val < 182 then (if i.val < 181 then 29 else 66) else (if i.val < 183 then 65 else 30))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 33 else 63) else (if i.val < 187 then 59 else 34)) else (if i.val < 190 then (if i.val < 189 then 30 else 58) else (if i.val < 191 then 59 else 34)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 33 else 57) else (if i.val < 195 then 34 else 57)) else (if i.val < 198 then (if i.val < 197 then 60 else 93) else (if i.val < 199 then 57 else 14))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 36 else 57) else (if i.val < 203 then 59 else 60)) else (if i.val < 206 then (if i.val < 205 then 17 else 29) else (if i.val < 207 then 30 else 30)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 16 else 30) else (if i.val < 211 then 60 else 57)) else (if i.val < 214 then (if i.val < 213 then 61 else 57) else (if i.val < 215 then 59 else 57))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 58 else 17) else (if i.val < 219 then 57 else 30)) else (if i.val < 222 then (if i.val < 221 then 33 else 57) else (if i.val < 223 then 30 else 90))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 60 else 59) else (if i.val < 227 then 57 else 32)) else (if i.val < 230 then (if i.val < 229 then 30 else 36) else (if i.val < 231 then 61 else 16))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 66 else 30) else (if i.val < 235 then 58 else 57)) else (if i.val < 238 then (if i.val < 237 then 29 else 30) else (if i.val < 239 then 30 else 57)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 36 else 17) else (if i.val < 243 then 57 else 59)) else (if i.val < 246 then (if i.val < 245 then 61 else 66) else (if i.val < 247 then 34 else 57))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 61 else 33) else (if i.val < 251 then 17 else 62)) else (if i.val < 254 then (if i.val < 253 then 57 else 30) else (if i.val < 255 then 57 else 57))))))))

theorem g32p_supplierForest_actual_077 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_077 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_077 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_108117
  · exact g32p_supplierForest_actual_108135
  · exact g32p_supplierForest_actual_108176
  · exact g32p_supplierForest_actual_108321
  · exact g32p_supplierForest_actual_108330
  · exact g32p_supplierForest_actual_108344
  · exact g32p_supplierForest_actual_108383
  · exact g32p_supplierForest_actual_108405
  · exact g32p_supplierForest_actual_108409
  · exact g32p_supplierForest_actual_108471
  · exact g32p_supplierForest_actual_108507
  · exact g32p_supplierForest_actual_108510
  · exact g32p_supplierForest_actual_108520
  · exact g32p_supplierForest_actual_108523
  · exact g32p_supplierForest_actual_108528
  · exact g32p_supplierForest_actual_108531
  · exact g32p_supplierForest_actual_108545
  · exact g32p_supplierForest_actual_108560
  · exact g32p_supplierForest_actual_108606
  · exact g32p_supplierForest_actual_108617
  · exact g32p_supplierForest_actual_108623
  · exact g32p_supplierForest_actual_108635
  · exact g32p_supplierForest_actual_108638
  · exact g32p_supplierForest_actual_108640
  · exact g32p_supplierForest_actual_108641
  · exact g32p_supplierForest_actual_108692
  · exact g32p_supplierForest_actual_108696
  · exact g32p_supplierForest_actual_108720
  · exact g32p_supplierForest_actual_108750
  · exact g32p_supplierForest_actual_108780
  · exact g32p_supplierForest_actual_108783
  · exact g32p_supplierForest_actual_108787
  · exact g32p_supplierForest_actual_108789
  · exact g32p_supplierForest_actual_108821
  · exact g32p_supplierForest_actual_108837
  · exact g32p_supplierForest_actual_108840
  · exact g32p_supplierForest_actual_108858
  · exact g32p_supplierForest_actual_108866
  · exact g32p_supplierForest_actual_108884
  · exact g32p_supplierForest_actual_108885
  · exact g32p_supplierForest_actual_108899
  · exact g32p_supplierForest_actual_108925
  · exact g32p_supplierForest_actual_108954
  · exact g32p_supplierForest_actual_108963
  · exact g32p_supplierForest_actual_108991
  · exact g32p_supplierForest_actual_109010
  · exact g32p_supplierForest_actual_109063
  · exact g32p_supplierForest_actual_109064
  · exact g32p_supplierForest_actual_109068
  · exact g32p_supplierForest_actual_109082
  · exact g32p_supplierForest_actual_109106
  · exact g32p_supplierForest_actual_109109
  · exact g32p_supplierForest_actual_109156
  · exact g32p_supplierForest_actual_109166
  · exact g32p_supplierForest_actual_109172
  · exact g32p_supplierForest_actual_109174
  · exact g32p_supplierForest_actual_109176
  · exact g32p_supplierForest_actual_109178
  · exact g32p_supplierForest_actual_109179
  · exact g32p_supplierForest_actual_109187
  · exact g32p_supplierForest_actual_109214
  · exact g32p_supplierForest_actual_109267
  · exact g32p_supplierForest_actual_109345
  · exact g32p_supplierForest_actual_109356
  · exact g32p_supplierForest_actual_109366
  · exact g32p_supplierForest_actual_109416
  · exact g32p_supplierForest_actual_109438
  · exact g32p_supplierForest_actual_109469
  · exact g32p_supplierForest_actual_109479
  · exact g32p_supplierForest_actual_109500
  · exact g32p_supplierForest_actual_109579
  · exact g32p_supplierForest_actual_109614
  · exact g32p_supplierForest_actual_109615
  · exact g32p_supplierForest_actual_109631
  · exact g32p_supplierForest_actual_109634
  · exact g32p_supplierForest_actual_109639
  · exact g32p_supplierForest_actual_109648
  · exact g32p_supplierForest_actual_109675
  · exact g32p_supplierForest_actual_109683
  · exact g32p_supplierForest_actual_109685
  · exact g32p_supplierForest_actual_109696
  · exact g32p_supplierForest_actual_109721
  · exact g32p_supplierForest_actual_109731
  · exact g32p_supplierForest_actual_109782
  · exact g32p_supplierForest_actual_109783
  · exact g32p_supplierForest_actual_109800
  · exact g32p_supplierForest_actual_109930
  · exact g32p_supplierForest_actual_109934
  · exact g32p_supplierForest_actual_109949
  · exact g32p_supplierForest_actual_109990
  · exact g32p_supplierForest_actual_109991
  · exact g32p_supplierForest_actual_110008
  · exact g32p_supplierForest_actual_110021
  · exact g32p_supplierForest_actual_110026
  · exact g32p_supplierForest_actual_110032
  · exact g32p_supplierForest_actual_110055
  · exact g32p_supplierForest_actual_110058
  · exact g32p_supplierForest_actual_110091
  · exact g32p_supplierForest_actual_110103
  · exact g32p_supplierForest_actual_110134
  · exact g32p_supplierForest_actual_110169
  · exact g32p_supplierForest_actual_110201
  · exact g32p_supplierForest_actual_110238
  · exact g32p_supplierForest_actual_110245
  · exact g32p_supplierForest_actual_110271
  · exact g32p_supplierForest_actual_110272
  · exact g32p_supplierForest_actual_110306
  · exact g32p_supplierForest_actual_110310
  · exact g32p_supplierForest_actual_110329
  · exact g32p_supplierForest_actual_110398
  · exact g32p_supplierForest_actual_110403
  · exact g32p_supplierForest_actual_110409
  · exact g32p_supplierForest_actual_110436
  · exact g32p_supplierForest_actual_110501
  · exact g32p_supplierForest_actual_110537
  · exact g32p_supplierForest_actual_110584
  · exact g32p_supplierForest_actual_110601
  · exact g32p_supplierForest_actual_110613
  · exact g32p_supplierForest_actual_110617
  · exact g32p_supplierForest_actual_110672
  · exact g32p_supplierForest_actual_110690
  · exact g32p_supplierForest_actual_110732
  · exact g32p_supplierForest_actual_110734
  · exact g32p_supplierForest_actual_110751
  · exact g32p_supplierForest_actual_110802
  · exact g32p_supplierForest_actual_110859
  · exact g32p_supplierForest_actual_110892
  · exact g32p_supplierForest_actual_110949
  · exact g32p_supplierForest_actual_110959
  · exact g32p_supplierForest_actual_110964
  · exact g32p_supplierForest_actual_111009
  · exact g32p_supplierForest_actual_111038
  · exact g32p_supplierForest_actual_111043
  · exact g32p_supplierForest_actual_111111
  · exact g32p_supplierForest_actual_111141
  · exact g32p_supplierForest_actual_111146
  · exact g32p_supplierForest_actual_111175
  · exact g32p_supplierForest_actual_111191
  · exact g32p_supplierForest_actual_111201
  · exact g32p_supplierForest_actual_111225
  · exact g32p_supplierForest_actual_111226
  · exact g32p_supplierForest_actual_111230
  · exact g32p_supplierForest_actual_111238
  · exact g32p_supplierForest_actual_111249
  · exact g32p_supplierForest_actual_111265
  · exact g32p_supplierForest_actual_111274
  · exact g32p_supplierForest_actual_111297
  · exact g32p_supplierForest_actual_111306
  · exact g32p_supplierForest_actual_111309
  · exact g32p_supplierForest_actual_111319
  · exact g32p_supplierForest_actual_111320
  · exact g32p_supplierForest_actual_111372
  · exact g32p_supplierForest_actual_111375
  · exact g32p_supplierForest_actual_111419
  · exact g32p_supplierForest_actual_111443
  · exact g32p_supplierForest_actual_111481
  · exact g32p_supplierForest_actual_111482
  · exact g32p_supplierForest_actual_111511
  · exact g32p_supplierForest_actual_111531
  · exact g32p_supplierForest_actual_111539
  · exact g32p_supplierForest_actual_111606
  · exact g32p_supplierForest_actual_111655
  · exact g32p_supplierForest_actual_111713
  · exact g32p_supplierForest_actual_111714
  · exact g32p_supplierForest_actual_111730
  · exact g32p_supplierForest_actual_111740
  · exact g32p_supplierForest_actual_111768
  · exact g32p_supplierForest_actual_111789
  · exact g32p_supplierForest_actual_111857
  · exact g32p_supplierForest_actual_111897
  · exact g32p_supplierForest_actual_111907
  · exact g32p_supplierForest_actual_111928
  · exact g32p_supplierForest_actual_111946
  · exact g32p_supplierForest_actual_111972
  · exact g32p_supplierForest_actual_111979
  · exact g32p_supplierForest_actual_111991
  · exact g32p_supplierForest_actual_112006
  · exact g32p_supplierForest_actual_112039
  · exact g32p_supplierForest_actual_112098
  · exact g32p_supplierForest_actual_112118
  · exact g32p_supplierForest_actual_112127
  · exact g32p_supplierForest_actual_112138
  · exact g32p_supplierForest_actual_112146
  · exact g32p_supplierForest_actual_112148
  · exact g32p_supplierForest_actual_112172
  · exact g32p_supplierForest_actual_112181
  · exact g32p_supplierForest_actual_112206
  · exact g32p_supplierForest_actual_112246
  · exact g32p_supplierForest_actual_112267
  · exact g32p_supplierForest_actual_112271
  · exact g32p_supplierForest_actual_112284
  · exact g32p_supplierForest_actual_112285
  · exact g32p_supplierForest_actual_112300
  · exact g32p_supplierForest_actual_112307
  · exact g32p_supplierForest_actual_112338
  · exact g32p_supplierForest_actual_112343
  · exact g32p_supplierForest_actual_112426
  · exact g32p_supplierForest_actual_112432
  · exact g32p_supplierForest_actual_112443
  · exact g32p_supplierForest_actual_112450
  · exact g32p_supplierForest_actual_112552
  · exact g32p_supplierForest_actual_112554
  · exact g32p_supplierForest_actual_112558
  · exact g32p_supplierForest_actual_112622
  · exact g32p_supplierForest_actual_112694
  · exact g32p_supplierForest_actual_112699
  · exact g32p_supplierForest_actual_112719
  · exact g32p_supplierForest_actual_112738
  · exact g32p_supplierForest_actual_112777
  · exact g32p_supplierForest_actual_112780
  · exact g32p_supplierForest_actual_112790
  · exact g32p_supplierForest_actual_112794
  · exact g32p_supplierForest_actual_112824
  · exact g32p_supplierForest_actual_112875
  · exact g32p_supplierForest_actual_112886
  · exact g32p_supplierForest_actual_112899
  · exact g32p_supplierForest_actual_112900
  · exact g32p_supplierForest_actual_112901
  · exact g32p_supplierForest_actual_112904
  · exact g32p_supplierForest_actual_112911
  · exact g32p_supplierForest_actual_112928
  · exact g32p_supplierForest_actual_112937
  · exact g32p_supplierForest_actual_112993
  · exact g32p_supplierForest_actual_112994
  · exact g32p_supplierForest_actual_113013
  · exact g32p_supplierForest_actual_113018
  · exact g32p_supplierForest_actual_113042
  · exact g32p_supplierForest_actual_113048
  · exact g32p_supplierForest_actual_113071
  · exact g32p_supplierForest_actual_113081
  · exact g32p_supplierForest_actual_113084
  · exact g32p_supplierForest_actual_113092
  · exact g32p_supplierForest_actual_113096
  · exact g32p_supplierForest_actual_113104
  · exact g32p_supplierForest_actual_113114
  · exact g32p_supplierForest_actual_113165
  · exact g32p_supplierForest_actual_113177
  · exact g32p_supplierForest_actual_113196
  · exact g32p_supplierForest_actual_113205
  · exact g32p_supplierForest_actual_113221
  · exact g32p_supplierForest_actual_113231
  · exact g32p_supplierForest_actual_113269
  · exact g32p_supplierForest_actual_113274
  · exact g32p_supplierForest_actual_113297
  · exact g32p_supplierForest_actual_113304
  · exact g32p_supplierForest_actual_113319
  · exact g32p_supplierForest_actual_113323
  · exact g32p_supplierForest_actual_113327
  · exact g32p_supplierForest_actual_113360
  · exact g32p_supplierForest_actual_113400
  · exact g32p_supplierForest_actual_113408
  · exact g32p_supplierForest_actual_113413
  · exact g32p_supplierForest_actual_113418
  · exact g32p_supplierForest_actual_113434
  · exact g32p_supplierForest_actual_113446
  · exact g32p_supplierForest_actual_113481

def g32p_supplierForest_nodes_078 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_113483 else g32p_supplierForest_node_113551) else (if i.val < 3 then g32p_supplierForest_node_113590 else g32p_supplierForest_node_113600)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_113607 else g32p_supplierForest_node_113608) else (if i.val < 7 then g32p_supplierForest_node_113633 else g32p_supplierForest_node_113637))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_113690 else g32p_supplierForest_node_113692) else (if i.val < 11 then g32p_supplierForest_node_113694 else g32p_supplierForest_node_113697)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_113707 else g32p_supplierForest_node_113720) else (if i.val < 15 then g32p_supplierForest_node_113736 else g32p_supplierForest_node_113742)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_113790 else g32p_supplierForest_node_113797) else (if i.val < 19 then g32p_supplierForest_node_113816 else g32p_supplierForest_node_113819)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_113838 else g32p_supplierForest_node_113841) else (if i.val < 23 then g32p_supplierForest_node_113844 else g32p_supplierForest_node_113859))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_113879 else g32p_supplierForest_node_113889) else (if i.val < 27 then g32p_supplierForest_node_113926 else g32p_supplierForest_node_113933)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_113969 else g32p_supplierForest_node_113974) else (if i.val < 31 then g32p_supplierForest_node_114014 else g32p_supplierForest_node_114020))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_114032 else g32p_supplierForest_node_114075) else (if i.val < 35 then g32p_supplierForest_node_114131 else g32p_supplierForest_node_114133)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_114143 else g32p_supplierForest_node_114146) else (if i.val < 39 then g32p_supplierForest_node_114151 else g32p_supplierForest_node_114159))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_114163 else g32p_supplierForest_node_114205) else (if i.val < 43 then g32p_supplierForest_node_114232 else g32p_supplierForest_node_114266)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_114270 else g32p_supplierForest_node_114274) else (if i.val < 47 then g32p_supplierForest_node_114276 else g32p_supplierForest_node_114281)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_114289 else g32p_supplierForest_node_114317) else (if i.val < 51 then g32p_supplierForest_node_114354 else g32p_supplierForest_node_114394)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_114406 else g32p_supplierForest_node_114422) else (if i.val < 55 then g32p_supplierForest_node_114448 else g32p_supplierForest_node_114456))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_114500 else g32p_supplierForest_node_114544) else (if i.val < 59 then g32p_supplierForest_node_114581 else g32p_supplierForest_node_114635)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_114638 else g32p_supplierForest_node_114655) else (if i.val < 63 then g32p_supplierForest_node_114669 else g32p_supplierForest_node_114715)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_114783 else g32p_supplierForest_node_114785) else (if i.val < 67 then g32p_supplierForest_node_114810 else g32p_supplierForest_node_114854)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_114862 else g32p_supplierForest_node_114863) else (if i.val < 71 then g32p_supplierForest_node_114869 else g32p_supplierForest_node_114871))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_114884 else g32p_supplierForest_node_114898) else (if i.val < 75 then g32p_supplierForest_node_114922 else g32p_supplierForest_node_114933)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_114970 else g32p_supplierForest_node_114985) else (if i.val < 79 then g32p_supplierForest_node_114986 else g32p_supplierForest_node_115019)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_115027 else g32p_supplierForest_node_115046) else (if i.val < 83 then g32p_supplierForest_node_115101 else g32p_supplierForest_node_115109)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_115110 else g32p_supplierForest_node_115113) else (if i.val < 87 then g32p_supplierForest_node_115134 else g32p_supplierForest_node_115136))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_115139 else g32p_supplierForest_node_115175) else (if i.val < 91 then g32p_supplierForest_node_115200 else g32p_supplierForest_node_115236)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_115237 else g32p_supplierForest_node_115272) else (if i.val < 95 then g32p_supplierForest_node_115343 else g32p_supplierForest_node_115349))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_115375 else g32p_supplierForest_node_115394) else (if i.val < 99 then g32p_supplierForest_node_115400 else g32p_supplierForest_node_115420)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_115421 else g32p_supplierForest_node_115423) else (if i.val < 103 then g32p_supplierForest_node_115437 else g32p_supplierForest_node_115438))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_115452 else g32p_supplierForest_node_115460) else (if i.val < 107 then g32p_supplierForest_node_115463 else g32p_supplierForest_node_115465)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_115486 else g32p_supplierForest_node_115489) else (if i.val < 111 then g32p_supplierForest_node_115511 else g32p_supplierForest_node_115515)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_115526 else g32p_supplierForest_node_115535) else (if i.val < 115 then g32p_supplierForest_node_115539 else g32p_supplierForest_node_115554)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_115566 else g32p_supplierForest_node_115568) else (if i.val < 119 then g32p_supplierForest_node_115570 else g32p_supplierForest_node_115578))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_115588 else g32p_supplierForest_node_115592) else (if i.val < 123 then g32p_supplierForest_node_115595 else g32p_supplierForest_node_115631)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_115647 else g32p_supplierForest_node_115669) else (if i.val < 127 then g32p_supplierForest_node_115705 else g32p_supplierForest_node_115714))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_115742 else g32p_supplierForest_node_115759) else (if i.val < 131 then g32p_supplierForest_node_115812 else g32p_supplierForest_node_115815)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_115821 else g32p_supplierForest_node_115838) else (if i.val < 135 then g32p_supplierForest_node_115841 else g32p_supplierForest_node_115843))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_115860 else g32p_supplierForest_node_115864) else (if i.val < 139 then g32p_supplierForest_node_115883 else g32p_supplierForest_node_115887)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_115906 else g32p_supplierForest_node_115921) else (if i.val < 143 then g32p_supplierForest_node_115954 else g32p_supplierForest_node_115961)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_115975 else g32p_supplierForest_node_115991) else (if i.val < 147 then g32p_supplierForest_node_115993 else g32p_supplierForest_node_115997)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_116052 else g32p_supplierForest_node_116059) else (if i.val < 151 then g32p_supplierForest_node_116064 else g32p_supplierForest_node_116089))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_116095 else g32p_supplierForest_node_116106) else (if i.val < 155 then g32p_supplierForest_node_116145 else g32p_supplierForest_node_116156)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_116160 else g32p_supplierForest_node_116175) else (if i.val < 159 then g32p_supplierForest_node_116176 else g32p_supplierForest_node_116185))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_116198 else g32p_supplierForest_node_116238) else (if i.val < 163 then g32p_supplierForest_node_116325 else g32p_supplierForest_node_116368)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_116381 else g32p_supplierForest_node_116534) else (if i.val < 167 then g32p_supplierForest_node_116543 else g32p_supplierForest_node_116575))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_116604 else g32p_supplierForest_node_116627) else (if i.val < 171 then g32p_supplierForest_node_116657 else g32p_supplierForest_node_116715)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_116830 else g32p_supplierForest_node_116922) else (if i.val < 175 then g32p_supplierForest_node_116924 else g32p_supplierForest_node_116942)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_116969 else g32p_supplierForest_node_116988) else (if i.val < 179 then g32p_supplierForest_node_116993 else g32p_supplierForest_node_116998)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_117010 else g32p_supplierForest_node_117066) else (if i.val < 183 then g32p_supplierForest_node_117089 else g32p_supplierForest_node_117092))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_117100 else g32p_supplierForest_node_117115) else (if i.val < 187 then g32p_supplierForest_node_117125 else g32p_supplierForest_node_117142)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_117151 else g32p_supplierForest_node_117163) else (if i.val < 191 then g32p_supplierForest_node_117224 else g32p_supplierForest_node_117248)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_117264 else g32p_supplierForest_node_117272) else (if i.val < 195 then g32p_supplierForest_node_117319 else g32p_supplierForest_node_117353)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_117363 else g32p_supplierForest_node_117371) else (if i.val < 199 then g32p_supplierForest_node_117373 else g32p_supplierForest_node_117382))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_117383 else g32p_supplierForest_node_117388) else (if i.val < 203 then g32p_supplierForest_node_117473 else g32p_supplierForest_node_117490)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_117534 else g32p_supplierForest_node_117623) else (if i.val < 207 then g32p_supplierForest_node_117639 else g32p_supplierForest_node_117640)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_117650 else g32p_supplierForest_node_117677) else (if i.val < 211 then g32p_supplierForest_node_117678 else g32p_supplierForest_node_117696)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_117700 else g32p_supplierForest_node_117721) else (if i.val < 215 then g32p_supplierForest_node_117727 else g32p_supplierForest_node_117732))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_117751 else g32p_supplierForest_node_117770) else (if i.val < 219 then g32p_supplierForest_node_117809 else g32p_supplierForest_node_117841)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_117864 else g32p_supplierForest_node_117893) else (if i.val < 223 then g32p_supplierForest_node_117917 else g32p_supplierForest_node_117923))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_118054 else g32p_supplierForest_node_118084) else (if i.val < 227 then g32p_supplierForest_node_118101 else g32p_supplierForest_node_118134)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_118135 else g32p_supplierForest_node_118136) else (if i.val < 231 then g32p_supplierForest_node_118171 else g32p_supplierForest_node_118198))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_118213 else g32p_supplierForest_node_118223) else (if i.val < 235 then g32p_supplierForest_node_118242 else g32p_supplierForest_node_118276)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_118279 else g32p_supplierForest_node_118310) else (if i.val < 239 then g32p_supplierForest_node_118337 else g32p_supplierForest_node_118387)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_118440 else g32p_supplierForest_node_118478) else (if i.val < 243 then g32p_supplierForest_node_118480 else g32p_supplierForest_node_118547)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_118550 else g32p_supplierForest_node_118558) else (if i.val < 247 then g32p_supplierForest_node_118578 else g32p_supplierForest_node_118584))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_118595 else g32p_supplierForest_node_118610) else (if i.val < 251 then g32p_supplierForest_node_118656 else g32p_supplierForest_node_118666)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_118685 else g32p_supplierForest_node_118687) else (if i.val < 255 then g32p_supplierForest_node_118724 else g32p_supplierForest_node_118737))))))))

def g32p_supplierForest_classes_078 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 63) else (if i.val < 3 then 60 else 29)) else (if i.val < 6 then (if i.val < 5 then 29 else 61) else (if i.val < 7 then 36 else 61))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 57 else 34) else (if i.val < 11 then 35 else 29)) else (if i.val < 14 then (if i.val < 13 then 34 else 15) else (if i.val < 15 then 30 else 15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 59 else 16) else (if i.val < 19 then 30 else 57)) else (if i.val < 22 then (if i.val < 21 then 66 else 63) else (if i.val < 23 then 31 else 57))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 29 else 57) else (if i.val < 27 then 33 else 57)) else (if i.val < 30 then (if i.val < 29 then 30 else 61) else (if i.val < 31 then 34 else 57))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 57 else 30) else (if i.val < 35 then 29 else 62)) else (if i.val < 38 then (if i.val < 37 then 61 else 58) else (if i.val < 39 then 30 else 30))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 30 else 17) else (if i.val < 43 then 66 else 16)) else (if i.val < 46 then (if i.val < 45 then 29 else 57) else (if i.val < 47 then 57 else 60)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 66 else 66) else (if i.val < 51 then 33 else 57)) else (if i.val < 54 then (if i.val < 53 then 29 else 35) else (if i.val < 55 then 33 else 62))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 57 else 57) else (if i.val < 59 then 66 else 16)) else (if i.val < 62 then (if i.val < 61 then 66 else 57) else (if i.val < 63 then 60 else 29)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 58 else 91) else (if i.val < 67 then 59 else 57)) else (if i.val < 70 then (if i.val < 69 then 60 else 61) else (if i.val < 71 then 60 else 57))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 29 else 34) else (if i.val < 75 then 33 else 57)) else (if i.val < 78 then (if i.val < 77 then 57 else 29) else (if i.val < 79 then 36 else 57)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 33 else 66) else (if i.val < 83 then 29 else 33)) else (if i.val < 86 then (if i.val < 85 then 57 else 62) else (if i.val < 87 then 30 else 59))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 29 else 30) else (if i.val < 91 then 30 else 62)) else (if i.val < 94 then (if i.val < 93 then 60 else 15) else (if i.val < 95 then 29 else 60))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 59 else 61) else (if i.val < 99 then 60 else 66)) else (if i.val < 102 then (if i.val < 101 then 35 else 57) else (if i.val < 103 then 30 else 59))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 15 else 57) else (if i.val < 107 then 35 else 30)) else (if i.val < 110 then (if i.val < 109 then 30 else 35) else (if i.val < 111 then 29 else 30)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 14 else 17) else (if i.val < 115 then 15 else 30)) else (if i.val < 118 then (if i.val < 117 then 34 else 57) else (if i.val < 119 then 59 else 57))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 59 else 15) else (if i.val < 123 then 60 else 29)) else (if i.val < 126 then (if i.val < 125 then 89 else 59) else (if i.val < 127 then 66 else 30))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 90 else 60) else (if i.val < 131 then 66 else 90)) else (if i.val < 134 then (if i.val < 133 then 33 else 91) else (if i.val < 135 then 36 else 35))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 30 else 59) else (if i.val < 139 then 33 else 34)) else (if i.val < 142 then (if i.val < 141 then 36 else 29) else (if i.val < 143 then 30 else 36)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 61 else 58) else (if i.val < 147 then 60 else 30)) else (if i.val < 150 then (if i.val < 149 then 60 else 92) else (if i.val < 151 then 90 else 60))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 57 else 16) else (if i.val < 155 then 57 else 63)) else (if i.val < 158 then (if i.val < 157 then 30 else 61) else (if i.val < 159 then 63 else 30))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 60 else 66) else (if i.val < 163 then 60 else 29)) else (if i.val < 166 then (if i.val < 165 then 60 else 91) else (if i.val < 167 then 34 else 91))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 61 else 33) else (if i.val < 171 then 60 else 60)) else (if i.val < 174 then (if i.val < 173 then 34 else 62) else (if i.val < 175 then 36 else 30)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 57 else 36) else (if i.val < 179 then 34 else 16)) else (if i.val < 182 then (if i.val < 181 then 66 else 30) else (if i.val < 183 then 60 else 92))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 15 else 34) else (if i.val < 187 then 89 else 30)) else (if i.val < 190 then (if i.val < 189 then 87 else 91) else (if i.val < 191 then 57 else 57)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 34 else 57) else (if i.val < 195 then 60 else 59)) else (if i.val < 198 then (if i.val < 197 then 34 else 60) else (if i.val < 199 then 29 else 29))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 30 else 29) else (if i.val < 203 then 34 else 16)) else (if i.val < 206 then (if i.val < 205 then 66 else 57) else (if i.val < 207 then 66 else 66)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 61 else 61) else (if i.val < 211 then 90 else 33)) else (if i.val < 214 then (if i.val < 213 then 89 else 30) else (if i.val < 215 then 60 else 60))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 60 else 61) else (if i.val < 219 then 91 else 36)) else (if i.val < 222 then (if i.val < 221 then 89 else 59) else (if i.val < 223 then 30 else 15))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 66 else 59) else (if i.val < 227 then 60 else 57)) else (if i.val < 230 then (if i.val < 229 then 57 else 30) else (if i.val < 231 then 57 else 66))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 59 else 66) else (if i.val < 235 then 30 else 57)) else (if i.val < 238 then (if i.val < 237 then 57 else 35) else (if i.val < 239 then 57 else 36)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 57 else 66) else (if i.val < 243 then 36 else 66)) else (if i.val < 246 then (if i.val < 245 then 90 else 57) else (if i.val < 247 then 60 else 30))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 32 else 93) else (if i.val < 251 then 36 else 60)) else (if i.val < 254 then (if i.val < 253 then 65 else 59) else (if i.val < 255 then 57 else 57))))))))

theorem g32p_supplierForest_actual_078 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_078 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_078 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_113483
  · exact g32p_supplierForest_actual_113551
  · exact g32p_supplierForest_actual_113590
  · exact g32p_supplierForest_actual_113600
  · exact g32p_supplierForest_actual_113607
  · exact g32p_supplierForest_actual_113608
  · exact g32p_supplierForest_actual_113633
  · exact g32p_supplierForest_actual_113637
  · exact g32p_supplierForest_actual_113690
  · exact g32p_supplierForest_actual_113692
  · exact g32p_supplierForest_actual_113694
  · exact g32p_supplierForest_actual_113697
  · exact g32p_supplierForest_actual_113707
  · exact g32p_supplierForest_actual_113720
  · exact g32p_supplierForest_actual_113736
  · exact g32p_supplierForest_actual_113742
  · exact g32p_supplierForest_actual_113790
  · exact g32p_supplierForest_actual_113797
  · exact g32p_supplierForest_actual_113816
  · exact g32p_supplierForest_actual_113819
  · exact g32p_supplierForest_actual_113838
  · exact g32p_supplierForest_actual_113841
  · exact g32p_supplierForest_actual_113844
  · exact g32p_supplierForest_actual_113859
  · exact g32p_supplierForest_actual_113879
  · exact g32p_supplierForest_actual_113889
  · exact g32p_supplierForest_actual_113926
  · exact g32p_supplierForest_actual_113933
  · exact g32p_supplierForest_actual_113969
  · exact g32p_supplierForest_actual_113974
  · exact g32p_supplierForest_actual_114014
  · exact g32p_supplierForest_actual_114020
  · exact g32p_supplierForest_actual_114032
  · exact g32p_supplierForest_actual_114075
  · exact g32p_supplierForest_actual_114131
  · exact g32p_supplierForest_actual_114133
  · exact g32p_supplierForest_actual_114143
  · exact g32p_supplierForest_actual_114146
  · exact g32p_supplierForest_actual_114151
  · exact g32p_supplierForest_actual_114159
  · exact g32p_supplierForest_actual_114163
  · exact g32p_supplierForest_actual_114205
  · exact g32p_supplierForest_actual_114232
  · exact g32p_supplierForest_actual_114266
  · exact g32p_supplierForest_actual_114270
  · exact g32p_supplierForest_actual_114274
  · exact g32p_supplierForest_actual_114276
  · exact g32p_supplierForest_actual_114281
  · exact g32p_supplierForest_actual_114289
  · exact g32p_supplierForest_actual_114317
  · exact g32p_supplierForest_actual_114354
  · exact g32p_supplierForest_actual_114394
  · exact g32p_supplierForest_actual_114406
  · exact g32p_supplierForest_actual_114422
  · exact g32p_supplierForest_actual_114448
  · exact g32p_supplierForest_actual_114456
  · exact g32p_supplierForest_actual_114500
  · exact g32p_supplierForest_actual_114544
  · exact g32p_supplierForest_actual_114581
  · exact g32p_supplierForest_actual_114635
  · exact g32p_supplierForest_actual_114638
  · exact g32p_supplierForest_actual_114655
  · exact g32p_supplierForest_actual_114669
  · exact g32p_supplierForest_actual_114715
  · exact g32p_supplierForest_actual_114783
  · exact g32p_supplierForest_actual_114785
  · exact g32p_supplierForest_actual_114810
  · exact g32p_supplierForest_actual_114854
  · exact g32p_supplierForest_actual_114862
  · exact g32p_supplierForest_actual_114863
  · exact g32p_supplierForest_actual_114869
  · exact g32p_supplierForest_actual_114871
  · exact g32p_supplierForest_actual_114884
  · exact g32p_supplierForest_actual_114898
  · exact g32p_supplierForest_actual_114922
  · exact g32p_supplierForest_actual_114933
  · exact g32p_supplierForest_actual_114970
  · exact g32p_supplierForest_actual_114985
  · exact g32p_supplierForest_actual_114986
  · exact g32p_supplierForest_actual_115019
  · exact g32p_supplierForest_actual_115027
  · exact g32p_supplierForest_actual_115046
  · exact g32p_supplierForest_actual_115101
  · exact g32p_supplierForest_actual_115109
  · exact g32p_supplierForest_actual_115110
  · exact g32p_supplierForest_actual_115113
  · exact g32p_supplierForest_actual_115134
  · exact g32p_supplierForest_actual_115136
  · exact g32p_supplierForest_actual_115139
  · exact g32p_supplierForest_actual_115175
  · exact g32p_supplierForest_actual_115200
  · exact g32p_supplierForest_actual_115236
  · exact g32p_supplierForest_actual_115237
  · exact g32p_supplierForest_actual_115272
  · exact g32p_supplierForest_actual_115343
  · exact g32p_supplierForest_actual_115349
  · exact g32p_supplierForest_actual_115375
  · exact g32p_supplierForest_actual_115394
  · exact g32p_supplierForest_actual_115400
  · exact g32p_supplierForest_actual_115420
  · exact g32p_supplierForest_actual_115421
  · exact g32p_supplierForest_actual_115423
  · exact g32p_supplierForest_actual_115437
  · exact g32p_supplierForest_actual_115438
  · exact g32p_supplierForest_actual_115452
  · exact g32p_supplierForest_actual_115460
  · exact g32p_supplierForest_actual_115463
  · exact g32p_supplierForest_actual_115465
  · exact g32p_supplierForest_actual_115486
  · exact g32p_supplierForest_actual_115489
  · exact g32p_supplierForest_actual_115511
  · exact g32p_supplierForest_actual_115515
  · exact g32p_supplierForest_actual_115526
  · exact g32p_supplierForest_actual_115535
  · exact g32p_supplierForest_actual_115539
  · exact g32p_supplierForest_actual_115554
  · exact g32p_supplierForest_actual_115566
  · exact g32p_supplierForest_actual_115568
  · exact g32p_supplierForest_actual_115570
  · exact g32p_supplierForest_actual_115578
  · exact g32p_supplierForest_actual_115588
  · exact g32p_supplierForest_actual_115592
  · exact g32p_supplierForest_actual_115595
  · exact g32p_supplierForest_actual_115631
  · exact g32p_supplierForest_actual_115647
  · exact g32p_supplierForest_actual_115669
  · exact g32p_supplierForest_actual_115705
  · exact g32p_supplierForest_actual_115714
  · exact g32p_supplierForest_actual_115742
  · exact g32p_supplierForest_actual_115759
  · exact g32p_supplierForest_actual_115812
  · exact g32p_supplierForest_actual_115815
  · exact g32p_supplierForest_actual_115821
  · exact g32p_supplierForest_actual_115838
  · exact g32p_supplierForest_actual_115841
  · exact g32p_supplierForest_actual_115843
  · exact g32p_supplierForest_actual_115860
  · exact g32p_supplierForest_actual_115864
  · exact g32p_supplierForest_actual_115883
  · exact g32p_supplierForest_actual_115887
  · exact g32p_supplierForest_actual_115906
  · exact g32p_supplierForest_actual_115921
  · exact g32p_supplierForest_actual_115954
  · exact g32p_supplierForest_actual_115961
  · exact g32p_supplierForest_actual_115975
  · exact g32p_supplierForest_actual_115991
  · exact g32p_supplierForest_actual_115993
  · exact g32p_supplierForest_actual_115997
  · exact g32p_supplierForest_actual_116052
  · exact g32p_supplierForest_actual_116059
  · exact g32p_supplierForest_actual_116064
  · exact g32p_supplierForest_actual_116089
  · exact g32p_supplierForest_actual_116095
  · exact g32p_supplierForest_actual_116106
  · exact g32p_supplierForest_actual_116145
  · exact g32p_supplierForest_actual_116156
  · exact g32p_supplierForest_actual_116160
  · exact g32p_supplierForest_actual_116175
  · exact g32p_supplierForest_actual_116176
  · exact g32p_supplierForest_actual_116185
  · exact g32p_supplierForest_actual_116198
  · exact g32p_supplierForest_actual_116238
  · exact g32p_supplierForest_actual_116325
  · exact g32p_supplierForest_actual_116368
  · exact g32p_supplierForest_actual_116381
  · exact g32p_supplierForest_actual_116534
  · exact g32p_supplierForest_actual_116543
  · exact g32p_supplierForest_actual_116575
  · exact g32p_supplierForest_actual_116604
  · exact g32p_supplierForest_actual_116627
  · exact g32p_supplierForest_actual_116657
  · exact g32p_supplierForest_actual_116715
  · exact g32p_supplierForest_actual_116830
  · exact g32p_supplierForest_actual_116922
  · exact g32p_supplierForest_actual_116924
  · exact g32p_supplierForest_actual_116942
  · exact g32p_supplierForest_actual_116969
  · exact g32p_supplierForest_actual_116988
  · exact g32p_supplierForest_actual_116993
  · exact g32p_supplierForest_actual_116998
  · exact g32p_supplierForest_actual_117010
  · exact g32p_supplierForest_actual_117066
  · exact g32p_supplierForest_actual_117089
  · exact g32p_supplierForest_actual_117092
  · exact g32p_supplierForest_actual_117100
  · exact g32p_supplierForest_actual_117115
  · exact g32p_supplierForest_actual_117125
  · exact g32p_supplierForest_actual_117142
  · exact g32p_supplierForest_actual_117151
  · exact g32p_supplierForest_actual_117163
  · exact g32p_supplierForest_actual_117224
  · exact g32p_supplierForest_actual_117248
  · exact g32p_supplierForest_actual_117264
  · exact g32p_supplierForest_actual_117272
  · exact g32p_supplierForest_actual_117319
  · exact g32p_supplierForest_actual_117353
  · exact g32p_supplierForest_actual_117363
  · exact g32p_supplierForest_actual_117371
  · exact g32p_supplierForest_actual_117373
  · exact g32p_supplierForest_actual_117382
  · exact g32p_supplierForest_actual_117383
  · exact g32p_supplierForest_actual_117388
  · exact g32p_supplierForest_actual_117473
  · exact g32p_supplierForest_actual_117490
  · exact g32p_supplierForest_actual_117534
  · exact g32p_supplierForest_actual_117623
  · exact g32p_supplierForest_actual_117639
  · exact g32p_supplierForest_actual_117640
  · exact g32p_supplierForest_actual_117650
  · exact g32p_supplierForest_actual_117677
  · exact g32p_supplierForest_actual_117678
  · exact g32p_supplierForest_actual_117696
  · exact g32p_supplierForest_actual_117700
  · exact g32p_supplierForest_actual_117721
  · exact g32p_supplierForest_actual_117727
  · exact g32p_supplierForest_actual_117732
  · exact g32p_supplierForest_actual_117751
  · exact g32p_supplierForest_actual_117770
  · exact g32p_supplierForest_actual_117809
  · exact g32p_supplierForest_actual_117841
  · exact g32p_supplierForest_actual_117864
  · exact g32p_supplierForest_actual_117893
  · exact g32p_supplierForest_actual_117917
  · exact g32p_supplierForest_actual_117923
  · exact g32p_supplierForest_actual_118054
  · exact g32p_supplierForest_actual_118084
  · exact g32p_supplierForest_actual_118101
  · exact g32p_supplierForest_actual_118134
  · exact g32p_supplierForest_actual_118135
  · exact g32p_supplierForest_actual_118136
  · exact g32p_supplierForest_actual_118171
  · exact g32p_supplierForest_actual_118198
  · exact g32p_supplierForest_actual_118213
  · exact g32p_supplierForest_actual_118223
  · exact g32p_supplierForest_actual_118242
  · exact g32p_supplierForest_actual_118276
  · exact g32p_supplierForest_actual_118279
  · exact g32p_supplierForest_actual_118310
  · exact g32p_supplierForest_actual_118337
  · exact g32p_supplierForest_actual_118387
  · exact g32p_supplierForest_actual_118440
  · exact g32p_supplierForest_actual_118478
  · exact g32p_supplierForest_actual_118480
  · exact g32p_supplierForest_actual_118547
  · exact g32p_supplierForest_actual_118550
  · exact g32p_supplierForest_actual_118558
  · exact g32p_supplierForest_actual_118578
  · exact g32p_supplierForest_actual_118584
  · exact g32p_supplierForest_actual_118595
  · exact g32p_supplierForest_actual_118610
  · exact g32p_supplierForest_actual_118656
  · exact g32p_supplierForest_actual_118666
  · exact g32p_supplierForest_actual_118685
  · exact g32p_supplierForest_actual_118687
  · exact g32p_supplierForest_actual_118724
  · exact g32p_supplierForest_actual_118737

def g32p_supplierForest_nodes_079 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_118746 else g32p_supplierForest_node_118748) else (if i.val < 3 then g32p_supplierForest_node_118758 else g32p_supplierForest_node_118783)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_118784 else g32p_supplierForest_node_118811) else (if i.val < 7 then g32p_supplierForest_node_118837 else g32p_supplierForest_node_118855))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_118867 else g32p_supplierForest_node_118874) else (if i.val < 11 then g32p_supplierForest_node_118885 else g32p_supplierForest_node_118917)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_118940 else g32p_supplierForest_node_118953) else (if i.val < 15 then g32p_supplierForest_node_118955 else g32p_supplierForest_node_118957)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_118969 else g32p_supplierForest_node_118978) else (if i.val < 19 then g32p_supplierForest_node_119009 else g32p_supplierForest_node_119063)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_119078 else g32p_supplierForest_node_119083) else (if i.val < 23 then g32p_supplierForest_node_119145 else g32p_supplierForest_node_119151))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_119170 else g32p_supplierForest_node_119172) else (if i.val < 27 then g32p_supplierForest_node_119194 else g32p_supplierForest_node_119228)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_119230 else g32p_supplierForest_node_119241) else (if i.val < 31 then g32p_supplierForest_node_119244 else g32p_supplierForest_node_119287))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_119299 else g32p_supplierForest_node_119309) else (if i.val < 35 then g32p_supplierForest_node_119334 else g32p_supplierForest_node_119346)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_119348 else g32p_supplierForest_node_119378) else (if i.val < 39 then g32p_supplierForest_node_119410 else g32p_supplierForest_node_119412))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_119445 else g32p_supplierForest_node_119466) else (if i.val < 43 then g32p_supplierForest_node_119507 else g32p_supplierForest_node_119525)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_119585 else g32p_supplierForest_node_119587) else (if i.val < 47 then g32p_supplierForest_node_119590 else g32p_supplierForest_node_119604)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_119637 else g32p_supplierForest_node_119642) else (if i.val < 51 then g32p_supplierForest_node_119653 else g32p_supplierForest_node_119737)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_119752 else g32p_supplierForest_node_119796) else (if i.val < 55 then g32p_supplierForest_node_119833 else g32p_supplierForest_node_119902))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_119934 else g32p_supplierForest_node_119955) else (if i.val < 59 then g32p_supplierForest_node_119958 else g32p_supplierForest_node_119973)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_119993 else g32p_supplierForest_node_120066) else (if i.val < 63 then g32p_supplierForest_node_120086 else g32p_supplierForest_node_120095)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_120111 else g32p_supplierForest_node_120128) else (if i.val < 67 then g32p_supplierForest_node_120143 else g32p_supplierForest_node_120155)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_120168 else g32p_supplierForest_node_120186) else (if i.val < 71 then g32p_supplierForest_node_120202 else g32p_supplierForest_node_120218))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_120242 else g32p_supplierForest_node_120246) else (if i.val < 75 then g32p_supplierForest_node_120310 else g32p_supplierForest_node_120328)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_120341 else g32p_supplierForest_node_120409) else (if i.val < 79 then g32p_supplierForest_node_120418 else g32p_supplierForest_node_120530)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_120540 else g32p_supplierForest_node_120577) else (if i.val < 83 then g32p_supplierForest_node_120590 else g32p_supplierForest_node_120605)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_120692 else g32p_supplierForest_node_120707) else (if i.val < 87 then g32p_supplierForest_node_120714 else g32p_supplierForest_node_120733))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_120785 else g32p_supplierForest_node_120787) else (if i.val < 91 then g32p_supplierForest_node_120796 else g32p_supplierForest_node_120842)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_120853 else g32p_supplierForest_node_120927) else (if i.val < 95 then g32p_supplierForest_node_120960 else g32p_supplierForest_node_121071))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_121115 else g32p_supplierForest_node_121134) else (if i.val < 99 then g32p_supplierForest_node_121196 else g32p_supplierForest_node_121197)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_121236 else g32p_supplierForest_node_121244) else (if i.val < 103 then g32p_supplierForest_node_121253 else g32p_supplierForest_node_121285))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_121295 else g32p_supplierForest_node_121332) else (if i.val < 107 then g32p_supplierForest_node_121395 else g32p_supplierForest_node_121411)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_121462 else g32p_supplierForest_node_121468) else (if i.val < 111 then g32p_supplierForest_node_121470 else g32p_supplierForest_node_121525)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_121558 else g32p_supplierForest_node_121578) else (if i.val < 115 then g32p_supplierForest_node_121585 else g32p_supplierForest_node_121619)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_121631 else g32p_supplierForest_node_121634) else (if i.val < 119 then g32p_supplierForest_node_121674 else g32p_supplierForest_node_121689))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_121700 else g32p_supplierForest_node_121742) else (if i.val < 123 then g32p_supplierForest_node_121755 else g32p_supplierForest_node_121766)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_121774 else g32p_supplierForest_node_121792) else (if i.val < 127 then g32p_supplierForest_node_121841 else g32p_supplierForest_node_121870))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_121927 else g32p_supplierForest_node_121952) else (if i.val < 131 then g32p_supplierForest_node_121967 else g32p_supplierForest_node_121982)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_121987 else g32p_supplierForest_node_122048) else (if i.val < 135 then g32p_supplierForest_node_122056 else g32p_supplierForest_node_122079))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_122120 else g32p_supplierForest_node_122154) else (if i.val < 139 then g32p_supplierForest_node_122171 else g32p_supplierForest_node_122184)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_122195 else g32p_supplierForest_node_122216) else (if i.val < 143 then g32p_supplierForest_node_122218 else g32p_supplierForest_node_122222)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_122245 else g32p_supplierForest_node_122257) else (if i.val < 147 then g32p_supplierForest_node_122282 else g32p_supplierForest_node_122312)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_122315 else g32p_supplierForest_node_122320) else (if i.val < 151 then g32p_supplierForest_node_122329 else g32p_supplierForest_node_122338))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_122341 else g32p_supplierForest_node_122371) else (if i.val < 155 then g32p_supplierForest_node_122387 else g32p_supplierForest_node_122413)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_122450 else g32p_supplierForest_node_122458) else (if i.val < 159 then g32p_supplierForest_node_122471 else g32p_supplierForest_node_122478))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_122524 else g32p_supplierForest_node_122530) else (if i.val < 163 then g32p_supplierForest_node_122575 else g32p_supplierForest_node_122609)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_122627 else g32p_supplierForest_node_122667) else (if i.val < 167 then g32p_supplierForest_node_122698 else g32p_supplierForest_node_122714))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_122717 else g32p_supplierForest_node_122719) else (if i.val < 171 then g32p_supplierForest_node_122726 else g32p_supplierForest_node_122731)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_122738 else g32p_supplierForest_node_122769) else (if i.val < 175 then g32p_supplierForest_node_122771 else g32p_supplierForest_node_122796)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_122817 else g32p_supplierForest_node_122857) else (if i.val < 179 then g32p_supplierForest_node_122860 else g32p_supplierForest_node_122884)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_122895 else g32p_supplierForest_node_122936) else (if i.val < 183 then g32p_supplierForest_node_122937 else g32p_supplierForest_node_122953))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_122976 else g32p_supplierForest_node_122979) else (if i.val < 187 then g32p_supplierForest_node_123040 else g32p_supplierForest_node_123070)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_123104 else g32p_supplierForest_node_123107) else (if i.val < 191 then g32p_supplierForest_node_123150 else g32p_supplierForest_node_123170)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_123178 else g32p_supplierForest_node_123181) else (if i.val < 195 then g32p_supplierForest_node_123206 else g32p_supplierForest_node_123246)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_123247 else g32p_supplierForest_node_123259) else (if i.val < 199 then g32p_supplierForest_node_123283 else g32p_supplierForest_node_123287))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_123328 else g32p_supplierForest_node_123335) else (if i.val < 203 then g32p_supplierForest_node_123336 else g32p_supplierForest_node_123361)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_123368 else g32p_supplierForest_node_123371) else (if i.val < 207 then g32p_supplierForest_node_123373 else g32p_supplierForest_node_123402)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_123456 else g32p_supplierForest_node_123517) else (if i.val < 211 then g32p_supplierForest_node_123579 else g32p_supplierForest_node_123599)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_123605 else g32p_supplierForest_node_123615) else (if i.val < 215 then g32p_supplierForest_node_123618 else g32p_supplierForest_node_123656))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_123676 else g32p_supplierForest_node_123682) else (if i.val < 219 then g32p_supplierForest_node_123691 else g32p_supplierForest_node_123771)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_123804 else g32p_supplierForest_node_123811) else (if i.val < 223 then g32p_supplierForest_node_123833 else g32p_supplierForest_node_123868))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_123886 else g32p_supplierForest_node_123890) else (if i.val < 227 then g32p_supplierForest_node_123919 else g32p_supplierForest_node_123927)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_123966 else g32p_supplierForest_node_123993) else (if i.val < 231 then g32p_supplierForest_node_124006 else g32p_supplierForest_node_124009))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_124029 else g32p_supplierForest_node_124069) else (if i.val < 235 then g32p_supplierForest_node_124086 else g32p_supplierForest_node_124133)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_124149 else g32p_supplierForest_node_124151) else (if i.val < 239 then g32p_supplierForest_node_124168 else g32p_supplierForest_node_124173)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_124183 else g32p_supplierForest_node_124198) else (if i.val < 243 then g32p_supplierForest_node_124202 else g32p_supplierForest_node_124231)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_124285 else g32p_supplierForest_node_124290) else (if i.val < 247 then g32p_supplierForest_node_124306 else g32p_supplierForest_node_124353))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_124378 else g32p_supplierForest_node_124423) else (if i.val < 251 then g32p_supplierForest_node_124457 else g32p_supplierForest_node_124468)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_124475 else g32p_supplierForest_node_124476) else (if i.val < 255 then g32p_supplierForest_node_124480 else g32p_supplierForest_node_124485))))))))

def g32p_supplierForest_classes_079 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 34 else 30) else (if i.val < 3 then 57 else 62)) else (if i.val < 6 then (if i.val < 5 then 57 else 57) else (if i.val < 7 then 36 else 60))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 57 else 61) else (if i.val < 11 then 34 else 65)) else (if i.val < 14 then (if i.val < 13 then 30 else 62) else (if i.val < 15 then 62 else 59)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 60 else 29) else (if i.val < 19 then 57 else 62)) else (if i.val < 22 then (if i.val < 21 then 91 else 57) else (if i.val < 23 then 62 else 60))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 60 else 57) else (if i.val < 27 then 66 else 57)) else (if i.val < 30 then (if i.val < 29 then 60 else 89) else (if i.val < 31 then 35 else 89))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 34 else 59) else (if i.val < 35 then 29 else 62)) else (if i.val < 38 then (if i.val < 37 then 59 else 58) else (if i.val < 39 then 57 else 57))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 29 else 30) else (if i.val < 43 then 30 else 62)) else (if i.val < 46 then (if i.val < 45 then 33 else 60) else (if i.val < 47 then 57 else 57)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 17 else 66) else (if i.val < 51 then 57 else 90)) else (if i.val < 54 then (if i.val < 53 then 29 else 57) else (if i.val < 55 then 66 else 62))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 57 else 30) else (if i.val < 59 then 33 else 57)) else (if i.val < 62 then (if i.val < 61 then 66 else 62) else (if i.val < 63 then 92 else 66)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 62 else 57) else (if i.val < 67 then 30 else 30)) else (if i.val < 70 then (if i.val < 69 then 66 else 62) else (if i.val < 71 then 57 else 66))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 59 else 66) else (if i.val < 75 then 60 else 29)) else (if i.val < 78 then (if i.val < 77 then 34 else 29) else (if i.val < 79 then 36 else 29)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 61 else 59) else (if i.val < 83 then 61 else 58)) else (if i.val < 86 then (if i.val < 85 then 34 else 34) else (if i.val < 87 then 66 else 30))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 57 else 30) else (if i.val < 91 then 59 else 31)) else (if i.val < 94 then (if i.val < 93 then 59 else 34) else (if i.val < 95 then 60 else 61))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 60 else 61) else (if i.val < 99 then 58 else 58)) else (if i.val < 102 then (if i.val < 101 then 66 else 92) else (if i.val < 103 then 91 else 17))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 59 else 30) else (if i.val < 107 then 30 else 34)) else (if i.val < 110 then (if i.val < 109 then 34 else 60) else (if i.val < 111 then 15 else 34)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 60 else 32) else (if i.val < 115 then 30 else 57)) else (if i.val < 118 then (if i.val < 117 then 62 else 60) else (if i.val < 119 then 66 else 66))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 63 else 35) else (if i.val < 123 then 57 else 61)) else (if i.val < 126 then (if i.val < 125 then 61 else 29) else (if i.val < 127 then 30 else 60))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 15 else 15) else (if i.val < 131 then 30 else 66)) else (if i.val < 134 then (if i.val < 133 then 61 else 35) else (if i.val < 135 then 30 else 60))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 30 else 90) else (if i.val < 139 then 60 else 17)) else (if i.val < 142 then (if i.val < 141 then 33 else 60) else (if i.val < 143 then 90 else 90)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 89 else 35) else (if i.val < 147 then 92 else 61)) else (if i.val < 150 then (if i.val < 149 then 57 else 89) else (if i.val < 151 then 89 else 60))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 57 else 57) else (if i.val < 155 then 29 else 29)) else (if i.val < 158 then (if i.val < 157 then 15 else 57) else (if i.val < 159 then 35 else 61))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 58 else 30) else (if i.val < 163 then 60 else 66)) else (if i.val < 166 then (if i.val < 165 then 61 else 66) else (if i.val < 167 then 59 else 60))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 34 else 60) else (if i.val < 171 then 34 else 35)) else (if i.val < 174 then (if i.val < 173 then 16 else 29) else (if i.val < 175 then 30 else 16)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 60 else 57) else (if i.val < 179 then 60 else 60)) else (if i.val < 182 then (if i.val < 181 then 57 else 34) else (if i.val < 183 then 29 else 35))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 35 else 60) else (if i.val < 187 then 63 else 63)) else (if i.val < 190 then (if i.val < 189 then 34 else 33) else (if i.val < 191 then 63 else 30)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 57 else 29) else (if i.val < 195 then 35 else 66)) else (if i.val < 198 then (if i.val < 197 then 62 else 16) else (if i.val < 199 then 60 else 57))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 61 else 57) else (if i.val < 203 then 65 else 29)) else (if i.val < 206 then (if i.val < 205 then 57 else 35) else (if i.val < 207 then 57 else 66)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 34 else 66) else (if i.val < 211 then 60 else 58)) else (if i.val < 214 then (if i.val < 213 then 91 else 92) else (if i.val < 215 then 57 else 57))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 34 else 66) else (if i.val < 219 then 33 else 62)) else (if i.val < 222 then (if i.val < 221 then 59 else 62) else (if i.val < 223 then 58 else 66))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 57 else 35) else (if i.val < 227 then 89 else 57)) else (if i.val < 230 then (if i.val < 229 then 33 else 60) else (if i.val < 231 then 90 else 66))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 57 else 34) else (if i.val < 235 then 60 else 30)) else (if i.val < 238 then (if i.val < 237 then 57 else 34) else (if i.val < 239 then 29 else 62)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 57 else 59) else (if i.val < 243 then 66 else 58)) else (if i.val < 246 then (if i.val < 245 then 30 else 15) else (if i.val < 247 then 91 else 58))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 30 else 60) else (if i.val < 251 then 30 else 34)) else (if i.val < 254 then (if i.val < 253 then 57 else 57) else (if i.val < 255 then 63 else 34))))))))

theorem g32p_supplierForest_actual_079 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_079 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_079 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_118746
  · exact g32p_supplierForest_actual_118748
  · exact g32p_supplierForest_actual_118758
  · exact g32p_supplierForest_actual_118783
  · exact g32p_supplierForest_actual_118784
  · exact g32p_supplierForest_actual_118811
  · exact g32p_supplierForest_actual_118837
  · exact g32p_supplierForest_actual_118855
  · exact g32p_supplierForest_actual_118867
  · exact g32p_supplierForest_actual_118874
  · exact g32p_supplierForest_actual_118885
  · exact g32p_supplierForest_actual_118917
  · exact g32p_supplierForest_actual_118940
  · exact g32p_supplierForest_actual_118953
  · exact g32p_supplierForest_actual_118955
  · exact g32p_supplierForest_actual_118957
  · exact g32p_supplierForest_actual_118969
  · exact g32p_supplierForest_actual_118978
  · exact g32p_supplierForest_actual_119009
  · exact g32p_supplierForest_actual_119063
  · exact g32p_supplierForest_actual_119078
  · exact g32p_supplierForest_actual_119083
  · exact g32p_supplierForest_actual_119145
  · exact g32p_supplierForest_actual_119151
  · exact g32p_supplierForest_actual_119170
  · exact g32p_supplierForest_actual_119172
  · exact g32p_supplierForest_actual_119194
  · exact g32p_supplierForest_actual_119228
  · exact g32p_supplierForest_actual_119230
  · exact g32p_supplierForest_actual_119241
  · exact g32p_supplierForest_actual_119244
  · exact g32p_supplierForest_actual_119287
  · exact g32p_supplierForest_actual_119299
  · exact g32p_supplierForest_actual_119309
  · exact g32p_supplierForest_actual_119334
  · exact g32p_supplierForest_actual_119346
  · exact g32p_supplierForest_actual_119348
  · exact g32p_supplierForest_actual_119378
  · exact g32p_supplierForest_actual_119410
  · exact g32p_supplierForest_actual_119412
  · exact g32p_supplierForest_actual_119445
  · exact g32p_supplierForest_actual_119466
  · exact g32p_supplierForest_actual_119507
  · exact g32p_supplierForest_actual_119525
  · exact g32p_supplierForest_actual_119585
  · exact g32p_supplierForest_actual_119587
  · exact g32p_supplierForest_actual_119590
  · exact g32p_supplierForest_actual_119604
  · exact g32p_supplierForest_actual_119637
  · exact g32p_supplierForest_actual_119642
  · exact g32p_supplierForest_actual_119653
  · exact g32p_supplierForest_actual_119737
  · exact g32p_supplierForest_actual_119752
  · exact g32p_supplierForest_actual_119796
  · exact g32p_supplierForest_actual_119833
  · exact g32p_supplierForest_actual_119902
  · exact g32p_supplierForest_actual_119934
  · exact g32p_supplierForest_actual_119955
  · exact g32p_supplierForest_actual_119958
  · exact g32p_supplierForest_actual_119973
  · exact g32p_supplierForest_actual_119993
  · exact g32p_supplierForest_actual_120066
  · exact g32p_supplierForest_actual_120086
  · exact g32p_supplierForest_actual_120095
  · exact g32p_supplierForest_actual_120111
  · exact g32p_supplierForest_actual_120128
  · exact g32p_supplierForest_actual_120143
  · exact g32p_supplierForest_actual_120155
  · exact g32p_supplierForest_actual_120168
  · exact g32p_supplierForest_actual_120186
  · exact g32p_supplierForest_actual_120202
  · exact g32p_supplierForest_actual_120218
  · exact g32p_supplierForest_actual_120242
  · exact g32p_supplierForest_actual_120246
  · exact g32p_supplierForest_actual_120310
  · exact g32p_supplierForest_actual_120328
  · exact g32p_supplierForest_actual_120341
  · exact g32p_supplierForest_actual_120409
  · exact g32p_supplierForest_actual_120418
  · exact g32p_supplierForest_actual_120530
  · exact g32p_supplierForest_actual_120540
  · exact g32p_supplierForest_actual_120577
  · exact g32p_supplierForest_actual_120590
  · exact g32p_supplierForest_actual_120605
  · exact g32p_supplierForest_actual_120692
  · exact g32p_supplierForest_actual_120707
  · exact g32p_supplierForest_actual_120714
  · exact g32p_supplierForest_actual_120733
  · exact g32p_supplierForest_actual_120785
  · exact g32p_supplierForest_actual_120787
  · exact g32p_supplierForest_actual_120796
  · exact g32p_supplierForest_actual_120842
  · exact g32p_supplierForest_actual_120853
  · exact g32p_supplierForest_actual_120927
  · exact g32p_supplierForest_actual_120960
  · exact g32p_supplierForest_actual_121071
  · exact g32p_supplierForest_actual_121115
  · exact g32p_supplierForest_actual_121134
  · exact g32p_supplierForest_actual_121196
  · exact g32p_supplierForest_actual_121197
  · exact g32p_supplierForest_actual_121236
  · exact g32p_supplierForest_actual_121244
  · exact g32p_supplierForest_actual_121253
  · exact g32p_supplierForest_actual_121285
  · exact g32p_supplierForest_actual_121295
  · exact g32p_supplierForest_actual_121332
  · exact g32p_supplierForest_actual_121395
  · exact g32p_supplierForest_actual_121411
  · exact g32p_supplierForest_actual_121462
  · exact g32p_supplierForest_actual_121468
  · exact g32p_supplierForest_actual_121470
  · exact g32p_supplierForest_actual_121525
  · exact g32p_supplierForest_actual_121558
  · exact g32p_supplierForest_actual_121578
  · exact g32p_supplierForest_actual_121585
  · exact g32p_supplierForest_actual_121619
  · exact g32p_supplierForest_actual_121631
  · exact g32p_supplierForest_actual_121634
  · exact g32p_supplierForest_actual_121674
  · exact g32p_supplierForest_actual_121689
  · exact g32p_supplierForest_actual_121700
  · exact g32p_supplierForest_actual_121742
  · exact g32p_supplierForest_actual_121755
  · exact g32p_supplierForest_actual_121766
  · exact g32p_supplierForest_actual_121774
  · exact g32p_supplierForest_actual_121792
  · exact g32p_supplierForest_actual_121841
  · exact g32p_supplierForest_actual_121870
  · exact g32p_supplierForest_actual_121927
  · exact g32p_supplierForest_actual_121952
  · exact g32p_supplierForest_actual_121967
  · exact g32p_supplierForest_actual_121982
  · exact g32p_supplierForest_actual_121987
  · exact g32p_supplierForest_actual_122048
  · exact g32p_supplierForest_actual_122056
  · exact g32p_supplierForest_actual_122079
  · exact g32p_supplierForest_actual_122120
  · exact g32p_supplierForest_actual_122154
  · exact g32p_supplierForest_actual_122171
  · exact g32p_supplierForest_actual_122184
  · exact g32p_supplierForest_actual_122195
  · exact g32p_supplierForest_actual_122216
  · exact g32p_supplierForest_actual_122218
  · exact g32p_supplierForest_actual_122222
  · exact g32p_supplierForest_actual_122245
  · exact g32p_supplierForest_actual_122257
  · exact g32p_supplierForest_actual_122282
  · exact g32p_supplierForest_actual_122312
  · exact g32p_supplierForest_actual_122315
  · exact g32p_supplierForest_actual_122320
  · exact g32p_supplierForest_actual_122329
  · exact g32p_supplierForest_actual_122338
  · exact g32p_supplierForest_actual_122341
  · exact g32p_supplierForest_actual_122371
  · exact g32p_supplierForest_actual_122387
  · exact g32p_supplierForest_actual_122413
  · exact g32p_supplierForest_actual_122450
  · exact g32p_supplierForest_actual_122458
  · exact g32p_supplierForest_actual_122471
  · exact g32p_supplierForest_actual_122478
  · exact g32p_supplierForest_actual_122524
  · exact g32p_supplierForest_actual_122530
  · exact g32p_supplierForest_actual_122575
  · exact g32p_supplierForest_actual_122609
  · exact g32p_supplierForest_actual_122627
  · exact g32p_supplierForest_actual_122667
  · exact g32p_supplierForest_actual_122698
  · exact g32p_supplierForest_actual_122714
  · exact g32p_supplierForest_actual_122717
  · exact g32p_supplierForest_actual_122719
  · exact g32p_supplierForest_actual_122726
  · exact g32p_supplierForest_actual_122731
  · exact g32p_supplierForest_actual_122738
  · exact g32p_supplierForest_actual_122769
  · exact g32p_supplierForest_actual_122771
  · exact g32p_supplierForest_actual_122796
  · exact g32p_supplierForest_actual_122817
  · exact g32p_supplierForest_actual_122857
  · exact g32p_supplierForest_actual_122860
  · exact g32p_supplierForest_actual_122884
  · exact g32p_supplierForest_actual_122895
  · exact g32p_supplierForest_actual_122936
  · exact g32p_supplierForest_actual_122937
  · exact g32p_supplierForest_actual_122953
  · exact g32p_supplierForest_actual_122976
  · exact g32p_supplierForest_actual_122979
  · exact g32p_supplierForest_actual_123040
  · exact g32p_supplierForest_actual_123070
  · exact g32p_supplierForest_actual_123104
  · exact g32p_supplierForest_actual_123107
  · exact g32p_supplierForest_actual_123150
  · exact g32p_supplierForest_actual_123170
  · exact g32p_supplierForest_actual_123178
  · exact g32p_supplierForest_actual_123181
  · exact g32p_supplierForest_actual_123206
  · exact g32p_supplierForest_actual_123246
  · exact g32p_supplierForest_actual_123247
  · exact g32p_supplierForest_actual_123259
  · exact g32p_supplierForest_actual_123283
  · exact g32p_supplierForest_actual_123287
  · exact g32p_supplierForest_actual_123328
  · exact g32p_supplierForest_actual_123335
  · exact g32p_supplierForest_actual_123336
  · exact g32p_supplierForest_actual_123361
  · exact g32p_supplierForest_actual_123368
  · exact g32p_supplierForest_actual_123371
  · exact g32p_supplierForest_actual_123373
  · exact g32p_supplierForest_actual_123402
  · exact g32p_supplierForest_actual_123456
  · exact g32p_supplierForest_actual_123517
  · exact g32p_supplierForest_actual_123579
  · exact g32p_supplierForest_actual_123599
  · exact g32p_supplierForest_actual_123605
  · exact g32p_supplierForest_actual_123615
  · exact g32p_supplierForest_actual_123618
  · exact g32p_supplierForest_actual_123656
  · exact g32p_supplierForest_actual_123676
  · exact g32p_supplierForest_actual_123682
  · exact g32p_supplierForest_actual_123691
  · exact g32p_supplierForest_actual_123771
  · exact g32p_supplierForest_actual_123804
  · exact g32p_supplierForest_actual_123811
  · exact g32p_supplierForest_actual_123833
  · exact g32p_supplierForest_actual_123868
  · exact g32p_supplierForest_actual_123886
  · exact g32p_supplierForest_actual_123890
  · exact g32p_supplierForest_actual_123919
  · exact g32p_supplierForest_actual_123927
  · exact g32p_supplierForest_actual_123966
  · exact g32p_supplierForest_actual_123993
  · exact g32p_supplierForest_actual_124006
  · exact g32p_supplierForest_actual_124009
  · exact g32p_supplierForest_actual_124029
  · exact g32p_supplierForest_actual_124069
  · exact g32p_supplierForest_actual_124086
  · exact g32p_supplierForest_actual_124133
  · exact g32p_supplierForest_actual_124149
  · exact g32p_supplierForest_actual_124151
  · exact g32p_supplierForest_actual_124168
  · exact g32p_supplierForest_actual_124173
  · exact g32p_supplierForest_actual_124183
  · exact g32p_supplierForest_actual_124198
  · exact g32p_supplierForest_actual_124202
  · exact g32p_supplierForest_actual_124231
  · exact g32p_supplierForest_actual_124285
  · exact g32p_supplierForest_actual_124290
  · exact g32p_supplierForest_actual_124306
  · exact g32p_supplierForest_actual_124353
  · exact g32p_supplierForest_actual_124378
  · exact g32p_supplierForest_actual_124423
  · exact g32p_supplierForest_actual_124457
  · exact g32p_supplierForest_actual_124468
  · exact g32p_supplierForest_actual_124475
  · exact g32p_supplierForest_actual_124476
  · exact g32p_supplierForest_actual_124480
  · exact g32p_supplierForest_actual_124485

end HodgeLean.Foundations.Program

end
end
