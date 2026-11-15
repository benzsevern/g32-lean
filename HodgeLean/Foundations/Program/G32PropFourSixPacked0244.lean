import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0227
import HodgeLean.Foundations.Program.G32PropFourSixPacked0228
import HodgeLean.Foundations.Program.G32PropFourSixPacked0229
import HodgeLean.Foundations.Program.G32PropFourSixPacked0230
import HodgeLean.Foundations.Program.G32PropFourSixPacked0236
import HodgeLean.Foundations.Program.G32PropFourSixPacked0237
import HodgeLean.Foundations.Program.G32PropFourSixPacked0240
import HodgeLean.Foundations.Program.G32PropFourSixPacked0241
import HodgeLean.Foundations.Program.G32PropFourSixPacked0242
import HodgeLean.Foundations.Program.G32PropFourSixPacked0243

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_038795 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_038795 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_038795 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_106901 := by
  decide +kernel

theorem g32p_supplierForest_actual_038795 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_038795) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 0 g32p_supplierForest_edge_038795
    g32p_supplierForest_actual_106901

def g32p_supplierForest_node_038833 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_038833 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_038833 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_035005 := by
  decide +kernel

theorem g32p_supplierForest_actual_038833 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_038833) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_038833
    g32p_supplierForest_actual_035005

def g32p_supplierForest_node_038837 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_038837 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_038837 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_041576 := by
  decide +kernel

theorem g32p_supplierForest_actual_038837 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_038837) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_038837
    g32p_supplierForest_actual_041576

def g32p_supplierForest_node_038967 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_038967 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_038967 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_109376 := by
  decide +kernel

theorem g32p_supplierForest_actual_038967 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_038967) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_038967
    g32p_supplierForest_actual_109376

def g32p_supplierForest_node_038976 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_038976 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_038976 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_103313 := by
  decide +kernel

theorem g32p_supplierForest_actual_038976 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_038976) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 0 g32p_supplierForest_edge_038976
    g32p_supplierForest_actual_103313

def g32p_supplierForest_node_039007 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_039007 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039007 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_032582 := by
  decide +kernel

theorem g32p_supplierForest_actual_039007 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039007) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 3 g32p_supplierForest_edge_039007
    g32p_supplierForest_actual_032582

def g32p_supplierForest_node_039056 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_039056 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039056 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_042005 := by
  decide +kernel

theorem g32p_supplierForest_actual_039056 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039056) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_039056
    g32p_supplierForest_actual_042005

def g32p_supplierForest_node_039076 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_039076 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039076 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_003851 := by
  decide +kernel

theorem g32p_supplierForest_actual_039076 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039076) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 3 g32p_supplierForest_edge_039076
    g32p_supplierForest_actual_003851

def g32p_supplierForest_node_039080 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_039080 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039080 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004614 := by
  decide +kernel

theorem g32p_supplierForest_actual_039080 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039080) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_039080
    g32p_supplierForest_actual_004614

def g32p_supplierForest_node_039119 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_039119 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039119 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123066 := by
  decide +kernel

theorem g32p_supplierForest_actual_039119 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039119) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_039119
    g32p_supplierForest_actual_123066

def g32p_supplierForest_node_039125 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_039125 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039125 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_111577 := by
  decide +kernel

theorem g32p_supplierForest_actual_039125 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039125) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_039125
    g32p_supplierForest_actual_111577

def g32p_supplierForest_node_039143 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_039143 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039143 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_035093 := by
  decide +kernel

theorem g32p_supplierForest_actual_039143 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039143) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_039143
    g32p_supplierForest_actual_035093

def g32p_supplierForest_node_039205 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_039205 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039205 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_032988 := by
  decide +kernel

theorem g32p_supplierForest_actual_039205 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039205) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 0 g32p_supplierForest_edge_039205
    g32p_supplierForest_actual_032988

def g32p_supplierForest_node_039232 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_039232 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039232 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_028737 := by
  decide +kernel

theorem g32p_supplierForest_actual_039232 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039232) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_039232
    g32p_supplierForest_actual_028737

def g32p_supplierForest_node_039236 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_039236 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039236 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_039243 := by
  decide +kernel

theorem g32p_supplierForest_actual_039236 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039236) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 3 g32p_supplierForest_edge_039236
    g32p_supplierForest_actual_039243

def g32p_supplierForest_node_039248 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_039248 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039248 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_035309 := by
  decide +kernel

theorem g32p_supplierForest_actual_039248 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039248) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_039248
    g32p_supplierForest_actual_035309

def g32p_supplierForest_node_039305 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_039305 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039305 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_037689 := by
  decide +kernel

theorem g32p_supplierForest_actual_039305 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039305) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_039305
    g32p_supplierForest_actual_037689

def g32p_supplierForest_node_039323 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_039323 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039323 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_043235 := by
  decide +kernel

theorem g32p_supplierForest_actual_039323 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039323) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_039323
    g32p_supplierForest_actual_043235

def g32p_supplierForest_node_039347 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_039347 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039347 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_107552 := by
  decide +kernel

theorem g32p_supplierForest_actual_039347 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039347) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_039347
    g32p_supplierForest_actual_107552

def g32p_supplierForest_node_039349 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-2, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_039349 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039349 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004508 := by
  decide +kernel

theorem g32p_supplierForest_actual_039349 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039349) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_039349
    g32p_supplierForest_actual_004508

def g32p_supplierForest_node_039354 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_039354 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039354 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_037669 := by
  decide +kernel

theorem g32p_supplierForest_actual_039354 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039354) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_039354
    g32p_supplierForest_actual_037669

def g32p_supplierForest_node_039362 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_039362 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039362 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_042661 := by
  decide +kernel

theorem g32p_supplierForest_actual_039362 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039362) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_039362
    g32p_supplierForest_actual_042661

def g32p_supplierForest_node_039388 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_039388 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039388 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_024926 := by
  decide +kernel

theorem g32p_supplierForest_actual_039388 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039388) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_039388
    g32p_supplierForest_actual_024926

def g32p_supplierForest_node_039410 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_039410 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039410 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_034806 := by
  decide +kernel

theorem g32p_supplierForest_actual_039410 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039410) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_039410
    g32p_supplierForest_actual_034806

def g32p_supplierForest_node_039413 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_039413 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039413 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_035309 := by
  decide +kernel

theorem g32p_supplierForest_actual_039413 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039413) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_039413
    g32p_supplierForest_actual_035309

def g32p_supplierForest_node_039439 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_039439 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039439 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_110393 := by
  decide +kernel

theorem g32p_supplierForest_actual_039439 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039439) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_039439
    g32p_supplierForest_actual_110393

def g32p_supplierForest_node_039459 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_039459 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039459 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_042849 := by
  decide +kernel

theorem g32p_supplierForest_actual_039459 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039459) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_039459
    g32p_supplierForest_actual_042849

def g32p_supplierForest_node_039482 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_039482 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039482 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_037981 := by
  decide +kernel

theorem g32p_supplierForest_actual_039482 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039482) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_039482
    g32p_supplierForest_actual_037981

def g32p_supplierForest_node_039490 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_039490 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039490 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_033665 := by
  decide +kernel

theorem g32p_supplierForest_actual_039490 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039490) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_039490
    g32p_supplierForest_actual_033665

def g32p_supplierForest_node_039522 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_039522 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039522 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_003854 := by
  decide +kernel

theorem g32p_supplierForest_actual_039522 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039522) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_039522
    g32p_supplierForest_actual_003854

def g32p_supplierForest_node_039573 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_039573 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039573 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_034925 := by
  decide +kernel

theorem g32p_supplierForest_actual_039573 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039573) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_039573
    g32p_supplierForest_actual_034925

def g32p_supplierForest_node_039575 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_039575 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039575 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_034930 := by
  decide +kernel

theorem g32p_supplierForest_actual_039575 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039575) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_039575
    g32p_supplierForest_actual_034930

def g32p_supplierForest_node_039584 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_039584 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039584 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_034928 := by
  decide +kernel

theorem g32p_supplierForest_actual_039584 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039584) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_039584
    g32p_supplierForest_actual_034928

def g32p_supplierForest_node_039621 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_039621 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039621 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_042593 := by
  decide +kernel

theorem g32p_supplierForest_actual_039621 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039621) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_039621
    g32p_supplierForest_actual_042593

def g32p_supplierForest_node_039636 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_039636 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039636 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_107873 := by
  decide +kernel

theorem g32p_supplierForest_actual_039636 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039636) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_039636
    g32p_supplierForest_actual_107873

def g32p_supplierForest_node_039653 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_039653 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039653 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_034806 := by
  decide +kernel

theorem g32p_supplierForest_actual_039653 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039653) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_039653
    g32p_supplierForest_actual_034806

def g32p_supplierForest_node_039660 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_039660 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039660 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_043166 := by
  decide +kernel

theorem g32p_supplierForest_actual_039660 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039660) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_039660
    g32p_supplierForest_actual_043166

def g32p_supplierForest_node_039704 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_039704 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039704 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_035330 := by
  decide +kernel

theorem g32p_supplierForest_actual_039704 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039704) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_039704
    g32p_supplierForest_actual_035330

def g32p_supplierForest_node_039754 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_039754 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039754 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_024661 := by
  decide +kernel

theorem g32p_supplierForest_actual_039754 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039754) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 3 g32p_supplierForest_edge_039754
    g32p_supplierForest_actual_024661

def g32p_supplierForest_node_039786 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_039786 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039786 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_028728 := by
  decide +kernel

theorem g32p_supplierForest_actual_039786 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039786) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_039786
    g32p_supplierForest_actual_028728

def g32p_supplierForest_node_039792 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_039792 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039792 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_108051 := by
  decide +kernel

theorem g32p_supplierForest_actual_039792 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039792) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_039792
    g32p_supplierForest_actual_108051

def g32p_supplierForest_node_039796 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_039796 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039796 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108121 := by
  decide +kernel

theorem g32p_supplierForest_actual_039796 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039796) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_039796
    g32p_supplierForest_actual_108121

def g32p_supplierForest_node_039853 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_039853 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039853 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_028971 := by
  decide +kernel

theorem g32p_supplierForest_actual_039853 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039853) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_039853
    g32p_supplierForest_actual_028971

def g32p_supplierForest_node_039862 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_039862 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039862 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029058 := by
  decide +kernel

theorem g32p_supplierForest_actual_039862 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039862) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 3 g32p_supplierForest_edge_039862
    g32p_supplierForest_actual_029058

def g32p_supplierForest_node_039883 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_039883 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039883 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_026084 := by
  decide +kernel

theorem g32p_supplierForest_actual_039883 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039883) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_039883
    g32p_supplierForest_actual_026084

def g32p_supplierForest_node_039889 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_039889 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039889 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_024823 := by
  decide +kernel

theorem g32p_supplierForest_actual_039889 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039889) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_039889
    g32p_supplierForest_actual_024823

def g32p_supplierForest_node_039897 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_039897 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039897 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_043618 := by
  decide +kernel

theorem g32p_supplierForest_actual_039897 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039897) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 1 g32p_supplierForest_edge_039897
    g32p_supplierForest_actual_043618

def g32p_supplierForest_node_039900 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_039900 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039900 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_031266 := by
  decide +kernel

theorem g32p_supplierForest_actual_039900 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039900) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 0 g32p_supplierForest_edge_039900
    g32p_supplierForest_actual_031266

def g32p_supplierForest_node_039952 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_039952 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039952 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108166 := by
  decide +kernel

theorem g32p_supplierForest_actual_039952 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039952) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_039952
    g32p_supplierForest_actual_108166

def g32p_supplierForest_node_039965 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_039965 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039965 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_108295 := by
  decide +kernel

theorem g32p_supplierForest_actual_039965 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039965) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_039965
    g32p_supplierForest_actual_108295

def g32p_supplierForest_node_039999 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_039999 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_039999 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_107540 := by
  decide +kernel

theorem g32p_supplierForest_actual_039999 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_039999) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_039999
    g32p_supplierForest_actual_107540

def g32p_supplierForest_node_040008 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_040008 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040008 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_114352 := by
  decide +kernel

theorem g32p_supplierForest_actual_040008 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040008) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_040008
    g32p_supplierForest_actual_114352

def g32p_supplierForest_node_040036 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_040036 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040036 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_106654 := by
  decide +kernel

theorem g32p_supplierForest_actual_040036 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040036) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_040036
    g32p_supplierForest_actual_106654

def g32p_supplierForest_node_040052 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_040052 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040052 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_043241 := by
  decide +kernel

theorem g32p_supplierForest_actual_040052 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040052) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_040052
    g32p_supplierForest_actual_043241

def g32p_supplierForest_node_040058 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_040058 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040058 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_025036 := by
  decide +kernel

theorem g32p_supplierForest_actual_040058 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040058) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_040058
    g32p_supplierForest_actual_025036

def g32p_supplierForest_node_040091 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_040091 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040091 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_105615 := by
  decide +kernel

theorem g32p_supplierForest_actual_040091 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040091) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_040091
    g32p_supplierForest_actual_105615

def g32p_supplierForest_node_040113 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_040113 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040113 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_042801 := by
  decide +kernel

theorem g32p_supplierForest_actual_040113 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040113) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 1 g32p_supplierForest_edge_040113
    g32p_supplierForest_actual_042801

def g32p_supplierForest_node_040142 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_040142 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040142 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043104 := by
  decide +kernel

theorem g32p_supplierForest_actual_040142 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040142) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_040142
    g32p_supplierForest_actual_043104

def g32p_supplierForest_node_040155 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_040155 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040155 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113518 := by
  decide +kernel

theorem g32p_supplierForest_actual_040155 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040155) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_040155
    g32p_supplierForest_actual_113518

def g32p_supplierForest_node_040164 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_040164 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040164 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_103181 := by
  decide +kernel

theorem g32p_supplierForest_actual_040164 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040164) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_040164
    g32p_supplierForest_actual_103181

def g32p_supplierForest_node_040170 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_040170 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040170 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_039994 := by
  decide +kernel

theorem g32p_supplierForest_actual_040170 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040170) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_040170
    g32p_supplierForest_actual_039994

def g32p_supplierForest_node_040208 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_040208 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040208 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_108587 := by
  decide +kernel

theorem g32p_supplierForest_actual_040208 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040208) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_040208
    g32p_supplierForest_actual_108587

def g32p_supplierForest_node_040240 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_040240 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040240 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_104225 := by
  decide +kernel

theorem g32p_supplierForest_actual_040240 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040240) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_040240
    g32p_supplierForest_actual_104225

def g32p_supplierForest_node_040249 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_040249 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040249 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_106306 := by
  decide +kernel

theorem g32p_supplierForest_actual_040249 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040249) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_040249
    g32p_supplierForest_actual_106306

def g32p_supplierForest_node_040251 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_040251 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040251 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_039467 := by
  decide +kernel

theorem g32p_supplierForest_actual_040251 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040251) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_040251
    g32p_supplierForest_actual_039467

def g32p_supplierForest_node_040253 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_040253 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040253 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118682 := by
  decide +kernel

theorem g32p_supplierForest_actual_040253 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040253) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_040253
    g32p_supplierForest_actual_118682

def g32p_supplierForest_node_040263 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_040263 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040263 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_026489 := by
  decide +kernel

theorem g32p_supplierForest_actual_040263 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040263) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_040263
    g32p_supplierForest_actual_026489

def g32p_supplierForest_node_040283 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_040283 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040283 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118644 := by
  decide +kernel

theorem g32p_supplierForest_actual_040283 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040283) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_040283
    g32p_supplierForest_actual_118644

def g32p_supplierForest_node_040326 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_040326 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040326 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_108721 := by
  decide +kernel

theorem g32p_supplierForest_actual_040326 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040326) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_040326
    g32p_supplierForest_actual_108721

def g32p_supplierForest_node_040348 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_040348 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040348 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_043480 := by
  decide +kernel

theorem g32p_supplierForest_actual_040348 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040348) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_040348
    g32p_supplierForest_actual_043480

def g32p_supplierForest_node_040351 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_040351 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040351 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_104576 := by
  decide +kernel

theorem g32p_supplierForest_actual_040351 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040351) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_040351
    g32p_supplierForest_actual_104576

def g32p_supplierForest_node_040357 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_040357 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040357 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_003861 := by
  decide +kernel

theorem g32p_supplierForest_actual_040357 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040357) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 2 g32p_supplierForest_edge_040357
    g32p_supplierForest_actual_003861

def g32p_supplierForest_node_040364 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_040364 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040364 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122718 := by
  decide +kernel

theorem g32p_supplierForest_actual_040364 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040364) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_040364
    g32p_supplierForest_actual_122718

def g32p_supplierForest_node_040394 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_040394 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040394 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_026210 := by
  decide +kernel

theorem g32p_supplierForest_actual_040394 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040394) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 1 g32p_supplierForest_edge_040394
    g32p_supplierForest_actual_026210

def g32p_supplierForest_node_040428 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_040428 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040428 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_037269 := by
  decide +kernel

theorem g32p_supplierForest_actual_040428 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040428) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_040428
    g32p_supplierForest_actual_037269

def g32p_supplierForest_node_040432 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_040432 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040432 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_109912 := by
  decide +kernel

theorem g32p_supplierForest_actual_040432 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040432) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_040432
    g32p_supplierForest_actual_109912

def g32p_supplierForest_node_040446 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_040446 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040446 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_027569 := by
  decide +kernel

theorem g32p_supplierForest_actual_040446 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040446) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 1 g32p_supplierForest_edge_040446
    g32p_supplierForest_actual_027569

def g32p_supplierForest_node_040458 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_040458 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040458 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_035405 := by
  decide +kernel

theorem g32p_supplierForest_actual_040458 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040458) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_040458
    g32p_supplierForest_actual_035405

def g32p_supplierForest_node_040487 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_040487 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040487 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_035401 := by
  decide +kernel

theorem g32p_supplierForest_actual_040487 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040487) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_040487
    g32p_supplierForest_actual_035401

def g32p_supplierForest_node_040530 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_040530 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040530 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_036248 := by
  decide +kernel

theorem g32p_supplierForest_actual_040530 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040530) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_040530
    g32p_supplierForest_actual_036248

def g32p_supplierForest_node_040542 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_040542 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040542 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_110725 := by
  decide +kernel

theorem g32p_supplierForest_actual_040542 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040542) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 3 g32p_supplierForest_edge_040542
    g32p_supplierForest_actual_110725

def g32p_supplierForest_node_040554 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_040554 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040554 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_036121 := by
  decide +kernel

theorem g32p_supplierForest_actual_040554 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040554) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_040554
    g32p_supplierForest_actual_036121

def g32p_supplierForest_node_040579 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_040579 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040579 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_036371 := by
  decide +kernel

theorem g32p_supplierForest_actual_040579 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040579) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_040579
    g32p_supplierForest_actual_036371

def g32p_supplierForest_node_040631 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_040631 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040631 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_036500 := by
  decide +kernel

theorem g32p_supplierForest_actual_040631 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040631) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_040631
    g32p_supplierForest_actual_036500

def g32p_supplierForest_node_040715 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_040715 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040715 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_036781 := by
  decide +kernel

theorem g32p_supplierForest_actual_040715 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040715) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_040715
    g32p_supplierForest_actual_036781

def g32p_supplierForest_node_040795 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_040795 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040795 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_026986 := by
  decide +kernel

theorem g32p_supplierForest_actual_040795 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040795) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 0 g32p_supplierForest_edge_040795
    g32p_supplierForest_actual_026986

def g32p_supplierForest_node_040810 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_040810 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040810 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_025104 := by
  decide +kernel

theorem g32p_supplierForest_actual_040810 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040810) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_040810
    g32p_supplierForest_actual_025104

def g32p_supplierForest_node_040849 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_040849 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040849 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_040429 := by
  decide +kernel

theorem g32p_supplierForest_actual_040849 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040849) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_040849
    g32p_supplierForest_actual_040429

def g32p_supplierForest_node_040856 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_040856 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040856 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037211 := by
  decide +kernel

theorem g32p_supplierForest_actual_040856 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040856) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 2 g32p_supplierForest_edge_040856
    g32p_supplierForest_actual_037211

def g32p_supplierForest_node_040857 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_040857 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040857 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109306 := by
  decide +kernel

theorem g32p_supplierForest_actual_040857 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040857) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 1 g32p_supplierForest_edge_040857
    g32p_supplierForest_actual_109306

def g32p_supplierForest_node_040859 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_040859 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040859 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_106239 := by
  decide +kernel

theorem g32p_supplierForest_actual_040859 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040859) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_040859
    g32p_supplierForest_actual_106239

def g32p_supplierForest_node_040866 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_040866 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040866 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_109320 := by
  decide +kernel

theorem g32p_supplierForest_actual_040866 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040866) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 0 g32p_supplierForest_edge_040866
    g32p_supplierForest_actual_109320

def g32p_supplierForest_node_040904 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_040904 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040904 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_026803 := by
  decide +kernel

theorem g32p_supplierForest_actual_040904 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040904) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_040904
    g32p_supplierForest_actual_026803

def g32p_supplierForest_node_040919 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_040919 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040919 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_038716 := by
  decide +kernel

theorem g32p_supplierForest_actual_040919 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040919) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_040919
    g32p_supplierForest_actual_038716

def g32p_supplierForest_node_040955 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_040955 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040955 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029406 := by
  decide +kernel

theorem g32p_supplierForest_actual_040955 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040955) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_040955
    g32p_supplierForest_actual_029406

def g32p_supplierForest_node_040957 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_040957 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040957 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_124513 := by
  decide +kernel

theorem g32p_supplierForest_actual_040957 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040957) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_040957
    g32p_supplierForest_actual_124513

def g32p_supplierForest_node_040981 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_040981 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040981 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_029378 := by
  decide +kernel

theorem g32p_supplierForest_actual_040981 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040981) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_040981
    g32p_supplierForest_actual_029378

def g32p_supplierForest_node_040990 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_040990 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_040990 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037884 := by
  decide +kernel

theorem g32p_supplierForest_actual_040990 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_040990) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_040990
    g32p_supplierForest_actual_037884

def g32p_supplierForest_node_041013 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_041013 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041013 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_104618 := by
  decide +kernel

theorem g32p_supplierForest_actual_041013 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041013) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_041013
    g32p_supplierForest_actual_104618

def g32p_supplierForest_node_041032 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_041032 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041032 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_109506 := by
  decide +kernel

theorem g32p_supplierForest_actual_041032 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041032) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_041032
    g32p_supplierForest_actual_109506

def g32p_supplierForest_node_041040 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_041040 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041040 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_105230 := by
  decide +kernel

theorem g32p_supplierForest_actual_041040 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041040) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_041040
    g32p_supplierForest_actual_105230

def g32p_supplierForest_node_041044 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_041044 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041044 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_041215 := by
  decide +kernel

theorem g32p_supplierForest_actual_041044 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041044) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_041044
    g32p_supplierForest_actual_041215

def g32p_supplierForest_node_041078 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_041078 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041078 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038007 := by
  decide +kernel

theorem g32p_supplierForest_actual_041078 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041078) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 2 g32p_supplierForest_edge_041078
    g32p_supplierForest_actual_038007

def g32p_supplierForest_node_041126 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_041126 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041126 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038200 := by
  decide +kernel

theorem g32p_supplierForest_actual_041126 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041126) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_041126
    g32p_supplierForest_actual_038200

def g32p_supplierForest_node_041142 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_041142 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041142 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038199 := by
  decide +kernel

theorem g32p_supplierForest_actual_041142 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041142) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_041142
    g32p_supplierForest_actual_038199

def g32p_supplierForest_node_041144 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_041144 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041144 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122366 := by
  decide +kernel

theorem g32p_supplierForest_actual_041144 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041144) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_041144
    g32p_supplierForest_actual_122366

def g32p_supplierForest_node_041151 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_041151 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041151 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038241 := by
  decide +kernel

theorem g32p_supplierForest_actual_041151 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041151) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_041151
    g32p_supplierForest_actual_038241

def g32p_supplierForest_node_041187 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_041187 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041187 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037827 := by
  decide +kernel

theorem g32p_supplierForest_actual_041187 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041187) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_041187
    g32p_supplierForest_actual_037827

def g32p_supplierForest_node_041189 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_041189 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041189 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_028298 := by
  decide +kernel

theorem g32p_supplierForest_actual_041189 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041189) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_041189
    g32p_supplierForest_actual_028298

def g32p_supplierForest_node_041260 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_041260 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041260 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_028463 := by
  decide +kernel

theorem g32p_supplierForest_actual_041260 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041260) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_041260
    g32p_supplierForest_actual_028463

def g32p_supplierForest_node_041286 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_041286 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041286 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112073 := by
  decide +kernel

theorem g32p_supplierForest_actual_041286 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041286) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 1 g32p_supplierForest_edge_041286
    g32p_supplierForest_actual_112073

def g32p_supplierForest_node_041292 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_041292 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041292 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_103890 := by
  decide +kernel

theorem g32p_supplierForest_actual_041292 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041292) ∧
        IsConj g (g32p_literalRepresentative 64) := by
  exact g32p_archive_step_lift _ _ 64 0 g32p_supplierForest_edge_041292
    g32p_supplierForest_actual_103890

def g32p_supplierForest_node_041313 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_041313 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041313 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_038680 := by
  decide +kernel

theorem g32p_supplierForest_actual_041313 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041313) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 3 g32p_supplierForest_edge_041313
    g32p_supplierForest_actual_038680

def g32p_supplierForest_node_041366 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_041366 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041366 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122532 := by
  decide +kernel

theorem g32p_supplierForest_actual_041366 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041366) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_041366
    g32p_supplierForest_actual_122532

def g32p_supplierForest_node_041374 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_041374 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041374 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_025033 := by
  decide +kernel

theorem g32p_supplierForest_actual_041374 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041374) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_041374
    g32p_supplierForest_actual_025033

def g32p_supplierForest_node_041387 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_041387 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041387 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_102467 := by
  decide +kernel

theorem g32p_supplierForest_actual_041387 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041387) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_041387
    g32p_supplierForest_actual_102467

def g32p_supplierForest_node_041388 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_041388 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041388 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_109912 := by
  decide +kernel

theorem g32p_supplierForest_actual_041388 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041388) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_041388
    g32p_supplierForest_actual_109912

def g32p_supplierForest_node_041444 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_041444 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041444 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_033208 := by
  decide +kernel

theorem g32p_supplierForest_actual_041444 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041444) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_041444
    g32p_supplierForest_actual_033208

def g32p_supplierForest_node_041446 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_041446 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041446 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_109981 := by
  decide +kernel

theorem g32p_supplierForest_actual_041446 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041446) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 0 g32p_supplierForest_edge_041446
    g32p_supplierForest_actual_109981

def g32p_supplierForest_node_041453 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_041453 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041453 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_044023 := by
  decide +kernel

theorem g32p_supplierForest_actual_041453 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041453) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_041453
    g32p_supplierForest_actual_044023

def g32p_supplierForest_node_041472 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_041472 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041472 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_115462 := by
  decide +kernel

theorem g32p_supplierForest_actual_041472 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041472) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 1 g32p_supplierForest_edge_041472
    g32p_supplierForest_actual_115462

def g32p_supplierForest_node_041484 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_041484 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041484 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_040391 := by
  decide +kernel

theorem g32p_supplierForest_actual_041484 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041484) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_041484
    g32p_supplierForest_actual_040391

def g32p_supplierForest_node_041488 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_041488 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041488 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004869 := by
  decide +kernel

theorem g32p_supplierForest_actual_041488 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041488) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_041488
    g32p_supplierForest_actual_004869

def g32p_supplierForest_node_041496 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_041496 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041496 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_040533 := by
  decide +kernel

theorem g32p_supplierForest_actual_041496 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041496) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_041496
    g32p_supplierForest_actual_040533

def g32p_supplierForest_node_041497 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_041497 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041497 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_106172 := by
  decide +kernel

theorem g32p_supplierForest_actual_041497 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041497) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_041497
    g32p_supplierForest_actual_106172

def g32p_supplierForest_node_041505 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_041505 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041505 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_027757 := by
  decide +kernel

theorem g32p_supplierForest_actual_041505 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041505) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_041505
    g32p_supplierForest_actual_027757

def g32p_supplierForest_node_041518 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_041518 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041518 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_040471 := by
  decide +kernel

theorem g32p_supplierForest_actual_041518 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041518) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_041518
    g32p_supplierForest_actual_040471

def g32p_supplierForest_node_041536 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_041536 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041536 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_028176 := by
  decide +kernel

theorem g32p_supplierForest_actual_041536 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041536) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_041536
    g32p_supplierForest_actual_028176

def g32p_supplierForest_node_041537 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_041537 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041537 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112293 := by
  decide +kernel

theorem g32p_supplierForest_actual_041537 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041537) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 1 g32p_supplierForest_edge_041537
    g32p_supplierForest_actual_112293

def g32p_supplierForest_node_041570 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_041570 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041570 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_026449 := by
  decide +kernel

theorem g32p_supplierForest_actual_041570 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041570) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_041570
    g32p_supplierForest_actual_026449

def g32p_supplierForest_node_041598 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_041598 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041598 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_111475 := by
  decide +kernel

theorem g32p_supplierForest_actual_041598 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041598) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 1 g32p_supplierForest_edge_041598
    g32p_supplierForest_actual_111475

def g32p_supplierForest_node_041827 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_041827 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041827 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_032140 := by
  decide +kernel

theorem g32p_supplierForest_actual_041827 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041827) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_041827
    g32p_supplierForest_actual_032140

def g32p_supplierForest_node_041829 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_041829 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041829 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_110383 := by
  decide +kernel

theorem g32p_supplierForest_actual_041829 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041829) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_041829
    g32p_supplierForest_actual_110383

def g32p_supplierForest_node_041840 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_041840 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041840 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029466 := by
  decide +kernel

theorem g32p_supplierForest_actual_041840 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041840) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_041840
    g32p_supplierForest_actual_029466

def g32p_supplierForest_node_041841 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_041841 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041841 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112910 := by
  decide +kernel

theorem g32p_supplierForest_actual_041841 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041841) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 1 g32p_supplierForest_edge_041841
    g32p_supplierForest_actual_112910

def g32p_supplierForest_node_041848 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_041848 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041848 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_108166 := by
  decide +kernel

theorem g32p_supplierForest_actual_041848 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041848) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_041848
    g32p_supplierForest_actual_108166

def g32p_supplierForest_node_041890 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_041890 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041890 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_110443 := by
  decide +kernel

theorem g32p_supplierForest_actual_041890 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041890) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_041890
    g32p_supplierForest_actual_110443

def g32p_supplierForest_node_041908 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_041908 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041908 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_033518 := by
  decide +kernel

theorem g32p_supplierForest_actual_041908 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041908) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_041908
    g32p_supplierForest_actual_033518

def g32p_supplierForest_node_041922 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_041922 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041922 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_121180 := by
  decide +kernel

theorem g32p_supplierForest_actual_041922 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041922) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_041922
    g32p_supplierForest_actual_121180

def g32p_supplierForest_node_041940 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_041940 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041940 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_025584 := by
  decide +kernel

theorem g32p_supplierForest_actual_041940 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041940) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 1 g32p_supplierForest_edge_041940
    g32p_supplierForest_actual_025584

def g32p_supplierForest_node_041955 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_041955 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041955 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_110504 := by
  decide +kernel

theorem g32p_supplierForest_actual_041955 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041955) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 0 g32p_supplierForest_edge_041955
    g32p_supplierForest_actual_110504

def g32p_supplierForest_node_041971 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_041971 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041971 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_114495 := by
  decide +kernel

theorem g32p_supplierForest_actual_041971 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041971) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_041971
    g32p_supplierForest_actual_114495

def g32p_supplierForest_node_041988 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_041988 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_041988 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_028582 := by
  decide +kernel

theorem g32p_supplierForest_actual_041988 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_041988) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_041988
    g32p_supplierForest_actual_028582

def g32p_supplierForest_node_042007 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_042007 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042007 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_104910 := by
  decide +kernel

theorem g32p_supplierForest_actual_042007 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042007) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_042007
    g32p_supplierForest_actual_104910

def g32p_supplierForest_node_042011 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_042011 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042011 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_042801 := by
  decide +kernel

theorem g32p_supplierForest_actual_042011 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042011) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 3 g32p_supplierForest_edge_042011
    g32p_supplierForest_actual_042801

def g32p_supplierForest_node_042030 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_042030 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042030 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_037604 := by
  decide +kernel

theorem g32p_supplierForest_actual_042030 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042030) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_042030
    g32p_supplierForest_actual_037604

def g32p_supplierForest_node_042058 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_042058 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042058 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_110059 := by
  decide +kernel

theorem g32p_supplierForest_actual_042058 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042058) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_042058
    g32p_supplierForest_actual_110059

def g32p_supplierForest_node_042071 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_042071 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042071 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_032840 := by
  decide +kernel

theorem g32p_supplierForest_actual_042071 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042071) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_042071
    g32p_supplierForest_actual_032840

def g32p_supplierForest_node_042094 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_042094 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042094 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_041838 := by
  decide +kernel

theorem g32p_supplierForest_actual_042094 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042094) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 3 g32p_supplierForest_edge_042094
    g32p_supplierForest_actual_041838

def g32p_supplierForest_node_042120 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_042120 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042120 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_043850 := by
  decide +kernel

theorem g32p_supplierForest_actual_042120 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042120) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_042120
    g32p_supplierForest_actual_043850

def g32p_supplierForest_node_042128 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_042128 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042128 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_110676 := by
  decide +kernel

theorem g32p_supplierForest_actual_042128 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042128) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 0 g32p_supplierForest_edge_042128
    g32p_supplierForest_actual_110676

def g32p_supplierForest_node_042146 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_042146 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042146 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_027122 := by
  decide +kernel

theorem g32p_supplierForest_actual_042146 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042146) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_042146
    g32p_supplierForest_actual_027122

def g32p_supplierForest_node_042174 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_042174 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042174 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122168 := by
  decide +kernel

theorem g32p_supplierForest_actual_042174 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042174) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_042174
    g32p_supplierForest_actual_122168

def g32p_supplierForest_node_042220 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_042220 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042220 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109332 := by
  decide +kernel

theorem g32p_supplierForest_actual_042220 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042220) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_042220
    g32p_supplierForest_actual_109332

def g32p_supplierForest_node_042258 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_042258 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042258 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_025276 := by
  decide +kernel

theorem g32p_supplierForest_actual_042258 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042258) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_042258
    g32p_supplierForest_actual_025276

def g32p_supplierForest_node_042275 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_042275 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042275 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_038171 := by
  decide +kernel

theorem g32p_supplierForest_actual_042275 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042275) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_042275
    g32p_supplierForest_actual_038171

def g32p_supplierForest_node_042278 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_042278 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042278 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_037633 := by
  decide +kernel

theorem g32p_supplierForest_actual_042278 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042278) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_042278
    g32p_supplierForest_actual_037633

def g32p_supplierForest_node_042301 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_042301 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042301 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_025659 := by
  decide +kernel

theorem g32p_supplierForest_actual_042301 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042301) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_042301
    g32p_supplierForest_actual_025659

def g32p_supplierForest_node_042305 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_042305 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042305 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_034062 := by
  decide +kernel

theorem g32p_supplierForest_actual_042305 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042305) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_042305
    g32p_supplierForest_actual_034062

def g32p_supplierForest_node_042327 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_042327 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042327 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_111941 := by
  decide +kernel

theorem g32p_supplierForest_actual_042327 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042327) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 1 g32p_supplierForest_edge_042327
    g32p_supplierForest_actual_111941

def g32p_supplierForest_node_042345 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_042345 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042345 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043317 := by
  decide +kernel

theorem g32p_supplierForest_actual_042345 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042345) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_042345
    g32p_supplierForest_actual_043317

def g32p_supplierForest_node_042354 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_042354 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042354 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043341 := by
  decide +kernel

theorem g32p_supplierForest_actual_042354 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042354) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_042354
    g32p_supplierForest_actual_043341

def g32p_supplierForest_node_042366 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_042366 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042366 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_030597 := by
  decide +kernel

theorem g32p_supplierForest_actual_042366 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042366) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_042366
    g32p_supplierForest_actual_030597

def g32p_supplierForest_node_042375 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_042375 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042375 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_039989 := by
  decide +kernel

theorem g32p_supplierForest_actual_042375 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042375) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_042375
    g32p_supplierForest_actual_039989

def g32p_supplierForest_node_042395 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_042395 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042395 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_005524 := by
  decide +kernel

theorem g32p_supplierForest_actual_042395 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042395) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 2 g32p_supplierForest_edge_042395
    g32p_supplierForest_actual_005524

def g32p_supplierForest_node_042404 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_042404 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042404 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_031003 := by
  decide +kernel

theorem g32p_supplierForest_actual_042404 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042404) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 1 g32p_supplierForest_edge_042404
    g32p_supplierForest_actual_031003

def g32p_supplierForest_node_042502 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_042502 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042502 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038317 := by
  decide +kernel

theorem g32p_supplierForest_actual_042502 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042502) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 2 g32p_supplierForest_edge_042502
    g32p_supplierForest_actual_038317

def g32p_supplierForest_node_042518 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_042518 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042518 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_030650 := by
  decide +kernel

theorem g32p_supplierForest_actual_042518 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042518) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_042518
    g32p_supplierForest_actual_030650

def g32p_supplierForest_node_042529 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_042529 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042529 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_032632 := by
  decide +kernel

theorem g32p_supplierForest_actual_042529 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042529) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_042529
    g32p_supplierForest_actual_032632

def g32p_supplierForest_node_042544 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_042544 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042544 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_028229 := by
  decide +kernel

theorem g32p_supplierForest_actual_042544 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042544) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_042544
    g32p_supplierForest_actual_028229

def g32p_supplierForest_node_042562 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_042562 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042562 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_027689 := by
  decide +kernel

theorem g32p_supplierForest_actual_042562 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042562) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_042562
    g32p_supplierForest_actual_027689

def g32p_supplierForest_node_042579 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_042579 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042579 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043788 := by
  decide +kernel

theorem g32p_supplierForest_actual_042579 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042579) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_042579
    g32p_supplierForest_actual_043788

def g32p_supplierForest_node_042609 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_042609 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042609 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_040970 := by
  decide +kernel

theorem g32p_supplierForest_actual_042609 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042609) ∧
        IsConj g (g32p_literalRepresentative 64) := by
  exact g32p_archive_step_lift _ _ 64 3 g32p_supplierForest_edge_042609
    g32p_supplierForest_actual_040970

def g32p_supplierForest_node_042643 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_042643 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042643 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_039601 := by
  decide +kernel

theorem g32p_supplierForest_actual_042643 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042643) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 3 g32p_supplierForest_edge_042643
    g32p_supplierForest_actual_039601

def g32p_supplierForest_node_042704 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_042704 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042704 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_027489 := by
  decide +kernel

theorem g32p_supplierForest_actual_042704 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042704) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_042704
    g32p_supplierForest_actual_027489

def g32p_supplierForest_node_042747 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_042747 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042747 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_104823 := by
  decide +kernel

theorem g32p_supplierForest_actual_042747 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042747) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_042747
    g32p_supplierForest_actual_104823

def g32p_supplierForest_node_042748 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_042748 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042748 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112769 := by
  decide +kernel

theorem g32p_supplierForest_actual_042748 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042748) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_042748
    g32p_supplierForest_actual_112769

def g32p_supplierForest_node_042749 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_042749 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042749 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_044177 := by
  decide +kernel

theorem g32p_supplierForest_actual_042749 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042749) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_042749
    g32p_supplierForest_actual_044177

def g32p_supplierForest_node_042750 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_042750 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042750 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_031282 := by
  decide +kernel

theorem g32p_supplierForest_actual_042750 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042750) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_042750
    g32p_supplierForest_actual_031282

def g32p_supplierForest_node_042751 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_042751 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042751 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_114310 := by
  decide +kernel

theorem g32p_supplierForest_actual_042751 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042751) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_042751
    g32p_supplierForest_actual_114310

def g32p_supplierForest_node_042752 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_042752 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042752 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_044067 := by
  decide +kernel

theorem g32p_supplierForest_actual_042752 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042752) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_042752
    g32p_supplierForest_actual_044067

def g32p_supplierForest_node_042757 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_042757 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042757 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_038534 := by
  decide +kernel

theorem g32p_supplierForest_actual_042757 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042757) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_042757
    g32p_supplierForest_actual_038534

def g32p_supplierForest_node_042788 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_042788 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042788 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_031912 := by
  decide +kernel

theorem g32p_supplierForest_actual_042788 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042788) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_042788
    g32p_supplierForest_actual_031912

def g32p_supplierForest_node_042872 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_042872 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042872 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_028208 := by
  decide +kernel

theorem g32p_supplierForest_actual_042872 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042872) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_042872
    g32p_supplierForest_actual_028208

def g32p_supplierForest_node_042905 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_042905 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042905 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_030175 := by
  decide +kernel

theorem g32p_supplierForest_actual_042905 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042905) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_042905
    g32p_supplierForest_actual_030175

def g32p_supplierForest_node_042957 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_042957 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042957 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_103009 := by
  decide +kernel

theorem g32p_supplierForest_actual_042957 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042957) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_042957
    g32p_supplierForest_actual_103009

def g32p_supplierForest_node_042959 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_042959 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042959 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_025843 := by
  decide +kernel

theorem g32p_supplierForest_actual_042959 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042959) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_042959
    g32p_supplierForest_actual_025843

def g32p_supplierForest_node_042960 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_042960 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042960 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_108324 := by
  decide +kernel

theorem g32p_supplierForest_actual_042960 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042960) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_042960
    g32p_supplierForest_actual_108324

def g32p_supplierForest_node_042967 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_042967 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042967 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_025864 := by
  decide +kernel

theorem g32p_supplierForest_actual_042967 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042967) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_042967
    g32p_supplierForest_actual_025864

def g32p_supplierForest_node_043071 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_043071 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043071 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004866 := by
  decide +kernel

theorem g32p_supplierForest_actual_043071 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043071) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_043071
    g32p_supplierForest_actual_004866

def g32p_supplierForest_node_043074 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_043074 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043074 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004869 := by
  decide +kernel

theorem g32p_supplierForest_actual_043074 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043074) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_043074
    g32p_supplierForest_actual_004869

def g32p_supplierForest_node_043097 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_043097 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043097 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_042661 := by
  decide +kernel

theorem g32p_supplierForest_actual_043097 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043097) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_043097
    g32p_supplierForest_actual_042661

def g32p_supplierForest_node_043105 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_043105 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043105 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_025674 := by
  decide +kernel

theorem g32p_supplierForest_actual_043105 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043105) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_043105
    g32p_supplierForest_actual_025674

def g32p_supplierForest_node_043106 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_043106 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043106 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_032201 := by
  decide +kernel

theorem g32p_supplierForest_actual_043106 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043106) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_043106
    g32p_supplierForest_actual_032201

def g32p_supplierForest_node_043107 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_043107 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043107 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_039141 := by
  decide +kernel

theorem g32p_supplierForest_actual_043107 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043107) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_043107
    g32p_supplierForest_actual_039141

def g32p_supplierForest_node_043142 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_043142 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043142 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_111514 := by
  decide +kernel

theorem g32p_supplierForest_actual_043142 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043142) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_043142
    g32p_supplierForest_actual_111514

def g32p_supplierForest_node_043157 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_043157 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043157 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002810 := by
  decide +kernel

theorem g32p_supplierForest_actual_043157 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043157) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_043157
    g32p_supplierForest_actual_002810

def g32p_supplierForest_node_043281 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_043281 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043281 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029514 := by
  decide +kernel

theorem g32p_supplierForest_actual_043281 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043281) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_043281
    g32p_supplierForest_actual_029514

def g32p_supplierForest_node_043301 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_043301 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043301 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_025072 := by
  decide +kernel

theorem g32p_supplierForest_actual_043301 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043301) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_043301
    g32p_supplierForest_actual_025072

def g32p_supplierForest_node_043304 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_043304 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043304 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_024983 := by
  decide +kernel

theorem g32p_supplierForest_actual_043304 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043304) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_043304
    g32p_supplierForest_actual_024983

def g32p_supplierForest_node_043342 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_043342 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043342 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_038380 := by
  decide +kernel

theorem g32p_supplierForest_actual_043342 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043342) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 0 g32p_supplierForest_edge_043342
    g32p_supplierForest_actual_038380

def g32p_supplierForest_node_043346 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_043346 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043346 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029800 := by
  decide +kernel

theorem g32p_supplierForest_actual_043346 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043346) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 3 g32p_supplierForest_edge_043346
    g32p_supplierForest_actual_029800

def g32p_supplierForest_node_043348 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_043348 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043348 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121415 := by
  decide +kernel

theorem g32p_supplierForest_actual_043348 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043348) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_043348
    g32p_supplierForest_actual_121415

def g32p_supplierForest_node_043351 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_043351 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043351 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_111925 := by
  decide +kernel

theorem g32p_supplierForest_actual_043351 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043351) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_043351
    g32p_supplierForest_actual_111925

def g32p_supplierForest_node_043358 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_043358 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043358 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_028545 := by
  decide +kernel

theorem g32p_supplierForest_actual_043358 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043358) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_043358
    g32p_supplierForest_actual_028545

def g32p_supplierForest_node_043367 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_043367 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043367 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_037939 := by
  decide +kernel

theorem g32p_supplierForest_actual_043367 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043367) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_043367
    g32p_supplierForest_actual_037939

def g32p_supplierForest_node_043368 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_043368 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043368 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_105888 := by
  decide +kernel

theorem g32p_supplierForest_actual_043368 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043368) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_043368
    g32p_supplierForest_actual_105888

def g32p_supplierForest_node_043402 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_043402 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043402 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_044240 := by
  decide +kernel

theorem g32p_supplierForest_actual_043402 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043402) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_043402
    g32p_supplierForest_actual_044240

def g32p_supplierForest_node_043421 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_043421 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043421 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_124892 := by
  decide +kernel

theorem g32p_supplierForest_actual_043421 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043421) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 1 g32p_supplierForest_edge_043421
    g32p_supplierForest_actual_124892

def g32p_supplierForest_node_043441 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_043441 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043441 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_038655 := by
  decide +kernel

theorem g32p_supplierForest_actual_043441 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043441) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 1 g32p_supplierForest_edge_043441
    g32p_supplierForest_actual_038655

def g32p_supplierForest_node_043493 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_043493 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043493 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_030918 := by
  decide +kernel

theorem g32p_supplierForest_actual_043493 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043493) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_043493
    g32p_supplierForest_actual_030918

def g32p_supplierForest_node_043534 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_043534 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043534 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_042840 := by
  decide +kernel

theorem g32p_supplierForest_actual_043534 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043534) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_043534
    g32p_supplierForest_actual_042840

def g32p_supplierForest_node_043548 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_043548 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043548 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_029095 := by
  decide +kernel

theorem g32p_supplierForest_actual_043548 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043548) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 1 g32p_supplierForest_edge_043548
    g32p_supplierForest_actual_029095

def g32p_supplierForest_node_043569 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_043569 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043569 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_030578 := by
  decide +kernel

theorem g32p_supplierForest_actual_043569 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043569) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_043569
    g32p_supplierForest_actual_030578

def g32p_supplierForest_node_043582 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_043582 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043582 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_124944 := by
  decide +kernel

theorem g32p_supplierForest_actual_043582 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043582) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_043582
    g32p_supplierForest_actual_124944

def g32p_supplierForest_node_043590 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_043590 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043590 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_124951 := by
  decide +kernel

theorem g32p_supplierForest_actual_043590 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043590) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_043590
    g32p_supplierForest_actual_124951

def g32p_supplierForest_node_043602 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_043602 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043602 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_032187 := by
  decide +kernel

theorem g32p_supplierForest_actual_043602 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043602) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 3 g32p_supplierForest_edge_043602
    g32p_supplierForest_actual_032187

def g32p_supplierForest_node_043622 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_043622 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043622 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_027120 := by
  decide +kernel

theorem g32p_supplierForest_actual_043622 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043622) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_043622
    g32p_supplierForest_actual_027120

def g32p_supplierForest_node_043692 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_043692 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043692 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_032713 := by
  decide +kernel

theorem g32p_supplierForest_actual_043692 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043692) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_043692
    g32p_supplierForest_actual_032713

def g32p_supplierForest_node_043694 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_043694 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043694 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_107278 := by
  decide +kernel

theorem g32p_supplierForest_actual_043694 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043694) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_043694
    g32p_supplierForest_actual_107278

def g32p_supplierForest_node_043705 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_043705 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043705 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_032718 := by
  decide +kernel

theorem g32p_supplierForest_actual_043705 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043705) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_043705
    g32p_supplierForest_actual_032718

def g32p_supplierForest_node_043715 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_043715 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043715 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_032865 := by
  decide +kernel

theorem g32p_supplierForest_actual_043715 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043715) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_043715
    g32p_supplierForest_actual_032865

def g32p_supplierForest_node_043726 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_043726 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043726 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_032909 := by
  decide +kernel

theorem g32p_supplierForest_actual_043726 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043726) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_043726
    g32p_supplierForest_actual_032909

def g32p_supplierForest_node_043744 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_043744 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043744 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_025797 := by
  decide +kernel

theorem g32p_supplierForest_actual_043744 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043744) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_043744
    g32p_supplierForest_actual_025797

def g32p_supplierForest_node_043756 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_043756 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043756 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_003668 := by
  decide +kernel

theorem g32p_supplierForest_actual_043756 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043756) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_043756
    g32p_supplierForest_actual_003668

def g32p_supplierForest_node_043781 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_043781 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043781 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_040363 := by
  decide +kernel

theorem g32p_supplierForest_actual_043781 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043781) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_043781
    g32p_supplierForest_actual_040363

def g32p_supplierForest_node_043785 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_043785 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043785 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_038070 := by
  decide +kernel

theorem g32p_supplierForest_actual_043785 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043785) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_043785
    g32p_supplierForest_actual_038070

def g32p_supplierForest_node_043789 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_043789 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043789 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_028308 := by
  decide +kernel

theorem g32p_supplierForest_actual_043789 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043789) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_043789
    g32p_supplierForest_actual_028308

def g32p_supplierForest_node_043801 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_043801 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043801 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112408 := by
  decide +kernel

theorem g32p_supplierForest_actual_043801 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043801) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_043801
    g32p_supplierForest_actual_112408

def g32p_supplierForest_node_043805 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_043805 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043805 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_114995 := by
  decide +kernel

theorem g32p_supplierForest_actual_043805 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043805) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_043805
    g32p_supplierForest_actual_114995

def g32p_supplierForest_node_043835 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_043835 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043835 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_032685 := by
  decide +kernel

theorem g32p_supplierForest_actual_043835 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043835) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 0 g32p_supplierForest_edge_043835
    g32p_supplierForest_actual_032685

def g32p_supplierForest_node_043861 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_043861 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043861 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004945 := by
  decide +kernel

theorem g32p_supplierForest_actual_043861 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043861) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_043861
    g32p_supplierForest_actual_004945

def g32p_supplierForest_node_043877 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_043877 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043877 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_040744 := by
  decide +kernel

theorem g32p_supplierForest_actual_043877 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043877) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 3 g32p_supplierForest_edge_043877
    g32p_supplierForest_actual_040744

def g32p_supplierForest_node_043887 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_043887 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043887 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_037663 := by
  decide +kernel

theorem g32p_supplierForest_actual_043887 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043887) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_043887
    g32p_supplierForest_actual_037663

def g32p_supplierForest_node_043897 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_043897 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043897 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113230 := by
  decide +kernel

theorem g32p_supplierForest_actual_043897 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043897) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_043897
    g32p_supplierForest_actual_113230

def g32p_supplierForest_node_043908 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_043908 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043908 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_112525 := by
  decide +kernel

theorem g32p_supplierForest_actual_043908 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043908) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_043908
    g32p_supplierForest_actual_112525

def g32p_supplierForest_node_043948 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_043948 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043948 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_107704 := by
  decide +kernel

theorem g32p_supplierForest_actual_043948 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043948) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_043948
    g32p_supplierForest_actual_107704

def g32p_supplierForest_node_043957 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_043957 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043957 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121733 := by
  decide +kernel

theorem g32p_supplierForest_actual_043957 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043957) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_043957
    g32p_supplierForest_actual_121733

def g32p_supplierForest_node_043989 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_043989 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043989 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_121434 := by
  decide +kernel

theorem g32p_supplierForest_actual_043989 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043989) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_043989
    g32p_supplierForest_actual_121434

def g32p_supplierForest_node_044012 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_044012 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044012 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_039736 := by
  decide +kernel

theorem g32p_supplierForest_actual_044012 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044012) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_044012
    g32p_supplierForest_actual_039736

def g32p_supplierForest_node_044064 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_044064 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044064 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_042932 := by
  decide +kernel

theorem g32p_supplierForest_actual_044064 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044064) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 1 g32p_supplierForest_edge_044064
    g32p_supplierForest_actual_042932

def g32p_supplierForest_node_044089 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_044089 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044089 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_034281 := by
  decide +kernel

theorem g32p_supplierForest_actual_044089 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044089) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 1 g32p_supplierForest_edge_044089
    g32p_supplierForest_actual_034281

def g32p_supplierForest_node_044097 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_044097 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044097 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_025726 := by
  decide +kernel

theorem g32p_supplierForest_actual_044097 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044097) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 2 g32p_supplierForest_edge_044097
    g32p_supplierForest_actual_025726

def g32p_supplierForest_node_044101 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-2, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_044101 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044101 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_027713 := by
  decide +kernel

theorem g32p_supplierForest_actual_044101 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044101) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 2 g32p_supplierForest_edge_044101
    g32p_supplierForest_actual_027713

def g32p_supplierForest_node_044147 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_044147 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044147 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_104027 := by
  decide +kernel

theorem g32p_supplierForest_actual_044147 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044147) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_044147
    g32p_supplierForest_actual_104027

def g32p_supplierForest_node_044159 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_044159 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044159 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_036176 := by
  decide +kernel

theorem g32p_supplierForest_actual_044159 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044159) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_044159
    g32p_supplierForest_actual_036176

def g32p_supplierForest_node_044172 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_044172 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044172 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_104825 := by
  decide +kernel

theorem g32p_supplierForest_actual_044172 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044172) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_044172
    g32p_supplierForest_actual_104825

def g32p_supplierForest_node_044194 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_044194 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044194 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_038198 := by
  decide +kernel

theorem g32p_supplierForest_actual_044194 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044194) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 0 g32p_supplierForest_edge_044194
    g32p_supplierForest_actual_038198

def g32p_supplierForest_node_044198 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_044198 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044198 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_038201 := by
  decide +kernel

theorem g32p_supplierForest_actual_044198 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044198) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_044198
    g32p_supplierForest_actual_038201

def g32p_supplierForest_node_044209 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_044209 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044209 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118527 := by
  decide +kernel

theorem g32p_supplierForest_actual_044209 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044209) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_044209
    g32p_supplierForest_actual_118527

def g32p_supplierForest_node_044216 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_044216 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044216 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_028136 := by
  decide +kernel

theorem g32p_supplierForest_actual_044216 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044216) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_044216
    g32p_supplierForest_actual_028136

def g32p_supplierForest_node_044229 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_044229 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044229 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_038214 := by
  decide +kernel

theorem g32p_supplierForest_actual_044229 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044229) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_044229
    g32p_supplierForest_actual_038214

def g32p_supplierForest_node_044250 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_044250 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044250 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_112793 := by
  decide +kernel

theorem g32p_supplierForest_actual_044250 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044250) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_044250
    g32p_supplierForest_actual_112793

def g32p_supplierForest_node_044253 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_044253 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044253 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_005559 := by
  decide +kernel

theorem g32p_supplierForest_actual_044253 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044253) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 3 g32p_supplierForest_edge_044253
    g32p_supplierForest_actual_005559

def g32p_supplierForest_node_044270 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_044270 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044270 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_112868 := by
  decide +kernel

theorem g32p_supplierForest_actual_044270 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044270) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_044270
    g32p_supplierForest_actual_112868

def g32p_supplierForest_node_044314 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_044314 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044314 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037081 := by
  decide +kernel

theorem g32p_supplierForest_actual_044314 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044314) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_044314
    g32p_supplierForest_actual_037081

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_056 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_152303 else g32p_supplierForest_node_152316) else (if i.val < 3 then g32p_supplierForest_node_152317 else g32p_supplierForest_node_152332)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_152352 else g32p_supplierForest_node_152369) else (if i.val < 7 then g32p_supplierForest_node_152398 else g32p_supplierForest_node_152419))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_152432 else g32p_supplierForest_node_152460) else (if i.val < 11 then g32p_supplierForest_node_152490 else g32p_supplierForest_node_152493)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_152501 else g32p_supplierForest_node_152512) else (if i.val < 15 then g32p_supplierForest_node_152559 else g32p_supplierForest_node_152567)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_152571 else g32p_supplierForest_node_152572) else (if i.val < 19 then g32p_supplierForest_node_152605 else g32p_supplierForest_node_152608)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_152616 else g32p_supplierForest_node_152713) else (if i.val < 23 then g32p_supplierForest_node_152758 else g32p_supplierForest_node_152780))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_152792 else g32p_supplierForest_node_152801) else (if i.val < 27 then g32p_supplierForest_node_152802 else g32p_supplierForest_node_152846)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_152891 else g32p_supplierForest_node_152942) else (if i.val < 31 then g32p_supplierForest_node_152952 else g32p_supplierForest_node_153008))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_153012 else g32p_supplierForest_node_153035) else (if i.val < 35 then g32p_supplierForest_node_153047 else g32p_supplierForest_node_153065)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_153096 else g32p_supplierForest_node_153099) else (if i.val < 39 then g32p_supplierForest_node_153107 else g32p_supplierForest_node_153128))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_153160 else g32p_supplierForest_node_153199) else (if i.val < 43 then g32p_supplierForest_node_153209 else g32p_supplierForest_node_153211)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_153218 else g32p_supplierForest_node_153227) else (if i.val < 47 then g32p_supplierForest_node_153236 else g32p_supplierForest_node_153239)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_153244 else g32p_supplierForest_node_153248) else (if i.val < 51 then g32p_supplierForest_node_153255 else g32p_supplierForest_node_153262)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_153331 else g32p_supplierForest_node_153334) else (if i.val < 55 then g32p_supplierForest_node_153355 else g32p_supplierForest_node_153361))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_153365 else g32p_supplierForest_node_153377) else (if i.val < 59 then g32p_supplierForest_node_153383 else g32p_supplierForest_node_153420)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_153445 else g32p_supplierForest_node_153449) else (if i.val < 63 then g32p_supplierForest_node_153482 else g32p_supplierForest_node_153500)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_153503 else g32p_supplierForest_node_153518) else (if i.val < 67 then g32p_supplierForest_node_153523 else g32p_supplierForest_node_153529)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_153536 else g32p_supplierForest_node_153559) else (if i.val < 71 then g32p_supplierForest_node_153594 else g32p_supplierForest_node_153597))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_153615 else g32p_supplierForest_node_153645) else (if i.val < 75 then g32p_supplierForest_node_153670 else g32p_supplierForest_node_153708)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_153711 else g32p_supplierForest_node_153712) else (if i.val < 79 then g32p_supplierForest_node_153732 else g32p_supplierForest_node_153783)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_153793 else g32p_supplierForest_node_153798) else (if i.val < 83 then g32p_supplierForest_node_153835 else g32p_supplierForest_node_153837)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_153861 else g32p_supplierForest_node_153909) else (if i.val < 87 then g32p_supplierForest_node_153963 else g32p_supplierForest_node_153969))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_153980 else g32p_supplierForest_node_154009) else (if i.val < 91 then g32p_supplierForest_node_154040 else g32p_supplierForest_node_154063)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_154130 else g32p_supplierForest_node_154154) else (if i.val < 95 then g32p_supplierForest_node_154171 else g32p_supplierForest_node_154246))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_154278 else g32p_supplierForest_node_154322) else (if i.val < 99 then g32p_supplierForest_node_154353 else g32p_supplierForest_node_154439)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_154456 else g32p_supplierForest_node_154466) else (if i.val < 103 then g32p_supplierForest_node_154479 else g32p_supplierForest_node_154517))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_154522 else g32p_supplierForest_node_154526) else (if i.val < 107 then g32p_supplierForest_node_154539 else g32p_supplierForest_node_154545)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_154702 else g32p_supplierForest_node_154749) else (if i.val < 111 then g32p_supplierForest_node_154773 else g32p_supplierForest_node_154806)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_154867 else g32p_supplierForest_node_154881) else (if i.val < 115 then g32p_supplierForest_node_154893 else g32p_supplierForest_node_154899)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_154931 else g32p_supplierForest_node_154938) else (if i.val < 119 then g32p_supplierForest_node_154973 else g32p_supplierForest_node_154996))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_155035 else g32p_supplierForest_node_155036) else (if i.val < 123 then g32p_supplierForest_node_155083 else g32p_supplierForest_node_155102)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_155113 else g32p_supplierForest_node_155119) else (if i.val < 127 then g32p_supplierForest_node_155135 else g32p_supplierForest_node_155141))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_155144 else g32p_supplierForest_node_155172) else (if i.val < 131 then g32p_supplierForest_node_155196 else g32p_supplierForest_node_155211)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_155213 else g32p_supplierForest_node_155226) else (if i.val < 135 then g32p_supplierForest_node_155228 else g32p_supplierForest_node_155244))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_155257 else g32p_supplierForest_node_155309) else (if i.val < 139 then g32p_supplierForest_node_155318 else g32p_supplierForest_node_155324)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_155341 else g32p_supplierForest_node_155377) else (if i.val < 143 then g32p_supplierForest_node_155382 else g32p_supplierForest_node_155412)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_155416 else g32p_supplierForest_node_155419) else (if i.val < 147 then g32p_supplierForest_node_155436 else g32p_supplierForest_node_155440)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_155449 else g32p_supplierForest_node_155451) else (if i.val < 151 then g32p_supplierForest_node_155460 else g32p_supplierForest_node_155470))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_155475 else g32p_supplierForest_node_155479) else (if i.val < 155 then g32p_supplierForest_node_155509 else g32p_supplierForest_node_155518)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_000251 else g32p_supplierForest_node_000276) else (if i.val < 159 then g32p_supplierForest_node_000318 else g32p_supplierForest_node_000331))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_000376 else g32p_supplierForest_node_000459) else (if i.val < 163 then g32p_supplierForest_node_000495 else g32p_supplierForest_node_000503)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_000516 else g32p_supplierForest_node_000539) else (if i.val < 167 then g32p_supplierForest_node_000569 else g32p_supplierForest_node_000609))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_000629 else g32p_supplierForest_node_000654) else (if i.val < 171 then g32p_supplierForest_node_000687 else g32p_supplierForest_node_000772)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_000791 else g32p_supplierForest_node_000803) else (if i.val < 175 then g32p_supplierForest_node_000806 else g32p_supplierForest_node_000821)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_000823 else g32p_supplierForest_node_000834) else (if i.val < 179 then g32p_supplierForest_node_000885 else g32p_supplierForest_node_000886)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_000912 else g32p_supplierForest_node_000954) else (if i.val < 183 then g32p_supplierForest_node_000962 else g32p_supplierForest_node_000971))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_001027 else g32p_supplierForest_node_001028) else (if i.val < 187 then g32p_supplierForest_node_001088 else g32p_supplierForest_node_001097)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_001106 else g32p_supplierForest_node_001188) else (if i.val < 191 then g32p_supplierForest_node_001221 else g32p_supplierForest_node_001227)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_001240 else g32p_supplierForest_node_001260) else (if i.val < 195 then g32p_supplierForest_node_001303 else g32p_supplierForest_node_001316)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_001403 else g32p_supplierForest_node_001430) else (if i.val < 199 then g32p_supplierForest_node_001431 else g32p_supplierForest_node_001434))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_001445 else g32p_supplierForest_node_001451) else (if i.val < 203 then g32p_supplierForest_node_001467 else g32p_supplierForest_node_001517)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_001545 else g32p_supplierForest_node_001565) else (if i.val < 207 then g32p_supplierForest_node_001575 else g32p_supplierForest_node_001583)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_001678 else g32p_supplierForest_node_001705) else (if i.val < 211 then g32p_supplierForest_node_001723 else g32p_supplierForest_node_001727)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_001733 else g32p_supplierForest_node_001740) else (if i.val < 215 then g32p_supplierForest_node_001743 else g32p_supplierForest_node_001756))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_001782 else g32p_supplierForest_node_001827) else (if i.val < 219 then g32p_supplierForest_node_001883 else g32p_supplierForest_node_001920)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_001952 else g32p_supplierForest_node_002058) else (if i.val < 223 then g32p_supplierForest_node_002080 else g32p_supplierForest_node_002102))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_002140 else g32p_supplierForest_node_002169) else (if i.val < 227 then g32p_supplierForest_node_002225 else g32p_supplierForest_node_002254)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_002297 else g32p_supplierForest_node_002302) else (if i.val < 231 then g32p_supplierForest_node_002366 else g32p_supplierForest_node_002376))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_002395 else g32p_supplierForest_node_002479) else (if i.val < 235 then g32p_supplierForest_node_002588 else g32p_supplierForest_node_002621)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_002648 else g32p_supplierForest_node_002661) else (if i.val < 239 then g32p_supplierForest_node_002689 else g32p_supplierForest_node_002693)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_002727 else g32p_supplierForest_node_002800) else (if i.val < 243 then g32p_supplierForest_node_002866 else g32p_supplierForest_node_002887)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_002977 else g32p_supplierForest_node_002983) else (if i.val < 247 then g32p_supplierForest_node_002986 else g32p_supplierForest_node_003002))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_003033 else g32p_supplierForest_node_003039) else (if i.val < 251 then g32p_supplierForest_node_003040 else g32p_supplierForest_node_003050)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_003082 else g32p_supplierForest_node_003098) else (if i.val < 255 then g32p_supplierForest_node_003108 else g32p_supplierForest_node_003126))))))))

def g32p_supplierForest_classes_056 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 85 else 11) else (if i.val < 3 then 85 else 83)) else (if i.val < 6 then (if i.val < 5 then 86 else 25) else (if i.val < 7 then 86 else 86))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 98 else 86) else (if i.val < 11 then 86 else 80)) else (if i.val < 14 then (if i.val < 13 then 85 else 92) else (if i.val < 15 then 90 else 92)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 90 else 92) else (if i.val < 19 then 29 else 35)) else (if i.val < 22 then (if i.val < 21 then 92 else 92) else (if i.val < 23 then 35 else 92))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 61 else 92) else (if i.val < 27 then 92 else 91)) else (if i.val < 30 then (if i.val < 29 then 66 else 36) else (if i.val < 31 then 60 else 66))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 89 else 62) else (if i.val < 35 then 58 else 60)) else (if i.val < 38 then (if i.val < 37 then 60 else 90) else (if i.val < 39 then 35 else 89))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 62 else 90) else (if i.val < 43 then 35 else 90)) else (if i.val < 46 then (if i.val < 45 then 35 else 66) else (if i.val < 47 then 60 else 90)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 89 else 66) else (if i.val < 51 then 60 else 90)) else (if i.val < 54 then (if i.val < 53 then 90 else 92) else (if i.val < 55 then 90 else 36))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 91 else 35) else (if i.val < 59 then 35 else 35)) else (if i.val < 62 then (if i.val < 61 then 90 else 91) else (if i.val < 63 then 61 else 92)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 66 else 58) else (if i.val < 67 then 62 else 58)) else (if i.val < 70 then (if i.val < 69 then 58 else 30) else (if i.val < 71 then 89 else 66))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 89 else 66) else (if i.val < 75 then 66 else 92)) else (if i.val < 78 then (if i.val < 77 then 62 else 57) else (if i.val < 79 then 35 else 90)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 35 else 60) else (if i.val < 83 then 92 else 90)) else (if i.val < 86 then (if i.val < 85 then 89 else 66) else (if i.val < 87 then 92 else 90))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 92 else 62) else (if i.val < 91 then 35 else 66)) else (if i.val < 94 then (if i.val < 93 then 92 else 62) else (if i.val < 95 then 92 else 92))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 89 else 89) else (if i.val < 99 then 62 else 92)) else (if i.val < 102 then (if i.val < 101 then 89 else 90) else (if i.val < 103 then 92 else 61))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 66 else 89) else (if i.val < 107 then 92 else 61)) else (if i.val < 110 then (if i.val < 109 then 62 else 90) else (if i.val < 111 then 92 else 30)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 66 else 66) else (if i.val < 115 then 90 else 89)) else (if i.val < 118 then (if i.val < 117 then 89 else 89) else (if i.val < 119 then 90 else 90))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 76 else 77) else (if i.val < 123 then 77 else 78)) else (if i.val < 126 then (if i.val < 125 then 78 else 72) else (if i.val < 127 then 78 else 94))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 94 else 78) else (if i.val < 131 then 77 else 78)) else (if i.val < 134 then (if i.val < 133 then 76 else 71) else (if i.val < 135 then 76 else 42))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 78 else 78) else (if i.val < 139 then 77 else 77)) else (if i.val < 142 then (if i.val < 141 then 72 else 77) else (if i.val < 143 then 94 else 76)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 76 else 78) else (if i.val < 147 then 77 else 78)) else (if i.val < 150 then (if i.val < 149 then 78 else 78) else (if i.val < 151 then 77 else 100))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 100 else 100) else (if i.val < 155 then 100 else 100)) else (if i.val < 158 then (if i.val < 157 then 15 else 14) else (if i.val < 159 then 15 else 15))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 16 else 22) else (if i.val < 163 then 5 else 5)) else (if i.val < 166 then (if i.val < 165 then 19 else 7) else (if i.val < 167 then 24 else 5))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 5 else 19) else (if i.val < 171 then 19 else 22)) else (if i.val < 174 then (if i.val < 173 then 24 else 19) else (if i.val < 175 then 22 else 21)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 5 else 19) else (if i.val < 179 then 19 else 24)) else (if i.val < 182 then (if i.val < 181 then 7 else 18) else (if i.val < 183 then 22 else 7))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 22 else 24) else (if i.val < 187 then 10 else 10)) else (if i.val < 190 then (if i.val < 189 then 10 else 10) else (if i.val < 191 then 10 else 10)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 10 else 10) else (if i.val < 195 then 10 else 26)) else (if i.val < 198 then (if i.val < 197 then 10 else 10) else (if i.val < 199 then 10 else 10))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 10 else 10) else (if i.val < 203 then 10 else 26)) else (if i.val < 206 then (if i.val < 205 then 28 else 27) else (if i.val < 207 then 10 else 10)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 10 else 10) else (if i.val < 211 then 10 else 26)) else (if i.val < 214 then (if i.val < 213 then 10 else 10) else (if i.val < 215 then 9 else 10))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 10 else 10) else (if i.val < 219 then 10 else 10)) else (if i.val < 222 then (if i.val < 221 then 9 else 9) else (if i.val < 223 then 10 else 10))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 10 else 10) else (if i.val < 227 then 10 else 25)) else (if i.val < 230 then (if i.val < 229 then 26 else 27) else (if i.val < 231 then 27 else 8))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 10 else 12) else (if i.val < 235 then 4 else 15)) else (if i.val < 238 then (if i.val < 237 then 15 else 33) else (if i.val < 239 then 14 else 16)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 16 else 17) else (if i.val < 243 then 15 else 4)) else (if i.val < 246 then (if i.val < 245 then 4 else 3) else (if i.val < 247 then 4 else 15))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 15 else 16) else (if i.val < 251 then 4 else 4)) else (if i.val < 254 then (if i.val < 253 then 31 else 15) else (if i.val < 255 then 16 else 31))))))))

theorem g32p_supplierForest_actual_056 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_056 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_056 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_152303
  · exact g32p_supplierForest_actual_152316
  · exact g32p_supplierForest_actual_152317
  · exact g32p_supplierForest_actual_152332
  · exact g32p_supplierForest_actual_152352
  · exact g32p_supplierForest_actual_152369
  · exact g32p_supplierForest_actual_152398
  · exact g32p_supplierForest_actual_152419
  · exact g32p_supplierForest_actual_152432
  · exact g32p_supplierForest_actual_152460
  · exact g32p_supplierForest_actual_152490
  · exact g32p_supplierForest_actual_152493
  · exact g32p_supplierForest_actual_152501
  · exact g32p_supplierForest_actual_152512
  · exact g32p_supplierForest_actual_152559
  · exact g32p_supplierForest_actual_152567
  · exact g32p_supplierForest_actual_152571
  · exact g32p_supplierForest_actual_152572
  · exact g32p_supplierForest_actual_152605
  · exact g32p_supplierForest_actual_152608
  · exact g32p_supplierForest_actual_152616
  · exact g32p_supplierForest_actual_152713
  · exact g32p_supplierForest_actual_152758
  · exact g32p_supplierForest_actual_152780
  · exact g32p_supplierForest_actual_152792
  · exact g32p_supplierForest_actual_152801
  · exact g32p_supplierForest_actual_152802
  · exact g32p_supplierForest_actual_152846
  · exact g32p_supplierForest_actual_152891
  · exact g32p_supplierForest_actual_152942
  · exact g32p_supplierForest_actual_152952
  · exact g32p_supplierForest_actual_153008
  · exact g32p_supplierForest_actual_153012
  · exact g32p_supplierForest_actual_153035
  · exact g32p_supplierForest_actual_153047
  · exact g32p_supplierForest_actual_153065
  · exact g32p_supplierForest_actual_153096
  · exact g32p_supplierForest_actual_153099
  · exact g32p_supplierForest_actual_153107
  · exact g32p_supplierForest_actual_153128
  · exact g32p_supplierForest_actual_153160
  · exact g32p_supplierForest_actual_153199
  · exact g32p_supplierForest_actual_153209
  · exact g32p_supplierForest_actual_153211
  · exact g32p_supplierForest_actual_153218
  · exact g32p_supplierForest_actual_153227
  · exact g32p_supplierForest_actual_153236
  · exact g32p_supplierForest_actual_153239
  · exact g32p_supplierForest_actual_153244
  · exact g32p_supplierForest_actual_153248
  · exact g32p_supplierForest_actual_153255
  · exact g32p_supplierForest_actual_153262
  · exact g32p_supplierForest_actual_153331
  · exact g32p_supplierForest_actual_153334
  · exact g32p_supplierForest_actual_153355
  · exact g32p_supplierForest_actual_153361
  · exact g32p_supplierForest_actual_153365
  · exact g32p_supplierForest_actual_153377
  · exact g32p_supplierForest_actual_153383
  · exact g32p_supplierForest_actual_153420
  · exact g32p_supplierForest_actual_153445
  · exact g32p_supplierForest_actual_153449
  · exact g32p_supplierForest_actual_153482
  · exact g32p_supplierForest_actual_153500
  · exact g32p_supplierForest_actual_153503
  · exact g32p_supplierForest_actual_153518
  · exact g32p_supplierForest_actual_153523
  · exact g32p_supplierForest_actual_153529
  · exact g32p_supplierForest_actual_153536
  · exact g32p_supplierForest_actual_153559
  · exact g32p_supplierForest_actual_153594
  · exact g32p_supplierForest_actual_153597
  · exact g32p_supplierForest_actual_153615
  · exact g32p_supplierForest_actual_153645
  · exact g32p_supplierForest_actual_153670
  · exact g32p_supplierForest_actual_153708
  · exact g32p_supplierForest_actual_153711
  · exact g32p_supplierForest_actual_153712
  · exact g32p_supplierForest_actual_153732
  · exact g32p_supplierForest_actual_153783
  · exact g32p_supplierForest_actual_153793
  · exact g32p_supplierForest_actual_153798
  · exact g32p_supplierForest_actual_153835
  · exact g32p_supplierForest_actual_153837
  · exact g32p_supplierForest_actual_153861
  · exact g32p_supplierForest_actual_153909
  · exact g32p_supplierForest_actual_153963
  · exact g32p_supplierForest_actual_153969
  · exact g32p_supplierForest_actual_153980
  · exact g32p_supplierForest_actual_154009
  · exact g32p_supplierForest_actual_154040
  · exact g32p_supplierForest_actual_154063
  · exact g32p_supplierForest_actual_154130
  · exact g32p_supplierForest_actual_154154
  · exact g32p_supplierForest_actual_154171
  · exact g32p_supplierForest_actual_154246
  · exact g32p_supplierForest_actual_154278
  · exact g32p_supplierForest_actual_154322
  · exact g32p_supplierForest_actual_154353
  · exact g32p_supplierForest_actual_154439
  · exact g32p_supplierForest_actual_154456
  · exact g32p_supplierForest_actual_154466
  · exact g32p_supplierForest_actual_154479
  · exact g32p_supplierForest_actual_154517
  · exact g32p_supplierForest_actual_154522
  · exact g32p_supplierForest_actual_154526
  · exact g32p_supplierForest_actual_154539
  · exact g32p_supplierForest_actual_154545
  · exact g32p_supplierForest_actual_154702
  · exact g32p_supplierForest_actual_154749
  · exact g32p_supplierForest_actual_154773
  · exact g32p_supplierForest_actual_154806
  · exact g32p_supplierForest_actual_154867
  · exact g32p_supplierForest_actual_154881
  · exact g32p_supplierForest_actual_154893
  · exact g32p_supplierForest_actual_154899
  · exact g32p_supplierForest_actual_154931
  · exact g32p_supplierForest_actual_154938
  · exact g32p_supplierForest_actual_154973
  · exact g32p_supplierForest_actual_154996
  · exact g32p_supplierForest_actual_155035
  · exact g32p_supplierForest_actual_155036
  · exact g32p_supplierForest_actual_155083
  · exact g32p_supplierForest_actual_155102
  · exact g32p_supplierForest_actual_155113
  · exact g32p_supplierForest_actual_155119
  · exact g32p_supplierForest_actual_155135
  · exact g32p_supplierForest_actual_155141
  · exact g32p_supplierForest_actual_155144
  · exact g32p_supplierForest_actual_155172
  · exact g32p_supplierForest_actual_155196
  · exact g32p_supplierForest_actual_155211
  · exact g32p_supplierForest_actual_155213
  · exact g32p_supplierForest_actual_155226
  · exact g32p_supplierForest_actual_155228
  · exact g32p_supplierForest_actual_155244
  · exact g32p_supplierForest_actual_155257
  · exact g32p_supplierForest_actual_155309
  · exact g32p_supplierForest_actual_155318
  · exact g32p_supplierForest_actual_155324
  · exact g32p_supplierForest_actual_155341
  · exact g32p_supplierForest_actual_155377
  · exact g32p_supplierForest_actual_155382
  · exact g32p_supplierForest_actual_155412
  · exact g32p_supplierForest_actual_155416
  · exact g32p_supplierForest_actual_155419
  · exact g32p_supplierForest_actual_155436
  · exact g32p_supplierForest_actual_155440
  · exact g32p_supplierForest_actual_155449
  · exact g32p_supplierForest_actual_155451
  · exact g32p_supplierForest_actual_155460
  · exact g32p_supplierForest_actual_155470
  · exact g32p_supplierForest_actual_155475
  · exact g32p_supplierForest_actual_155479
  · exact g32p_supplierForest_actual_155509
  · exact g32p_supplierForest_actual_155518
  · exact g32p_supplierForest_actual_000251
  · exact g32p_supplierForest_actual_000276
  · exact g32p_supplierForest_actual_000318
  · exact g32p_supplierForest_actual_000331
  · exact g32p_supplierForest_actual_000376
  · exact g32p_supplierForest_actual_000459
  · exact g32p_supplierForest_actual_000495
  · exact g32p_supplierForest_actual_000503
  · exact g32p_supplierForest_actual_000516
  · exact g32p_supplierForest_actual_000539
  · exact g32p_supplierForest_actual_000569
  · exact g32p_supplierForest_actual_000609
  · exact g32p_supplierForest_actual_000629
  · exact g32p_supplierForest_actual_000654
  · exact g32p_supplierForest_actual_000687
  · exact g32p_supplierForest_actual_000772
  · exact g32p_supplierForest_actual_000791
  · exact g32p_supplierForest_actual_000803
  · exact g32p_supplierForest_actual_000806
  · exact g32p_supplierForest_actual_000821
  · exact g32p_supplierForest_actual_000823
  · exact g32p_supplierForest_actual_000834
  · exact g32p_supplierForest_actual_000885
  · exact g32p_supplierForest_actual_000886
  · exact g32p_supplierForest_actual_000912
  · exact g32p_supplierForest_actual_000954
  · exact g32p_supplierForest_actual_000962
  · exact g32p_supplierForest_actual_000971
  · exact g32p_supplierForest_actual_001027
  · exact g32p_supplierForest_actual_001028
  · exact g32p_supplierForest_actual_001088
  · exact g32p_supplierForest_actual_001097
  · exact g32p_supplierForest_actual_001106
  · exact g32p_supplierForest_actual_001188
  · exact g32p_supplierForest_actual_001221
  · exact g32p_supplierForest_actual_001227
  · exact g32p_supplierForest_actual_001240
  · exact g32p_supplierForest_actual_001260
  · exact g32p_supplierForest_actual_001303
  · exact g32p_supplierForest_actual_001316
  · exact g32p_supplierForest_actual_001403
  · exact g32p_supplierForest_actual_001430
  · exact g32p_supplierForest_actual_001431
  · exact g32p_supplierForest_actual_001434
  · exact g32p_supplierForest_actual_001445
  · exact g32p_supplierForest_actual_001451
  · exact g32p_supplierForest_actual_001467
  · exact g32p_supplierForest_actual_001517
  · exact g32p_supplierForest_actual_001545
  · exact g32p_supplierForest_actual_001565
  · exact g32p_supplierForest_actual_001575
  · exact g32p_supplierForest_actual_001583
  · exact g32p_supplierForest_actual_001678
  · exact g32p_supplierForest_actual_001705
  · exact g32p_supplierForest_actual_001723
  · exact g32p_supplierForest_actual_001727
  · exact g32p_supplierForest_actual_001733
  · exact g32p_supplierForest_actual_001740
  · exact g32p_supplierForest_actual_001743
  · exact g32p_supplierForest_actual_001756
  · exact g32p_supplierForest_actual_001782
  · exact g32p_supplierForest_actual_001827
  · exact g32p_supplierForest_actual_001883
  · exact g32p_supplierForest_actual_001920
  · exact g32p_supplierForest_actual_001952
  · exact g32p_supplierForest_actual_002058
  · exact g32p_supplierForest_actual_002080
  · exact g32p_supplierForest_actual_002102
  · exact g32p_supplierForest_actual_002140
  · exact g32p_supplierForest_actual_002169
  · exact g32p_supplierForest_actual_002225
  · exact g32p_supplierForest_actual_002254
  · exact g32p_supplierForest_actual_002297
  · exact g32p_supplierForest_actual_002302
  · exact g32p_supplierForest_actual_002366
  · exact g32p_supplierForest_actual_002376
  · exact g32p_supplierForest_actual_002395
  · exact g32p_supplierForest_actual_002479
  · exact g32p_supplierForest_actual_002588
  · exact g32p_supplierForest_actual_002621
  · exact g32p_supplierForest_actual_002648
  · exact g32p_supplierForest_actual_002661
  · exact g32p_supplierForest_actual_002689
  · exact g32p_supplierForest_actual_002693
  · exact g32p_supplierForest_actual_002727
  · exact g32p_supplierForest_actual_002800
  · exact g32p_supplierForest_actual_002866
  · exact g32p_supplierForest_actual_002887
  · exact g32p_supplierForest_actual_002977
  · exact g32p_supplierForest_actual_002983
  · exact g32p_supplierForest_actual_002986
  · exact g32p_supplierForest_actual_003002
  · exact g32p_supplierForest_actual_003033
  · exact g32p_supplierForest_actual_003039
  · exact g32p_supplierForest_actual_003040
  · exact g32p_supplierForest_actual_003050
  · exact g32p_supplierForest_actual_003082
  · exact g32p_supplierForest_actual_003098
  · exact g32p_supplierForest_actual_003108
  · exact g32p_supplierForest_actual_003126

def g32p_supplierForest_nodes_057 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_003168 else g32p_supplierForest_node_003172) else (if i.val < 3 then g32p_supplierForest_node_003176 else g32p_supplierForest_node_003228)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_003250 else g32p_supplierForest_node_003285) else (if i.val < 7 then g32p_supplierForest_node_003286 else g32p_supplierForest_node_003307))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_003308 else g32p_supplierForest_node_003318) else (if i.val < 11 then g32p_supplierForest_node_003325 else g32p_supplierForest_node_003327)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_003333 else g32p_supplierForest_node_003357) else (if i.val < 15 then g32p_supplierForest_node_003383 else g32p_supplierForest_node_003420)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_003421 else g32p_supplierForest_node_003422) else (if i.val < 19 then g32p_supplierForest_node_003604 else g32p_supplierForest_node_003607)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_003658 else g32p_supplierForest_node_003666) else (if i.val < 23 then g32p_supplierForest_node_003685 else g32p_supplierForest_node_003713))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_003718 else g32p_supplierForest_node_003721) else (if i.val < 27 then g32p_supplierForest_node_003741 else g32p_supplierForest_node_003756)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_003841 else g32p_supplierForest_node_003875) else (if i.val < 31 then g32p_supplierForest_node_003886 else g32p_supplierForest_node_003912))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_003974 else g32p_supplierForest_node_003985) else (if i.val < 35 then g32p_supplierForest_node_004026 else g32p_supplierForest_node_004057)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_004064 else g32p_supplierForest_node_004069) else (if i.val < 39 then g32p_supplierForest_node_004077 else g32p_supplierForest_node_004096))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_004142 else g32p_supplierForest_node_004177) else (if i.val < 43 then g32p_supplierForest_node_004194 else g32p_supplierForest_node_004227)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_004299 else g32p_supplierForest_node_004304) else (if i.val < 47 then g32p_supplierForest_node_004354 else g32p_supplierForest_node_004361)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_004378 else g32p_supplierForest_node_004383) else (if i.val < 51 then g32p_supplierForest_node_004408 else g32p_supplierForest_node_004456)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_004466 else g32p_supplierForest_node_004483) else (if i.val < 55 then g32p_supplierForest_node_004497 else g32p_supplierForest_node_004511))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_004540 else g32p_supplierForest_node_004542) else (if i.val < 59 then g32p_supplierForest_node_004548 else g32p_supplierForest_node_004640)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_004668 else g32p_supplierForest_node_004670) else (if i.val < 63 then g32p_supplierForest_node_004782 else g32p_supplierForest_node_004809)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_004819 else g32p_supplierForest_node_004932) else (if i.val < 67 then g32p_supplierForest_node_004961 else g32p_supplierForest_node_005135)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_005179 else g32p_supplierForest_node_005230) else (if i.val < 71 then g32p_supplierForest_node_005290 else g32p_supplierForest_node_005384))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_005423 else g32p_supplierForest_node_005425) else (if i.val < 75 then g32p_supplierForest_node_005435 else g32p_supplierForest_node_005458)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_005496 else g32p_supplierForest_node_005558) else (if i.val < 79 then g32p_supplierForest_node_005560 else g32p_supplierForest_node_005666)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_005714 else g32p_supplierForest_node_005737) else (if i.val < 83 then g32p_supplierForest_node_005847 else g32p_supplierForest_node_005889)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_005895 else g32p_supplierForest_node_005934) else (if i.val < 87 then g32p_supplierForest_node_005939 else g32p_supplierForest_node_005943))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_005983 else g32p_supplierForest_node_005985) else (if i.val < 91 then g32p_supplierForest_node_005987 else g32p_supplierForest_node_005988)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_005998 else g32p_supplierForest_node_006001) else (if i.val < 95 then g32p_supplierForest_node_006053 else g32p_supplierForest_node_006211))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_006268 else g32p_supplierForest_node_006303) else (if i.val < 99 then g32p_supplierForest_node_006350 else g32p_supplierForest_node_006382)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_006384 else g32p_supplierForest_node_006385) else (if i.val < 103 then g32p_supplierForest_node_006390 else g32p_supplierForest_node_006409))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_006434 else g32p_supplierForest_node_006437) else (if i.val < 107 then g32p_supplierForest_node_006448 else g32p_supplierForest_node_006456)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_006495 else g32p_supplierForest_node_006497) else (if i.val < 111 then g32p_supplierForest_node_006521 else g32p_supplierForest_node_006532)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_006549 else g32p_supplierForest_node_006622) else (if i.val < 115 then g32p_supplierForest_node_006679 else g32p_supplierForest_node_006707)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_006738 else g32p_supplierForest_node_006755) else (if i.val < 119 then g32p_supplierForest_node_006803 else g32p_supplierForest_node_006839))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_006860 else g32p_supplierForest_node_006877) else (if i.val < 123 then g32p_supplierForest_node_006965 else g32p_supplierForest_node_007001)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_007044 else g32p_supplierForest_node_007046) else (if i.val < 127 then g32p_supplierForest_node_007083 else g32p_supplierForest_node_007136))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_007145 else g32p_supplierForest_node_007176) else (if i.val < 131 then g32p_supplierForest_node_007190 else g32p_supplierForest_node_007199)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_007247 else g32p_supplierForest_node_007253) else (if i.val < 135 then g32p_supplierForest_node_007285 else g32p_supplierForest_node_007304))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_007348 else g32p_supplierForest_node_007382) else (if i.val < 139 then g32p_supplierForest_node_007393 else g32p_supplierForest_node_007402)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_007410 else g32p_supplierForest_node_007444) else (if i.val < 143 then g32p_supplierForest_node_007454 else g32p_supplierForest_node_007458)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_007461 else g32p_supplierForest_node_007484) else (if i.val < 147 then g32p_supplierForest_node_007546 else g32p_supplierForest_node_007590)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_007745 else g32p_supplierForest_node_007752) else (if i.val < 151 then g32p_supplierForest_node_007786 else g32p_supplierForest_node_007940))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_007950 else g32p_supplierForest_node_007956) else (if i.val < 155 then g32p_supplierForest_node_007993 else g32p_supplierForest_node_007997)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_008013 else g32p_supplierForest_node_008060) else (if i.val < 159 then g32p_supplierForest_node_008124 else g32p_supplierForest_node_008143))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_008203 else g32p_supplierForest_node_008223) else (if i.val < 163 then g32p_supplierForest_node_008233 else g32p_supplierForest_node_008235)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_008236 else g32p_supplierForest_node_008276) else (if i.val < 167 then g32p_supplierForest_node_008304 else g32p_supplierForest_node_008333))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_008356 else g32p_supplierForest_node_008394) else (if i.val < 171 then g32p_supplierForest_node_008400 else g32p_supplierForest_node_008476)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_008494 else g32p_supplierForest_node_008497) else (if i.val < 175 then g32p_supplierForest_node_008551 else g32p_supplierForest_node_008570)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_008601 else g32p_supplierForest_node_008603) else (if i.val < 179 then g32p_supplierForest_node_008612 else g32p_supplierForest_node_008614)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_008640 else g32p_supplierForest_node_008654) else (if i.val < 183 then g32p_supplierForest_node_008659 else g32p_supplierForest_node_008662))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_008671 else g32p_supplierForest_node_008723) else (if i.val < 187 then g32p_supplierForest_node_008732 else g32p_supplierForest_node_008754)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_008798 else g32p_supplierForest_node_008800) else (if i.val < 191 then g32p_supplierForest_node_008803 else g32p_supplierForest_node_008907)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_008920 else g32p_supplierForest_node_008930) else (if i.val < 195 then g32p_supplierForest_node_008952 else g32p_supplierForest_node_008960)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_008969 else g32p_supplierForest_node_008986) else (if i.val < 199 then g32p_supplierForest_node_009011 else g32p_supplierForest_node_009017))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_009044 else g32p_supplierForest_node_009065) else (if i.val < 203 then g32p_supplierForest_node_009080 else g32p_supplierForest_node_009094)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_009100 else g32p_supplierForest_node_009131) else (if i.val < 207 then g32p_supplierForest_node_009159 else g32p_supplierForest_node_009174)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_009181 else g32p_supplierForest_node_009228) else (if i.val < 211 then g32p_supplierForest_node_009239 else g32p_supplierForest_node_009257)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_009284 else g32p_supplierForest_node_009317) else (if i.val < 215 then g32p_supplierForest_node_009367 else g32p_supplierForest_node_009373))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_009375 else g32p_supplierForest_node_009472) else (if i.val < 219 then g32p_supplierForest_node_009485 else g32p_supplierForest_node_009499)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_009538 else g32p_supplierForest_node_009539) else (if i.val < 223 then g32p_supplierForest_node_009545 else g32p_supplierForest_node_009568))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_009570 else g32p_supplierForest_node_009584) else (if i.val < 227 then g32p_supplierForest_node_009644 else g32p_supplierForest_node_009655)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_009656 else g32p_supplierForest_node_009684) else (if i.val < 231 then g32p_supplierForest_node_009715 else g32p_supplierForest_node_009754))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_009782 else g32p_supplierForest_node_009806) else (if i.val < 235 then g32p_supplierForest_node_009833 else g32p_supplierForest_node_009851)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_009875 else g32p_supplierForest_node_009877) else (if i.val < 239 then g32p_supplierForest_node_009915 else g32p_supplierForest_node_009927)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_009934 else g32p_supplierForest_node_009971) else (if i.val < 243 then g32p_supplierForest_node_009998 else g32p_supplierForest_node_010010)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_010015 else g32p_supplierForest_node_010048) else (if i.val < 247 then g32p_supplierForest_node_010051 else g32p_supplierForest_node_010056))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_010058 else g32p_supplierForest_node_010096) else (if i.val < 251 then g32p_supplierForest_node_010107 else g32p_supplierForest_node_010193)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_010241 else g32p_supplierForest_node_010270) else (if i.val < 255 then g32p_supplierForest_node_010372 else g32p_supplierForest_node_010383))))))))

def g32p_supplierForest_classes_057 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 17) else (if i.val < 3 then 30 else 3)) else (if i.val < 6 then (if i.val < 5 then 32 else 30) else (if i.val < 7 then 33 else 17))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 3 else 31) else (if i.val < 11 then 31 else 3)) else (if i.val < 14 then (if i.val < 13 then 17 else 4) else (if i.val < 15 then 17 else 16)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 30 else 16) else (if i.val < 19 then 16 else 31)) else (if i.val < 22 then (if i.val < 21 then 15 else 30) else (if i.val < 23 then 4 else 17))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 16 else 4) else (if i.val < 27 then 31 else 31)) else (if i.val < 30 then (if i.val < 29 then 17 else 4) else (if i.val < 31 then 17 else 16))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 17 else 31) else (if i.val < 35 then 3 else 31)) else (if i.val < 38 then (if i.val < 37 then 34 else 3) else (if i.val < 39 then 3 else 17))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 17 else 17) else (if i.val < 43 then 30 else 17)) else (if i.val < 46 then (if i.val < 45 then 14 else 4) else (if i.val < 47 then 16 else 14)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 16 else 14) else (if i.val < 51 then 30 else 31)) else (if i.val < 54 then (if i.val < 53 then 4 else 3) else (if i.val < 55 then 30 else 32))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 4 else 30) else (if i.val < 59 then 16 else 30)) else (if i.val < 62 then (if i.val < 61 then 14 else 4) else (if i.val < 63 then 32 else 14)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 15 else 15) else (if i.val < 67 then 15 else 15)) else (if i.val < 70 then (if i.val < 69 then 15 else 15) else (if i.val < 71 then 4 else 30))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 14 else 14) else (if i.val < 75 then 30 else 33)) else (if i.val < 78 then (if i.val < 77 then 17 else 14) else (if i.val < 79 then 34 else 16)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 17 else 30) else (if i.val < 83 then 22 else 40)) else (if i.val < 86 then (if i.val < 85 then 22 else 23) else (if i.val < 87 then 6 else 22))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 22 else 21) else (if i.val < 91 then 5 else 5)) else (if i.val < 94 then (if i.val < 93 then 5 else 21) else (if i.val < 95 then 40 else 5))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 21 else 24) else (if i.val < 99 then 7 else 22)) else (if i.val < 102 then (if i.val < 101 then 38 else 7) else (if i.val < 103 then 5 else 5))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 21 else 5) else (if i.val < 107 then 22 else 40)) else (if i.val < 110 then (if i.val < 109 then 23 else 5) else (if i.val < 111 then 22 else 22)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 19 else 20) else (if i.val < 115 then 20 else 24)) else (if i.val < 118 then (if i.val < 117 then 7 else 21) else (if i.val < 119 then 6 else 38))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 6 else 40) else (if i.val < 123 then 24 else 20)) else (if i.val < 126 then (if i.val < 125 then 6 else 21) else (if i.val < 127 then 39 else 5))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 21 else 38) else (if i.val < 131 then 38 else 6)) else (if i.val < 134 then (if i.val < 133 then 6 else 22) else (if i.val < 135 then 5 else 19))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 7 else 38) else (if i.val < 139 then 22 else 38)) else (if i.val < 142 then (if i.val < 141 then 22 else 19) else (if i.val < 143 then 40 else 21)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 22 else 22) else (if i.val < 147 then 22 else 40)) else (if i.val < 150 then (if i.val < 149 then 5 else 22) else (if i.val < 151 then 21 else 21))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 22 else 24) else (if i.val < 155 then 19 else 7)) else (if i.val < 158 then (if i.val < 157 then 38 else 5) else (if i.val < 159 then 40 else 19))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 21 else 23) else (if i.val < 163 then 5 else 38)) else (if i.val < 166 then (if i.val < 165 then 24 else 21) else (if i.val < 167 then 22 else 24))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 6 else 40) else (if i.val < 171 then 38 else 7)) else (if i.val < 174 then (if i.val < 173 then 23 else 6) else (if i.val < 175 then 22 else 22)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 21 else 21) else (if i.val < 179 then 21 else 20)) else (if i.val < 182 then (if i.val < 181 then 38 else 39) else (if i.val < 183 then 21 else 6))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 22 else 22) else (if i.val < 187 then 22 else 5)) else (if i.val < 190 then (if i.val < 189 then 40 else 22) else (if i.val < 191 then 24 else 39)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 22 else 40) else (if i.val < 195 then 24 else 39)) else (if i.val < 198 then (if i.val < 197 then 23 else 38) else (if i.val < 199 then 40 else 7))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 6 else 22) else (if i.val < 203 then 19 else 39)) else (if i.val < 206 then (if i.val < 205 then 40 else 22) else (if i.val < 207 then 5 else 40)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 40 else 21) else (if i.val < 211 then 5 else 5)) else (if i.val < 214 then (if i.val < 213 then 39 else 38) else (if i.val < 215 then 22 else 7))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 19 else 38) else (if i.val < 219 then 21 else 38)) else (if i.val < 222 then (if i.val < 221 then 21 else 6) else (if i.val < 223 then 20 else 38))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 5 else 5) else (if i.val < 227 then 5 else 6)) else (if i.val < 230 then (if i.val < 229 then 21 else 22) else (if i.val < 231 then 7 else 6))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 19 else 22) else (if i.val < 235 then 40 else 6)) else (if i.val < 238 then (if i.val < 237 then 38 else 22) else (if i.val < 239 then 40 else 6)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 41 else 19) else (if i.val < 243 then 39 else 6)) else (if i.val < 246 then (if i.val < 245 then 5 else 6) else (if i.val < 247 then 20 else 22))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 22 else 22) else (if i.val < 251 then 7 else 7)) else (if i.val < 254 then (if i.val < 253 then 6 else 6) else (if i.val < 255 then 22 else 39))))))))

theorem g32p_supplierForest_actual_057 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_057 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_057 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_003168
  · exact g32p_supplierForest_actual_003172
  · exact g32p_supplierForest_actual_003176
  · exact g32p_supplierForest_actual_003228
  · exact g32p_supplierForest_actual_003250
  · exact g32p_supplierForest_actual_003285
  · exact g32p_supplierForest_actual_003286
  · exact g32p_supplierForest_actual_003307
  · exact g32p_supplierForest_actual_003308
  · exact g32p_supplierForest_actual_003318
  · exact g32p_supplierForest_actual_003325
  · exact g32p_supplierForest_actual_003327
  · exact g32p_supplierForest_actual_003333
  · exact g32p_supplierForest_actual_003357
  · exact g32p_supplierForest_actual_003383
  · exact g32p_supplierForest_actual_003420
  · exact g32p_supplierForest_actual_003421
  · exact g32p_supplierForest_actual_003422
  · exact g32p_supplierForest_actual_003604
  · exact g32p_supplierForest_actual_003607
  · exact g32p_supplierForest_actual_003658
  · exact g32p_supplierForest_actual_003666
  · exact g32p_supplierForest_actual_003685
  · exact g32p_supplierForest_actual_003713
  · exact g32p_supplierForest_actual_003718
  · exact g32p_supplierForest_actual_003721
  · exact g32p_supplierForest_actual_003741
  · exact g32p_supplierForest_actual_003756
  · exact g32p_supplierForest_actual_003841
  · exact g32p_supplierForest_actual_003875
  · exact g32p_supplierForest_actual_003886
  · exact g32p_supplierForest_actual_003912
  · exact g32p_supplierForest_actual_003974
  · exact g32p_supplierForest_actual_003985
  · exact g32p_supplierForest_actual_004026
  · exact g32p_supplierForest_actual_004057
  · exact g32p_supplierForest_actual_004064
  · exact g32p_supplierForest_actual_004069
  · exact g32p_supplierForest_actual_004077
  · exact g32p_supplierForest_actual_004096
  · exact g32p_supplierForest_actual_004142
  · exact g32p_supplierForest_actual_004177
  · exact g32p_supplierForest_actual_004194
  · exact g32p_supplierForest_actual_004227
  · exact g32p_supplierForest_actual_004299
  · exact g32p_supplierForest_actual_004304
  · exact g32p_supplierForest_actual_004354
  · exact g32p_supplierForest_actual_004361
  · exact g32p_supplierForest_actual_004378
  · exact g32p_supplierForest_actual_004383
  · exact g32p_supplierForest_actual_004408
  · exact g32p_supplierForest_actual_004456
  · exact g32p_supplierForest_actual_004466
  · exact g32p_supplierForest_actual_004483
  · exact g32p_supplierForest_actual_004497
  · exact g32p_supplierForest_actual_004511
  · exact g32p_supplierForest_actual_004540
  · exact g32p_supplierForest_actual_004542
  · exact g32p_supplierForest_actual_004548
  · exact g32p_supplierForest_actual_004640
  · exact g32p_supplierForest_actual_004668
  · exact g32p_supplierForest_actual_004670
  · exact g32p_supplierForest_actual_004782
  · exact g32p_supplierForest_actual_004809
  · exact g32p_supplierForest_actual_004819
  · exact g32p_supplierForest_actual_004932
  · exact g32p_supplierForest_actual_004961
  · exact g32p_supplierForest_actual_005135
  · exact g32p_supplierForest_actual_005179
  · exact g32p_supplierForest_actual_005230
  · exact g32p_supplierForest_actual_005290
  · exact g32p_supplierForest_actual_005384
  · exact g32p_supplierForest_actual_005423
  · exact g32p_supplierForest_actual_005425
  · exact g32p_supplierForest_actual_005435
  · exact g32p_supplierForest_actual_005458
  · exact g32p_supplierForest_actual_005496
  · exact g32p_supplierForest_actual_005558
  · exact g32p_supplierForest_actual_005560
  · exact g32p_supplierForest_actual_005666
  · exact g32p_supplierForest_actual_005714
  · exact g32p_supplierForest_actual_005737
  · exact g32p_supplierForest_actual_005847
  · exact g32p_supplierForest_actual_005889
  · exact g32p_supplierForest_actual_005895
  · exact g32p_supplierForest_actual_005934
  · exact g32p_supplierForest_actual_005939
  · exact g32p_supplierForest_actual_005943
  · exact g32p_supplierForest_actual_005983
  · exact g32p_supplierForest_actual_005985
  · exact g32p_supplierForest_actual_005987
  · exact g32p_supplierForest_actual_005988
  · exact g32p_supplierForest_actual_005998
  · exact g32p_supplierForest_actual_006001
  · exact g32p_supplierForest_actual_006053
  · exact g32p_supplierForest_actual_006211
  · exact g32p_supplierForest_actual_006268
  · exact g32p_supplierForest_actual_006303
  · exact g32p_supplierForest_actual_006350
  · exact g32p_supplierForest_actual_006382
  · exact g32p_supplierForest_actual_006384
  · exact g32p_supplierForest_actual_006385
  · exact g32p_supplierForest_actual_006390
  · exact g32p_supplierForest_actual_006409
  · exact g32p_supplierForest_actual_006434
  · exact g32p_supplierForest_actual_006437
  · exact g32p_supplierForest_actual_006448
  · exact g32p_supplierForest_actual_006456
  · exact g32p_supplierForest_actual_006495
  · exact g32p_supplierForest_actual_006497
  · exact g32p_supplierForest_actual_006521
  · exact g32p_supplierForest_actual_006532
  · exact g32p_supplierForest_actual_006549
  · exact g32p_supplierForest_actual_006622
  · exact g32p_supplierForest_actual_006679
  · exact g32p_supplierForest_actual_006707
  · exact g32p_supplierForest_actual_006738
  · exact g32p_supplierForest_actual_006755
  · exact g32p_supplierForest_actual_006803
  · exact g32p_supplierForest_actual_006839
  · exact g32p_supplierForest_actual_006860
  · exact g32p_supplierForest_actual_006877
  · exact g32p_supplierForest_actual_006965
  · exact g32p_supplierForest_actual_007001
  · exact g32p_supplierForest_actual_007044
  · exact g32p_supplierForest_actual_007046
  · exact g32p_supplierForest_actual_007083
  · exact g32p_supplierForest_actual_007136
  · exact g32p_supplierForest_actual_007145
  · exact g32p_supplierForest_actual_007176
  · exact g32p_supplierForest_actual_007190
  · exact g32p_supplierForest_actual_007199
  · exact g32p_supplierForest_actual_007247
  · exact g32p_supplierForest_actual_007253
  · exact g32p_supplierForest_actual_007285
  · exact g32p_supplierForest_actual_007304
  · exact g32p_supplierForest_actual_007348
  · exact g32p_supplierForest_actual_007382
  · exact g32p_supplierForest_actual_007393
  · exact g32p_supplierForest_actual_007402
  · exact g32p_supplierForest_actual_007410
  · exact g32p_supplierForest_actual_007444
  · exact g32p_supplierForest_actual_007454
  · exact g32p_supplierForest_actual_007458
  · exact g32p_supplierForest_actual_007461
  · exact g32p_supplierForest_actual_007484
  · exact g32p_supplierForest_actual_007546
  · exact g32p_supplierForest_actual_007590
  · exact g32p_supplierForest_actual_007745
  · exact g32p_supplierForest_actual_007752
  · exact g32p_supplierForest_actual_007786
  · exact g32p_supplierForest_actual_007940
  · exact g32p_supplierForest_actual_007950
  · exact g32p_supplierForest_actual_007956
  · exact g32p_supplierForest_actual_007993
  · exact g32p_supplierForest_actual_007997
  · exact g32p_supplierForest_actual_008013
  · exact g32p_supplierForest_actual_008060
  · exact g32p_supplierForest_actual_008124
  · exact g32p_supplierForest_actual_008143
  · exact g32p_supplierForest_actual_008203
  · exact g32p_supplierForest_actual_008223
  · exact g32p_supplierForest_actual_008233
  · exact g32p_supplierForest_actual_008235
  · exact g32p_supplierForest_actual_008236
  · exact g32p_supplierForest_actual_008276
  · exact g32p_supplierForest_actual_008304
  · exact g32p_supplierForest_actual_008333
  · exact g32p_supplierForest_actual_008356
  · exact g32p_supplierForest_actual_008394
  · exact g32p_supplierForest_actual_008400
  · exact g32p_supplierForest_actual_008476
  · exact g32p_supplierForest_actual_008494
  · exact g32p_supplierForest_actual_008497
  · exact g32p_supplierForest_actual_008551
  · exact g32p_supplierForest_actual_008570
  · exact g32p_supplierForest_actual_008601
  · exact g32p_supplierForest_actual_008603
  · exact g32p_supplierForest_actual_008612
  · exact g32p_supplierForest_actual_008614
  · exact g32p_supplierForest_actual_008640
  · exact g32p_supplierForest_actual_008654
  · exact g32p_supplierForest_actual_008659
  · exact g32p_supplierForest_actual_008662
  · exact g32p_supplierForest_actual_008671
  · exact g32p_supplierForest_actual_008723
  · exact g32p_supplierForest_actual_008732
  · exact g32p_supplierForest_actual_008754
  · exact g32p_supplierForest_actual_008798
  · exact g32p_supplierForest_actual_008800
  · exact g32p_supplierForest_actual_008803
  · exact g32p_supplierForest_actual_008907
  · exact g32p_supplierForest_actual_008920
  · exact g32p_supplierForest_actual_008930
  · exact g32p_supplierForest_actual_008952
  · exact g32p_supplierForest_actual_008960
  · exact g32p_supplierForest_actual_008969
  · exact g32p_supplierForest_actual_008986
  · exact g32p_supplierForest_actual_009011
  · exact g32p_supplierForest_actual_009017
  · exact g32p_supplierForest_actual_009044
  · exact g32p_supplierForest_actual_009065
  · exact g32p_supplierForest_actual_009080
  · exact g32p_supplierForest_actual_009094
  · exact g32p_supplierForest_actual_009100
  · exact g32p_supplierForest_actual_009131
  · exact g32p_supplierForest_actual_009159
  · exact g32p_supplierForest_actual_009174
  · exact g32p_supplierForest_actual_009181
  · exact g32p_supplierForest_actual_009228
  · exact g32p_supplierForest_actual_009239
  · exact g32p_supplierForest_actual_009257
  · exact g32p_supplierForest_actual_009284
  · exact g32p_supplierForest_actual_009317
  · exact g32p_supplierForest_actual_009367
  · exact g32p_supplierForest_actual_009373
  · exact g32p_supplierForest_actual_009375
  · exact g32p_supplierForest_actual_009472
  · exact g32p_supplierForest_actual_009485
  · exact g32p_supplierForest_actual_009499
  · exact g32p_supplierForest_actual_009538
  · exact g32p_supplierForest_actual_009539
  · exact g32p_supplierForest_actual_009545
  · exact g32p_supplierForest_actual_009568
  · exact g32p_supplierForest_actual_009570
  · exact g32p_supplierForest_actual_009584
  · exact g32p_supplierForest_actual_009644
  · exact g32p_supplierForest_actual_009655
  · exact g32p_supplierForest_actual_009656
  · exact g32p_supplierForest_actual_009684
  · exact g32p_supplierForest_actual_009715
  · exact g32p_supplierForest_actual_009754
  · exact g32p_supplierForest_actual_009782
  · exact g32p_supplierForest_actual_009806
  · exact g32p_supplierForest_actual_009833
  · exact g32p_supplierForest_actual_009851
  · exact g32p_supplierForest_actual_009875
  · exact g32p_supplierForest_actual_009877
  · exact g32p_supplierForest_actual_009915
  · exact g32p_supplierForest_actual_009927
  · exact g32p_supplierForest_actual_009934
  · exact g32p_supplierForest_actual_009971
  · exact g32p_supplierForest_actual_009998
  · exact g32p_supplierForest_actual_010010
  · exact g32p_supplierForest_actual_010015
  · exact g32p_supplierForest_actual_010048
  · exact g32p_supplierForest_actual_010051
  · exact g32p_supplierForest_actual_010056
  · exact g32p_supplierForest_actual_010058
  · exact g32p_supplierForest_actual_010096
  · exact g32p_supplierForest_actual_010107
  · exact g32p_supplierForest_actual_010193
  · exact g32p_supplierForest_actual_010241
  · exact g32p_supplierForest_actual_010270
  · exact g32p_supplierForest_actual_010372
  · exact g32p_supplierForest_actual_010383

def g32p_supplierForest_nodes_058 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_010443 else g32p_supplierForest_node_010454) else (if i.val < 3 then g32p_supplierForest_node_010475 else g32p_supplierForest_node_010482)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_010565 else g32p_supplierForest_node_010581) else (if i.val < 7 then g32p_supplierForest_node_010612 else g32p_supplierForest_node_010614))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_010620 else g32p_supplierForest_node_010640) else (if i.val < 11 then g32p_supplierForest_node_010670 else g32p_supplierForest_node_010695)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_010718 else g32p_supplierForest_node_010741) else (if i.val < 15 then g32p_supplierForest_node_010744 else g32p_supplierForest_node_010798)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_010842 else g32p_supplierForest_node_010848) else (if i.val < 19 then g32p_supplierForest_node_010859 else g32p_supplierForest_node_010970)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_010998 else g32p_supplierForest_node_011005) else (if i.val < 23 then g32p_supplierForest_node_011009 else g32p_supplierForest_node_011018))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_011068 else g32p_supplierForest_node_011095) else (if i.val < 27 then g32p_supplierForest_node_011158 else g32p_supplierForest_node_011162)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_011167 else g32p_supplierForest_node_011226) else (if i.val < 31 then g32p_supplierForest_node_011227 else g32p_supplierForest_node_011283))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_011289 else g32p_supplierForest_node_011304) else (if i.val < 35 then g32p_supplierForest_node_011308 else g32p_supplierForest_node_011369)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_011371 else g32p_supplierForest_node_011407) else (if i.val < 39 then g32p_supplierForest_node_011427 else g32p_supplierForest_node_011441))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_011481 else g32p_supplierForest_node_011503) else (if i.val < 43 then g32p_supplierForest_node_011534 else g32p_supplierForest_node_011535)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_011536 else g32p_supplierForest_node_011602) else (if i.val < 47 then g32p_supplierForest_node_011610 else g32p_supplierForest_node_011620)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_011630 else g32p_supplierForest_node_011666) else (if i.val < 51 then g32p_supplierForest_node_011670 else g32p_supplierForest_node_011787)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_011832 else g32p_supplierForest_node_011848) else (if i.val < 55 then g32p_supplierForest_node_011856 else g32p_supplierForest_node_011890))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_011912 else g32p_supplierForest_node_011918) else (if i.val < 59 then g32p_supplierForest_node_011963 else g32p_supplierForest_node_011970)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_011991 else g32p_supplierForest_node_012081) else (if i.val < 63 then g32p_supplierForest_node_012096 else g32p_supplierForest_node_012143)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_012147 else g32p_supplierForest_node_012187) else (if i.val < 67 then g32p_supplierForest_node_012197 else g32p_supplierForest_node_012256)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_012308 else g32p_supplierForest_node_012325) else (if i.val < 71 then g32p_supplierForest_node_012329 else g32p_supplierForest_node_012350))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_012386 else g32p_supplierForest_node_012395) else (if i.val < 75 then g32p_supplierForest_node_012510 else g32p_supplierForest_node_012581)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_012601 else g32p_supplierForest_node_012684) else (if i.val < 79 then g32p_supplierForest_node_012696 else g32p_supplierForest_node_012706)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_012735 else g32p_supplierForest_node_012762) else (if i.val < 83 then g32p_supplierForest_node_012804 else g32p_supplierForest_node_012815)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_012839 else g32p_supplierForest_node_012841) else (if i.val < 87 then g32p_supplierForest_node_012859 else g32p_supplierForest_node_012895))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_012902 else g32p_supplierForest_node_012914) else (if i.val < 91 then g32p_supplierForest_node_012984 else g32p_supplierForest_node_013067)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_013072 else g32p_supplierForest_node_013078) else (if i.val < 95 then g32p_supplierForest_node_013085 else g32p_supplierForest_node_013120))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_013126 else g32p_supplierForest_node_013162) else (if i.val < 99 then g32p_supplierForest_node_013193 else g32p_supplierForest_node_013229)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_013238 else g32p_supplierForest_node_013244) else (if i.val < 103 then g32p_supplierForest_node_013261 else g32p_supplierForest_node_013268))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_013315 else g32p_supplierForest_node_013323) else (if i.val < 107 then g32p_supplierForest_node_013343 else g32p_supplierForest_node_013396)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_013406 else g32p_supplierForest_node_013416) else (if i.val < 111 then g32p_supplierForest_node_013422 else g32p_supplierForest_node_013459)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_013473 else g32p_supplierForest_node_013508) else (if i.val < 115 then g32p_supplierForest_node_013539 else g32p_supplierForest_node_013545)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_013566 else g32p_supplierForest_node_013578) else (if i.val < 119 then g32p_supplierForest_node_013722 else g32p_supplierForest_node_013729))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_013762 else g32p_supplierForest_node_013806) else (if i.val < 123 then g32p_supplierForest_node_013813 else g32p_supplierForest_node_013859)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_013871 else g32p_supplierForest_node_013881) else (if i.val < 127 then g32p_supplierForest_node_013883 else g32p_supplierForest_node_013893))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_013898 else g32p_supplierForest_node_013955) else (if i.val < 131 then g32p_supplierForest_node_013967 else g32p_supplierForest_node_013993)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_014007 else g32p_supplierForest_node_014040) else (if i.val < 135 then g32p_supplierForest_node_014091 else g32p_supplierForest_node_014131))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_014134 else g32p_supplierForest_node_014146) else (if i.val < 139 then g32p_supplierForest_node_014176 else g32p_supplierForest_node_014232)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_014274 else g32p_supplierForest_node_014290) else (if i.val < 143 then g32p_supplierForest_node_014313 else g32p_supplierForest_node_014316)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_014349 else g32p_supplierForest_node_014511) else (if i.val < 147 then g32p_supplierForest_node_014537 else g32p_supplierForest_node_014544)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_014553 else g32p_supplierForest_node_014554) else (if i.val < 151 then g32p_supplierForest_node_014559 else g32p_supplierForest_node_014573))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_014577 else g32p_supplierForest_node_014582) else (if i.val < 155 then g32p_supplierForest_node_014584 else g32p_supplierForest_node_014590)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_014593 else g32p_supplierForest_node_014613) else (if i.val < 159 then g32p_supplierForest_node_014620 else g32p_supplierForest_node_014658))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_014699 else g32p_supplierForest_node_014701) else (if i.val < 163 then g32p_supplierForest_node_014743 else g32p_supplierForest_node_014753)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_014823 else g32p_supplierForest_node_014833) else (if i.val < 167 then g32p_supplierForest_node_014844 else g32p_supplierForest_node_014848))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_014862 else g32p_supplierForest_node_014878) else (if i.val < 171 then g32p_supplierForest_node_014880 else g32p_supplierForest_node_014940)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_014963 else g32p_supplierForest_node_014965) else (if i.val < 175 then g32p_supplierForest_node_014968 else g32p_supplierForest_node_015012)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_015017 else g32p_supplierForest_node_015021) else (if i.val < 179 then g32p_supplierForest_node_015084 else g32p_supplierForest_node_015092)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_015103 else g32p_supplierForest_node_015224) else (if i.val < 183 then g32p_supplierForest_node_015286 else g32p_supplierForest_node_015289))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_015312 else g32p_supplierForest_node_015331) else (if i.val < 187 then g32p_supplierForest_node_015342 else g32p_supplierForest_node_015348)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_015380 else g32p_supplierForest_node_015382) else (if i.val < 191 then g32p_supplierForest_node_015423 else g32p_supplierForest_node_015464)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_015484 else g32p_supplierForest_node_015488) else (if i.val < 195 then g32p_supplierForest_node_015491 else g32p_supplierForest_node_015518)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_015520 else g32p_supplierForest_node_015588) else (if i.val < 199 then g32p_supplierForest_node_015590 else g32p_supplierForest_node_015592))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_015607 else g32p_supplierForest_node_015615) else (if i.val < 203 then g32p_supplierForest_node_015647 else g32p_supplierForest_node_015668)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_015670 else g32p_supplierForest_node_015673) else (if i.val < 207 then g32p_supplierForest_node_015684 else g32p_supplierForest_node_015696)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_015706 else g32p_supplierForest_node_015714) else (if i.val < 211 then g32p_supplierForest_node_015717 else g32p_supplierForest_node_015730)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_015779 else g32p_supplierForest_node_015786) else (if i.val < 215 then g32p_supplierForest_node_015853 else g32p_supplierForest_node_015974))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_015979 else g32p_supplierForest_node_015985) else (if i.val < 219 then g32p_supplierForest_node_016078 else g32p_supplierForest_node_016085)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_016117 else g32p_supplierForest_node_016161) else (if i.val < 223 then g32p_supplierForest_node_016214 else g32p_supplierForest_node_016232))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_016235 else g32p_supplierForest_node_016260) else (if i.val < 227 then g32p_supplierForest_node_016270 else g32p_supplierForest_node_016271)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_016321 else g32p_supplierForest_node_016363) else (if i.val < 231 then g32p_supplierForest_node_016370 else g32p_supplierForest_node_016392))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_016409 else g32p_supplierForest_node_016454) else (if i.val < 235 then g32p_supplierForest_node_016455 else g32p_supplierForest_node_016469)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_016487 else g32p_supplierForest_node_016555) else (if i.val < 239 then g32p_supplierForest_node_016583 else g32p_supplierForest_node_016591)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_016655 else g32p_supplierForest_node_016710) else (if i.val < 243 then g32p_supplierForest_node_016737 else g32p_supplierForest_node_016785)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_016801 else g32p_supplierForest_node_016805) else (if i.val < 247 then g32p_supplierForest_node_016806 else g32p_supplierForest_node_016840))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_016865 else g32p_supplierForest_node_016873) else (if i.val < 251 then g32p_supplierForest_node_016877 else g32p_supplierForest_node_016888)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_016955 else g32p_supplierForest_node_016961) else (if i.val < 255 then g32p_supplierForest_node_016964 else g32p_supplierForest_node_017032))))))))

def g32p_supplierForest_classes_058 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 40 else 6) else (if i.val < 3 then 40 else 38)) else (if i.val < 6 then (if i.val < 5 then 19 else 40) else (if i.val < 7 then 22 else 23))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 38 else 39) else (if i.val < 11 then 7 else 40)) else (if i.val < 14 then (if i.val < 13 then 38 else 22) else (if i.val < 15 then 5 else 22)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 5 else 22) else (if i.val < 19 then 22 else 39)) else (if i.val < 22 then (if i.val < 21 then 23 else 21) else (if i.val < 23 then 7 else 38))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 24 else 5) else (if i.val < 27 then 19 else 40)) else (if i.val < 30 then (if i.val < 29 then 21 else 40) else (if i.val < 31 then 21 else 40))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 41 else 38) else (if i.val < 35 then 21 else 7)) else (if i.val < 38 then (if i.val < 37 then 21 else 20) else (if i.val < 39 then 24 else 40))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 38 else 38) else (if i.val < 43 then 40 else 39)) else (if i.val < 46 then (if i.val < 45 then 38 else 38) else (if i.val < 47 then 22 else 20)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 21 else 22) else (if i.val < 51 then 23 else 22)) else (if i.val < 54 then (if i.val < 53 then 38 else 38) else (if i.val < 55 then 38 else 19))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 40) else (if i.val < 59 then 22 else 40)) else (if i.val < 62 then (if i.val < 61 then 22 else 38) else (if i.val < 63 then 6 else 21)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 20 else 5) else (if i.val < 67 then 22 else 22)) else (if i.val < 70 then (if i.val < 69 then 22 else 10) else (if i.val < 71 then 10 else 10))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 47 else 10) else (if i.val < 75 then 26 else 10)) else (if i.val < 78 then (if i.val < 77 then 11 else 27) else (if i.val < 79 then 26 else 11)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 11 else 46) else (if i.val < 83 then 27 else 8)) else (if i.val < 86 then (if i.val < 85 then 9 else 27) else (if i.val < 87 then 49 else 9))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 26 else 49) else (if i.val < 91 then 25 else 12)) else (if i.val < 94 then (if i.val < 93 then 25 else 10) else (if i.val < 95 then 25 else 25))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 50 else 26) else (if i.val < 99 then 50 else 10)) else (if i.val < 102 then (if i.val < 101 then 10 else 48) else (if i.val < 103 then 48 else 9))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 10 else 49) else (if i.val < 107 then 10 else 50)) else (if i.val < 110 then (if i.val < 109 then 27 else 50) else (if i.val < 111 then 48 else 12)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 27 else 10) else (if i.val < 115 then 9 else 49)) else (if i.val < 118 then (if i.val < 117 then 10 else 25) else (if i.val < 119 then 26 else 12))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 27 else 10) else (if i.val < 123 then 13 else 48)) else (if i.val < 126 then (if i.val < 125 then 8 else 9) else (if i.val < 127 then 9 else 25))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 25 else 10) else (if i.val < 131 then 47 else 10)) else (if i.val < 134 then (if i.val < 133 then 46 else 10) else (if i.val < 135 then 13 else 27))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 25 else 9) else (if i.val < 139 then 11 else 27)) else (if i.val < 142 then (if i.val < 141 then 27 else 48) else (if i.val < 143 then 11 else 49)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 50 else 47) else (if i.val < 147 then 10 else 50)) else (if i.val < 150 then (if i.val < 149 then 51 else 56) else (if i.val < 151 then 49 else 48))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 50 else 27) else (if i.val < 155 then 49 else 47)) else (if i.val < 158 then (if i.val < 157 then 46 else 10) else (if i.val < 159 then 25 else 12))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 50 else 10) else (if i.val < 163 then 10 else 51)) else (if i.val < 166 then (if i.val < 165 then 10 else 12) else (if i.val < 167 then 10 else 10))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 9 else 9) else (if i.val < 171 then 11 else 47)) else (if i.val < 174 then (if i.val < 173 then 49 else 50) else (if i.val < 175 then 49 else 9)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 11 else 47) else (if i.val < 179 then 49 else 49)) else (if i.val < 182 then (if i.val < 181 then 12 else 10) else (if i.val < 183 then 26 else 27))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 50 else 46) else (if i.val < 187 then 12 else 27)) else (if i.val < 190 then (if i.val < 189 then 56 else 50) else (if i.val < 191 then 26 else 27)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 10 else 50) else (if i.val < 195 then 12 else 12)) else (if i.val < 198 then (if i.val < 197 then 9 else 49) else (if i.val < 199 then 48 else 13))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 51 else 47) else (if i.val < 203 then 51 else 10)) else (if i.val < 206 then (if i.val < 205 then 46 else 47) else (if i.val < 207 then 9 else 13)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 49 else 13) else (if i.val < 211 then 12 else 49)) else (if i.val < 214 then (if i.val < 213 then 10 else 9) else (if i.val < 215 then 27 else 49))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 12 else 50) else (if i.val < 219 then 12 else 47)) else (if i.val < 222 then (if i.val < 221 then 48 else 25) else (if i.val < 223 then 48 else 12))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 56 else 12) else (if i.val < 227 then 25 else 12)) else (if i.val < 230 then (if i.val < 229 then 12 else 49) else (if i.val < 231 then 10 else 8))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 49 else 49) else (if i.val < 235 then 49 else 13)) else (if i.val < 238 then (if i.val < 237 then 49 else 49) else (if i.val < 239 then 48 else 48)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 49 else 49) else (if i.val < 243 then 49 else 46)) else (if i.val < 246 then (if i.val < 245 then 25 else 47) else (if i.val < 247 then 12 else 49))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 9 else 12) else (if i.val < 251 then 10 else 25)) else (if i.val < 254 then (if i.val < 253 then 25 else 9) else (if i.val < 255 then 8 else 10))))))))

theorem g32p_supplierForest_actual_058 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_058 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_058 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_010443
  · exact g32p_supplierForest_actual_010454
  · exact g32p_supplierForest_actual_010475
  · exact g32p_supplierForest_actual_010482
  · exact g32p_supplierForest_actual_010565
  · exact g32p_supplierForest_actual_010581
  · exact g32p_supplierForest_actual_010612
  · exact g32p_supplierForest_actual_010614
  · exact g32p_supplierForest_actual_010620
  · exact g32p_supplierForest_actual_010640
  · exact g32p_supplierForest_actual_010670
  · exact g32p_supplierForest_actual_010695
  · exact g32p_supplierForest_actual_010718
  · exact g32p_supplierForest_actual_010741
  · exact g32p_supplierForest_actual_010744
  · exact g32p_supplierForest_actual_010798
  · exact g32p_supplierForest_actual_010842
  · exact g32p_supplierForest_actual_010848
  · exact g32p_supplierForest_actual_010859
  · exact g32p_supplierForest_actual_010970
  · exact g32p_supplierForest_actual_010998
  · exact g32p_supplierForest_actual_011005
  · exact g32p_supplierForest_actual_011009
  · exact g32p_supplierForest_actual_011018
  · exact g32p_supplierForest_actual_011068
  · exact g32p_supplierForest_actual_011095
  · exact g32p_supplierForest_actual_011158
  · exact g32p_supplierForest_actual_011162
  · exact g32p_supplierForest_actual_011167
  · exact g32p_supplierForest_actual_011226
  · exact g32p_supplierForest_actual_011227
  · exact g32p_supplierForest_actual_011283
  · exact g32p_supplierForest_actual_011289
  · exact g32p_supplierForest_actual_011304
  · exact g32p_supplierForest_actual_011308
  · exact g32p_supplierForest_actual_011369
  · exact g32p_supplierForest_actual_011371
  · exact g32p_supplierForest_actual_011407
  · exact g32p_supplierForest_actual_011427
  · exact g32p_supplierForest_actual_011441
  · exact g32p_supplierForest_actual_011481
  · exact g32p_supplierForest_actual_011503
  · exact g32p_supplierForest_actual_011534
  · exact g32p_supplierForest_actual_011535
  · exact g32p_supplierForest_actual_011536
  · exact g32p_supplierForest_actual_011602
  · exact g32p_supplierForest_actual_011610
  · exact g32p_supplierForest_actual_011620
  · exact g32p_supplierForest_actual_011630
  · exact g32p_supplierForest_actual_011666
  · exact g32p_supplierForest_actual_011670
  · exact g32p_supplierForest_actual_011787
  · exact g32p_supplierForest_actual_011832
  · exact g32p_supplierForest_actual_011848
  · exact g32p_supplierForest_actual_011856
  · exact g32p_supplierForest_actual_011890
  · exact g32p_supplierForest_actual_011912
  · exact g32p_supplierForest_actual_011918
  · exact g32p_supplierForest_actual_011963
  · exact g32p_supplierForest_actual_011970
  · exact g32p_supplierForest_actual_011991
  · exact g32p_supplierForest_actual_012081
  · exact g32p_supplierForest_actual_012096
  · exact g32p_supplierForest_actual_012143
  · exact g32p_supplierForest_actual_012147
  · exact g32p_supplierForest_actual_012187
  · exact g32p_supplierForest_actual_012197
  · exact g32p_supplierForest_actual_012256
  · exact g32p_supplierForest_actual_012308
  · exact g32p_supplierForest_actual_012325
  · exact g32p_supplierForest_actual_012329
  · exact g32p_supplierForest_actual_012350
  · exact g32p_supplierForest_actual_012386
  · exact g32p_supplierForest_actual_012395
  · exact g32p_supplierForest_actual_012510
  · exact g32p_supplierForest_actual_012581
  · exact g32p_supplierForest_actual_012601
  · exact g32p_supplierForest_actual_012684
  · exact g32p_supplierForest_actual_012696
  · exact g32p_supplierForest_actual_012706
  · exact g32p_supplierForest_actual_012735
  · exact g32p_supplierForest_actual_012762
  · exact g32p_supplierForest_actual_012804
  · exact g32p_supplierForest_actual_012815
  · exact g32p_supplierForest_actual_012839
  · exact g32p_supplierForest_actual_012841
  · exact g32p_supplierForest_actual_012859
  · exact g32p_supplierForest_actual_012895
  · exact g32p_supplierForest_actual_012902
  · exact g32p_supplierForest_actual_012914
  · exact g32p_supplierForest_actual_012984
  · exact g32p_supplierForest_actual_013067
  · exact g32p_supplierForest_actual_013072
  · exact g32p_supplierForest_actual_013078
  · exact g32p_supplierForest_actual_013085
  · exact g32p_supplierForest_actual_013120
  · exact g32p_supplierForest_actual_013126
  · exact g32p_supplierForest_actual_013162
  · exact g32p_supplierForest_actual_013193
  · exact g32p_supplierForest_actual_013229
  · exact g32p_supplierForest_actual_013238
  · exact g32p_supplierForest_actual_013244
  · exact g32p_supplierForest_actual_013261
  · exact g32p_supplierForest_actual_013268
  · exact g32p_supplierForest_actual_013315
  · exact g32p_supplierForest_actual_013323
  · exact g32p_supplierForest_actual_013343
  · exact g32p_supplierForest_actual_013396
  · exact g32p_supplierForest_actual_013406
  · exact g32p_supplierForest_actual_013416
  · exact g32p_supplierForest_actual_013422
  · exact g32p_supplierForest_actual_013459
  · exact g32p_supplierForest_actual_013473
  · exact g32p_supplierForest_actual_013508
  · exact g32p_supplierForest_actual_013539
  · exact g32p_supplierForest_actual_013545
  · exact g32p_supplierForest_actual_013566
  · exact g32p_supplierForest_actual_013578
  · exact g32p_supplierForest_actual_013722
  · exact g32p_supplierForest_actual_013729
  · exact g32p_supplierForest_actual_013762
  · exact g32p_supplierForest_actual_013806
  · exact g32p_supplierForest_actual_013813
  · exact g32p_supplierForest_actual_013859
  · exact g32p_supplierForest_actual_013871
  · exact g32p_supplierForest_actual_013881
  · exact g32p_supplierForest_actual_013883
  · exact g32p_supplierForest_actual_013893
  · exact g32p_supplierForest_actual_013898
  · exact g32p_supplierForest_actual_013955
  · exact g32p_supplierForest_actual_013967
  · exact g32p_supplierForest_actual_013993
  · exact g32p_supplierForest_actual_014007
  · exact g32p_supplierForest_actual_014040
  · exact g32p_supplierForest_actual_014091
  · exact g32p_supplierForest_actual_014131
  · exact g32p_supplierForest_actual_014134
  · exact g32p_supplierForest_actual_014146
  · exact g32p_supplierForest_actual_014176
  · exact g32p_supplierForest_actual_014232
  · exact g32p_supplierForest_actual_014274
  · exact g32p_supplierForest_actual_014290
  · exact g32p_supplierForest_actual_014313
  · exact g32p_supplierForest_actual_014316
  · exact g32p_supplierForest_actual_014349
  · exact g32p_supplierForest_actual_014511
  · exact g32p_supplierForest_actual_014537
  · exact g32p_supplierForest_actual_014544
  · exact g32p_supplierForest_actual_014553
  · exact g32p_supplierForest_actual_014554
  · exact g32p_supplierForest_actual_014559
  · exact g32p_supplierForest_actual_014573
  · exact g32p_supplierForest_actual_014577
  · exact g32p_supplierForest_actual_014582
  · exact g32p_supplierForest_actual_014584
  · exact g32p_supplierForest_actual_014590
  · exact g32p_supplierForest_actual_014593
  · exact g32p_supplierForest_actual_014613
  · exact g32p_supplierForest_actual_014620
  · exact g32p_supplierForest_actual_014658
  · exact g32p_supplierForest_actual_014699
  · exact g32p_supplierForest_actual_014701
  · exact g32p_supplierForest_actual_014743
  · exact g32p_supplierForest_actual_014753
  · exact g32p_supplierForest_actual_014823
  · exact g32p_supplierForest_actual_014833
  · exact g32p_supplierForest_actual_014844
  · exact g32p_supplierForest_actual_014848
  · exact g32p_supplierForest_actual_014862
  · exact g32p_supplierForest_actual_014878
  · exact g32p_supplierForest_actual_014880
  · exact g32p_supplierForest_actual_014940
  · exact g32p_supplierForest_actual_014963
  · exact g32p_supplierForest_actual_014965
  · exact g32p_supplierForest_actual_014968
  · exact g32p_supplierForest_actual_015012
  · exact g32p_supplierForest_actual_015017
  · exact g32p_supplierForest_actual_015021
  · exact g32p_supplierForest_actual_015084
  · exact g32p_supplierForest_actual_015092
  · exact g32p_supplierForest_actual_015103
  · exact g32p_supplierForest_actual_015224
  · exact g32p_supplierForest_actual_015286
  · exact g32p_supplierForest_actual_015289
  · exact g32p_supplierForest_actual_015312
  · exact g32p_supplierForest_actual_015331
  · exact g32p_supplierForest_actual_015342
  · exact g32p_supplierForest_actual_015348
  · exact g32p_supplierForest_actual_015380
  · exact g32p_supplierForest_actual_015382
  · exact g32p_supplierForest_actual_015423
  · exact g32p_supplierForest_actual_015464
  · exact g32p_supplierForest_actual_015484
  · exact g32p_supplierForest_actual_015488
  · exact g32p_supplierForest_actual_015491
  · exact g32p_supplierForest_actual_015518
  · exact g32p_supplierForest_actual_015520
  · exact g32p_supplierForest_actual_015588
  · exact g32p_supplierForest_actual_015590
  · exact g32p_supplierForest_actual_015592
  · exact g32p_supplierForest_actual_015607
  · exact g32p_supplierForest_actual_015615
  · exact g32p_supplierForest_actual_015647
  · exact g32p_supplierForest_actual_015668
  · exact g32p_supplierForest_actual_015670
  · exact g32p_supplierForest_actual_015673
  · exact g32p_supplierForest_actual_015684
  · exact g32p_supplierForest_actual_015696
  · exact g32p_supplierForest_actual_015706
  · exact g32p_supplierForest_actual_015714
  · exact g32p_supplierForest_actual_015717
  · exact g32p_supplierForest_actual_015730
  · exact g32p_supplierForest_actual_015779
  · exact g32p_supplierForest_actual_015786
  · exact g32p_supplierForest_actual_015853
  · exact g32p_supplierForest_actual_015974
  · exact g32p_supplierForest_actual_015979
  · exact g32p_supplierForest_actual_015985
  · exact g32p_supplierForest_actual_016078
  · exact g32p_supplierForest_actual_016085
  · exact g32p_supplierForest_actual_016117
  · exact g32p_supplierForest_actual_016161
  · exact g32p_supplierForest_actual_016214
  · exact g32p_supplierForest_actual_016232
  · exact g32p_supplierForest_actual_016235
  · exact g32p_supplierForest_actual_016260
  · exact g32p_supplierForest_actual_016270
  · exact g32p_supplierForest_actual_016271
  · exact g32p_supplierForest_actual_016321
  · exact g32p_supplierForest_actual_016363
  · exact g32p_supplierForest_actual_016370
  · exact g32p_supplierForest_actual_016392
  · exact g32p_supplierForest_actual_016409
  · exact g32p_supplierForest_actual_016454
  · exact g32p_supplierForest_actual_016455
  · exact g32p_supplierForest_actual_016469
  · exact g32p_supplierForest_actual_016487
  · exact g32p_supplierForest_actual_016555
  · exact g32p_supplierForest_actual_016583
  · exact g32p_supplierForest_actual_016591
  · exact g32p_supplierForest_actual_016655
  · exact g32p_supplierForest_actual_016710
  · exact g32p_supplierForest_actual_016737
  · exact g32p_supplierForest_actual_016785
  · exact g32p_supplierForest_actual_016801
  · exact g32p_supplierForest_actual_016805
  · exact g32p_supplierForest_actual_016806
  · exact g32p_supplierForest_actual_016840
  · exact g32p_supplierForest_actual_016865
  · exact g32p_supplierForest_actual_016873
  · exact g32p_supplierForest_actual_016877
  · exact g32p_supplierForest_actual_016888
  · exact g32p_supplierForest_actual_016955
  · exact g32p_supplierForest_actual_016961
  · exact g32p_supplierForest_actual_016964
  · exact g32p_supplierForest_actual_017032

def g32p_supplierForest_nodes_059 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_017085 else g32p_supplierForest_node_017176) else (if i.val < 3 then g32p_supplierForest_node_017216 else g32p_supplierForest_node_017217)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_017239 else g32p_supplierForest_node_017273) else (if i.val < 7 then g32p_supplierForest_node_017281 else g32p_supplierForest_node_017299))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_017304 else g32p_supplierForest_node_017326) else (if i.val < 11 then g32p_supplierForest_node_017331 else g32p_supplierForest_node_017361)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_017381 else g32p_supplierForest_node_017391) else (if i.val < 15 then g32p_supplierForest_node_017452 else g32p_supplierForest_node_017496)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_017507 else g32p_supplierForest_node_017514) else (if i.val < 19 then g32p_supplierForest_node_017585 else g32p_supplierForest_node_017586)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_017609 else g32p_supplierForest_node_017631) else (if i.val < 23 then g32p_supplierForest_node_017715 else g32p_supplierForest_node_017747))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_017774 else g32p_supplierForest_node_017778) else (if i.val < 27 then g32p_supplierForest_node_017801 else g32p_supplierForest_node_017818)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_017850 else g32p_supplierForest_node_017858) else (if i.val < 31 then g32p_supplierForest_node_017861 else g32p_supplierForest_node_017883))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_017887 else g32p_supplierForest_node_017892) else (if i.val < 35 then g32p_supplierForest_node_017895 else g32p_supplierForest_node_017922)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_017931 else g32p_supplierForest_node_017945) else (if i.val < 39 then g32p_supplierForest_node_017975 else g32p_supplierForest_node_017996))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_018022 else g32p_supplierForest_node_018045) else (if i.val < 43 then g32p_supplierForest_node_018046 else g32p_supplierForest_node_018061)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_018071 else g32p_supplierForest_node_018085) else (if i.val < 47 then g32p_supplierForest_node_018095 else g32p_supplierForest_node_018102)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_018121 else g32p_supplierForest_node_018124) else (if i.val < 51 then g32p_supplierForest_node_018136 else g32p_supplierForest_node_018144)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_018169 else g32p_supplierForest_node_018172) else (if i.val < 55 then g32p_supplierForest_node_018203 else g32p_supplierForest_node_018211))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_018221 else g32p_supplierForest_node_018268) else (if i.val < 59 then g32p_supplierForest_node_018282 else g32p_supplierForest_node_018317)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_018346 else g32p_supplierForest_node_018386) else (if i.val < 63 then g32p_supplierForest_node_018413 else g32p_supplierForest_node_018474)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_018484 else g32p_supplierForest_node_018499) else (if i.val < 67 then g32p_supplierForest_node_018515 else g32p_supplierForest_node_018531)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_018566 else g32p_supplierForest_node_018575) else (if i.val < 71 then g32p_supplierForest_node_018587 else g32p_supplierForest_node_018652))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_018682 else g32p_supplierForest_node_018731) else (if i.val < 75 then g32p_supplierForest_node_018735 else g32p_supplierForest_node_018760)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_018786 else g32p_supplierForest_node_018801) else (if i.val < 79 then g32p_supplierForest_node_018802 else g32p_supplierForest_node_018892)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_018909 else g32p_supplierForest_node_018975) else (if i.val < 83 then g32p_supplierForest_node_018982 else g32p_supplierForest_node_018985)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_019016 else g32p_supplierForest_node_019020) else (if i.val < 87 then g32p_supplierForest_node_019045 else g32p_supplierForest_node_019060))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_019065 else g32p_supplierForest_node_019071) else (if i.val < 91 then g32p_supplierForest_node_019087 else g32p_supplierForest_node_019094)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_019111 else g32p_supplierForest_node_019115) else (if i.val < 95 then g32p_supplierForest_node_019131 else g32p_supplierForest_node_019139))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_019166 else g32p_supplierForest_node_019198) else (if i.val < 99 then g32p_supplierForest_node_019235 else g32p_supplierForest_node_019272)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_019280 else g32p_supplierForest_node_019287) else (if i.val < 103 then g32p_supplierForest_node_019319 else g32p_supplierForest_node_019322))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_019326 else g32p_supplierForest_node_019349) else (if i.val < 107 then g32p_supplierForest_node_019406 else g32p_supplierForest_node_019442)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_019494 else g32p_supplierForest_node_019497) else (if i.val < 111 then g32p_supplierForest_node_019556 else g32p_supplierForest_node_019613)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_019657 else g32p_supplierForest_node_019659) else (if i.val < 115 then g32p_supplierForest_node_019673 else g32p_supplierForest_node_019708)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_019720 else g32p_supplierForest_node_019769) else (if i.val < 119 then g32p_supplierForest_node_019821 else g32p_supplierForest_node_019848))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_019850 else g32p_supplierForest_node_019852) else (if i.val < 123 then g32p_supplierForest_node_019867 else g32p_supplierForest_node_019912)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_019915 else g32p_supplierForest_node_019922) else (if i.val < 127 then g32p_supplierForest_node_019925 else g32p_supplierForest_node_019940))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_019953 else g32p_supplierForest_node_020013) else (if i.val < 131 then g32p_supplierForest_node_020049 else g32p_supplierForest_node_020068)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_020108 else g32p_supplierForest_node_020129) else (if i.val < 135 then g32p_supplierForest_node_020168 else g32p_supplierForest_node_020185))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_020186 else g32p_supplierForest_node_020228) else (if i.val < 139 then g32p_supplierForest_node_020316 else g32p_supplierForest_node_020341)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_020368 else g32p_supplierForest_node_020403) else (if i.val < 143 then g32p_supplierForest_node_020443 else g32p_supplierForest_node_020456)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_020472 else g32p_supplierForest_node_020508) else (if i.val < 147 then g32p_supplierForest_node_020510 else g32p_supplierForest_node_020566)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_020583 else g32p_supplierForest_node_020590) else (if i.val < 151 then g32p_supplierForest_node_020614 else g32p_supplierForest_node_020686))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_020703 else g32p_supplierForest_node_020752) else (if i.val < 155 then g32p_supplierForest_node_020793 else g32p_supplierForest_node_020802)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_020809 else g32p_supplierForest_node_020861) else (if i.val < 159 then g32p_supplierForest_node_020876 else g32p_supplierForest_node_020883))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_020972 else g32p_supplierForest_node_020978) else (if i.val < 163 then g32p_supplierForest_node_020986 else g32p_supplierForest_node_021002)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_021014 else g32p_supplierForest_node_021049) else (if i.val < 167 then g32p_supplierForest_node_021059 else g32p_supplierForest_node_021073))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_021106 else g32p_supplierForest_node_021110) else (if i.val < 171 then g32p_supplierForest_node_021159 else g32p_supplierForest_node_021195)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_021226 else g32p_supplierForest_node_021255) else (if i.val < 175 then g32p_supplierForest_node_021311 else g32p_supplierForest_node_021312)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_021326 else g32p_supplierForest_node_021339) else (if i.val < 179 then g32p_supplierForest_node_021372 else g32p_supplierForest_node_021429)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_021440 else g32p_supplierForest_node_021448) else (if i.val < 183 then g32p_supplierForest_node_021480 else g32p_supplierForest_node_021483))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_021505 else g32p_supplierForest_node_021527) else (if i.val < 187 then g32p_supplierForest_node_021528 else g32p_supplierForest_node_021532)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_021559 else g32p_supplierForest_node_021608) else (if i.val < 191 then g32p_supplierForest_node_021612 else g32p_supplierForest_node_021637)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_021644 else g32p_supplierForest_node_021649) else (if i.val < 195 then g32p_supplierForest_node_021677 else g32p_supplierForest_node_021681)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_021685 else g32p_supplierForest_node_021686) else (if i.val < 199 then g32p_supplierForest_node_021700 else g32p_supplierForest_node_021702))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_021710 else g32p_supplierForest_node_021827) else (if i.val < 203 then g32p_supplierForest_node_021845 else g32p_supplierForest_node_021850)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_021855 else g32p_supplierForest_node_021862) else (if i.val < 207 then g32p_supplierForest_node_021867 else g32p_supplierForest_node_021885)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_021906 else g32p_supplierForest_node_021933) else (if i.val < 211 then g32p_supplierForest_node_021942 else g32p_supplierForest_node_021971)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_022062 else g32p_supplierForest_node_022070) else (if i.val < 215 then g32p_supplierForest_node_022081 else g32p_supplierForest_node_022102))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_022108 else g32p_supplierForest_node_022114) else (if i.val < 219 then g32p_supplierForest_node_022120 else g32p_supplierForest_node_022143)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_022176 else g32p_supplierForest_node_022180) else (if i.val < 223 then g32p_supplierForest_node_022213 else g32p_supplierForest_node_022226))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_022256 else g32p_supplierForest_node_022309) else (if i.val < 227 then g32p_supplierForest_node_022310 else g32p_supplierForest_node_022311)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_022312 else g32p_supplierForest_node_022326) else (if i.val < 231 then g32p_supplierForest_node_022376 else g32p_supplierForest_node_022381))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_022392 else g32p_supplierForest_node_022423) else (if i.val < 235 then g32p_supplierForest_node_022439 else g32p_supplierForest_node_022473)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_022516 else g32p_supplierForest_node_022517) else (if i.val < 239 then g32p_supplierForest_node_022575 else g32p_supplierForest_node_022608)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_022622 else g32p_supplierForest_node_022639) else (if i.val < 243 then g32p_supplierForest_node_022660 else g32p_supplierForest_node_022671)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_022693 else g32p_supplierForest_node_022699) else (if i.val < 247 then g32p_supplierForest_node_022729 else g32p_supplierForest_node_022735))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_022767 else g32p_supplierForest_node_022770) else (if i.val < 251 then g32p_supplierForest_node_022799 else g32p_supplierForest_node_022803)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_022845 else g32p_supplierForest_node_022890) else (if i.val < 255 then g32p_supplierForest_node_022902 else g32p_supplierForest_node_022942))))))))

def g32p_supplierForest_classes_059 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 47 else 13) else (if i.val < 3 then 27 else 12)) else (if i.val < 6 then (if i.val < 5 then 48 else 27) else (if i.val < 7 then 12 else 13))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 49 else 26) else (if i.val < 11 then 11 else 10)) else (if i.val < 14 then (if i.val < 13 then 49 else 27) else (if i.val < 15 then 10 else 25)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 12 else 47) else (if i.val < 19 then 10 else 51)) else (if i.val < 22 then (if i.val < 21 then 27 else 10) else (if i.val < 23 then 26 else 12))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 13 else 12) else (if i.val < 27 then 46 else 11)) else (if i.val < 30 then (if i.val < 29 then 49 else 49) else (if i.val < 31 then 11 else 9))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 47 else 26) else (if i.val < 35 then 9 else 46)) else (if i.val < 38 then (if i.val < 37 then 9 else 48) else (if i.val < 39 then 27 else 12))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 26 else 47) else (if i.val < 43 then 47 else 48)) else (if i.val < 46 then (if i.val < 45 then 49 else 48) else (if i.val < 47 then 27 else 49)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 49 else 9) else (if i.val < 51 then 12 else 50)) else (if i.val < 54 then (if i.val < 53 then 49 else 50) else (if i.val < 55 then 50 else 56))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 49 else 46) else (if i.val < 59 then 9 else 10)) else (if i.val < 62 then (if i.val < 61 then 25 else 50) else (if i.val < 63 then 25 else 56)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 49) else (if i.val < 67 then 49 else 49)) else (if i.val < 70 then (if i.val < 69 then 51 else 51) else (if i.val < 71 then 49 else 9))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 8 else 48) else (if i.val < 75 then 47 else 47)) else (if i.val < 78 then (if i.val < 77 then 49 else 47) else (if i.val < 79 then 49 else 50)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 49 else 50) else (if i.val < 83 then 47 else 48)) else (if i.val < 86 then (if i.val < 85 then 51 else 25) else (if i.val < 87 then 8 else 49))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 47 else 46) else (if i.val < 91 then 47 else 48)) else (if i.val < 94 then (if i.val < 93 then 10 else 50) else (if i.val < 95 then 9 else 49))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 27 else 25) else (if i.val < 99 then 26 else 47)) else (if i.val < 102 then (if i.val < 101 then 47 else 26) else (if i.val < 103 then 10 else 49))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 26 else 27) else (if i.val < 107 then 26 else 10)) else (if i.val < 110 then (if i.val < 109 then 13 else 47) else (if i.val < 111 then 12 else 46)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 49 else 11) else (if i.val < 115 then 10 else 8)) else (if i.val < 118 then (if i.val < 117 then 26 else 46) else (if i.val < 119 then 27 else 25))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 10 else 26) else (if i.val < 123 then 10 else 49)) else (if i.val < 126 then (if i.val < 125 then 50 else 10) else (if i.val < 127 then 26 else 13))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 9 else 49) else (if i.val < 131 then 48 else 48)) else (if i.val < 134 then (if i.val < 133 then 25 else 8) else (if i.val < 135 then 10 else 25))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 9 else 49) else (if i.val < 139 then 10 else 46)) else (if i.val < 142 then (if i.val < 141 then 1 else 47) else (if i.val < 143 then 11 else 26)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 25 else 48) else (if i.val < 147 then 50 else 49)) else (if i.val < 150 then (if i.val < 149 then 26 else 48) else (if i.val < 151 then 9 else 49))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 49 else 50) else (if i.val < 155 then 10 else 25)) else (if i.val < 158 then (if i.val < 157 then 49 else 25) else (if i.val < 159 then 47 else 51))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 10 else 10) else (if i.val < 163 then 48 else 12)) else (if i.val < 166 then (if i.val < 165 then 25 else 8) else (if i.val < 167 then 27 else 49))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 49 else 49) else (if i.val < 171 then 46 else 48)) else (if i.val < 174 then (if i.val < 173 then 25 else 25) else (if i.val < 175 then 47 else 47)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 47 else 49) else (if i.val < 179 then 49 else 13)) else (if i.val < 182 then (if i.val < 181 then 11 else 46) else (if i.val < 183 then 46 else 10))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 49 else 49) else (if i.val < 187 then 26 else 49)) else (if i.val < 190 then (if i.val < 189 then 49 else 46) else (if i.val < 191 then 25 else 25)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 12 else 49) else (if i.val < 195 then 10 else 25)) else (if i.val < 198 then (if i.val < 197 then 46 else 25) else (if i.val < 199 then 10 else 10))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 49 else 26) else (if i.val < 203 then 25 else 47)) else (if i.val < 206 then (if i.val < 205 then 10 else 27) else (if i.val < 207 then 49 else 49)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 11 else 26) else (if i.val < 211 then 25 else 26)) else (if i.val < 214 then (if i.val < 213 then 47 else 9) else (if i.val < 215 then 56 else 10))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 26 else 48) else (if i.val < 219 then 27 else 49)) else (if i.val < 222 then (if i.val < 221 then 49 else 25) else (if i.val < 223 then 10 else 50))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 47 else 48) else (if i.val < 227 then 46 else 49)) else (if i.val < 230 then (if i.val < 229 then 49 else 9) else (if i.val < 231 then 25 else 9))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 46 else 50) else (if i.val < 235 then 49 else 9)) else (if i.val < 238 then (if i.val < 237 then 10 else 9) else (if i.val < 239 then 10 else 49)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 26 else 48) else (if i.val < 243 then 46 else 25)) else (if i.val < 246 then (if i.val < 245 then 49 else 25) else (if i.val < 247 then 26 else 25))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 9 else 27) else (if i.val < 251 then 47 else 27)) else (if i.val < 254 then (if i.val < 253 then 9 else 48) else (if i.val < 255 then 12 else 49))))))))

theorem g32p_supplierForest_actual_059 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_059 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_059 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_017085
  · exact g32p_supplierForest_actual_017176
  · exact g32p_supplierForest_actual_017216
  · exact g32p_supplierForest_actual_017217
  · exact g32p_supplierForest_actual_017239
  · exact g32p_supplierForest_actual_017273
  · exact g32p_supplierForest_actual_017281
  · exact g32p_supplierForest_actual_017299
  · exact g32p_supplierForest_actual_017304
  · exact g32p_supplierForest_actual_017326
  · exact g32p_supplierForest_actual_017331
  · exact g32p_supplierForest_actual_017361
  · exact g32p_supplierForest_actual_017381
  · exact g32p_supplierForest_actual_017391
  · exact g32p_supplierForest_actual_017452
  · exact g32p_supplierForest_actual_017496
  · exact g32p_supplierForest_actual_017507
  · exact g32p_supplierForest_actual_017514
  · exact g32p_supplierForest_actual_017585
  · exact g32p_supplierForest_actual_017586
  · exact g32p_supplierForest_actual_017609
  · exact g32p_supplierForest_actual_017631
  · exact g32p_supplierForest_actual_017715
  · exact g32p_supplierForest_actual_017747
  · exact g32p_supplierForest_actual_017774
  · exact g32p_supplierForest_actual_017778
  · exact g32p_supplierForest_actual_017801
  · exact g32p_supplierForest_actual_017818
  · exact g32p_supplierForest_actual_017850
  · exact g32p_supplierForest_actual_017858
  · exact g32p_supplierForest_actual_017861
  · exact g32p_supplierForest_actual_017883
  · exact g32p_supplierForest_actual_017887
  · exact g32p_supplierForest_actual_017892
  · exact g32p_supplierForest_actual_017895
  · exact g32p_supplierForest_actual_017922
  · exact g32p_supplierForest_actual_017931
  · exact g32p_supplierForest_actual_017945
  · exact g32p_supplierForest_actual_017975
  · exact g32p_supplierForest_actual_017996
  · exact g32p_supplierForest_actual_018022
  · exact g32p_supplierForest_actual_018045
  · exact g32p_supplierForest_actual_018046
  · exact g32p_supplierForest_actual_018061
  · exact g32p_supplierForest_actual_018071
  · exact g32p_supplierForest_actual_018085
  · exact g32p_supplierForest_actual_018095
  · exact g32p_supplierForest_actual_018102
  · exact g32p_supplierForest_actual_018121
  · exact g32p_supplierForest_actual_018124
  · exact g32p_supplierForest_actual_018136
  · exact g32p_supplierForest_actual_018144
  · exact g32p_supplierForest_actual_018169
  · exact g32p_supplierForest_actual_018172
  · exact g32p_supplierForest_actual_018203
  · exact g32p_supplierForest_actual_018211
  · exact g32p_supplierForest_actual_018221
  · exact g32p_supplierForest_actual_018268
  · exact g32p_supplierForest_actual_018282
  · exact g32p_supplierForest_actual_018317
  · exact g32p_supplierForest_actual_018346
  · exact g32p_supplierForest_actual_018386
  · exact g32p_supplierForest_actual_018413
  · exact g32p_supplierForest_actual_018474
  · exact g32p_supplierForest_actual_018484
  · exact g32p_supplierForest_actual_018499
  · exact g32p_supplierForest_actual_018515
  · exact g32p_supplierForest_actual_018531
  · exact g32p_supplierForest_actual_018566
  · exact g32p_supplierForest_actual_018575
  · exact g32p_supplierForest_actual_018587
  · exact g32p_supplierForest_actual_018652
  · exact g32p_supplierForest_actual_018682
  · exact g32p_supplierForest_actual_018731
  · exact g32p_supplierForest_actual_018735
  · exact g32p_supplierForest_actual_018760
  · exact g32p_supplierForest_actual_018786
  · exact g32p_supplierForest_actual_018801
  · exact g32p_supplierForest_actual_018802
  · exact g32p_supplierForest_actual_018892
  · exact g32p_supplierForest_actual_018909
  · exact g32p_supplierForest_actual_018975
  · exact g32p_supplierForest_actual_018982
  · exact g32p_supplierForest_actual_018985
  · exact g32p_supplierForest_actual_019016
  · exact g32p_supplierForest_actual_019020
  · exact g32p_supplierForest_actual_019045
  · exact g32p_supplierForest_actual_019060
  · exact g32p_supplierForest_actual_019065
  · exact g32p_supplierForest_actual_019071
  · exact g32p_supplierForest_actual_019087
  · exact g32p_supplierForest_actual_019094
  · exact g32p_supplierForest_actual_019111
  · exact g32p_supplierForest_actual_019115
  · exact g32p_supplierForest_actual_019131
  · exact g32p_supplierForest_actual_019139
  · exact g32p_supplierForest_actual_019166
  · exact g32p_supplierForest_actual_019198
  · exact g32p_supplierForest_actual_019235
  · exact g32p_supplierForest_actual_019272
  · exact g32p_supplierForest_actual_019280
  · exact g32p_supplierForest_actual_019287
  · exact g32p_supplierForest_actual_019319
  · exact g32p_supplierForest_actual_019322
  · exact g32p_supplierForest_actual_019326
  · exact g32p_supplierForest_actual_019349
  · exact g32p_supplierForest_actual_019406
  · exact g32p_supplierForest_actual_019442
  · exact g32p_supplierForest_actual_019494
  · exact g32p_supplierForest_actual_019497
  · exact g32p_supplierForest_actual_019556
  · exact g32p_supplierForest_actual_019613
  · exact g32p_supplierForest_actual_019657
  · exact g32p_supplierForest_actual_019659
  · exact g32p_supplierForest_actual_019673
  · exact g32p_supplierForest_actual_019708
  · exact g32p_supplierForest_actual_019720
  · exact g32p_supplierForest_actual_019769
  · exact g32p_supplierForest_actual_019821
  · exact g32p_supplierForest_actual_019848
  · exact g32p_supplierForest_actual_019850
  · exact g32p_supplierForest_actual_019852
  · exact g32p_supplierForest_actual_019867
  · exact g32p_supplierForest_actual_019912
  · exact g32p_supplierForest_actual_019915
  · exact g32p_supplierForest_actual_019922
  · exact g32p_supplierForest_actual_019925
  · exact g32p_supplierForest_actual_019940
  · exact g32p_supplierForest_actual_019953
  · exact g32p_supplierForest_actual_020013
  · exact g32p_supplierForest_actual_020049
  · exact g32p_supplierForest_actual_020068
  · exact g32p_supplierForest_actual_020108
  · exact g32p_supplierForest_actual_020129
  · exact g32p_supplierForest_actual_020168
  · exact g32p_supplierForest_actual_020185
  · exact g32p_supplierForest_actual_020186
  · exact g32p_supplierForest_actual_020228
  · exact g32p_supplierForest_actual_020316
  · exact g32p_supplierForest_actual_020341
  · exact g32p_supplierForest_actual_020368
  · exact g32p_supplierForest_actual_020403
  · exact g32p_supplierForest_actual_020443
  · exact g32p_supplierForest_actual_020456
  · exact g32p_supplierForest_actual_020472
  · exact g32p_supplierForest_actual_020508
  · exact g32p_supplierForest_actual_020510
  · exact g32p_supplierForest_actual_020566
  · exact g32p_supplierForest_actual_020583
  · exact g32p_supplierForest_actual_020590
  · exact g32p_supplierForest_actual_020614
  · exact g32p_supplierForest_actual_020686
  · exact g32p_supplierForest_actual_020703
  · exact g32p_supplierForest_actual_020752
  · exact g32p_supplierForest_actual_020793
  · exact g32p_supplierForest_actual_020802
  · exact g32p_supplierForest_actual_020809
  · exact g32p_supplierForest_actual_020861
  · exact g32p_supplierForest_actual_020876
  · exact g32p_supplierForest_actual_020883
  · exact g32p_supplierForest_actual_020972
  · exact g32p_supplierForest_actual_020978
  · exact g32p_supplierForest_actual_020986
  · exact g32p_supplierForest_actual_021002
  · exact g32p_supplierForest_actual_021014
  · exact g32p_supplierForest_actual_021049
  · exact g32p_supplierForest_actual_021059
  · exact g32p_supplierForest_actual_021073
  · exact g32p_supplierForest_actual_021106
  · exact g32p_supplierForest_actual_021110
  · exact g32p_supplierForest_actual_021159
  · exact g32p_supplierForest_actual_021195
  · exact g32p_supplierForest_actual_021226
  · exact g32p_supplierForest_actual_021255
  · exact g32p_supplierForest_actual_021311
  · exact g32p_supplierForest_actual_021312
  · exact g32p_supplierForest_actual_021326
  · exact g32p_supplierForest_actual_021339
  · exact g32p_supplierForest_actual_021372
  · exact g32p_supplierForest_actual_021429
  · exact g32p_supplierForest_actual_021440
  · exact g32p_supplierForest_actual_021448
  · exact g32p_supplierForest_actual_021480
  · exact g32p_supplierForest_actual_021483
  · exact g32p_supplierForest_actual_021505
  · exact g32p_supplierForest_actual_021527
  · exact g32p_supplierForest_actual_021528
  · exact g32p_supplierForest_actual_021532
  · exact g32p_supplierForest_actual_021559
  · exact g32p_supplierForest_actual_021608
  · exact g32p_supplierForest_actual_021612
  · exact g32p_supplierForest_actual_021637
  · exact g32p_supplierForest_actual_021644
  · exact g32p_supplierForest_actual_021649
  · exact g32p_supplierForest_actual_021677
  · exact g32p_supplierForest_actual_021681
  · exact g32p_supplierForest_actual_021685
  · exact g32p_supplierForest_actual_021686
  · exact g32p_supplierForest_actual_021700
  · exact g32p_supplierForest_actual_021702
  · exact g32p_supplierForest_actual_021710
  · exact g32p_supplierForest_actual_021827
  · exact g32p_supplierForest_actual_021845
  · exact g32p_supplierForest_actual_021850
  · exact g32p_supplierForest_actual_021855
  · exact g32p_supplierForest_actual_021862
  · exact g32p_supplierForest_actual_021867
  · exact g32p_supplierForest_actual_021885
  · exact g32p_supplierForest_actual_021906
  · exact g32p_supplierForest_actual_021933
  · exact g32p_supplierForest_actual_021942
  · exact g32p_supplierForest_actual_021971
  · exact g32p_supplierForest_actual_022062
  · exact g32p_supplierForest_actual_022070
  · exact g32p_supplierForest_actual_022081
  · exact g32p_supplierForest_actual_022102
  · exact g32p_supplierForest_actual_022108
  · exact g32p_supplierForest_actual_022114
  · exact g32p_supplierForest_actual_022120
  · exact g32p_supplierForest_actual_022143
  · exact g32p_supplierForest_actual_022176
  · exact g32p_supplierForest_actual_022180
  · exact g32p_supplierForest_actual_022213
  · exact g32p_supplierForest_actual_022226
  · exact g32p_supplierForest_actual_022256
  · exact g32p_supplierForest_actual_022309
  · exact g32p_supplierForest_actual_022310
  · exact g32p_supplierForest_actual_022311
  · exact g32p_supplierForest_actual_022312
  · exact g32p_supplierForest_actual_022326
  · exact g32p_supplierForest_actual_022376
  · exact g32p_supplierForest_actual_022381
  · exact g32p_supplierForest_actual_022392
  · exact g32p_supplierForest_actual_022423
  · exact g32p_supplierForest_actual_022439
  · exact g32p_supplierForest_actual_022473
  · exact g32p_supplierForest_actual_022516
  · exact g32p_supplierForest_actual_022517
  · exact g32p_supplierForest_actual_022575
  · exact g32p_supplierForest_actual_022608
  · exact g32p_supplierForest_actual_022622
  · exact g32p_supplierForest_actual_022639
  · exact g32p_supplierForest_actual_022660
  · exact g32p_supplierForest_actual_022671
  · exact g32p_supplierForest_actual_022693
  · exact g32p_supplierForest_actual_022699
  · exact g32p_supplierForest_actual_022729
  · exact g32p_supplierForest_actual_022735
  · exact g32p_supplierForest_actual_022767
  · exact g32p_supplierForest_actual_022770
  · exact g32p_supplierForest_actual_022799
  · exact g32p_supplierForest_actual_022803
  · exact g32p_supplierForest_actual_022845
  · exact g32p_supplierForest_actual_022890
  · exact g32p_supplierForest_actual_022902
  · exact g32p_supplierForest_actual_022942

def g32p_supplierForest_nodes_060 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_022978 else g32p_supplierForest_node_022992) else (if i.val < 3 then g32p_supplierForest_node_023143 else g32p_supplierForest_node_023145)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_023189 else g32p_supplierForest_node_023250) else (if i.val < 7 then g32p_supplierForest_node_023253 else g32p_supplierForest_node_023264))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_023266 else g32p_supplierForest_node_023270) else (if i.val < 11 then g32p_supplierForest_node_023271 else g32p_supplierForest_node_023297)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_023326 else g32p_supplierForest_node_023333) else (if i.val < 15 then g32p_supplierForest_node_023345 else g32p_supplierForest_node_023412)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_023452 else g32p_supplierForest_node_023459) else (if i.val < 19 then g32p_supplierForest_node_023470 else g32p_supplierForest_node_023549)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_023572 else g32p_supplierForest_node_023687) else (if i.val < 23 then g32p_supplierForest_node_023732 else g32p_supplierForest_node_023734))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_023771 else g32p_supplierForest_node_023800) else (if i.val < 27 then g32p_supplierForest_node_023810 else g32p_supplierForest_node_023812)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_023840 else g32p_supplierForest_node_023846) else (if i.val < 31 then g32p_supplierForest_node_023880 else g32p_supplierForest_node_023900))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_023904 else g32p_supplierForest_node_023916) else (if i.val < 35 then g32p_supplierForest_node_023958 else g32p_supplierForest_node_023984)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_024057 else g32p_supplierForest_node_024061) else (if i.val < 39 then g32p_supplierForest_node_024113 else g32p_supplierForest_node_024118))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_024140 else g32p_supplierForest_node_024147) else (if i.val < 43 then g32p_supplierForest_node_024202 else g32p_supplierForest_node_024284)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_024290 else g32p_supplierForest_node_024306) else (if i.val < 47 then g32p_supplierForest_node_024313 else g32p_supplierForest_node_024344)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_024353 else g32p_supplierForest_node_024356) else (if i.val < 51 then g32p_supplierForest_node_024395 else g32p_supplierForest_node_024441)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_024467 else g32p_supplierForest_node_024533) else (if i.val < 55 then g32p_supplierForest_node_024540 else g32p_supplierForest_node_024553))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_024565 else g32p_supplierForest_node_024570) else (if i.val < 59 then g32p_supplierForest_node_024572 else g32p_supplierForest_node_024609)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_024620 else g32p_supplierForest_node_024622) else (if i.val < 63 then g32p_supplierForest_node_024624 else g32p_supplierForest_node_024648)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_024673 else g32p_supplierForest_node_024729) else (if i.val < 67 then g32p_supplierForest_node_024737 else g32p_supplierForest_node_024742)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_024758 else g32p_supplierForest_node_024788) else (if i.val < 71 then g32p_supplierForest_node_024790 else g32p_supplierForest_node_024799))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_024857 else g32p_supplierForest_node_024894) else (if i.val < 75 then g32p_supplierForest_node_024911 else g32p_supplierForest_node_024916)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_024930 else g32p_supplierForest_node_024932) else (if i.val < 79 then g32p_supplierForest_node_025007 else g32p_supplierForest_node_025018)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_025031 else g32p_supplierForest_node_025099) else (if i.val < 83 then g32p_supplierForest_node_025110 else g32p_supplierForest_node_025124)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_025146 else g32p_supplierForest_node_025154) else (if i.val < 87 then g32p_supplierForest_node_025155 else g32p_supplierForest_node_025174))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_025181 else g32p_supplierForest_node_025185) else (if i.val < 91 then g32p_supplierForest_node_025210 else g32p_supplierForest_node_025218)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_025255 else g32p_supplierForest_node_025281) else (if i.val < 95 then g32p_supplierForest_node_025299 else g32p_supplierForest_node_025342))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_025368 else g32p_supplierForest_node_025382) else (if i.val < 99 then g32p_supplierForest_node_025420 else g32p_supplierForest_node_025425)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_025469 else g32p_supplierForest_node_025470) else (if i.val < 103 then g32p_supplierForest_node_025476 else g32p_supplierForest_node_025523))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_025545 else g32p_supplierForest_node_025553) else (if i.val < 107 then g32p_supplierForest_node_025562 else g32p_supplierForest_node_025600)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_025607 else g32p_supplierForest_node_025653) else (if i.val < 111 then g32p_supplierForest_node_025662 else g32p_supplierForest_node_025684)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_025691 else g32p_supplierForest_node_025695) else (if i.val < 115 then g32p_supplierForest_node_025720 else g32p_supplierForest_node_025769)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_025776 else g32p_supplierForest_node_025787) else (if i.val < 119 then g32p_supplierForest_node_025788 else g32p_supplierForest_node_025809))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_025840 else g32p_supplierForest_node_025852) else (if i.val < 123 then g32p_supplierForest_node_025925 else g32p_supplierForest_node_025948)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_025957 else g32p_supplierForest_node_025963) else (if i.val < 127 then g32p_supplierForest_node_025970 else g32p_supplierForest_node_026016))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_026054 else g32p_supplierForest_node_026061) else (if i.val < 131 then g32p_supplierForest_node_026078 else g32p_supplierForest_node_026114)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_026119 else g32p_supplierForest_node_026165) else (if i.val < 135 then g32p_supplierForest_node_026168 else g32p_supplierForest_node_026194))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_026253 else g32p_supplierForest_node_026277) else (if i.val < 139 then g32p_supplierForest_node_026332 else g32p_supplierForest_node_026337)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_026383 else g32p_supplierForest_node_026391) else (if i.val < 143 then g32p_supplierForest_node_026455 else g32p_supplierForest_node_026477)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_026545 else g32p_supplierForest_node_026589) else (if i.val < 147 then g32p_supplierForest_node_026626 else g32p_supplierForest_node_026633)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_026649 else g32p_supplierForest_node_026707) else (if i.val < 151 then g32p_supplierForest_node_026708 else g32p_supplierForest_node_026719))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_026746 else g32p_supplierForest_node_026776) else (if i.val < 155 then g32p_supplierForest_node_026820 else g32p_supplierForest_node_026831)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_026832 else g32p_supplierForest_node_026868) else (if i.val < 159 then g32p_supplierForest_node_026881 else g32p_supplierForest_node_026907))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_026931 else g32p_supplierForest_node_026963) else (if i.val < 163 then g32p_supplierForest_node_027005 else g32p_supplierForest_node_027010)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_027016 else g32p_supplierForest_node_027066) else (if i.val < 167 then g32p_supplierForest_node_027073 else g32p_supplierForest_node_027084))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_027092 else g32p_supplierForest_node_027117) else (if i.val < 171 then g32p_supplierForest_node_027126 else g32p_supplierForest_node_027214)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_027216 else g32p_supplierForest_node_027217) else (if i.val < 175 then g32p_supplierForest_node_027229 else g32p_supplierForest_node_027257)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_027269 else g32p_supplierForest_node_027283) else (if i.val < 179 then g32p_supplierForest_node_027319 else g32p_supplierForest_node_027369)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_027395 else g32p_supplierForest_node_027408) else (if i.val < 183 then g32p_supplierForest_node_027449 else g32p_supplierForest_node_027455))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_027474 else g32p_supplierForest_node_027505) else (if i.val < 187 then g32p_supplierForest_node_027567 else g32p_supplierForest_node_027572)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_027588 else g32p_supplierForest_node_027590) else (if i.val < 191 then g32p_supplierForest_node_027627 else g32p_supplierForest_node_027633)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_027640 else g32p_supplierForest_node_027649) else (if i.val < 195 then g32p_supplierForest_node_027652 else g32p_supplierForest_node_027653)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_027716 else g32p_supplierForest_node_027733) else (if i.val < 199 then g32p_supplierForest_node_027754 else g32p_supplierForest_node_027835))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_027853 else g32p_supplierForest_node_027871) else (if i.val < 203 then g32p_supplierForest_node_027880 else g32p_supplierForest_node_027894)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_027946 else g32p_supplierForest_node_027955) else (if i.val < 207 then g32p_supplierForest_node_027957 else g32p_supplierForest_node_028030)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_028071 else g32p_supplierForest_node_028224) else (if i.val < 211 then g32p_supplierForest_node_028231 else g32p_supplierForest_node_028240)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_028261 else g32p_supplierForest_node_028264) else (if i.val < 215 then g32p_supplierForest_node_028265 else g32p_supplierForest_node_028277))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_028281 else g32p_supplierForest_node_028302) else (if i.val < 219 then g32p_supplierForest_node_028324 else g32p_supplierForest_node_028331)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_028348 else g32p_supplierForest_node_028359) else (if i.val < 223 then g32p_supplierForest_node_028367 else g32p_supplierForest_node_028372))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_028375 else g32p_supplierForest_node_028391) else (if i.val < 227 then g32p_supplierForest_node_028399 else g32p_supplierForest_node_028406)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_028416 else g32p_supplierForest_node_028430) else (if i.val < 231 then g32p_supplierForest_node_028440 else g32p_supplierForest_node_028461))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_028471 else g32p_supplierForest_node_028506) else (if i.val < 235 then g32p_supplierForest_node_028527 else g32p_supplierForest_node_028549)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_028579 else g32p_supplierForest_node_028636) else (if i.val < 239 then g32p_supplierForest_node_028664 else g32p_supplierForest_node_028667)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_028696 else g32p_supplierForest_node_028705) else (if i.val < 243 then g32p_supplierForest_node_028725 else g32p_supplierForest_node_028733)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_028742 else g32p_supplierForest_node_028759) else (if i.val < 247 then g32p_supplierForest_node_028763 else g32p_supplierForest_node_028777))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_028792 else g32p_supplierForest_node_028793) else (if i.val < 251 then g32p_supplierForest_node_028797 else g32p_supplierForest_node_028804)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_028822 else g32p_supplierForest_node_028827) else (if i.val < 255 then g32p_supplierForest_node_028855 else g32p_supplierForest_node_028865))))))))

def g32p_supplierForest_classes_060 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 54 else 49) else (if i.val < 3 then 10 else 27)) else (if i.val < 6 then (if i.val < 5 then 25 else 26) else (if i.val < 7 then 46 else 10))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9 else 9) else (if i.val < 11 then 25 else 49)) else (if i.val < 14 then (if i.val < 13 then 26 else 11) else (if i.val < 15 then 26 else 12)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 47 else 50) else (if i.val < 19 then 9 else 50)) else (if i.val < 22 then (if i.val < 21 then 27 else 50) else (if i.val < 23 then 26 else 10))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 51 else 8) else (if i.val < 27 then 26 else 50)) else (if i.val < 30 then (if i.val < 29 then 27 else 49) else (if i.val < 31 then 47 else 27))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 51 else 47) else (if i.val < 35 then 8 else 49)) else (if i.val < 38 then (if i.val < 37 then 47 else 47) else (if i.val < 39 then 49 else 25))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 25 else 27) else (if i.val < 43 then 49 else 26)) else (if i.val < 46 then (if i.val < 45 then 49 else 25) else (if i.val < 47 then 46 else 8)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 13 else 25) else (if i.val < 51 then 12 else 49)) else (if i.val < 54 then (if i.val < 53 then 25 else 32) else (if i.val < 55 then 34 else 16))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 34 else 14) else (if i.val < 59 then 30 else 4)) else (if i.val < 62 then (if i.val < 61 then 57 else 57) else (if i.val < 63 then 57 else 17)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 15 else 17) else (if i.val < 67 then 15 else 62)) else (if i.val < 70 then (if i.val < 69 then 32 else 32) else (if i.val < 71 then 16 else 16))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 15 else 17) else (if i.val < 75 then 31 else 16)) else (if i.val < 78 then (if i.val < 77 then 57 else 34) else (if i.val < 79 then 57 else 17)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 57 else 31) else (if i.val < 83 then 57 else 15)) else (if i.val < 86 then (if i.val < 85 then 33 else 57) else (if i.val < 87 then 17 else 15))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 14 else 57) else (if i.val < 91 then 30 else 57)) else (if i.val < 94 then (if i.val < 93 then 16 else 17) else (if i.val < 95 then 4 else 57))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 30 else 30) else (if i.val < 99 then 16 else 31)) else (if i.val < 102 then (if i.val < 101 then 29 else 16) else (if i.val < 103 then 3 else 16))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 59 else 14) else (if i.val < 107 then 57 else 59)) else (if i.val < 110 then (if i.val < 109 then 57 else 30) else (if i.val < 111 then 15 else 17)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 57 else 17) else (if i.val < 115 then 16 else 57)) else (if i.val < 118 then (if i.val < 117 then 57 else 57) else (if i.val < 119 then 30 else 15))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 29 else 36) else (if i.val < 123 then 30 else 15)) else (if i.val < 126 then (if i.val < 125 then 14 else 60) else (if i.val < 127 then 30 else 17))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 17 else 57) else (if i.val < 131 then 30 else 57)) else (if i.val < 134 then (if i.val < 133 then 16 else 57) else (if i.val < 135 then 15 else 30))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 34 else 57) else (if i.val < 139 then 63 else 36)) else (if i.val < 142 then (if i.val < 141 then 62 else 17) else (if i.val < 143 then 15 else 57)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 17 else 64) else (if i.val < 147 then 59 else 15)) else (if i.val < 150 then (if i.val < 149 then 57 else 58) else (if i.val < 151 then 60 else 29))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 57 else 63) else (if i.val < 155 then 14 else 34)) else (if i.val < 158 then (if i.val < 157 then 62 else 63) else (if i.val < 159 then 63 else 57))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 59 else 60) else (if i.val < 163 then 57 else 29)) else (if i.val < 166 then (if i.val < 165 then 15 else 30) else (if i.val < 167 then 57 else 3))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 30 else 33) else (if i.val < 171 then 30 else 16)) else (if i.val < 174 then (if i.val < 173 then 15 else 15) else (if i.val < 175 then 17 else 17)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 32 else 14) else (if i.val < 179 then 57 else 30)) else (if i.val < 182 then (if i.val < 181 then 32 else 16) else (if i.val < 183 then 30 else 32))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 62 else 15) else (if i.val < 187 then 14 else 30)) else (if i.val < 190 then (if i.val < 189 then 14 else 29) else (if i.val < 191 then 29 else 30)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 34 else 4) else (if i.val < 195 then 3 else 57)) else (if i.val < 198 then (if i.val < 197 then 34 else 57) else (if i.val < 199 then 30 else 14))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 34 else 31) else (if i.val < 203 then 32 else 15)) else (if i.val < 206 then (if i.val < 205 then 17 else 62) else (if i.val < 207 then 57 else 30)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 15 else 14) else (if i.val < 211 then 4 else 57)) else (if i.val < 214 then (if i.val < 213 then 30 else 16) else (if i.val < 215 then 57 else 15))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 33 else 17) else (if i.val < 219 then 57 else 59)) else (if i.val < 222 then (if i.val < 221 then 14 else 15) else (if i.val < 223 then 58 else 57))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 57 else 30) else (if i.val < 227 then 36 else 31)) else (if i.val < 230 then (if i.val < 229 then 57 else 17) else (if i.val < 231 then 4 else 57))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 30 else 59) else (if i.val < 235 then 30 else 31)) else (if i.val < 238 then (if i.val < 237 then 15 else 32) else (if i.val < 239 then 58 else 57)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 30 else 16) else (if i.val < 243 then 30 else 57)) else (if i.val < 246 then (if i.val < 245 then 31 else 16) else (if i.val < 247 then 61 else 16))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 4 else 64) else (if i.val < 251 then 57 else 16)) else (if i.val < 254 then (if i.val < 253 then 30 else 63) else (if i.val < 255 then 57 else 32))))))))

theorem g32p_supplierForest_actual_060 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_060 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_060 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_022978
  · exact g32p_supplierForest_actual_022992
  · exact g32p_supplierForest_actual_023143
  · exact g32p_supplierForest_actual_023145
  · exact g32p_supplierForest_actual_023189
  · exact g32p_supplierForest_actual_023250
  · exact g32p_supplierForest_actual_023253
  · exact g32p_supplierForest_actual_023264
  · exact g32p_supplierForest_actual_023266
  · exact g32p_supplierForest_actual_023270
  · exact g32p_supplierForest_actual_023271
  · exact g32p_supplierForest_actual_023297
  · exact g32p_supplierForest_actual_023326
  · exact g32p_supplierForest_actual_023333
  · exact g32p_supplierForest_actual_023345
  · exact g32p_supplierForest_actual_023412
  · exact g32p_supplierForest_actual_023452
  · exact g32p_supplierForest_actual_023459
  · exact g32p_supplierForest_actual_023470
  · exact g32p_supplierForest_actual_023549
  · exact g32p_supplierForest_actual_023572
  · exact g32p_supplierForest_actual_023687
  · exact g32p_supplierForest_actual_023732
  · exact g32p_supplierForest_actual_023734
  · exact g32p_supplierForest_actual_023771
  · exact g32p_supplierForest_actual_023800
  · exact g32p_supplierForest_actual_023810
  · exact g32p_supplierForest_actual_023812
  · exact g32p_supplierForest_actual_023840
  · exact g32p_supplierForest_actual_023846
  · exact g32p_supplierForest_actual_023880
  · exact g32p_supplierForest_actual_023900
  · exact g32p_supplierForest_actual_023904
  · exact g32p_supplierForest_actual_023916
  · exact g32p_supplierForest_actual_023958
  · exact g32p_supplierForest_actual_023984
  · exact g32p_supplierForest_actual_024057
  · exact g32p_supplierForest_actual_024061
  · exact g32p_supplierForest_actual_024113
  · exact g32p_supplierForest_actual_024118
  · exact g32p_supplierForest_actual_024140
  · exact g32p_supplierForest_actual_024147
  · exact g32p_supplierForest_actual_024202
  · exact g32p_supplierForest_actual_024284
  · exact g32p_supplierForest_actual_024290
  · exact g32p_supplierForest_actual_024306
  · exact g32p_supplierForest_actual_024313
  · exact g32p_supplierForest_actual_024344
  · exact g32p_supplierForest_actual_024353
  · exact g32p_supplierForest_actual_024356
  · exact g32p_supplierForest_actual_024395
  · exact g32p_supplierForest_actual_024441
  · exact g32p_supplierForest_actual_024467
  · exact g32p_supplierForest_actual_024533
  · exact g32p_supplierForest_actual_024540
  · exact g32p_supplierForest_actual_024553
  · exact g32p_supplierForest_actual_024565
  · exact g32p_supplierForest_actual_024570
  · exact g32p_supplierForest_actual_024572
  · exact g32p_supplierForest_actual_024609
  · exact g32p_supplierForest_actual_024620
  · exact g32p_supplierForest_actual_024622
  · exact g32p_supplierForest_actual_024624
  · exact g32p_supplierForest_actual_024648
  · exact g32p_supplierForest_actual_024673
  · exact g32p_supplierForest_actual_024729
  · exact g32p_supplierForest_actual_024737
  · exact g32p_supplierForest_actual_024742
  · exact g32p_supplierForest_actual_024758
  · exact g32p_supplierForest_actual_024788
  · exact g32p_supplierForest_actual_024790
  · exact g32p_supplierForest_actual_024799
  · exact g32p_supplierForest_actual_024857
  · exact g32p_supplierForest_actual_024894
  · exact g32p_supplierForest_actual_024911
  · exact g32p_supplierForest_actual_024916
  · exact g32p_supplierForest_actual_024930
  · exact g32p_supplierForest_actual_024932
  · exact g32p_supplierForest_actual_025007
  · exact g32p_supplierForest_actual_025018
  · exact g32p_supplierForest_actual_025031
  · exact g32p_supplierForest_actual_025099
  · exact g32p_supplierForest_actual_025110
  · exact g32p_supplierForest_actual_025124
  · exact g32p_supplierForest_actual_025146
  · exact g32p_supplierForest_actual_025154
  · exact g32p_supplierForest_actual_025155
  · exact g32p_supplierForest_actual_025174
  · exact g32p_supplierForest_actual_025181
  · exact g32p_supplierForest_actual_025185
  · exact g32p_supplierForest_actual_025210
  · exact g32p_supplierForest_actual_025218
  · exact g32p_supplierForest_actual_025255
  · exact g32p_supplierForest_actual_025281
  · exact g32p_supplierForest_actual_025299
  · exact g32p_supplierForest_actual_025342
  · exact g32p_supplierForest_actual_025368
  · exact g32p_supplierForest_actual_025382
  · exact g32p_supplierForest_actual_025420
  · exact g32p_supplierForest_actual_025425
  · exact g32p_supplierForest_actual_025469
  · exact g32p_supplierForest_actual_025470
  · exact g32p_supplierForest_actual_025476
  · exact g32p_supplierForest_actual_025523
  · exact g32p_supplierForest_actual_025545
  · exact g32p_supplierForest_actual_025553
  · exact g32p_supplierForest_actual_025562
  · exact g32p_supplierForest_actual_025600
  · exact g32p_supplierForest_actual_025607
  · exact g32p_supplierForest_actual_025653
  · exact g32p_supplierForest_actual_025662
  · exact g32p_supplierForest_actual_025684
  · exact g32p_supplierForest_actual_025691
  · exact g32p_supplierForest_actual_025695
  · exact g32p_supplierForest_actual_025720
  · exact g32p_supplierForest_actual_025769
  · exact g32p_supplierForest_actual_025776
  · exact g32p_supplierForest_actual_025787
  · exact g32p_supplierForest_actual_025788
  · exact g32p_supplierForest_actual_025809
  · exact g32p_supplierForest_actual_025840
  · exact g32p_supplierForest_actual_025852
  · exact g32p_supplierForest_actual_025925
  · exact g32p_supplierForest_actual_025948
  · exact g32p_supplierForest_actual_025957
  · exact g32p_supplierForest_actual_025963
  · exact g32p_supplierForest_actual_025970
  · exact g32p_supplierForest_actual_026016
  · exact g32p_supplierForest_actual_026054
  · exact g32p_supplierForest_actual_026061
  · exact g32p_supplierForest_actual_026078
  · exact g32p_supplierForest_actual_026114
  · exact g32p_supplierForest_actual_026119
  · exact g32p_supplierForest_actual_026165
  · exact g32p_supplierForest_actual_026168
  · exact g32p_supplierForest_actual_026194
  · exact g32p_supplierForest_actual_026253
  · exact g32p_supplierForest_actual_026277
  · exact g32p_supplierForest_actual_026332
  · exact g32p_supplierForest_actual_026337
  · exact g32p_supplierForest_actual_026383
  · exact g32p_supplierForest_actual_026391
  · exact g32p_supplierForest_actual_026455
  · exact g32p_supplierForest_actual_026477
  · exact g32p_supplierForest_actual_026545
  · exact g32p_supplierForest_actual_026589
  · exact g32p_supplierForest_actual_026626
  · exact g32p_supplierForest_actual_026633
  · exact g32p_supplierForest_actual_026649
  · exact g32p_supplierForest_actual_026707
  · exact g32p_supplierForest_actual_026708
  · exact g32p_supplierForest_actual_026719
  · exact g32p_supplierForest_actual_026746
  · exact g32p_supplierForest_actual_026776
  · exact g32p_supplierForest_actual_026820
  · exact g32p_supplierForest_actual_026831
  · exact g32p_supplierForest_actual_026832
  · exact g32p_supplierForest_actual_026868
  · exact g32p_supplierForest_actual_026881
  · exact g32p_supplierForest_actual_026907
  · exact g32p_supplierForest_actual_026931
  · exact g32p_supplierForest_actual_026963
  · exact g32p_supplierForest_actual_027005
  · exact g32p_supplierForest_actual_027010
  · exact g32p_supplierForest_actual_027016
  · exact g32p_supplierForest_actual_027066
  · exact g32p_supplierForest_actual_027073
  · exact g32p_supplierForest_actual_027084
  · exact g32p_supplierForest_actual_027092
  · exact g32p_supplierForest_actual_027117
  · exact g32p_supplierForest_actual_027126
  · exact g32p_supplierForest_actual_027214
  · exact g32p_supplierForest_actual_027216
  · exact g32p_supplierForest_actual_027217
  · exact g32p_supplierForest_actual_027229
  · exact g32p_supplierForest_actual_027257
  · exact g32p_supplierForest_actual_027269
  · exact g32p_supplierForest_actual_027283
  · exact g32p_supplierForest_actual_027319
  · exact g32p_supplierForest_actual_027369
  · exact g32p_supplierForest_actual_027395
  · exact g32p_supplierForest_actual_027408
  · exact g32p_supplierForest_actual_027449
  · exact g32p_supplierForest_actual_027455
  · exact g32p_supplierForest_actual_027474
  · exact g32p_supplierForest_actual_027505
  · exact g32p_supplierForest_actual_027567
  · exact g32p_supplierForest_actual_027572
  · exact g32p_supplierForest_actual_027588
  · exact g32p_supplierForest_actual_027590
  · exact g32p_supplierForest_actual_027627
  · exact g32p_supplierForest_actual_027633
  · exact g32p_supplierForest_actual_027640
  · exact g32p_supplierForest_actual_027649
  · exact g32p_supplierForest_actual_027652
  · exact g32p_supplierForest_actual_027653
  · exact g32p_supplierForest_actual_027716
  · exact g32p_supplierForest_actual_027733
  · exact g32p_supplierForest_actual_027754
  · exact g32p_supplierForest_actual_027835
  · exact g32p_supplierForest_actual_027853
  · exact g32p_supplierForest_actual_027871
  · exact g32p_supplierForest_actual_027880
  · exact g32p_supplierForest_actual_027894
  · exact g32p_supplierForest_actual_027946
  · exact g32p_supplierForest_actual_027955
  · exact g32p_supplierForest_actual_027957
  · exact g32p_supplierForest_actual_028030
  · exact g32p_supplierForest_actual_028071
  · exact g32p_supplierForest_actual_028224
  · exact g32p_supplierForest_actual_028231
  · exact g32p_supplierForest_actual_028240
  · exact g32p_supplierForest_actual_028261
  · exact g32p_supplierForest_actual_028264
  · exact g32p_supplierForest_actual_028265
  · exact g32p_supplierForest_actual_028277
  · exact g32p_supplierForest_actual_028281
  · exact g32p_supplierForest_actual_028302
  · exact g32p_supplierForest_actual_028324
  · exact g32p_supplierForest_actual_028331
  · exact g32p_supplierForest_actual_028348
  · exact g32p_supplierForest_actual_028359
  · exact g32p_supplierForest_actual_028367
  · exact g32p_supplierForest_actual_028372
  · exact g32p_supplierForest_actual_028375
  · exact g32p_supplierForest_actual_028391
  · exact g32p_supplierForest_actual_028399
  · exact g32p_supplierForest_actual_028406
  · exact g32p_supplierForest_actual_028416
  · exact g32p_supplierForest_actual_028430
  · exact g32p_supplierForest_actual_028440
  · exact g32p_supplierForest_actual_028461
  · exact g32p_supplierForest_actual_028471
  · exact g32p_supplierForest_actual_028506
  · exact g32p_supplierForest_actual_028527
  · exact g32p_supplierForest_actual_028549
  · exact g32p_supplierForest_actual_028579
  · exact g32p_supplierForest_actual_028636
  · exact g32p_supplierForest_actual_028664
  · exact g32p_supplierForest_actual_028667
  · exact g32p_supplierForest_actual_028696
  · exact g32p_supplierForest_actual_028705
  · exact g32p_supplierForest_actual_028725
  · exact g32p_supplierForest_actual_028733
  · exact g32p_supplierForest_actual_028742
  · exact g32p_supplierForest_actual_028759
  · exact g32p_supplierForest_actual_028763
  · exact g32p_supplierForest_actual_028777
  · exact g32p_supplierForest_actual_028792
  · exact g32p_supplierForest_actual_028793
  · exact g32p_supplierForest_actual_028797
  · exact g32p_supplierForest_actual_028804
  · exact g32p_supplierForest_actual_028822
  · exact g32p_supplierForest_actual_028827
  · exact g32p_supplierForest_actual_028855
  · exact g32p_supplierForest_actual_028865

def g32p_supplierForest_nodes_061 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_028883 else g32p_supplierForest_node_028891) else (if i.val < 3 then g32p_supplierForest_node_028904 else g32p_supplierForest_node_028905)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_028913 else g32p_supplierForest_node_028987) else (if i.val < 7 then g32p_supplierForest_node_029004 else g32p_supplierForest_node_029033))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_029076 else g32p_supplierForest_node_029078) else (if i.val < 11 then g32p_supplierForest_node_029144 else g32p_supplierForest_node_029163)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_029170 else g32p_supplierForest_node_029202) else (if i.val < 15 then g32p_supplierForest_node_029225 else g32p_supplierForest_node_029238)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_029250 else g32p_supplierForest_node_029256) else (if i.val < 19 then g32p_supplierForest_node_029317 else g32p_supplierForest_node_029320)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_029332 else g32p_supplierForest_node_029339) else (if i.val < 23 then g32p_supplierForest_node_029348 else g32p_supplierForest_node_029353))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_029371 else g32p_supplierForest_node_029385) else (if i.val < 27 then g32p_supplierForest_node_029441 else g32p_supplierForest_node_029451)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_029463 else g32p_supplierForest_node_029471) else (if i.val < 31 then g32p_supplierForest_node_029476 else g32p_supplierForest_node_029503))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_029530 else g32p_supplierForest_node_029551) else (if i.val < 35 then g32p_supplierForest_node_029559 else g32p_supplierForest_node_029565)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_029574 else g32p_supplierForest_node_029579) else (if i.val < 39 then g32p_supplierForest_node_029585 else g32p_supplierForest_node_029588))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_029627 else g32p_supplierForest_node_029643) else (if i.val < 43 then g32p_supplierForest_node_029644 else g32p_supplierForest_node_029648)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_029656 else g32p_supplierForest_node_029662) else (if i.val < 47 then g32p_supplierForest_node_029697 else g32p_supplierForest_node_029698)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_029726 else g32p_supplierForest_node_029773) else (if i.val < 51 then g32p_supplierForest_node_029804 else g32p_supplierForest_node_029810)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_029837 else g32p_supplierForest_node_029840) else (if i.val < 55 then g32p_supplierForest_node_029843 else g32p_supplierForest_node_029853))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_029872 else g32p_supplierForest_node_029882) else (if i.val < 59 then g32p_supplierForest_node_029890 else g32p_supplierForest_node_029913)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_029932 else g32p_supplierForest_node_029964) else (if i.val < 63 then g32p_supplierForest_node_030027 else g32p_supplierForest_node_030052)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_030057 else g32p_supplierForest_node_030079) else (if i.val < 67 then g32p_supplierForest_node_030114 else g32p_supplierForest_node_030128)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_030151 else g32p_supplierForest_node_030163) else (if i.val < 71 then g32p_supplierForest_node_030180 else g32p_supplierForest_node_030183))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_030213 else g32p_supplierForest_node_030218) else (if i.val < 75 then g32p_supplierForest_node_030261 else g32p_supplierForest_node_030280)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_030324 else g32p_supplierForest_node_030361) else (if i.val < 79 then g32p_supplierForest_node_030364 else g32p_supplierForest_node_030384)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_030399 else g32p_supplierForest_node_030407) else (if i.val < 83 then g32p_supplierForest_node_030426 else g32p_supplierForest_node_030428)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_030491 else g32p_supplierForest_node_030496) else (if i.val < 87 then g32p_supplierForest_node_030563 else g32p_supplierForest_node_030573))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_030585 else g32p_supplierForest_node_030601) else (if i.val < 91 then g32p_supplierForest_node_030613 else g32p_supplierForest_node_030621)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_030638 else g32p_supplierForest_node_030641) else (if i.val < 95 then g32p_supplierForest_node_030654 else g32p_supplierForest_node_030683))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_030698 else g32p_supplierForest_node_030712) else (if i.val < 99 then g32p_supplierForest_node_030726 else g32p_supplierForest_node_030728)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_030754 else g32p_supplierForest_node_030769) else (if i.val < 103 then g32p_supplierForest_node_030795 else g32p_supplierForest_node_030796))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_030809 else g32p_supplierForest_node_030820) else (if i.val < 107 then g32p_supplierForest_node_030823 else g32p_supplierForest_node_030827)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_030840 else g32p_supplierForest_node_030855) else (if i.val < 111 then g32p_supplierForest_node_030860 else g32p_supplierForest_node_030863)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_030942 else g32p_supplierForest_node_030954) else (if i.val < 115 then g32p_supplierForest_node_030955 else g32p_supplierForest_node_030972)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_030973 else g32p_supplierForest_node_030974) else (if i.val < 119 then g32p_supplierForest_node_031002 else g32p_supplierForest_node_031037))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_031042 else g32p_supplierForest_node_031043) else (if i.val < 123 then g32p_supplierForest_node_031054 else g32p_supplierForest_node_031067)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_031073 else g32p_supplierForest_node_031110) else (if i.val < 127 then g32p_supplierForest_node_031137 else g32p_supplierForest_node_031147))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_031190 else g32p_supplierForest_node_031193) else (if i.val < 131 then g32p_supplierForest_node_031196 else g32p_supplierForest_node_031203)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_031214 else g32p_supplierForest_node_031229) else (if i.val < 135 then g32p_supplierForest_node_031265 else g32p_supplierForest_node_031314))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_031325 else g32p_supplierForest_node_031333) else (if i.val < 139 then g32p_supplierForest_node_031342 else g32p_supplierForest_node_031383)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_031384 else g32p_supplierForest_node_031441) else (if i.val < 143 then g32p_supplierForest_node_031459 else g32p_supplierForest_node_031465)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_031474 else g32p_supplierForest_node_031475) else (if i.val < 147 then g32p_supplierForest_node_031495 else g32p_supplierForest_node_031501)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_031505 else g32p_supplierForest_node_031509) else (if i.val < 151 then g32p_supplierForest_node_031522 else g32p_supplierForest_node_031551))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_031553 else g32p_supplierForest_node_031565) else (if i.val < 155 then g32p_supplierForest_node_031570 else g32p_supplierForest_node_031635)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_031695 else g32p_supplierForest_node_031708) else (if i.val < 159 then g32p_supplierForest_node_031726 else g32p_supplierForest_node_031728))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_031742 else g32p_supplierForest_node_031756) else (if i.val < 163 then g32p_supplierForest_node_031766 else g32p_supplierForest_node_031778)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_031799 else g32p_supplierForest_node_031814) else (if i.val < 167 then g32p_supplierForest_node_031837 else g32p_supplierForest_node_031848))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_031849 else g32p_supplierForest_node_031872) else (if i.val < 171 then g32p_supplierForest_node_031881 else g32p_supplierForest_node_031899)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_031933 else g32p_supplierForest_node_031965) else (if i.val < 175 then g32p_supplierForest_node_031993 else g32p_supplierForest_node_032003)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_032087 else g32p_supplierForest_node_032110) else (if i.val < 179 then g32p_supplierForest_node_032128 else g32p_supplierForest_node_032133)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_032137 else g32p_supplierForest_node_032139) else (if i.val < 183 then g32p_supplierForest_node_032147 else g32p_supplierForest_node_032152))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_032163 else g32p_supplierForest_node_032225) else (if i.val < 187 then g32p_supplierForest_node_032279 else g32p_supplierForest_node_032285)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_032303 else g32p_supplierForest_node_032311) else (if i.val < 191 then g32p_supplierForest_node_032345 else g32p_supplierForest_node_032350)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_032354 else g32p_supplierForest_node_032375) else (if i.val < 195 then g32p_supplierForest_node_032383 else g32p_supplierForest_node_032387)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_032428 else g32p_supplierForest_node_032455) else (if i.val < 199 then g32p_supplierForest_node_032456 else g32p_supplierForest_node_032495))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_032520 else g32p_supplierForest_node_032527) else (if i.val < 203 then g32p_supplierForest_node_032543 else g32p_supplierForest_node_032560)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_032566 else g32p_supplierForest_node_032574) else (if i.val < 207 then g32p_supplierForest_node_032575 else g32p_supplierForest_node_032599)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_032629 else g32p_supplierForest_node_032649) else (if i.val < 211 then g32p_supplierForest_node_032728 else g32p_supplierForest_node_032732)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_032805 else g32p_supplierForest_node_032818) else (if i.val < 215 then g32p_supplierForest_node_032871 else g32p_supplierForest_node_032930))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_032968 else g32p_supplierForest_node_033000) else (if i.val < 219 then g32p_supplierForest_node_033008 else g32p_supplierForest_node_033075)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_033078 else g32p_supplierForest_node_033127) else (if i.val < 223 then g32p_supplierForest_node_033128 else g32p_supplierForest_node_033160))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_033187 else g32p_supplierForest_node_033235) else (if i.val < 227 then g32p_supplierForest_node_033291 else g32p_supplierForest_node_033327)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_033333 else g32p_supplierForest_node_033343) else (if i.val < 231 then g32p_supplierForest_node_033380 else g32p_supplierForest_node_033430))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_033500 else g32p_supplierForest_node_033502) else (if i.val < 235 then g32p_supplierForest_node_033503 else g32p_supplierForest_node_033506)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_033519 else g32p_supplierForest_node_033535) else (if i.val < 239 then g32p_supplierForest_node_033547 else g32p_supplierForest_node_033557)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_033570 else g32p_supplierForest_node_033575) else (if i.val < 243 then g32p_supplierForest_node_033576 else g32p_supplierForest_node_033583)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_033593 else g32p_supplierForest_node_033617) else (if i.val < 247 then g32p_supplierForest_node_033628 else g32p_supplierForest_node_033630))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_033659 else g32p_supplierForest_node_033669) else (if i.val < 251 then g32p_supplierForest_node_033670 else g32p_supplierForest_node_033705)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_033723 else g32p_supplierForest_node_033745) else (if i.val < 255 then g32p_supplierForest_node_033765 else g32p_supplierForest_node_033780))))))))

def g32p_supplierForest_classes_061 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 34 else 57) else (if i.val < 3 then 17 else 14)) else (if i.val < 6 then (if i.val < 5 then 32 else 32) else (if i.val < 7 then 30 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 59 else 57) else (if i.val < 11 then 32 else 57)) else (if i.val < 14 then (if i.val < 13 then 57 else 31) else (if i.val < 15 then 32 else 36)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 57 else 57) else (if i.val < 19 then 16 else 30)) else (if i.val < 22 then (if i.val < 21 then 59 else 64) else (if i.val < 23 then 57 else 32))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 3) else (if i.val < 27 then 15 else 30)) else (if i.val < 30 then (if i.val < 29 then 57 else 30) else (if i.val < 31 then 57 else 59))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 30 else 16) else (if i.val < 35 then 60 else 36)) else (if i.val < 38 then (if i.val < 37 then 17 else 58) else (if i.val < 39 then 57 else 16))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 36 else 16) else (if i.val < 43 then 59 else 57)) else (if i.val < 46 then (if i.val < 45 then 15 else 30) else (if i.val < 47 then 4 else 59)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 57 else 57) else (if i.val < 51 then 60 else 35)) else (if i.val < 54 then (if i.val < 53 then 57 else 30) else (if i.val < 55 then 16 else 32))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 16 else 30) else (if i.val < 59 then 16 else 31)) else (if i.val < 62 then (if i.val < 61 then 16 else 33) else (if i.val < 63 then 32 else 14)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 15 else 30) else (if i.val < 67 then 30 else 30)) else (if i.val < 70 then (if i.val < 69 then 60 else 35) else (if i.val < 71 then 57 else 57))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 14 else 63) else (if i.val < 75 then 16 else 16)) else (if i.val < 78 then (if i.val < 77 then 57 else 29) else (if i.val < 79 then 57 else 16)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 15 else 57) else (if i.val < 83 then 58 else 57)) else (if i.val < 86 then (if i.val < 85 then 32 else 16) else (if i.val < 87 then 16 else 57))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 57 else 57) else (if i.val < 91 then 31 else 4)) else (if i.val < 94 then (if i.val < 93 then 30 else 63) else (if i.val < 95 then 16 else 15))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 57 else 16) else (if i.val < 99 then 66 else 4)) else (if i.val < 102 then (if i.val < 101 then 66 else 32) else (if i.val < 103 then 57 else 65))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 35 else 57) else (if i.val < 107 then 32 else 16)) else (if i.val < 110 then (if i.val < 109 then 57 else 57) else (if i.val < 111 then 16 else 14)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 30 else 57) else (if i.val < 115 then 57 else 33)) else (if i.val < 118 then (if i.val < 117 then 30 else 32) else (if i.val < 119 then 31 else 15))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 30 else 32) else (if i.val < 123 then 30 else 30)) else (if i.val < 126 then (if i.val < 125 then 57 else 62) else (if i.val < 127 then 64 else 30))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 4 else 30) else (if i.val < 131 then 57 else 30)) else (if i.val < 134 then (if i.val < 133 then 16 else 16) else (if i.val < 135 then 34 else 14))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 4 else 57) else (if i.val < 139 then 60 else 64)) else (if i.val < 142 then (if i.val < 141 then 63 else 64) else (if i.val < 143 then 30 else 57)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 16 else 30) else (if i.val < 147 then 16 else 30)) else (if i.val < 150 then (if i.val < 149 then 30 else 16) else (if i.val < 151 then 65 else 16))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 32 else 63) else (if i.val < 155 then 64 else 32)) else (if i.val < 158 then (if i.val < 157 then 30 else 36) else (if i.val < 159 then 57 else 59))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 57 else 63) else (if i.val < 163 then 57 else 57)) else (if i.val < 166 then (if i.val < 165 then 57 else 30) else (if i.val < 167 then 59 else 57))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 30 else 57) else (if i.val < 171 then 30 else 30)) else (if i.val < 174 then (if i.val < 173 then 57 else 4) else (if i.val < 175 then 30 else 64)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 59 else 17) else (if i.val < 179 then 16 else 60)) else (if i.val < 182 then (if i.val < 181 then 36 else 59) else (if i.val < 183 then 17 else 57))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 15 else 30) else (if i.val < 187 then 57 else 58)) else (if i.val < 190 then (if i.val < 189 then 16 else 57) else (if i.val < 191 then 63 else 4)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 32 else 57) else (if i.val < 195 then 30 else 59)) else (if i.val < 198 then (if i.val < 197 then 57 else 63) else (if i.val < 199 then 64 else 30))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 31 else 36) else (if i.val < 203 then 34 else 57)) else (if i.val < 206 then (if i.val < 205 then 59 else 59) else (if i.val < 207 then 58 else 31)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 14 else 17) else (if i.val < 211 then 15 else 60)) else (if i.val < 214 then (if i.val < 213 then 30 else 16) else (if i.val < 215 then 34 else 30))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 16 else 59) else (if i.val < 219 then 30 else 15)) else (if i.val < 222 then (if i.val < 221 then 16 else 15) else (if i.val < 223 then 57 else 16))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 16 else 29) else (if i.val < 227 then 31 else 57)) else (if i.val < 230 then (if i.val < 229 then 32 else 30) else (if i.val < 231 then 30 else 57))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 29 else 14) else (if i.val < 235 then 30 else 29)) else (if i.val < 238 then (if i.val < 237 then 17 else 58) else (if i.val < 239 then 59 else 33)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 16 else 15) else (if i.val < 243 then 30 else 17)) else (if i.val < 246 then (if i.val < 245 then 59 else 17) else (if i.val < 247 then 16 else 57))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 57 else 15) else (if i.val < 251 then 14 else 30)) else (if i.val < 254 then (if i.val < 253 then 29 else 16) else (if i.val < 255 then 30 else 15))))))))

theorem g32p_supplierForest_actual_061 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_061 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_061 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_028883
  · exact g32p_supplierForest_actual_028891
  · exact g32p_supplierForest_actual_028904
  · exact g32p_supplierForest_actual_028905
  · exact g32p_supplierForest_actual_028913
  · exact g32p_supplierForest_actual_028987
  · exact g32p_supplierForest_actual_029004
  · exact g32p_supplierForest_actual_029033
  · exact g32p_supplierForest_actual_029076
  · exact g32p_supplierForest_actual_029078
  · exact g32p_supplierForest_actual_029144
  · exact g32p_supplierForest_actual_029163
  · exact g32p_supplierForest_actual_029170
  · exact g32p_supplierForest_actual_029202
  · exact g32p_supplierForest_actual_029225
  · exact g32p_supplierForest_actual_029238
  · exact g32p_supplierForest_actual_029250
  · exact g32p_supplierForest_actual_029256
  · exact g32p_supplierForest_actual_029317
  · exact g32p_supplierForest_actual_029320
  · exact g32p_supplierForest_actual_029332
  · exact g32p_supplierForest_actual_029339
  · exact g32p_supplierForest_actual_029348
  · exact g32p_supplierForest_actual_029353
  · exact g32p_supplierForest_actual_029371
  · exact g32p_supplierForest_actual_029385
  · exact g32p_supplierForest_actual_029441
  · exact g32p_supplierForest_actual_029451
  · exact g32p_supplierForest_actual_029463
  · exact g32p_supplierForest_actual_029471
  · exact g32p_supplierForest_actual_029476
  · exact g32p_supplierForest_actual_029503
  · exact g32p_supplierForest_actual_029530
  · exact g32p_supplierForest_actual_029551
  · exact g32p_supplierForest_actual_029559
  · exact g32p_supplierForest_actual_029565
  · exact g32p_supplierForest_actual_029574
  · exact g32p_supplierForest_actual_029579
  · exact g32p_supplierForest_actual_029585
  · exact g32p_supplierForest_actual_029588
  · exact g32p_supplierForest_actual_029627
  · exact g32p_supplierForest_actual_029643
  · exact g32p_supplierForest_actual_029644
  · exact g32p_supplierForest_actual_029648
  · exact g32p_supplierForest_actual_029656
  · exact g32p_supplierForest_actual_029662
  · exact g32p_supplierForest_actual_029697
  · exact g32p_supplierForest_actual_029698
  · exact g32p_supplierForest_actual_029726
  · exact g32p_supplierForest_actual_029773
  · exact g32p_supplierForest_actual_029804
  · exact g32p_supplierForest_actual_029810
  · exact g32p_supplierForest_actual_029837
  · exact g32p_supplierForest_actual_029840
  · exact g32p_supplierForest_actual_029843
  · exact g32p_supplierForest_actual_029853
  · exact g32p_supplierForest_actual_029872
  · exact g32p_supplierForest_actual_029882
  · exact g32p_supplierForest_actual_029890
  · exact g32p_supplierForest_actual_029913
  · exact g32p_supplierForest_actual_029932
  · exact g32p_supplierForest_actual_029964
  · exact g32p_supplierForest_actual_030027
  · exact g32p_supplierForest_actual_030052
  · exact g32p_supplierForest_actual_030057
  · exact g32p_supplierForest_actual_030079
  · exact g32p_supplierForest_actual_030114
  · exact g32p_supplierForest_actual_030128
  · exact g32p_supplierForest_actual_030151
  · exact g32p_supplierForest_actual_030163
  · exact g32p_supplierForest_actual_030180
  · exact g32p_supplierForest_actual_030183
  · exact g32p_supplierForest_actual_030213
  · exact g32p_supplierForest_actual_030218
  · exact g32p_supplierForest_actual_030261
  · exact g32p_supplierForest_actual_030280
  · exact g32p_supplierForest_actual_030324
  · exact g32p_supplierForest_actual_030361
  · exact g32p_supplierForest_actual_030364
  · exact g32p_supplierForest_actual_030384
  · exact g32p_supplierForest_actual_030399
  · exact g32p_supplierForest_actual_030407
  · exact g32p_supplierForest_actual_030426
  · exact g32p_supplierForest_actual_030428
  · exact g32p_supplierForest_actual_030491
  · exact g32p_supplierForest_actual_030496
  · exact g32p_supplierForest_actual_030563
  · exact g32p_supplierForest_actual_030573
  · exact g32p_supplierForest_actual_030585
  · exact g32p_supplierForest_actual_030601
  · exact g32p_supplierForest_actual_030613
  · exact g32p_supplierForest_actual_030621
  · exact g32p_supplierForest_actual_030638
  · exact g32p_supplierForest_actual_030641
  · exact g32p_supplierForest_actual_030654
  · exact g32p_supplierForest_actual_030683
  · exact g32p_supplierForest_actual_030698
  · exact g32p_supplierForest_actual_030712
  · exact g32p_supplierForest_actual_030726
  · exact g32p_supplierForest_actual_030728
  · exact g32p_supplierForest_actual_030754
  · exact g32p_supplierForest_actual_030769
  · exact g32p_supplierForest_actual_030795
  · exact g32p_supplierForest_actual_030796
  · exact g32p_supplierForest_actual_030809
  · exact g32p_supplierForest_actual_030820
  · exact g32p_supplierForest_actual_030823
  · exact g32p_supplierForest_actual_030827
  · exact g32p_supplierForest_actual_030840
  · exact g32p_supplierForest_actual_030855
  · exact g32p_supplierForest_actual_030860
  · exact g32p_supplierForest_actual_030863
  · exact g32p_supplierForest_actual_030942
  · exact g32p_supplierForest_actual_030954
  · exact g32p_supplierForest_actual_030955
  · exact g32p_supplierForest_actual_030972
  · exact g32p_supplierForest_actual_030973
  · exact g32p_supplierForest_actual_030974
  · exact g32p_supplierForest_actual_031002
  · exact g32p_supplierForest_actual_031037
  · exact g32p_supplierForest_actual_031042
  · exact g32p_supplierForest_actual_031043
  · exact g32p_supplierForest_actual_031054
  · exact g32p_supplierForest_actual_031067
  · exact g32p_supplierForest_actual_031073
  · exact g32p_supplierForest_actual_031110
  · exact g32p_supplierForest_actual_031137
  · exact g32p_supplierForest_actual_031147
  · exact g32p_supplierForest_actual_031190
  · exact g32p_supplierForest_actual_031193
  · exact g32p_supplierForest_actual_031196
  · exact g32p_supplierForest_actual_031203
  · exact g32p_supplierForest_actual_031214
  · exact g32p_supplierForest_actual_031229
  · exact g32p_supplierForest_actual_031265
  · exact g32p_supplierForest_actual_031314
  · exact g32p_supplierForest_actual_031325
  · exact g32p_supplierForest_actual_031333
  · exact g32p_supplierForest_actual_031342
  · exact g32p_supplierForest_actual_031383
  · exact g32p_supplierForest_actual_031384
  · exact g32p_supplierForest_actual_031441
  · exact g32p_supplierForest_actual_031459
  · exact g32p_supplierForest_actual_031465
  · exact g32p_supplierForest_actual_031474
  · exact g32p_supplierForest_actual_031475
  · exact g32p_supplierForest_actual_031495
  · exact g32p_supplierForest_actual_031501
  · exact g32p_supplierForest_actual_031505
  · exact g32p_supplierForest_actual_031509
  · exact g32p_supplierForest_actual_031522
  · exact g32p_supplierForest_actual_031551
  · exact g32p_supplierForest_actual_031553
  · exact g32p_supplierForest_actual_031565
  · exact g32p_supplierForest_actual_031570
  · exact g32p_supplierForest_actual_031635
  · exact g32p_supplierForest_actual_031695
  · exact g32p_supplierForest_actual_031708
  · exact g32p_supplierForest_actual_031726
  · exact g32p_supplierForest_actual_031728
  · exact g32p_supplierForest_actual_031742
  · exact g32p_supplierForest_actual_031756
  · exact g32p_supplierForest_actual_031766
  · exact g32p_supplierForest_actual_031778
  · exact g32p_supplierForest_actual_031799
  · exact g32p_supplierForest_actual_031814
  · exact g32p_supplierForest_actual_031837
  · exact g32p_supplierForest_actual_031848
  · exact g32p_supplierForest_actual_031849
  · exact g32p_supplierForest_actual_031872
  · exact g32p_supplierForest_actual_031881
  · exact g32p_supplierForest_actual_031899
  · exact g32p_supplierForest_actual_031933
  · exact g32p_supplierForest_actual_031965
  · exact g32p_supplierForest_actual_031993
  · exact g32p_supplierForest_actual_032003
  · exact g32p_supplierForest_actual_032087
  · exact g32p_supplierForest_actual_032110
  · exact g32p_supplierForest_actual_032128
  · exact g32p_supplierForest_actual_032133
  · exact g32p_supplierForest_actual_032137
  · exact g32p_supplierForest_actual_032139
  · exact g32p_supplierForest_actual_032147
  · exact g32p_supplierForest_actual_032152
  · exact g32p_supplierForest_actual_032163
  · exact g32p_supplierForest_actual_032225
  · exact g32p_supplierForest_actual_032279
  · exact g32p_supplierForest_actual_032285
  · exact g32p_supplierForest_actual_032303
  · exact g32p_supplierForest_actual_032311
  · exact g32p_supplierForest_actual_032345
  · exact g32p_supplierForest_actual_032350
  · exact g32p_supplierForest_actual_032354
  · exact g32p_supplierForest_actual_032375
  · exact g32p_supplierForest_actual_032383
  · exact g32p_supplierForest_actual_032387
  · exact g32p_supplierForest_actual_032428
  · exact g32p_supplierForest_actual_032455
  · exact g32p_supplierForest_actual_032456
  · exact g32p_supplierForest_actual_032495
  · exact g32p_supplierForest_actual_032520
  · exact g32p_supplierForest_actual_032527
  · exact g32p_supplierForest_actual_032543
  · exact g32p_supplierForest_actual_032560
  · exact g32p_supplierForest_actual_032566
  · exact g32p_supplierForest_actual_032574
  · exact g32p_supplierForest_actual_032575
  · exact g32p_supplierForest_actual_032599
  · exact g32p_supplierForest_actual_032629
  · exact g32p_supplierForest_actual_032649
  · exact g32p_supplierForest_actual_032728
  · exact g32p_supplierForest_actual_032732
  · exact g32p_supplierForest_actual_032805
  · exact g32p_supplierForest_actual_032818
  · exact g32p_supplierForest_actual_032871
  · exact g32p_supplierForest_actual_032930
  · exact g32p_supplierForest_actual_032968
  · exact g32p_supplierForest_actual_033000
  · exact g32p_supplierForest_actual_033008
  · exact g32p_supplierForest_actual_033075
  · exact g32p_supplierForest_actual_033078
  · exact g32p_supplierForest_actual_033127
  · exact g32p_supplierForest_actual_033128
  · exact g32p_supplierForest_actual_033160
  · exact g32p_supplierForest_actual_033187
  · exact g32p_supplierForest_actual_033235
  · exact g32p_supplierForest_actual_033291
  · exact g32p_supplierForest_actual_033327
  · exact g32p_supplierForest_actual_033333
  · exact g32p_supplierForest_actual_033343
  · exact g32p_supplierForest_actual_033380
  · exact g32p_supplierForest_actual_033430
  · exact g32p_supplierForest_actual_033500
  · exact g32p_supplierForest_actual_033502
  · exact g32p_supplierForest_actual_033503
  · exact g32p_supplierForest_actual_033506
  · exact g32p_supplierForest_actual_033519
  · exact g32p_supplierForest_actual_033535
  · exact g32p_supplierForest_actual_033547
  · exact g32p_supplierForest_actual_033557
  · exact g32p_supplierForest_actual_033570
  · exact g32p_supplierForest_actual_033575
  · exact g32p_supplierForest_actual_033576
  · exact g32p_supplierForest_actual_033583
  · exact g32p_supplierForest_actual_033593
  · exact g32p_supplierForest_actual_033617
  · exact g32p_supplierForest_actual_033628
  · exact g32p_supplierForest_actual_033630
  · exact g32p_supplierForest_actual_033659
  · exact g32p_supplierForest_actual_033669
  · exact g32p_supplierForest_actual_033670
  · exact g32p_supplierForest_actual_033705
  · exact g32p_supplierForest_actual_033723
  · exact g32p_supplierForest_actual_033745
  · exact g32p_supplierForest_actual_033765
  · exact g32p_supplierForest_actual_033780

def g32p_supplierForest_nodes_062 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_033782 else g32p_supplierForest_node_033787) else (if i.val < 3 then g32p_supplierForest_node_033792 else g32p_supplierForest_node_033809)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_033835 else g32p_supplierForest_node_033954) else (if i.val < 7 then g32p_supplierForest_node_033971 else g32p_supplierForest_node_033993))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_034010 else g32p_supplierForest_node_034038) else (if i.val < 11 then g32p_supplierForest_node_034050 else g32p_supplierForest_node_034051)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_034052 else g32p_supplierForest_node_034055) else (if i.val < 15 then g32p_supplierForest_node_034093 else g32p_supplierForest_node_034114)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_034120 else g32p_supplierForest_node_034156) else (if i.val < 19 then g32p_supplierForest_node_034175 else g32p_supplierForest_node_034204)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_034221 else g32p_supplierForest_node_034231) else (if i.val < 23 then g32p_supplierForest_node_034232 else g32p_supplierForest_node_034270))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_034279 else g32p_supplierForest_node_034288) else (if i.val < 27 then g32p_supplierForest_node_034343 else g32p_supplierForest_node_034346)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_034354 else g32p_supplierForest_node_034372) else (if i.val < 31 then g32p_supplierForest_node_034382 else g32p_supplierForest_node_034428))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_034489 else g32p_supplierForest_node_034491) else (if i.val < 35 then g32p_supplierForest_node_034505 else g32p_supplierForest_node_034520)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_034556 else g32p_supplierForest_node_034605) else (if i.val < 39 then g32p_supplierForest_node_034612 else g32p_supplierForest_node_034621))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_034633 else g32p_supplierForest_node_034638) else (if i.val < 43 then g32p_supplierForest_node_034658 else g32p_supplierForest_node_034711)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_034759 else g32p_supplierForest_node_034791) else (if i.val < 47 then g32p_supplierForest_node_034817 else g32p_supplierForest_node_034828)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_034842 else g32p_supplierForest_node_034843) else (if i.val < 51 then g32p_supplierForest_node_034845 else g32p_supplierForest_node_034852)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_034891 else g32p_supplierForest_node_034904) else (if i.val < 55 then g32p_supplierForest_node_034922 else g32p_supplierForest_node_034993))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_035006 else g32p_supplierForest_node_035022) else (if i.val < 59 then g32p_supplierForest_node_035028 else g32p_supplierForest_node_035044)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_035079 else g32p_supplierForest_node_035084) else (if i.val < 63 then g32p_supplierForest_node_035109 else g32p_supplierForest_node_035149)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_035152 else g32p_supplierForest_node_035164) else (if i.val < 67 then g32p_supplierForest_node_035169 else g32p_supplierForest_node_035195)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_035230 else g32p_supplierForest_node_035232) else (if i.val < 71 then g32p_supplierForest_node_035277 else g32p_supplierForest_node_035332))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_035350 else g32p_supplierForest_node_035351) else (if i.val < 75 then g32p_supplierForest_node_035375 else g32p_supplierForest_node_035384)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_035456 else g32p_supplierForest_node_035472) else (if i.val < 79 then g32p_supplierForest_node_035498 else g32p_supplierForest_node_035527)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_035569 else g32p_supplierForest_node_035580) else (if i.val < 83 then g32p_supplierForest_node_035599 else g32p_supplierForest_node_035603)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_035611 else g32p_supplierForest_node_035612) else (if i.val < 87 then g32p_supplierForest_node_035614 else g32p_supplierForest_node_035636))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_035645 else g32p_supplierForest_node_035646) else (if i.val < 91 then g32p_supplierForest_node_035664 else g32p_supplierForest_node_035688)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_035699 else g32p_supplierForest_node_035750) else (if i.val < 95 then g32p_supplierForest_node_035751 else g32p_supplierForest_node_035753))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_035764 else g32p_supplierForest_node_035802) else (if i.val < 99 then g32p_supplierForest_node_035811 else g32p_supplierForest_node_035822)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_035836 else g32p_supplierForest_node_035845) else (if i.val < 103 then g32p_supplierForest_node_035847 else g32p_supplierForest_node_035870))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_035872 else g32p_supplierForest_node_035874) else (if i.val < 107 then g32p_supplierForest_node_035888 else g32p_supplierForest_node_035904)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_035954 else g32p_supplierForest_node_035965) else (if i.val < 111 then g32p_supplierForest_node_035972 else g32p_supplierForest_node_035985)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_035986 else g32p_supplierForest_node_035990) else (if i.val < 115 then g32p_supplierForest_node_036001 else g32p_supplierForest_node_036010)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_036029 else g32p_supplierForest_node_036039) else (if i.val < 119 then g32p_supplierForest_node_036053 else g32p_supplierForest_node_036072))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_036083 else g32p_supplierForest_node_036103) else (if i.val < 123 then g32p_supplierForest_node_036150 else g32p_supplierForest_node_036187)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_036311 else g32p_supplierForest_node_036331) else (if i.val < 127 then g32p_supplierForest_node_036342 else g32p_supplierForest_node_036388))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_036391 else g32p_supplierForest_node_036440) else (if i.val < 131 then g32p_supplierForest_node_036470 else g32p_supplierForest_node_036479)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_036491 else g32p_supplierForest_node_036495) else (if i.val < 135 then g32p_supplierForest_node_036514 else g32p_supplierForest_node_036522))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_036524 else g32p_supplierForest_node_036555) else (if i.val < 139 then g32p_supplierForest_node_036566 else g32p_supplierForest_node_036595)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_036599 else g32p_supplierForest_node_036604) else (if i.val < 143 then g32p_supplierForest_node_036609 else g32p_supplierForest_node_036650)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_036676 else g32p_supplierForest_node_036699) else (if i.val < 147 then g32p_supplierForest_node_036711 else g32p_supplierForest_node_036716)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_036717 else g32p_supplierForest_node_036722) else (if i.val < 151 then g32p_supplierForest_node_036754 else g32p_supplierForest_node_036765))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_036794 else g32p_supplierForest_node_036815) else (if i.val < 155 then g32p_supplierForest_node_036823 else g32p_supplierForest_node_036824)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_036839 else g32p_supplierForest_node_036857) else (if i.val < 159 then g32p_supplierForest_node_036929 else g32p_supplierForest_node_036947))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_036992 else g32p_supplierForest_node_037017) else (if i.val < 163 then g32p_supplierForest_node_037028 else g32p_supplierForest_node_037036)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_037075 else g32p_supplierForest_node_037157) else (if i.val < 167 then g32p_supplierForest_node_037186 else g32p_supplierForest_node_037190))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_037206 else g32p_supplierForest_node_037207) else (if i.val < 171 then g32p_supplierForest_node_037216 else g32p_supplierForest_node_037220)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_037229 else g32p_supplierForest_node_037234) else (if i.val < 175 then g32p_supplierForest_node_037248 else g32p_supplierForest_node_037259)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_037291 else g32p_supplierForest_node_037327) else (if i.val < 179 then g32p_supplierForest_node_037340 else g32p_supplierForest_node_037360)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_037367 else g32p_supplierForest_node_037373) else (if i.val < 183 then g32p_supplierForest_node_037427 else g32p_supplierForest_node_037429))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_037430 else g32p_supplierForest_node_037520) else (if i.val < 187 then g32p_supplierForest_node_037538 else g32p_supplierForest_node_037549)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_037558 else g32p_supplierForest_node_037576) else (if i.val < 191 then g32p_supplierForest_node_037586 else g32p_supplierForest_node_037610)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_037639 else g32p_supplierForest_node_037647) else (if i.val < 195 then g32p_supplierForest_node_037662 else g32p_supplierForest_node_037668)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_037678 else g32p_supplierForest_node_037724) else (if i.val < 199 then g32p_supplierForest_node_037737 else g32p_supplierForest_node_037756))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_037771 else g32p_supplierForest_node_037778) else (if i.val < 203 then g32p_supplierForest_node_037786 else g32p_supplierForest_node_037793)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_037826 else g32p_supplierForest_node_037844) else (if i.val < 207 then g32p_supplierForest_node_037872 else g32p_supplierForest_node_037950)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_037958 else g32p_supplierForest_node_037963) else (if i.val < 211 then g32p_supplierForest_node_037991 else g32p_supplierForest_node_038009)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_038039 else g32p_supplierForest_node_038046) else (if i.val < 215 then g32p_supplierForest_node_038052 else g32p_supplierForest_node_038063))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_038073 else g32p_supplierForest_node_038074) else (if i.val < 219 then g32p_supplierForest_node_038075 else g32p_supplierForest_node_038096)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_038160 else g32p_supplierForest_node_038164) else (if i.val < 223 then g32p_supplierForest_node_038174 else g32p_supplierForest_node_038218))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_038225 else g32p_supplierForest_node_038238) else (if i.val < 227 then g32p_supplierForest_node_038243 else g32p_supplierForest_node_038248)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_038257 else g32p_supplierForest_node_038282) else (if i.val < 231 then g32p_supplierForest_node_038287 else g32p_supplierForest_node_038310))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_038316 else g32p_supplierForest_node_038346) else (if i.val < 235 then g32p_supplierForest_node_038383 else g32p_supplierForest_node_038384)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_038422 else g32p_supplierForest_node_038478) else (if i.val < 239 then g32p_supplierForest_node_038498 else g32p_supplierForest_node_038503)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_038515 else g32p_supplierForest_node_038525) else (if i.val < 243 then g32p_supplierForest_node_038542 else g32p_supplierForest_node_038622)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_038637 else g32p_supplierForest_node_038654) else (if i.val < 247 then g32p_supplierForest_node_038657 else g32p_supplierForest_node_038689))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_038694 else g32p_supplierForest_node_038706) else (if i.val < 251 then g32p_supplierForest_node_038724 else g32p_supplierForest_node_038751)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_038757 else g32p_supplierForest_node_038758) else (if i.val < 255 then g32p_supplierForest_node_038764 else g32p_supplierForest_node_038775))))))))

def g32p_supplierForest_classes_062 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 30 else 32) else (if i.val < 3 then 4 else 57)) else (if i.val < 6 then (if i.val < 5 then 16 else 57) else (if i.val < 7 then 59 else 63))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 36 else 16) else (if i.val < 11 then 59 else 34)) else (if i.val < 14 then (if i.val < 13 then 32 else 57) else (if i.val < 15 then 16 else 31)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 57 else 36) else (if i.val < 19 then 36 else 32)) else (if i.val < 22 then (if i.val < 21 then 34 else 30) else (if i.val < 23 then 16 else 3))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 35 else 16) else (if i.val < 27 then 63 else 34)) else (if i.val < 30 then (if i.val < 29 then 30 else 32) else (if i.val < 31 then 32 else 57))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 16 else 57) else (if i.val < 35 then 3 else 57)) else (if i.val < 38 then (if i.val < 37 then 15 else 57) else (if i.val < 39 then 30 else 57))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 14 else 59) else (if i.val < 43 then 57 else 15)) else (if i.val < 46 then (if i.val < 45 then 59 else 59) else (if i.val < 47 then 57 else 30)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 33 else 35) else (if i.val < 51 then 16 else 15)) else (if i.val < 54 then (if i.val < 53 then 57 else 62) else (if i.val < 55 then 30 else 58))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 14 else 16) else (if i.val < 59 then 59 else 31)) else (if i.val < 62 then (if i.val < 61 then 57 else 14) else (if i.val < 63 then 57 else 64)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 63 else 36) else (if i.val < 67 then 57 else 63)) else (if i.val < 70 then (if i.val < 69 then 30 else 57) else (if i.val < 71 then 16 else 32))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 57 else 57) else (if i.val < 75 then 57 else 29)) else (if i.val < 78 then (if i.val < 77 then 32 else 62) else (if i.val < 79 then 30 else 57)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 14 else 16) else (if i.val < 83 then 30 else 17)) else (if i.val < 86 then (if i.val < 85 then 16 else 34) else (if i.val < 87 then 16 else 63))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 59 else 60) else (if i.val < 91 then 4 else 16)) else (if i.val < 94 then (if i.val < 93 then 64 else 30) else (if i.val < 95 then 57 else 60))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 57 else 4) else (if i.val < 99 then 61 else 30)) else (if i.val < 102 then (if i.val < 101 then 57 else 16) else (if i.val < 103 then 14 else 30))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 30 else 32) else (if i.val < 107 then 16 else 29)) else (if i.val < 110 then (if i.val < 109 then 63 else 32) else (if i.val < 111 then 32 else 57)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 30 else 32) else (if i.val < 115 then 59 else 30)) else (if i.val < 118 then (if i.val < 117 then 61 else 16) else (if i.val < 119 then 63 else 30))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 35 else 30) else (if i.val < 123 then 57 else 15)) else (if i.val < 126 then (if i.val < 125 then 32 else 57) else (if i.val < 127 then 65 else 57))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 32 else 14) else (if i.val < 131 then 57 else 57)) else (if i.val < 134 then (if i.val < 133 then 60 else 30) else (if i.val < 135 then 30 else 57))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 29 else 30) else (if i.val < 139 then 57 else 57)) else (if i.val < 142 then (if i.val < 141 then 4 else 59) else (if i.val < 143 then 17 else 15)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 59 else 15) else (if i.val < 147 then 30 else 30)) else (if i.val < 150 then (if i.val < 149 then 29 else 32) else (if i.val < 151 then 15 else 33))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 57 else 60) else (if i.val < 155 then 32 else 34)) else (if i.val < 158 then (if i.val < 157 then 30 else 60) else (if i.val < 159 then 14 else 57))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 32 else 32) else (if i.val < 163 then 60 else 16)) else (if i.val < 166 then (if i.val < 165 then 31 else 62) else (if i.val < 167 then 34 else 15))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 60 else 62) else (if i.val < 171 then 58 else 32)) else (if i.val < 174 then (if i.val < 173 then 35 else 30) else (if i.val < 175 then 35 else 36)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 34 else 34) else (if i.val < 179 then 34 else 15)) else (if i.val < 182 then (if i.val < 181 then 15 else 59) else (if i.val < 183 then 30 else 34))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 33 else 30) else (if i.val < 187 then 33 else 14)) else (if i.val < 190 then (if i.val < 189 then 14 else 16) else (if i.val < 191 then 16 else 29)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 16 else 57) else (if i.val < 195 then 30 else 16)) else (if i.val < 198 then (if i.val < 197 then 30 else 16) else (if i.val < 199 then 33 else 14))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 35 else 35) else (if i.val < 203 then 57 else 15)) else (if i.val < 206 then (if i.val < 205 then 15 else 4) else (if i.val < 207 then 17 else 30)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 4 else 64) else (if i.val < 211 then 16 else 32)) else (if i.val < 214 then (if i.val < 213 then 57 else 57) else (if i.val < 215 then 58 else 35))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 62 else 63) else (if i.val < 219 then 59 else 33)) else (if i.val < 222 then (if i.val < 221 then 29 else 15) else (if i.val < 223 then 15 else 30))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 35 else 57) else (if i.val < 227 then 15 else 57)) else (if i.val < 230 then (if i.val < 229 then 35 else 30) else (if i.val < 231 then 30 else 16))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 32 else 57) else (if i.val < 235 then 32 else 57)) else (if i.val < 238 then (if i.val < 237 then 15 else 34) else (if i.val < 239 then 2 else 15)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 63 else 34) else (if i.val < 243 then 16 else 33)) else (if i.val < 246 then (if i.val < 245 then 57 else 31) else (if i.val < 247 then 57 else 32))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 16 else 3) else (if i.val < 251 then 57 else 30)) else (if i.val < 254 then (if i.val < 253 then 58 else 57) else (if i.val < 255 then 30 else 30))))))))

theorem g32p_supplierForest_actual_062 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_062 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_062 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_033782
  · exact g32p_supplierForest_actual_033787
  · exact g32p_supplierForest_actual_033792
  · exact g32p_supplierForest_actual_033809
  · exact g32p_supplierForest_actual_033835
  · exact g32p_supplierForest_actual_033954
  · exact g32p_supplierForest_actual_033971
  · exact g32p_supplierForest_actual_033993
  · exact g32p_supplierForest_actual_034010
  · exact g32p_supplierForest_actual_034038
  · exact g32p_supplierForest_actual_034050
  · exact g32p_supplierForest_actual_034051
  · exact g32p_supplierForest_actual_034052
  · exact g32p_supplierForest_actual_034055
  · exact g32p_supplierForest_actual_034093
  · exact g32p_supplierForest_actual_034114
  · exact g32p_supplierForest_actual_034120
  · exact g32p_supplierForest_actual_034156
  · exact g32p_supplierForest_actual_034175
  · exact g32p_supplierForest_actual_034204
  · exact g32p_supplierForest_actual_034221
  · exact g32p_supplierForest_actual_034231
  · exact g32p_supplierForest_actual_034232
  · exact g32p_supplierForest_actual_034270
  · exact g32p_supplierForest_actual_034279
  · exact g32p_supplierForest_actual_034288
  · exact g32p_supplierForest_actual_034343
  · exact g32p_supplierForest_actual_034346
  · exact g32p_supplierForest_actual_034354
  · exact g32p_supplierForest_actual_034372
  · exact g32p_supplierForest_actual_034382
  · exact g32p_supplierForest_actual_034428
  · exact g32p_supplierForest_actual_034489
  · exact g32p_supplierForest_actual_034491
  · exact g32p_supplierForest_actual_034505
  · exact g32p_supplierForest_actual_034520
  · exact g32p_supplierForest_actual_034556
  · exact g32p_supplierForest_actual_034605
  · exact g32p_supplierForest_actual_034612
  · exact g32p_supplierForest_actual_034621
  · exact g32p_supplierForest_actual_034633
  · exact g32p_supplierForest_actual_034638
  · exact g32p_supplierForest_actual_034658
  · exact g32p_supplierForest_actual_034711
  · exact g32p_supplierForest_actual_034759
  · exact g32p_supplierForest_actual_034791
  · exact g32p_supplierForest_actual_034817
  · exact g32p_supplierForest_actual_034828
  · exact g32p_supplierForest_actual_034842
  · exact g32p_supplierForest_actual_034843
  · exact g32p_supplierForest_actual_034845
  · exact g32p_supplierForest_actual_034852
  · exact g32p_supplierForest_actual_034891
  · exact g32p_supplierForest_actual_034904
  · exact g32p_supplierForest_actual_034922
  · exact g32p_supplierForest_actual_034993
  · exact g32p_supplierForest_actual_035006
  · exact g32p_supplierForest_actual_035022
  · exact g32p_supplierForest_actual_035028
  · exact g32p_supplierForest_actual_035044
  · exact g32p_supplierForest_actual_035079
  · exact g32p_supplierForest_actual_035084
  · exact g32p_supplierForest_actual_035109
  · exact g32p_supplierForest_actual_035149
  · exact g32p_supplierForest_actual_035152
  · exact g32p_supplierForest_actual_035164
  · exact g32p_supplierForest_actual_035169
  · exact g32p_supplierForest_actual_035195
  · exact g32p_supplierForest_actual_035230
  · exact g32p_supplierForest_actual_035232
  · exact g32p_supplierForest_actual_035277
  · exact g32p_supplierForest_actual_035332
  · exact g32p_supplierForest_actual_035350
  · exact g32p_supplierForest_actual_035351
  · exact g32p_supplierForest_actual_035375
  · exact g32p_supplierForest_actual_035384
  · exact g32p_supplierForest_actual_035456
  · exact g32p_supplierForest_actual_035472
  · exact g32p_supplierForest_actual_035498
  · exact g32p_supplierForest_actual_035527
  · exact g32p_supplierForest_actual_035569
  · exact g32p_supplierForest_actual_035580
  · exact g32p_supplierForest_actual_035599
  · exact g32p_supplierForest_actual_035603
  · exact g32p_supplierForest_actual_035611
  · exact g32p_supplierForest_actual_035612
  · exact g32p_supplierForest_actual_035614
  · exact g32p_supplierForest_actual_035636
  · exact g32p_supplierForest_actual_035645
  · exact g32p_supplierForest_actual_035646
  · exact g32p_supplierForest_actual_035664
  · exact g32p_supplierForest_actual_035688
  · exact g32p_supplierForest_actual_035699
  · exact g32p_supplierForest_actual_035750
  · exact g32p_supplierForest_actual_035751
  · exact g32p_supplierForest_actual_035753
  · exact g32p_supplierForest_actual_035764
  · exact g32p_supplierForest_actual_035802
  · exact g32p_supplierForest_actual_035811
  · exact g32p_supplierForest_actual_035822
  · exact g32p_supplierForest_actual_035836
  · exact g32p_supplierForest_actual_035845
  · exact g32p_supplierForest_actual_035847
  · exact g32p_supplierForest_actual_035870
  · exact g32p_supplierForest_actual_035872
  · exact g32p_supplierForest_actual_035874
  · exact g32p_supplierForest_actual_035888
  · exact g32p_supplierForest_actual_035904
  · exact g32p_supplierForest_actual_035954
  · exact g32p_supplierForest_actual_035965
  · exact g32p_supplierForest_actual_035972
  · exact g32p_supplierForest_actual_035985
  · exact g32p_supplierForest_actual_035986
  · exact g32p_supplierForest_actual_035990
  · exact g32p_supplierForest_actual_036001
  · exact g32p_supplierForest_actual_036010
  · exact g32p_supplierForest_actual_036029
  · exact g32p_supplierForest_actual_036039
  · exact g32p_supplierForest_actual_036053
  · exact g32p_supplierForest_actual_036072
  · exact g32p_supplierForest_actual_036083
  · exact g32p_supplierForest_actual_036103
  · exact g32p_supplierForest_actual_036150
  · exact g32p_supplierForest_actual_036187
  · exact g32p_supplierForest_actual_036311
  · exact g32p_supplierForest_actual_036331
  · exact g32p_supplierForest_actual_036342
  · exact g32p_supplierForest_actual_036388
  · exact g32p_supplierForest_actual_036391
  · exact g32p_supplierForest_actual_036440
  · exact g32p_supplierForest_actual_036470
  · exact g32p_supplierForest_actual_036479
  · exact g32p_supplierForest_actual_036491
  · exact g32p_supplierForest_actual_036495
  · exact g32p_supplierForest_actual_036514
  · exact g32p_supplierForest_actual_036522
  · exact g32p_supplierForest_actual_036524
  · exact g32p_supplierForest_actual_036555
  · exact g32p_supplierForest_actual_036566
  · exact g32p_supplierForest_actual_036595
  · exact g32p_supplierForest_actual_036599
  · exact g32p_supplierForest_actual_036604
  · exact g32p_supplierForest_actual_036609
  · exact g32p_supplierForest_actual_036650
  · exact g32p_supplierForest_actual_036676
  · exact g32p_supplierForest_actual_036699
  · exact g32p_supplierForest_actual_036711
  · exact g32p_supplierForest_actual_036716
  · exact g32p_supplierForest_actual_036717
  · exact g32p_supplierForest_actual_036722
  · exact g32p_supplierForest_actual_036754
  · exact g32p_supplierForest_actual_036765
  · exact g32p_supplierForest_actual_036794
  · exact g32p_supplierForest_actual_036815
  · exact g32p_supplierForest_actual_036823
  · exact g32p_supplierForest_actual_036824
  · exact g32p_supplierForest_actual_036839
  · exact g32p_supplierForest_actual_036857
  · exact g32p_supplierForest_actual_036929
  · exact g32p_supplierForest_actual_036947
  · exact g32p_supplierForest_actual_036992
  · exact g32p_supplierForest_actual_037017
  · exact g32p_supplierForest_actual_037028
  · exact g32p_supplierForest_actual_037036
  · exact g32p_supplierForest_actual_037075
  · exact g32p_supplierForest_actual_037157
  · exact g32p_supplierForest_actual_037186
  · exact g32p_supplierForest_actual_037190
  · exact g32p_supplierForest_actual_037206
  · exact g32p_supplierForest_actual_037207
  · exact g32p_supplierForest_actual_037216
  · exact g32p_supplierForest_actual_037220
  · exact g32p_supplierForest_actual_037229
  · exact g32p_supplierForest_actual_037234
  · exact g32p_supplierForest_actual_037248
  · exact g32p_supplierForest_actual_037259
  · exact g32p_supplierForest_actual_037291
  · exact g32p_supplierForest_actual_037327
  · exact g32p_supplierForest_actual_037340
  · exact g32p_supplierForest_actual_037360
  · exact g32p_supplierForest_actual_037367
  · exact g32p_supplierForest_actual_037373
  · exact g32p_supplierForest_actual_037427
  · exact g32p_supplierForest_actual_037429
  · exact g32p_supplierForest_actual_037430
  · exact g32p_supplierForest_actual_037520
  · exact g32p_supplierForest_actual_037538
  · exact g32p_supplierForest_actual_037549
  · exact g32p_supplierForest_actual_037558
  · exact g32p_supplierForest_actual_037576
  · exact g32p_supplierForest_actual_037586
  · exact g32p_supplierForest_actual_037610
  · exact g32p_supplierForest_actual_037639
  · exact g32p_supplierForest_actual_037647
  · exact g32p_supplierForest_actual_037662
  · exact g32p_supplierForest_actual_037668
  · exact g32p_supplierForest_actual_037678
  · exact g32p_supplierForest_actual_037724
  · exact g32p_supplierForest_actual_037737
  · exact g32p_supplierForest_actual_037756
  · exact g32p_supplierForest_actual_037771
  · exact g32p_supplierForest_actual_037778
  · exact g32p_supplierForest_actual_037786
  · exact g32p_supplierForest_actual_037793
  · exact g32p_supplierForest_actual_037826
  · exact g32p_supplierForest_actual_037844
  · exact g32p_supplierForest_actual_037872
  · exact g32p_supplierForest_actual_037950
  · exact g32p_supplierForest_actual_037958
  · exact g32p_supplierForest_actual_037963
  · exact g32p_supplierForest_actual_037991
  · exact g32p_supplierForest_actual_038009
  · exact g32p_supplierForest_actual_038039
  · exact g32p_supplierForest_actual_038046
  · exact g32p_supplierForest_actual_038052
  · exact g32p_supplierForest_actual_038063
  · exact g32p_supplierForest_actual_038073
  · exact g32p_supplierForest_actual_038074
  · exact g32p_supplierForest_actual_038075
  · exact g32p_supplierForest_actual_038096
  · exact g32p_supplierForest_actual_038160
  · exact g32p_supplierForest_actual_038164
  · exact g32p_supplierForest_actual_038174
  · exact g32p_supplierForest_actual_038218
  · exact g32p_supplierForest_actual_038225
  · exact g32p_supplierForest_actual_038238
  · exact g32p_supplierForest_actual_038243
  · exact g32p_supplierForest_actual_038248
  · exact g32p_supplierForest_actual_038257
  · exact g32p_supplierForest_actual_038282
  · exact g32p_supplierForest_actual_038287
  · exact g32p_supplierForest_actual_038310
  · exact g32p_supplierForest_actual_038316
  · exact g32p_supplierForest_actual_038346
  · exact g32p_supplierForest_actual_038383
  · exact g32p_supplierForest_actual_038384
  · exact g32p_supplierForest_actual_038422
  · exact g32p_supplierForest_actual_038478
  · exact g32p_supplierForest_actual_038498
  · exact g32p_supplierForest_actual_038503
  · exact g32p_supplierForest_actual_038515
  · exact g32p_supplierForest_actual_038525
  · exact g32p_supplierForest_actual_038542
  · exact g32p_supplierForest_actual_038622
  · exact g32p_supplierForest_actual_038637
  · exact g32p_supplierForest_actual_038654
  · exact g32p_supplierForest_actual_038657
  · exact g32p_supplierForest_actual_038689
  · exact g32p_supplierForest_actual_038694
  · exact g32p_supplierForest_actual_038706
  · exact g32p_supplierForest_actual_038724
  · exact g32p_supplierForest_actual_038751
  · exact g32p_supplierForest_actual_038757
  · exact g32p_supplierForest_actual_038758
  · exact g32p_supplierForest_actual_038764
  · exact g32p_supplierForest_actual_038775

def g32p_supplierForest_nodes_063 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_038795 else g32p_supplierForest_node_038833) else (if i.val < 3 then g32p_supplierForest_node_038837 else g32p_supplierForest_node_038967)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_038976 else g32p_supplierForest_node_039007) else (if i.val < 7 then g32p_supplierForest_node_039056 else g32p_supplierForest_node_039076))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_039080 else g32p_supplierForest_node_039119) else (if i.val < 11 then g32p_supplierForest_node_039125 else g32p_supplierForest_node_039143)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_039205 else g32p_supplierForest_node_039232) else (if i.val < 15 then g32p_supplierForest_node_039236 else g32p_supplierForest_node_039248)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_039305 else g32p_supplierForest_node_039323) else (if i.val < 19 then g32p_supplierForest_node_039347 else g32p_supplierForest_node_039349)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_039354 else g32p_supplierForest_node_039362) else (if i.val < 23 then g32p_supplierForest_node_039388 else g32p_supplierForest_node_039410))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_039413 else g32p_supplierForest_node_039439) else (if i.val < 27 then g32p_supplierForest_node_039459 else g32p_supplierForest_node_039482)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_039490 else g32p_supplierForest_node_039522) else (if i.val < 31 then g32p_supplierForest_node_039573 else g32p_supplierForest_node_039575))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_039584 else g32p_supplierForest_node_039621) else (if i.val < 35 then g32p_supplierForest_node_039636 else g32p_supplierForest_node_039653)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_039660 else g32p_supplierForest_node_039704) else (if i.val < 39 then g32p_supplierForest_node_039754 else g32p_supplierForest_node_039786))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_039792 else g32p_supplierForest_node_039796) else (if i.val < 43 then g32p_supplierForest_node_039853 else g32p_supplierForest_node_039862)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_039883 else g32p_supplierForest_node_039889) else (if i.val < 47 then g32p_supplierForest_node_039897 else g32p_supplierForest_node_039900)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_039952 else g32p_supplierForest_node_039965) else (if i.val < 51 then g32p_supplierForest_node_039999 else g32p_supplierForest_node_040008)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_040036 else g32p_supplierForest_node_040052) else (if i.val < 55 then g32p_supplierForest_node_040058 else g32p_supplierForest_node_040091))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_040113 else g32p_supplierForest_node_040142) else (if i.val < 59 then g32p_supplierForest_node_040155 else g32p_supplierForest_node_040164)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_040170 else g32p_supplierForest_node_040208) else (if i.val < 63 then g32p_supplierForest_node_040240 else g32p_supplierForest_node_040249)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_040251 else g32p_supplierForest_node_040253) else (if i.val < 67 then g32p_supplierForest_node_040263 else g32p_supplierForest_node_040283)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_040326 else g32p_supplierForest_node_040348) else (if i.val < 71 then g32p_supplierForest_node_040351 else g32p_supplierForest_node_040357))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_040364 else g32p_supplierForest_node_040394) else (if i.val < 75 then g32p_supplierForest_node_040428 else g32p_supplierForest_node_040432)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_040446 else g32p_supplierForest_node_040458) else (if i.val < 79 then g32p_supplierForest_node_040487 else g32p_supplierForest_node_040530)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_040542 else g32p_supplierForest_node_040554) else (if i.val < 83 then g32p_supplierForest_node_040579 else g32p_supplierForest_node_040631)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_040715 else g32p_supplierForest_node_040795) else (if i.val < 87 then g32p_supplierForest_node_040810 else g32p_supplierForest_node_040849))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_040856 else g32p_supplierForest_node_040857) else (if i.val < 91 then g32p_supplierForest_node_040859 else g32p_supplierForest_node_040866)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_040904 else g32p_supplierForest_node_040919) else (if i.val < 95 then g32p_supplierForest_node_040955 else g32p_supplierForest_node_040957))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_040981 else g32p_supplierForest_node_040990) else (if i.val < 99 then g32p_supplierForest_node_041013 else g32p_supplierForest_node_041032)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_041040 else g32p_supplierForest_node_041044) else (if i.val < 103 then g32p_supplierForest_node_041078 else g32p_supplierForest_node_041126))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_041142 else g32p_supplierForest_node_041144) else (if i.val < 107 then g32p_supplierForest_node_041151 else g32p_supplierForest_node_041187)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_041189 else g32p_supplierForest_node_041260) else (if i.val < 111 then g32p_supplierForest_node_041286 else g32p_supplierForest_node_041292)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_041313 else g32p_supplierForest_node_041366) else (if i.val < 115 then g32p_supplierForest_node_041374 else g32p_supplierForest_node_041387)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_041388 else g32p_supplierForest_node_041444) else (if i.val < 119 then g32p_supplierForest_node_041446 else g32p_supplierForest_node_041453))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_041472 else g32p_supplierForest_node_041484) else (if i.val < 123 then g32p_supplierForest_node_041488 else g32p_supplierForest_node_041496)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_041497 else g32p_supplierForest_node_041505) else (if i.val < 127 then g32p_supplierForest_node_041518 else g32p_supplierForest_node_041536))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_041537 else g32p_supplierForest_node_041570) else (if i.val < 131 then g32p_supplierForest_node_041598 else g32p_supplierForest_node_041827)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_041829 else g32p_supplierForest_node_041840) else (if i.val < 135 then g32p_supplierForest_node_041841 else g32p_supplierForest_node_041848))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_041890 else g32p_supplierForest_node_041908) else (if i.val < 139 then g32p_supplierForest_node_041922 else g32p_supplierForest_node_041940)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_041955 else g32p_supplierForest_node_041971) else (if i.val < 143 then g32p_supplierForest_node_041988 else g32p_supplierForest_node_042007)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_042011 else g32p_supplierForest_node_042030) else (if i.val < 147 then g32p_supplierForest_node_042058 else g32p_supplierForest_node_042071)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_042094 else g32p_supplierForest_node_042120) else (if i.val < 151 then g32p_supplierForest_node_042128 else g32p_supplierForest_node_042146))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_042174 else g32p_supplierForest_node_042220) else (if i.val < 155 then g32p_supplierForest_node_042258 else g32p_supplierForest_node_042275)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_042278 else g32p_supplierForest_node_042301) else (if i.val < 159 then g32p_supplierForest_node_042305 else g32p_supplierForest_node_042327))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_042345 else g32p_supplierForest_node_042354) else (if i.val < 163 then g32p_supplierForest_node_042366 else g32p_supplierForest_node_042375)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_042395 else g32p_supplierForest_node_042404) else (if i.val < 167 then g32p_supplierForest_node_042502 else g32p_supplierForest_node_042518))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_042529 else g32p_supplierForest_node_042544) else (if i.val < 171 then g32p_supplierForest_node_042562 else g32p_supplierForest_node_042579)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_042609 else g32p_supplierForest_node_042643) else (if i.val < 175 then g32p_supplierForest_node_042704 else g32p_supplierForest_node_042747)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_042748 else g32p_supplierForest_node_042749) else (if i.val < 179 then g32p_supplierForest_node_042750 else g32p_supplierForest_node_042751)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_042752 else g32p_supplierForest_node_042757) else (if i.val < 183 then g32p_supplierForest_node_042788 else g32p_supplierForest_node_042872))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_042905 else g32p_supplierForest_node_042957) else (if i.val < 187 then g32p_supplierForest_node_042959 else g32p_supplierForest_node_042960)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_042967 else g32p_supplierForest_node_043071) else (if i.val < 191 then g32p_supplierForest_node_043074 else g32p_supplierForest_node_043097)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_043105 else g32p_supplierForest_node_043106) else (if i.val < 195 then g32p_supplierForest_node_043107 else g32p_supplierForest_node_043142)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_043157 else g32p_supplierForest_node_043281) else (if i.val < 199 then g32p_supplierForest_node_043301 else g32p_supplierForest_node_043304))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_043342 else g32p_supplierForest_node_043346) else (if i.val < 203 then g32p_supplierForest_node_043348 else g32p_supplierForest_node_043351)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_043358 else g32p_supplierForest_node_043367) else (if i.val < 207 then g32p_supplierForest_node_043368 else g32p_supplierForest_node_043402)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_043421 else g32p_supplierForest_node_043441) else (if i.val < 211 then g32p_supplierForest_node_043493 else g32p_supplierForest_node_043534)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_043548 else g32p_supplierForest_node_043569) else (if i.val < 215 then g32p_supplierForest_node_043582 else g32p_supplierForest_node_043590))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_043602 else g32p_supplierForest_node_043622) else (if i.val < 219 then g32p_supplierForest_node_043692 else g32p_supplierForest_node_043694)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_043705 else g32p_supplierForest_node_043715) else (if i.val < 223 then g32p_supplierForest_node_043726 else g32p_supplierForest_node_043744))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_043756 else g32p_supplierForest_node_043781) else (if i.val < 227 then g32p_supplierForest_node_043785 else g32p_supplierForest_node_043789)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_043801 else g32p_supplierForest_node_043805) else (if i.val < 231 then g32p_supplierForest_node_043835 else g32p_supplierForest_node_043861))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_043877 else g32p_supplierForest_node_043887) else (if i.val < 235 then g32p_supplierForest_node_043897 else g32p_supplierForest_node_043908)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_043948 else g32p_supplierForest_node_043957) else (if i.val < 239 then g32p_supplierForest_node_043989 else g32p_supplierForest_node_044012)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_044064 else g32p_supplierForest_node_044089) else (if i.val < 243 then g32p_supplierForest_node_044097 else g32p_supplierForest_node_044101)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_044147 else g32p_supplierForest_node_044159) else (if i.val < 247 then g32p_supplierForest_node_044172 else g32p_supplierForest_node_044194))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_044198 else g32p_supplierForest_node_044209) else (if i.val < 251 then g32p_supplierForest_node_044216 else g32p_supplierForest_node_044229)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_044250 else g32p_supplierForest_node_044253) else (if i.val < 255 then g32p_supplierForest_node_044270 else g32p_supplierForest_node_044314))))))))

def g32p_supplierForest_classes_063 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 3 else 34) else (if i.val < 3 then 57 else 16)) else (if i.val < 6 then (if i.val < 5 then 58 else 17) else (if i.val < 7 then 29 else 14))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 15 else 30) else (if i.val < 11 then 57 else 16)) else (if i.val < 14 then (if i.val < 13 then 32 else 57) else (if i.val < 15 then 4 else 57)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 57) else (if i.val < 19 then 16 else 30)) else (if i.val < 22 then (if i.val < 21 then 16 else 57) else (if i.val < 23 then 16 else 59))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 57 else 57) else (if i.val < 27 then 60 else 15)) else (if i.val < 30 then (if i.val < 29 then 30 else 29) else (if i.val < 31 then 59 else 60))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 59 else 57) else (if i.val < 35 then 59 else 59)) else (if i.val < 38 then (if i.val < 37 then 57 else 57) else (if i.val < 39 then 32 else 66))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 57 else 57) else (if i.val < 43 then 16 else 32)) else (if i.val < 46 then (if i.val < 45 then 30 else 57) else (if i.val < 47 then 63 else 63)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 57 else 35) else (if i.val < 51 then 61 else 61)) else (if i.val < 54 then (if i.val < 53 then 29 else 33) else (if i.val < 55 then 61 else 16))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 14 else 15) else (if i.val < 59 then 16 else 57)) else (if i.val < 62 then (if i.val < 61 then 59 else 30) else (if i.val < 63 then 17 else 60)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 35 else 30) else (if i.val < 67 then 57 else 59)) else (if i.val < 70 then (if i.val < 69 then 59 else 15) else (if i.val < 71 then 30 else 14))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 29 else 14) else (if i.val < 75 then 57 else 57)) else (if i.val < 78 then (if i.val < 77 then 14 else 30) else (if i.val < 79 then 30 else 66)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 36 else 57) else (if i.val < 83 then 16 else 34)) else (if i.val < 86 then (if i.val < 85 then 57 else 62) else (if i.val < 87 then 57 else 60))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 14 else 14) else (if i.val < 91 then 35 else 33)) else (if i.val < 94 then (if i.val < 93 then 59 else 34) else (if i.val < 95 then 15 else 29))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 57 else 16) else (if i.val < 99 then 30 else 57)) else (if i.val < 102 then (if i.val < 101 then 16 else 30) else (if i.val < 103 then 14 else 59))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 58 else 60) else (if i.val < 107 then 30 else 30)) else (if i.val < 110 then (if i.val < 109 then 30 else 16) else (if i.val < 111 then 63 else 64)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 32 else 57) else (if i.val < 115 then 57 else 59)) else (if i.val < 118 then (if i.val < 117 then 57 else 16) else (if i.val < 119 then 62 else 30))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 35 else 57) else (if i.val < 123 then 30 else 30)) else (if i.val < 126 then (if i.val < 125 then 60 else 29) else (if i.val < 127 then 15 else 15))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 36 else 34) else (if i.val < 131 then 14 else 59)) else (if i.val < 134 then (if i.val < 133 then 57 else 16) else (if i.val < 135 then 58 else 57))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 30 else 16) else (if i.val < 139 then 35 else 34)) else (if i.val < 142 then (if i.val < 141 then 4 else 30) else (if i.val < 143 then 57 else 33)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 14 else 34) else (if i.val < 147 then 57 else 30)) else (if i.val < 150 then (if i.val < 149 then 14 else 15) else (if i.val < 151 then 14 else 30))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 29 else 16) else (if i.val < 155 then 57 else 57)) else (if i.val < 158 then (if i.val < 157 then 16 else 29) else (if i.val < 159 then 29 else 63))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 34 else 30) else (if i.val < 163 then 16 else 63)) else (if i.val < 166 then (if i.val < 165 then 4 else 31) else (if i.val < 167 then 32 else 30))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 30 else 34) else (if i.val < 171 then 16 else 36)) else (if i.val < 174 then (if i.val < 173 then 64 else 32) else (if i.val < 175 then 15 else 35)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 30 else 60) else (if i.val < 179 then 15 else 29)) else (if i.val < 182 then (if i.val < 181 then 33 else 16) else (if i.val < 183 then 30 else 34))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 16 else 59) else (if i.val < 187 then 57 else 30)) else (if i.val < 190 then (if i.val < 189 then 16 else 16) else (if i.val < 191 then 30 else 57)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 15 else 57) else (if i.val < 195 then 16 else 30)) else (if i.val < 198 then (if i.val < 197 then 16 else 30) else (if i.val < 199 then 57 else 57))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 62 else 62) else (if i.val < 203 then 60 else 29)) else (if i.val < 206 then (if i.val < 205 then 30 else 16) else (if i.val < 207 then 30 else 16)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 63 else 4) else (if i.val < 211 then 57 else 17)) else (if i.val < 214 then (if i.val < 213 then 4 else 57) else (if i.val < 215 then 30 else 61))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 63 else 30) else (if i.val < 219 then 59 else 59)) else (if i.val < 222 then (if i.val < 221 then 59 else 57) else (if i.val < 223 then 57 else 16))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 34 else 34) else (if i.val < 227 then 61 else 16)) else (if i.val < 230 then (if i.val < 229 then 30 else 16) else (if i.val < 231 then 32 else 34))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 63 else 30) else (if i.val < 235 then 30 else 16)) else (if i.val < 238 then (if i.val < 237 then 57 else 30) else (if i.val < 239 then 58 else 30)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 34 else 14) else (if i.val < 243 then 14 else 17)) else (if i.val < 246 then (if i.val < 245 then 60 else 16) else (if i.val < 247 then 35 else 32))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 57 else 30) else (if i.val < 251 then 15 else 16)) else (if i.val < 254 then (if i.val < 253 then 60 else 32) else (if i.val < 255 then 30 else 57))))))))

theorem g32p_supplierForest_actual_063 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_063 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_063 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_038795
  · exact g32p_supplierForest_actual_038833
  · exact g32p_supplierForest_actual_038837
  · exact g32p_supplierForest_actual_038967
  · exact g32p_supplierForest_actual_038976
  · exact g32p_supplierForest_actual_039007
  · exact g32p_supplierForest_actual_039056
  · exact g32p_supplierForest_actual_039076
  · exact g32p_supplierForest_actual_039080
  · exact g32p_supplierForest_actual_039119
  · exact g32p_supplierForest_actual_039125
  · exact g32p_supplierForest_actual_039143
  · exact g32p_supplierForest_actual_039205
  · exact g32p_supplierForest_actual_039232
  · exact g32p_supplierForest_actual_039236
  · exact g32p_supplierForest_actual_039248
  · exact g32p_supplierForest_actual_039305
  · exact g32p_supplierForest_actual_039323
  · exact g32p_supplierForest_actual_039347
  · exact g32p_supplierForest_actual_039349
  · exact g32p_supplierForest_actual_039354
  · exact g32p_supplierForest_actual_039362
  · exact g32p_supplierForest_actual_039388
  · exact g32p_supplierForest_actual_039410
  · exact g32p_supplierForest_actual_039413
  · exact g32p_supplierForest_actual_039439
  · exact g32p_supplierForest_actual_039459
  · exact g32p_supplierForest_actual_039482
  · exact g32p_supplierForest_actual_039490
  · exact g32p_supplierForest_actual_039522
  · exact g32p_supplierForest_actual_039573
  · exact g32p_supplierForest_actual_039575
  · exact g32p_supplierForest_actual_039584
  · exact g32p_supplierForest_actual_039621
  · exact g32p_supplierForest_actual_039636
  · exact g32p_supplierForest_actual_039653
  · exact g32p_supplierForest_actual_039660
  · exact g32p_supplierForest_actual_039704
  · exact g32p_supplierForest_actual_039754
  · exact g32p_supplierForest_actual_039786
  · exact g32p_supplierForest_actual_039792
  · exact g32p_supplierForest_actual_039796
  · exact g32p_supplierForest_actual_039853
  · exact g32p_supplierForest_actual_039862
  · exact g32p_supplierForest_actual_039883
  · exact g32p_supplierForest_actual_039889
  · exact g32p_supplierForest_actual_039897
  · exact g32p_supplierForest_actual_039900
  · exact g32p_supplierForest_actual_039952
  · exact g32p_supplierForest_actual_039965
  · exact g32p_supplierForest_actual_039999
  · exact g32p_supplierForest_actual_040008
  · exact g32p_supplierForest_actual_040036
  · exact g32p_supplierForest_actual_040052
  · exact g32p_supplierForest_actual_040058
  · exact g32p_supplierForest_actual_040091
  · exact g32p_supplierForest_actual_040113
  · exact g32p_supplierForest_actual_040142
  · exact g32p_supplierForest_actual_040155
  · exact g32p_supplierForest_actual_040164
  · exact g32p_supplierForest_actual_040170
  · exact g32p_supplierForest_actual_040208
  · exact g32p_supplierForest_actual_040240
  · exact g32p_supplierForest_actual_040249
  · exact g32p_supplierForest_actual_040251
  · exact g32p_supplierForest_actual_040253
  · exact g32p_supplierForest_actual_040263
  · exact g32p_supplierForest_actual_040283
  · exact g32p_supplierForest_actual_040326
  · exact g32p_supplierForest_actual_040348
  · exact g32p_supplierForest_actual_040351
  · exact g32p_supplierForest_actual_040357
  · exact g32p_supplierForest_actual_040364
  · exact g32p_supplierForest_actual_040394
  · exact g32p_supplierForest_actual_040428
  · exact g32p_supplierForest_actual_040432
  · exact g32p_supplierForest_actual_040446
  · exact g32p_supplierForest_actual_040458
  · exact g32p_supplierForest_actual_040487
  · exact g32p_supplierForest_actual_040530
  · exact g32p_supplierForest_actual_040542
  · exact g32p_supplierForest_actual_040554
  · exact g32p_supplierForest_actual_040579
  · exact g32p_supplierForest_actual_040631
  · exact g32p_supplierForest_actual_040715
  · exact g32p_supplierForest_actual_040795
  · exact g32p_supplierForest_actual_040810
  · exact g32p_supplierForest_actual_040849
  · exact g32p_supplierForest_actual_040856
  · exact g32p_supplierForest_actual_040857
  · exact g32p_supplierForest_actual_040859
  · exact g32p_supplierForest_actual_040866
  · exact g32p_supplierForest_actual_040904
  · exact g32p_supplierForest_actual_040919
  · exact g32p_supplierForest_actual_040955
  · exact g32p_supplierForest_actual_040957
  · exact g32p_supplierForest_actual_040981
  · exact g32p_supplierForest_actual_040990
  · exact g32p_supplierForest_actual_041013
  · exact g32p_supplierForest_actual_041032
  · exact g32p_supplierForest_actual_041040
  · exact g32p_supplierForest_actual_041044
  · exact g32p_supplierForest_actual_041078
  · exact g32p_supplierForest_actual_041126
  · exact g32p_supplierForest_actual_041142
  · exact g32p_supplierForest_actual_041144
  · exact g32p_supplierForest_actual_041151
  · exact g32p_supplierForest_actual_041187
  · exact g32p_supplierForest_actual_041189
  · exact g32p_supplierForest_actual_041260
  · exact g32p_supplierForest_actual_041286
  · exact g32p_supplierForest_actual_041292
  · exact g32p_supplierForest_actual_041313
  · exact g32p_supplierForest_actual_041366
  · exact g32p_supplierForest_actual_041374
  · exact g32p_supplierForest_actual_041387
  · exact g32p_supplierForest_actual_041388
  · exact g32p_supplierForest_actual_041444
  · exact g32p_supplierForest_actual_041446
  · exact g32p_supplierForest_actual_041453
  · exact g32p_supplierForest_actual_041472
  · exact g32p_supplierForest_actual_041484
  · exact g32p_supplierForest_actual_041488
  · exact g32p_supplierForest_actual_041496
  · exact g32p_supplierForest_actual_041497
  · exact g32p_supplierForest_actual_041505
  · exact g32p_supplierForest_actual_041518
  · exact g32p_supplierForest_actual_041536
  · exact g32p_supplierForest_actual_041537
  · exact g32p_supplierForest_actual_041570
  · exact g32p_supplierForest_actual_041598
  · exact g32p_supplierForest_actual_041827
  · exact g32p_supplierForest_actual_041829
  · exact g32p_supplierForest_actual_041840
  · exact g32p_supplierForest_actual_041841
  · exact g32p_supplierForest_actual_041848
  · exact g32p_supplierForest_actual_041890
  · exact g32p_supplierForest_actual_041908
  · exact g32p_supplierForest_actual_041922
  · exact g32p_supplierForest_actual_041940
  · exact g32p_supplierForest_actual_041955
  · exact g32p_supplierForest_actual_041971
  · exact g32p_supplierForest_actual_041988
  · exact g32p_supplierForest_actual_042007
  · exact g32p_supplierForest_actual_042011
  · exact g32p_supplierForest_actual_042030
  · exact g32p_supplierForest_actual_042058
  · exact g32p_supplierForest_actual_042071
  · exact g32p_supplierForest_actual_042094
  · exact g32p_supplierForest_actual_042120
  · exact g32p_supplierForest_actual_042128
  · exact g32p_supplierForest_actual_042146
  · exact g32p_supplierForest_actual_042174
  · exact g32p_supplierForest_actual_042220
  · exact g32p_supplierForest_actual_042258
  · exact g32p_supplierForest_actual_042275
  · exact g32p_supplierForest_actual_042278
  · exact g32p_supplierForest_actual_042301
  · exact g32p_supplierForest_actual_042305
  · exact g32p_supplierForest_actual_042327
  · exact g32p_supplierForest_actual_042345
  · exact g32p_supplierForest_actual_042354
  · exact g32p_supplierForest_actual_042366
  · exact g32p_supplierForest_actual_042375
  · exact g32p_supplierForest_actual_042395
  · exact g32p_supplierForest_actual_042404
  · exact g32p_supplierForest_actual_042502
  · exact g32p_supplierForest_actual_042518
  · exact g32p_supplierForest_actual_042529
  · exact g32p_supplierForest_actual_042544
  · exact g32p_supplierForest_actual_042562
  · exact g32p_supplierForest_actual_042579
  · exact g32p_supplierForest_actual_042609
  · exact g32p_supplierForest_actual_042643
  · exact g32p_supplierForest_actual_042704
  · exact g32p_supplierForest_actual_042747
  · exact g32p_supplierForest_actual_042748
  · exact g32p_supplierForest_actual_042749
  · exact g32p_supplierForest_actual_042750
  · exact g32p_supplierForest_actual_042751
  · exact g32p_supplierForest_actual_042752
  · exact g32p_supplierForest_actual_042757
  · exact g32p_supplierForest_actual_042788
  · exact g32p_supplierForest_actual_042872
  · exact g32p_supplierForest_actual_042905
  · exact g32p_supplierForest_actual_042957
  · exact g32p_supplierForest_actual_042959
  · exact g32p_supplierForest_actual_042960
  · exact g32p_supplierForest_actual_042967
  · exact g32p_supplierForest_actual_043071
  · exact g32p_supplierForest_actual_043074
  · exact g32p_supplierForest_actual_043097
  · exact g32p_supplierForest_actual_043105
  · exact g32p_supplierForest_actual_043106
  · exact g32p_supplierForest_actual_043107
  · exact g32p_supplierForest_actual_043142
  · exact g32p_supplierForest_actual_043157
  · exact g32p_supplierForest_actual_043281
  · exact g32p_supplierForest_actual_043301
  · exact g32p_supplierForest_actual_043304
  · exact g32p_supplierForest_actual_043342
  · exact g32p_supplierForest_actual_043346
  · exact g32p_supplierForest_actual_043348
  · exact g32p_supplierForest_actual_043351
  · exact g32p_supplierForest_actual_043358
  · exact g32p_supplierForest_actual_043367
  · exact g32p_supplierForest_actual_043368
  · exact g32p_supplierForest_actual_043402
  · exact g32p_supplierForest_actual_043421
  · exact g32p_supplierForest_actual_043441
  · exact g32p_supplierForest_actual_043493
  · exact g32p_supplierForest_actual_043534
  · exact g32p_supplierForest_actual_043548
  · exact g32p_supplierForest_actual_043569
  · exact g32p_supplierForest_actual_043582
  · exact g32p_supplierForest_actual_043590
  · exact g32p_supplierForest_actual_043602
  · exact g32p_supplierForest_actual_043622
  · exact g32p_supplierForest_actual_043692
  · exact g32p_supplierForest_actual_043694
  · exact g32p_supplierForest_actual_043705
  · exact g32p_supplierForest_actual_043715
  · exact g32p_supplierForest_actual_043726
  · exact g32p_supplierForest_actual_043744
  · exact g32p_supplierForest_actual_043756
  · exact g32p_supplierForest_actual_043781
  · exact g32p_supplierForest_actual_043785
  · exact g32p_supplierForest_actual_043789
  · exact g32p_supplierForest_actual_043801
  · exact g32p_supplierForest_actual_043805
  · exact g32p_supplierForest_actual_043835
  · exact g32p_supplierForest_actual_043861
  · exact g32p_supplierForest_actual_043877
  · exact g32p_supplierForest_actual_043887
  · exact g32p_supplierForest_actual_043897
  · exact g32p_supplierForest_actual_043908
  · exact g32p_supplierForest_actual_043948
  · exact g32p_supplierForest_actual_043957
  · exact g32p_supplierForest_actual_043989
  · exact g32p_supplierForest_actual_044012
  · exact g32p_supplierForest_actual_044064
  · exact g32p_supplierForest_actual_044089
  · exact g32p_supplierForest_actual_044097
  · exact g32p_supplierForest_actual_044101
  · exact g32p_supplierForest_actual_044147
  · exact g32p_supplierForest_actual_044159
  · exact g32p_supplierForest_actual_044172
  · exact g32p_supplierForest_actual_044194
  · exact g32p_supplierForest_actual_044198
  · exact g32p_supplierForest_actual_044209
  · exact g32p_supplierForest_actual_044216
  · exact g32p_supplierForest_actual_044229
  · exact g32p_supplierForest_actual_044250
  · exact g32p_supplierForest_actual_044253
  · exact g32p_supplierForest_actual_044270
  · exact g32p_supplierForest_actual_044314

end HodgeLean.Foundations.Program

end
end
