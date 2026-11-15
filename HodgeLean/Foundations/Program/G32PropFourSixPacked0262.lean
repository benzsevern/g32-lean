import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0241
import HodgeLean.Foundations.Program.G32PropFourSixPacked0245
import HodgeLean.Foundations.Program.G32PropFourSixPacked0246
import HodgeLean.Foundations.Program.G32PropFourSixPacked0247
import HodgeLean.Foundations.Program.G32PropFourSixPacked0254
import HodgeLean.Foundations.Program.G32PropFourSixPacked0255
import HodgeLean.Foundations.Program.G32PropFourSixPacked0258
import HodgeLean.Foundations.Program.G32PropFourSixPacked0259
import HodgeLean.Foundations.Program.G32PropFourSixPacked0260
import HodgeLean.Foundations.Program.G32PropFourSixPacked0261

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_061069 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_061069 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061069 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070948 := by
  decide +kernel

theorem g32p_supplierForest_actual_061069 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061069) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_061069
    g32p_supplierForest_actual_070948

def g32p_supplierForest_node_061076 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_061076 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061076 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_127872 := by
  decide +kernel

theorem g32p_supplierForest_actual_061076 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061076) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_061076
    g32p_supplierForest_actual_127872

def g32p_supplierForest_node_061084 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061084 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061084 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_049643 := by
  decide +kernel

theorem g32p_supplierForest_actual_061084 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061084) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_061084
    g32p_supplierForest_actual_049643

def g32p_supplierForest_node_061113 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061113 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061113 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_046719 := by
  decide +kernel

theorem g32p_supplierForest_actual_061113 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061113) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 0 g32p_supplierForest_edge_061113
    g32p_supplierForest_actual_046719

def g32p_supplierForest_node_061115 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_061115 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061115 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128350 := by
  decide +kernel

theorem g32p_supplierForest_actual_061115 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061115) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_061115
    g32p_supplierForest_actual_128350

def g32p_supplierForest_node_061118 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_061118 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061118 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067610 := by
  decide +kernel

theorem g32p_supplierForest_actual_061118 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061118) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_061118
    g32p_supplierForest_actual_067610

def g32p_supplierForest_node_061153 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_061153 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061153 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_048617 := by
  decide +kernel

theorem g32p_supplierForest_actual_061153 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061153) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 1 g32p_supplierForest_edge_061153
    g32p_supplierForest_actual_048617

def g32p_supplierForest_node_061192 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061192 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061192 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_048739 := by
  decide +kernel

theorem g32p_supplierForest_actual_061192 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061192) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_061192
    g32p_supplierForest_actual_048739

def g32p_supplierForest_node_061212 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061212 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061212 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_058671 := by
  decide +kernel

theorem g32p_supplierForest_actual_061212 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061212) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_061212
    g32p_supplierForest_actual_058671

def g32p_supplierForest_node_061217 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061217 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061217 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_051111 := by
  decide +kernel

theorem g32p_supplierForest_actual_061217 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061217) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_061217
    g32p_supplierForest_actual_051111

def g32p_supplierForest_node_061234 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_061234 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061234 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_066976 := by
  decide +kernel

theorem g32p_supplierForest_actual_061234 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061234) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_061234
    g32p_supplierForest_actual_066976

def g32p_supplierForest_node_061242 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_061242 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061242 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_130543 := by
  decide +kernel

theorem g32p_supplierForest_actual_061242 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061242) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 2 g32p_supplierForest_edge_061242
    g32p_supplierForest_actual_130543

def g32p_supplierForest_node_061253 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061253 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061253 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_069571 := by
  decide +kernel

theorem g32p_supplierForest_actual_061253 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061253) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_061253
    g32p_supplierForest_actual_069571

def g32p_supplierForest_node_061254 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_061254 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061254 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065245 := by
  decide +kernel

theorem g32p_supplierForest_actual_061254 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061254) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_061254
    g32p_supplierForest_actual_065245

def g32p_supplierForest_node_061267 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_061267 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061267 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128515 := by
  decide +kernel

theorem g32p_supplierForest_actual_061267 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061267) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 0 g32p_supplierForest_edge_061267
    g32p_supplierForest_actual_128515

def g32p_supplierForest_node_061269 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_061269 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061269 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128518 := by
  decide +kernel

theorem g32p_supplierForest_actual_061269 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061269) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_061269
    g32p_supplierForest_actual_128518

def g32p_supplierForest_node_061270 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061270 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061270 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_062277 := by
  decide +kernel

theorem g32p_supplierForest_actual_061270 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061270) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_061270
    g32p_supplierForest_actual_062277

def g32p_supplierForest_node_061385 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_061385 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061385 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_046060 := by
  decide +kernel

theorem g32p_supplierForest_actual_061385 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061385) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_061385
    g32p_supplierForest_actual_046060

def g32p_supplierForest_node_061392 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_061392 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061392 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_141056 := by
  decide +kernel

theorem g32p_supplierForest_actual_061392 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061392) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_061392
    g32p_supplierForest_actual_141056

def g32p_supplierForest_node_061410 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_061410 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061410 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128677 := by
  decide +kernel

theorem g32p_supplierForest_actual_061410 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061410) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_061410
    g32p_supplierForest_actual_128677

def g32p_supplierForest_node_061458 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061458 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061458 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_047100 := by
  decide +kernel

theorem g32p_supplierForest_actual_061458 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061458) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_061458
    g32p_supplierForest_actual_047100

def g32p_supplierForest_node_061522 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061522 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061522 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_051297 := by
  decide +kernel

theorem g32p_supplierForest_actual_061522 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061522) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_061522
    g32p_supplierForest_actual_051297

def g32p_supplierForest_node_061565 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061565 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061565 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128836 := by
  decide +kernel

theorem g32p_supplierForest_actual_061565 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061565) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_061565
    g32p_supplierForest_actual_128836

def g32p_supplierForest_node_061569 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_061569 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061569 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_050080 := by
  decide +kernel

theorem g32p_supplierForest_actual_061569 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061569) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_061569
    g32p_supplierForest_actual_050080

def g32p_supplierForest_node_061621 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_061621 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061621 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_050553 := by
  decide +kernel

theorem g32p_supplierForest_actual_061621 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061621) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 1 g32p_supplierForest_edge_061621
    g32p_supplierForest_actual_050553

def g32p_supplierForest_node_061715 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_061715 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061715 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128975 := by
  decide +kernel

theorem g32p_supplierForest_actual_061715 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061715) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 0 g32p_supplierForest_edge_061715
    g32p_supplierForest_actual_128975

def g32p_supplierForest_node_061752 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061752 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061752 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_061932 := by
  decide +kernel

theorem g32p_supplierForest_actual_061752 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061752) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_061752
    g32p_supplierForest_actual_061932

def g32p_supplierForest_node_061761 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061761 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061761 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_056871 := by
  decide +kernel

theorem g32p_supplierForest_actual_061761 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061761) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_061761
    g32p_supplierForest_actual_056871

def g32p_supplierForest_node_061765 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061765 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061765 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065043 := by
  decide +kernel

theorem g32p_supplierForest_actual_061765 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061765) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_061765
    g32p_supplierForest_actual_065043

def g32p_supplierForest_node_061766 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_061766 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061766 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_047011 := by
  decide +kernel

theorem g32p_supplierForest_actual_061766 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061766) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_061766
    g32p_supplierForest_actual_047011

def g32p_supplierForest_node_061775 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_061775 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061775 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065065 := by
  decide +kernel

theorem g32p_supplierForest_actual_061775 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061775) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_061775
    g32p_supplierForest_actual_065065

def g32p_supplierForest_node_061794 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061794 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061794 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129041 := by
  decide +kernel

theorem g32p_supplierForest_actual_061794 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061794) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_061794
    g32p_supplierForest_actual_129041

def g32p_supplierForest_node_061858 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061858 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061858 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_055674 := by
  decide +kernel

theorem g32p_supplierForest_actual_061858 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061858) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 2 g32p_supplierForest_edge_061858
    g32p_supplierForest_actual_055674

def g32p_supplierForest_node_061889 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_061889 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061889 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128252 := by
  decide +kernel

theorem g32p_supplierForest_actual_061889 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061889) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 0 g32p_supplierForest_edge_061889
    g32p_supplierForest_actual_128252

def g32p_supplierForest_node_061898 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061898 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061898 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_138501 := by
  decide +kernel

theorem g32p_supplierForest_actual_061898 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061898) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_061898
    g32p_supplierForest_actual_138501

def g32p_supplierForest_node_061943 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_061943 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061943 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_049957 := by
  decide +kernel

theorem g32p_supplierForest_actual_061943 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061943) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_061943
    g32p_supplierForest_actual_049957

def g32p_supplierForest_node_061955 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_061955 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061955 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_060204 := by
  decide +kernel

theorem g32p_supplierForest_actual_061955 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061955) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_061955
    g32p_supplierForest_actual_060204

def g32p_supplierForest_node_061988 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061988 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061988 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_057653 := by
  decide +kernel

theorem g32p_supplierForest_actual_061988 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061988) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_061988
    g32p_supplierForest_actual_057653

def g32p_supplierForest_node_062044 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062044 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062044 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_048711 := by
  decide +kernel

theorem g32p_supplierForest_actual_062044 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062044) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_062044
    g32p_supplierForest_actual_048711

def g32p_supplierForest_node_062045 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062045 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062045 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_057983 := by
  decide +kernel

theorem g32p_supplierForest_actual_062045 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062045) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_062045
    g32p_supplierForest_actual_057983

def g32p_supplierForest_node_062111 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_062111 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062111 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_051078 := by
  decide +kernel

theorem g32p_supplierForest_actual_062111 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062111) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_062111
    g32p_supplierForest_actual_051078

def g32p_supplierForest_node_062122 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_062122 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062122 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_058170 := by
  decide +kernel

theorem g32p_supplierForest_actual_062122 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062122) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 1 g32p_supplierForest_edge_062122
    g32p_supplierForest_actual_058170

def g32p_supplierForest_node_062123 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_062123 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062123 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129315 := by
  decide +kernel

theorem g32p_supplierForest_actual_062123 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062123) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_062123
    g32p_supplierForest_actual_129315

def g32p_supplierForest_node_062132 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_062132 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062132 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_066277 := by
  decide +kernel

theorem g32p_supplierForest_actual_062132 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062132) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_062132
    g32p_supplierForest_actual_066277

def g32p_supplierForest_node_062135 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_062135 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062135 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128234 := by
  decide +kernel

theorem g32p_supplierForest_actual_062135 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062135) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_062135
    g32p_supplierForest_actual_128234

def g32p_supplierForest_node_062142 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062142 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062142 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_045117 := by
  decide +kernel

theorem g32p_supplierForest_actual_062142 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062142) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_062142
    g32p_supplierForest_actual_045117

def g32p_supplierForest_node_062176 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_062176 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062176 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_143061 := by
  decide +kernel

theorem g32p_supplierForest_actual_062176 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062176) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_062176
    g32p_supplierForest_actual_143061

def g32p_supplierForest_node_062189 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062189 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062189 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_136685 := by
  decide +kernel

theorem g32p_supplierForest_actual_062189 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062189) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_062189
    g32p_supplierForest_actual_136685

def g32p_supplierForest_node_062202 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_062202 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062202 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_045154 := by
  decide +kernel

theorem g32p_supplierForest_actual_062202 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062202) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_062202
    g32p_supplierForest_actual_045154

def g32p_supplierForest_node_062273 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_062273 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062273 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_068567 := by
  decide +kernel

theorem g32p_supplierForest_actual_062273 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062273) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 0 g32p_supplierForest_edge_062273
    g32p_supplierForest_actual_068567

def g32p_supplierForest_node_062291 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062291 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062291 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_045447 := by
  decide +kernel

theorem g32p_supplierForest_actual_062291 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062291) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_062291
    g32p_supplierForest_actual_045447

def g32p_supplierForest_node_062293 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062293 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062293 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_060628 := by
  decide +kernel

theorem g32p_supplierForest_actual_062293 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062293) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_062293
    g32p_supplierForest_actual_060628

def g32p_supplierForest_node_062299 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062299 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062299 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_011503 := by
  decide +kernel

theorem g32p_supplierForest_actual_062299 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062299) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_062299
    g32p_supplierForest_actual_011503

def g32p_supplierForest_node_062352 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_062352 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062352 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128549 := by
  decide +kernel

theorem g32p_supplierForest_actual_062352 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062352) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_062352
    g32p_supplierForest_actual_128549

def g32p_supplierForest_node_062360 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_062360 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062360 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129551 := by
  decide +kernel

theorem g32p_supplierForest_actual_062360 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062360) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_062360
    g32p_supplierForest_actual_129551

def g32p_supplierForest_node_062362 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_062362 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062362 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_058965 := by
  decide +kernel

theorem g32p_supplierForest_actual_062362 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062362) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_062362
    g32p_supplierForest_actual_058965

def g32p_supplierForest_node_062365 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_062365 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062365 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_060535 := by
  decide +kernel

theorem g32p_supplierForest_actual_062365 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062365) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_062365
    g32p_supplierForest_actual_060535

def g32p_supplierForest_node_062380 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_062380 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062380 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064255 := by
  decide +kernel

theorem g32p_supplierForest_actual_062380 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062380) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_062380
    g32p_supplierForest_actual_064255

def g32p_supplierForest_node_062384 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_062384 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062384 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129329 := by
  decide +kernel

theorem g32p_supplierForest_actual_062384 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062384) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_062384
    g32p_supplierForest_actual_129329

def g32p_supplierForest_node_062391 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062391 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062391 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129592 := by
  decide +kernel

theorem g32p_supplierForest_actual_062391 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062391) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_062391
    g32p_supplierForest_actual_129592

def g32p_supplierForest_node_062408 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062408 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062408 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_048531 := by
  decide +kernel

theorem g32p_supplierForest_actual_062408 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062408) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 2 g32p_supplierForest_edge_062408
    g32p_supplierForest_actual_048531

def g32p_supplierForest_node_062441 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_062441 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062441 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071052 := by
  decide +kernel

theorem g32p_supplierForest_actual_062441 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062441) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_062441
    g32p_supplierForest_actual_071052

def g32p_supplierForest_node_062492 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_062492 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062492 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_061067 := by
  decide +kernel

theorem g32p_supplierForest_actual_062492 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062492) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_062492
    g32p_supplierForest_actual_061067

def g32p_supplierForest_node_062508 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062508 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062508 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_046521 := by
  decide +kernel

theorem g32p_supplierForest_actual_062508 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062508) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 3 g32p_supplierForest_edge_062508
    g32p_supplierForest_actual_046521

def g32p_supplierForest_node_062527 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062527 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062527 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065821 := by
  decide +kernel

theorem g32p_supplierForest_actual_062527 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062527) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_062527
    g32p_supplierForest_actual_065821

def g32p_supplierForest_node_062532 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062532 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062532 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_059405 := by
  decide +kernel

theorem g32p_supplierForest_actual_062532 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062532) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_062532
    g32p_supplierForest_actual_059405

def g32p_supplierForest_node_062553 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_062553 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062553 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_055778 := by
  decide +kernel

theorem g32p_supplierForest_actual_062553 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062553) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 0 g32p_supplierForest_edge_062553
    g32p_supplierForest_actual_055778

def g32p_supplierForest_node_062615 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_062615 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062615 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_052125 := by
  decide +kernel

theorem g32p_supplierForest_actual_062615 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062615) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 3 g32p_supplierForest_edge_062615
    g32p_supplierForest_actual_052125

def g32p_supplierForest_node_062622 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨2, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_062622 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062622 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_011912 := by
  decide +kernel

theorem g32p_supplierForest_actual_062622 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062622) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_062622
    g32p_supplierForest_actual_011912

def g32p_supplierForest_node_062633 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_062633 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062633 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129669 := by
  decide +kernel

theorem g32p_supplierForest_actual_062633 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062633) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_062633
    g32p_supplierForest_actual_129669

def g32p_supplierForest_node_062638 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062638 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062638 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_055928 := by
  decide +kernel

theorem g32p_supplierForest_actual_062638 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062638) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_062638
    g32p_supplierForest_actual_055928

def g32p_supplierForest_node_062671 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_062671 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062671 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_059631 := by
  decide +kernel

theorem g32p_supplierForest_actual_062671 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062671) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 1 g32p_supplierForest_edge_062671
    g32p_supplierForest_actual_059631

def g32p_supplierForest_node_062679 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062679 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062679 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_059847 := by
  decide +kernel

theorem g32p_supplierForest_actual_062679 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062679) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 1 g32p_supplierForest_edge_062679
    g32p_supplierForest_actual_059847

def g32p_supplierForest_node_062700 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_062700 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062700 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_059909 := by
  decide +kernel

theorem g32p_supplierForest_actual_062700 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062700) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 1 g32p_supplierForest_edge_062700
    g32p_supplierForest_actual_059909

def g32p_supplierForest_node_062716 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_062716 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062716 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129903 := by
  decide +kernel

theorem g32p_supplierForest_actual_062716 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062716) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_062716
    g32p_supplierForest_actual_129903

def g32p_supplierForest_node_062749 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_062749 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062749 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_050462 := by
  decide +kernel

theorem g32p_supplierForest_actual_062749 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062749) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 1 g32p_supplierForest_edge_062749
    g32p_supplierForest_actual_050462

def g32p_supplierForest_node_062808 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062808 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062808 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062869 := by
  decide +kernel

theorem g32p_supplierForest_actual_062808 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062808) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_062808
    g32p_supplierForest_actual_062869

def g32p_supplierForest_node_062818 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062818 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062818 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_060191 := by
  decide +kernel

theorem g32p_supplierForest_actual_062818 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062818) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 1 g32p_supplierForest_edge_062818
    g32p_supplierForest_actual_060191

def g32p_supplierForest_node_062821 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062821 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062821 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_055937 := by
  decide +kernel

theorem g32p_supplierForest_actual_062821 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062821) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_062821
    g32p_supplierForest_actual_055937

def g32p_supplierForest_node_062824 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_062824 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062824 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071643 := by
  decide +kernel

theorem g32p_supplierForest_actual_062824 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062824) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_062824
    g32p_supplierForest_actual_071643

def g32p_supplierForest_node_062837 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_062837 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062837 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_058991 := by
  decide +kernel

theorem g32p_supplierForest_actual_062837 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062837) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_062837
    g32p_supplierForest_actual_058991

def g32p_supplierForest_node_062847 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_062847 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062847 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130047 := by
  decide +kernel

theorem g32p_supplierForest_actual_062847 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062847) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_062847
    g32p_supplierForest_actual_130047

def g32p_supplierForest_node_062858 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_062858 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062858 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_008494 := by
  decide +kernel

theorem g32p_supplierForest_actual_062858 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062858) ∧
        IsConj g (g32p_literalRepresentative 23) := by
  exact g32p_archive_step_lift _ _ 23 1 g32p_supplierForest_edge_062858
    g32p_supplierForest_actual_008494

def g32p_supplierForest_node_062885 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062885 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062885 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_071455 := by
  decide +kernel

theorem g32p_supplierForest_actual_062885 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062885) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_062885
    g32p_supplierForest_actual_071455

def g32p_supplierForest_node_062946 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062946 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062946 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_060423 := by
  decide +kernel

theorem g32p_supplierForest_actual_062946 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062946) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_062946
    g32p_supplierForest_actual_060423

def g32p_supplierForest_node_062962 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062962 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062962 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_060458 := by
  decide +kernel

theorem g32p_supplierForest_actual_062962 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062962) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_062962
    g32p_supplierForest_actual_060458

def g32p_supplierForest_node_062979 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_062979 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062979 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_142298 := by
  decide +kernel

theorem g32p_supplierForest_actual_062979 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062979) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_062979
    g32p_supplierForest_actual_142298

def g32p_supplierForest_node_062993 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062993 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062993 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062994 := by
  decide +kernel

theorem g32p_supplierForest_actual_062993 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062993) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_062993
    g32p_supplierForest_actual_062994

def g32p_supplierForest_node_062999 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062999 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062999 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_008659 := by
  decide +kernel

theorem g32p_supplierForest_actual_062999 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062999) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_062999
    g32p_supplierForest_actual_008659

def g32p_supplierForest_node_063054 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_063054 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063054 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130235 := by
  decide +kernel

theorem g32p_supplierForest_actual_063054 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063054) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 0 g32p_supplierForest_edge_063054
    g32p_supplierForest_actual_130235

def g32p_supplierForest_node_063055 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_063055 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063055 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127918 := by
  decide +kernel

theorem g32p_supplierForest_actual_063055 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063055) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 0 g32p_supplierForest_edge_063055
    g32p_supplierForest_actual_127918

def g32p_supplierForest_node_063060 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_063060 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063060 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130233 := by
  decide +kernel

theorem g32p_supplierForest_actual_063060 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063060) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_063060
    g32p_supplierForest_actual_130233

def g32p_supplierForest_node_063062 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063062 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063062 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130244 := by
  decide +kernel

theorem g32p_supplierForest_actual_063062 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063062) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_063062
    g32p_supplierForest_actual_130244

def g32p_supplierForest_node_063082 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_063082 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063082 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_061151 := by
  decide +kernel

theorem g32p_supplierForest_actual_063082 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063082) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 1 g32p_supplierForest_edge_063082
    g32p_supplierForest_actual_061151

def g32p_supplierForest_node_063105 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063105 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063105 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_059499 := by
  decide +kernel

theorem g32p_supplierForest_actual_063105 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063105) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_063105
    g32p_supplierForest_actual_059499

def g32p_supplierForest_node_063129 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_063129 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063129 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_136682 := by
  decide +kernel

theorem g32p_supplierForest_actual_063129 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063129) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_063129
    g32p_supplierForest_actual_136682

def g32p_supplierForest_node_063188 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_063188 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063188 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051297 := by
  decide +kernel

theorem g32p_supplierForest_actual_063188 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063188) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_063188
    g32p_supplierForest_actual_051297

def g32p_supplierForest_node_063200 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_063200 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063200 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130357 := by
  decide +kernel

theorem g32p_supplierForest_actual_063200 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063200) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_063200
    g32p_supplierForest_actual_130357

def g32p_supplierForest_node_063203 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063203 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063203 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130363 := by
  decide +kernel

theorem g32p_supplierForest_actual_063203 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063203) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_063203
    g32p_supplierForest_actual_130363

def g32p_supplierForest_node_063218 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063218 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063218 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_058965 := by
  decide +kernel

theorem g32p_supplierForest_actual_063218 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063218) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_063218
    g32p_supplierForest_actual_058965

def g32p_supplierForest_node_063254 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063254 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063254 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_061754 := by
  decide +kernel

theorem g32p_supplierForest_actual_063254 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063254) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 1 g32p_supplierForest_edge_063254
    g32p_supplierForest_actual_061754

def g32p_supplierForest_node_063265 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_063265 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063265 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_045739 := by
  decide +kernel

theorem g32p_supplierForest_actual_063265 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063265) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_063265
    g32p_supplierForest_actual_045739

def g32p_supplierForest_node_063275 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_063275 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063275 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_134685 := by
  decide +kernel

theorem g32p_supplierForest_actual_063275 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063275) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_063275
    g32p_supplierForest_actual_134685

def g32p_supplierForest_node_063290 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_063290 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063290 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_048312 := by
  decide +kernel

theorem g32p_supplierForest_actual_063290 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063290) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_063290
    g32p_supplierForest_actual_048312

def g32p_supplierForest_node_063341 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063341 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063341 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_061888 := by
  decide +kernel

theorem g32p_supplierForest_actual_063341 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063341) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_063341
    g32p_supplierForest_actual_061888

def g32p_supplierForest_node_063343 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063343 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063343 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_061842 := by
  decide +kernel

theorem g32p_supplierForest_actual_063343 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063343) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_063343
    g32p_supplierForest_actual_061842

def g32p_supplierForest_node_063435 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_063435 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063435 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_056023 := by
  decide +kernel

theorem g32p_supplierForest_actual_063435 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063435) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_063435
    g32p_supplierForest_actual_056023

def g32p_supplierForest_node_063458 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_063458 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063458 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_045821 := by
  decide +kernel

theorem g32p_supplierForest_actual_063458 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063458) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_063458
    g32p_supplierForest_actual_045821

def g32p_supplierForest_node_063462 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_063462 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063462 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130587 := by
  decide +kernel

theorem g32p_supplierForest_actual_063462 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063462) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_063462
    g32p_supplierForest_actual_130587

def g32p_supplierForest_node_063466 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_063466 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063466 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_062255 := by
  decide +kernel

theorem g32p_supplierForest_actual_063466 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063466) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_063466
    g32p_supplierForest_actual_062255

def g32p_supplierForest_node_063532 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063532 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063532 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_063594 := by
  decide +kernel

theorem g32p_supplierForest_actual_063532 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063532) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_063532
    g32p_supplierForest_actual_063594

def g32p_supplierForest_node_063556 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_063556 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063556 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_009065 := by
  decide +kernel

theorem g32p_supplierForest_actual_063556 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063556) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_063556
    g32p_supplierForest_actual_009065

def g32p_supplierForest_node_063562 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_063562 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063562 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_062536 := by
  decide +kernel

theorem g32p_supplierForest_actual_063562 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063562) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_063562
    g32p_supplierForest_actual_062536

def g32p_supplierForest_node_063607 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063607 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063607 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128221 := by
  decide +kernel

theorem g32p_supplierForest_actual_063607 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063607) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_063607
    g32p_supplierForest_actual_128221

def g32p_supplierForest_node_063628 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_063628 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063628 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062288 := by
  decide +kernel

theorem g32p_supplierForest_actual_063628 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063628) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_063628
    g32p_supplierForest_actual_062288

def g32p_supplierForest_node_063642 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_063642 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063642 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_058197 := by
  decide +kernel

theorem g32p_supplierForest_actual_063642 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063642) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_063642
    g32p_supplierForest_actual_058197

def g32p_supplierForest_node_063673 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_063673 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063673 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064804 := by
  decide +kernel

theorem g32p_supplierForest_actual_063673 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063673) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_063673
    g32p_supplierForest_actual_064804

def g32p_supplierForest_node_063682 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063682 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063682 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_065956 := by
  decide +kernel

theorem g32p_supplierForest_actual_063682 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063682) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_063682
    g32p_supplierForest_actual_065956

def g32p_supplierForest_node_063683 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063683 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063683 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_141329 := by
  decide +kernel

theorem g32p_supplierForest_actual_063683 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063683) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_063683
    g32p_supplierForest_actual_141329

def g32p_supplierForest_node_063692 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_063692 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063692 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_062812 := by
  decide +kernel

theorem g32p_supplierForest_actual_063692 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063692) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_063692
    g32p_supplierForest_actual_062812

def g32p_supplierForest_node_063697 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063697 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063697 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_068362 := by
  decide +kernel

theorem g32p_supplierForest_actual_063697 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063697) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_063697
    g32p_supplierForest_actual_068362

def g32p_supplierForest_node_063725 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063725 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063725 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_063157 := by
  decide +kernel

theorem g32p_supplierForest_actual_063725 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063725) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_063725
    g32p_supplierForest_actual_063157

def g32p_supplierForest_node_063738 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_063738 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063738 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_050978 := by
  decide +kernel

theorem g32p_supplierForest_actual_063738 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063738) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_063738
    g32p_supplierForest_actual_050978

def g32p_supplierForest_node_063769 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_063769 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063769 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_062393 := by
  decide +kernel

theorem g32p_supplierForest_actual_063769 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063769) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_063769
    g32p_supplierForest_actual_062393

def g32p_supplierForest_node_063784 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_063784 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063784 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_128481 := by
  decide +kernel

theorem g32p_supplierForest_actual_063784 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063784) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_063784
    g32p_supplierForest_actual_128481

def g32p_supplierForest_node_063786 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063786 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063786 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062411 := by
  decide +kernel

theorem g32p_supplierForest_actual_063786 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063786) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_063786
    g32p_supplierForest_actual_062411

def g32p_supplierForest_node_063798 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063798 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063798 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_060686 := by
  decide +kernel

theorem g32p_supplierForest_actual_063798 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063798) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 3 g32p_supplierForest_edge_063798
    g32p_supplierForest_actual_060686

def g32p_supplierForest_node_063800 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063800 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063800 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_008601 := by
  decide +kernel

theorem g32p_supplierForest_actual_063800 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063800) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_063800
    g32p_supplierForest_actual_008601

def g32p_supplierForest_node_063818 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063818 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063818 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_044467 := by
  decide +kernel

theorem g32p_supplierForest_actual_063818 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063818) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_063818
    g32p_supplierForest_actual_044467

def g32p_supplierForest_node_063829 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_063829 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063829 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129557 := by
  decide +kernel

theorem g32p_supplierForest_actual_063829 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063829) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_063829
    g32p_supplierForest_actual_129557

def g32p_supplierForest_node_063848 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_063848 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063848 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065606 := by
  decide +kernel

theorem g32p_supplierForest_actual_063848 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063848) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 2 g32p_supplierForest_edge_063848
    g32p_supplierForest_actual_065606

def g32p_supplierForest_node_063865 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063865 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063865 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_056420 := by
  decide +kernel

theorem g32p_supplierForest_actual_063865 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063865) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_063865
    g32p_supplierForest_actual_056420

def g32p_supplierForest_node_063885 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063885 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063885 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130959 := by
  decide +kernel

theorem g32p_supplierForest_actual_063885 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063885) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_063885
    g32p_supplierForest_actual_130959

def g32p_supplierForest_node_063898 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063898 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063898 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_009485 := by
  decide +kernel

theorem g32p_supplierForest_actual_063898 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063898) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_063898
    g32p_supplierForest_actual_009485

def g32p_supplierForest_node_063910 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063910 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063910 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062876 := by
  decide +kernel

theorem g32p_supplierForest_actual_063910 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063910) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 2 g32p_supplierForest_edge_063910
    g32p_supplierForest_actual_062876

def g32p_supplierForest_node_063936 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_063936 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063936 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_059145 := by
  decide +kernel

theorem g32p_supplierForest_actual_063936 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063936) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_063936
    g32p_supplierForest_actual_059145

def g32p_supplierForest_node_063946 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063946 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063946 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_065336 := by
  decide +kernel

theorem g32p_supplierForest_actual_063946 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063946) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_063946
    g32p_supplierForest_actual_065336

def g32p_supplierForest_node_063981 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_063981 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063981 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130976 := by
  decide +kernel

theorem g32p_supplierForest_actual_063981 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063981) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_063981
    g32p_supplierForest_actual_130976

def g32p_supplierForest_node_063983 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063983 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063983 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067736 := by
  decide +kernel

theorem g32p_supplierForest_actual_063983 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063983) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_063983
    g32p_supplierForest_actual_067736

def g32p_supplierForest_node_064016 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_064016 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064016 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129113 := by
  decide +kernel

theorem g32p_supplierForest_actual_064016 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064016) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_064016
    g32p_supplierForest_actual_129113

def g32p_supplierForest_node_064032 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064032 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064032 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_065550 := by
  decide +kernel

theorem g32p_supplierForest_actual_064032 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064032) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_064032
    g32p_supplierForest_actual_065550

def g32p_supplierForest_node_064037 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064037 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064037 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_067602 := by
  decide +kernel

theorem g32p_supplierForest_actual_064037 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064037) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_064037
    g32p_supplierForest_actual_067602

def g32p_supplierForest_node_064059 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064059 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064059 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_046154 := by
  decide +kernel

theorem g32p_supplierForest_actual_064059 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064059) ∧
        IsConj g (g32p_literalRepresentative 23) := by
  exact g32p_archive_step_lift _ _ 23 0 g32p_supplierForest_edge_064059
    g32p_supplierForest_actual_046154

def g32p_supplierForest_node_064091 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_064091 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064091 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048989 := by
  decide +kernel

theorem g32p_supplierForest_actual_064091 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064091) ∧
        IsConj g (g32p_literalRepresentative 23) := by
  exact g32p_archive_step_lift _ _ 23 3 g32p_supplierForest_edge_064091
    g32p_supplierForest_actual_048989

def g32p_supplierForest_node_064127 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_064127 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064127 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_065810 := by
  decide +kernel

theorem g32p_supplierForest_actual_064127 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064127) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_064127
    g32p_supplierForest_actual_065810

def g32p_supplierForest_node_064141 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064141 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064141 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_053931 := by
  decide +kernel

theorem g32p_supplierForest_actual_064141 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064141) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_064141
    g32p_supplierForest_actual_053931

def g32p_supplierForest_node_064160 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064160 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064160 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_135972 := by
  decide +kernel

theorem g32p_supplierForest_actual_064160 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064160) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_064160
    g32p_supplierForest_actual_135972

def g32p_supplierForest_node_064167 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064167 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064167 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_059884 := by
  decide +kernel

theorem g32p_supplierForest_actual_064167 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064167) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_064167
    g32p_supplierForest_actual_059884

def g32p_supplierForest_node_064184 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064184 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064184 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_131203 := by
  decide +kernel

theorem g32p_supplierForest_actual_064184 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064184) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_064184
    g32p_supplierForest_actual_131203

def g32p_supplierForest_node_064188 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_064188 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064188 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129697 := by
  decide +kernel

theorem g32p_supplierForest_actual_064188 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064188) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_064188
    g32p_supplierForest_actual_129697

def g32p_supplierForest_node_064195 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064195 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064195 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051445 := by
  decide +kernel

theorem g32p_supplierForest_actual_064195 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064195) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_064195
    g32p_supplierForest_actual_051445

def g32p_supplierForest_node_064238 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_064238 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064238 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_056277 := by
  decide +kernel

theorem g32p_supplierForest_actual_064238 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064238) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_064238
    g32p_supplierForest_actual_056277

def g32p_supplierForest_node_064254 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064254 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064254 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065880 := by
  decide +kernel

theorem g32p_supplierForest_actual_064254 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064254) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_064254
    g32p_supplierForest_actual_065880

def g32p_supplierForest_node_064262 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064262 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064262 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_060628 := by
  decide +kernel

theorem g32p_supplierForest_actual_064262 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064262) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_064262
    g32p_supplierForest_actual_060628

def g32p_supplierForest_node_064322 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_064322 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064322 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012081 := by
  decide +kernel

theorem g32p_supplierForest_actual_064322 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064322) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_064322
    g32p_supplierForest_actual_012081

def g32p_supplierForest_node_064375 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_064375 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064375 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_046341 := by
  decide +kernel

theorem g32p_supplierForest_actual_064375 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064375) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 0 g32p_supplierForest_edge_064375
    g32p_supplierForest_actual_046341

def g32p_supplierForest_node_064394 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_064394 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064394 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_066381 := by
  decide +kernel

theorem g32p_supplierForest_actual_064394 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064394) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_064394
    g32p_supplierForest_actual_066381

def g32p_supplierForest_node_064430 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064430 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064430 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_066450 := by
  decide +kernel

theorem g32p_supplierForest_actual_064430 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064430) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 1 g32p_supplierForest_edge_064430
    g32p_supplierForest_actual_066450

def g32p_supplierForest_node_064435 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064435 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064435 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_066459 := by
  decide +kernel

theorem g32p_supplierForest_actual_064435 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064435) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_064435
    g32p_supplierForest_actual_066459

def g32p_supplierForest_node_064457 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_064457 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064457 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_046887 := by
  decide +kernel

theorem g32p_supplierForest_actual_064457 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064457) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_064457
    g32p_supplierForest_actual_046887

def g32p_supplierForest_node_064497 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064497 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064497 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_131236 := by
  decide +kernel

theorem g32p_supplierForest_actual_064497 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064497) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_064497
    g32p_supplierForest_actual_131236

def g32p_supplierForest_node_064514 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_064514 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064514 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051046 := by
  decide +kernel

theorem g32p_supplierForest_actual_064514 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064514) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_064514
    g32p_supplierForest_actual_051046

def g32p_supplierForest_node_064581 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064581 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064581 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_044432 := by
  decide +kernel

theorem g32p_supplierForest_actual_064581 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064581) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 3 g32p_supplierForest_edge_064581
    g32p_supplierForest_actual_044432

def g32p_supplierForest_node_064584 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064584 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064584 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_066736 := by
  decide +kernel

theorem g32p_supplierForest_actual_064584 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064584) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 1 g32p_supplierForest_edge_064584
    g32p_supplierForest_actual_066736

def g32p_supplierForest_node_064596 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064596 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064596 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_054054 := by
  decide +kernel

theorem g32p_supplierForest_actual_064596 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064596) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_064596
    g32p_supplierForest_actual_054054

def g32p_supplierForest_node_064623 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_064623 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064623 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_051272 := by
  decide +kernel

theorem g32p_supplierForest_actual_064623 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064623) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_064623
    g32p_supplierForest_actual_051272

def g32p_supplierForest_node_064653 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_064653 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064653 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_051373 := by
  decide +kernel

theorem g32p_supplierForest_actual_064653 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064653) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_064653
    g32p_supplierForest_actual_051373

def g32p_supplierForest_node_064669 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_064669 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064669 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_055354 := by
  decide +kernel

theorem g32p_supplierForest_actual_064669 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064669) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_064669
    g32p_supplierForest_actual_055354

def g32p_supplierForest_node_064684 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064684 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064684 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130398 := by
  decide +kernel

theorem g32p_supplierForest_actual_064684 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064684) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 0 g32p_supplierForest_edge_064684
    g32p_supplierForest_actual_130398

def g32p_supplierForest_node_064691 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_064691 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064691 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_051257 := by
  decide +kernel

theorem g32p_supplierForest_actual_064691 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064691) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 3 g32p_supplierForest_edge_064691
    g32p_supplierForest_actual_051257

def g32p_supplierForest_node_064736 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_064736 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064736 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_131622 := by
  decide +kernel

theorem g32p_supplierForest_actual_064736 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064736) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_064736
    g32p_supplierForest_actual_131622

def g32p_supplierForest_node_064759 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064759 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064759 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_063493 := by
  decide +kernel

theorem g32p_supplierForest_actual_064759 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064759) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_064759
    g32p_supplierForest_actual_063493

def g32p_supplierForest_node_064772 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064772 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064772 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_058179 := by
  decide +kernel

theorem g32p_supplierForest_actual_064772 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064772) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_064772
    g32p_supplierForest_actual_058179

def g32p_supplierForest_node_064781 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064781 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064781 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067037 := by
  decide +kernel

theorem g32p_supplierForest_actual_064781 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064781) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_064781
    g32p_supplierForest_actual_067037

def g32p_supplierForest_node_064784 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064784 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064784 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_139255 := by
  decide +kernel

theorem g32p_supplierForest_actual_064784 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064784) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_064784
    g32p_supplierForest_actual_139255

def g32p_supplierForest_node_064788 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064788 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064788 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_061048 := by
  decide +kernel

theorem g32p_supplierForest_actual_064788 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064788) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_064788
    g32p_supplierForest_actual_061048

def g32p_supplierForest_node_064827 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064827 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064827 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067703 := by
  decide +kernel

theorem g32p_supplierForest_actual_064827 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064827) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 2 g32p_supplierForest_edge_064827
    g32p_supplierForest_actual_067703

def g32p_supplierForest_node_064835 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064835 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064835 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_054654 := by
  decide +kernel

theorem g32p_supplierForest_actual_064835 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064835) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_064835
    g32p_supplierForest_actual_054654

def g32p_supplierForest_node_064846 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064846 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064846 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_131825 := by
  decide +kernel

theorem g32p_supplierForest_actual_064846 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064846) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_064846
    g32p_supplierForest_actual_131825

def g32p_supplierForest_node_064882 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_064882 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064882 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_068933 := by
  decide +kernel

theorem g32p_supplierForest_actual_064882 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064882) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 2 g32p_supplierForest_edge_064882
    g32p_supplierForest_actual_068933

def g32p_supplierForest_node_064906 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_064906 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064906 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010058 := by
  decide +kernel

theorem g32p_supplierForest_actual_064906 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064906) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_064906
    g32p_supplierForest_actual_010058

def g32p_supplierForest_node_064947 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064947 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064947 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_062939 := by
  decide +kernel

theorem g32p_supplierForest_actual_064947 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064947) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_064947
    g32p_supplierForest_actual_062939

def g32p_supplierForest_node_064962 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_064962 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064962 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067124 := by
  decide +kernel

theorem g32p_supplierForest_actual_064962 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064962) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 2 g32p_supplierForest_edge_064962
    g32p_supplierForest_actual_067124

def g32p_supplierForest_node_065017 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065017 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065017 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064682 := by
  decide +kernel

theorem g32p_supplierForest_actual_065017 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065017) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_065017
    g32p_supplierForest_actual_064682

def g32p_supplierForest_node_065105 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065105 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065105 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132050 := by
  decide +kernel

theorem g32p_supplierForest_actual_065105 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065105) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_065105
    g32p_supplierForest_actual_132050

def g32p_supplierForest_node_065145 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065145 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065145 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067742 := by
  decide +kernel

theorem g32p_supplierForest_actual_065145 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065145) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_065145
    g32p_supplierForest_actual_067742

def g32p_supplierForest_node_065166 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_065166 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065166 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_010718 := by
  decide +kernel

theorem g32p_supplierForest_actual_065166 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065166) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_065166
    g32p_supplierForest_actual_010718

def g32p_supplierForest_node_065175 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065175 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065175 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_065117 := by
  decide +kernel

theorem g32p_supplierForest_actual_065175 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065175) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_065175
    g32p_supplierForest_actual_065117

def g32p_supplierForest_node_065176 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065176 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065176 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130238 := by
  decide +kernel

theorem g32p_supplierForest_actual_065176 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065176) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_065176
    g32p_supplierForest_actual_130238

def g32p_supplierForest_node_065192 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_065192 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065192 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_056864 := by
  decide +kernel

theorem g32p_supplierForest_actual_065192 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065192) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_065192
    g32p_supplierForest_actual_056864

def g32p_supplierForest_node_065243 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065243 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065243 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063758 := by
  decide +kernel

theorem g32p_supplierForest_actual_065243 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065243) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_065243
    g32p_supplierForest_actual_063758

def g32p_supplierForest_node_065265 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065265 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065265 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_061841 := by
  decide +kernel

theorem g32p_supplierForest_actual_065265 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065265) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_065265
    g32p_supplierForest_actual_061841

def g32p_supplierForest_node_065283 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065283 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065283 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_047213 := by
  decide +kernel

theorem g32p_supplierForest_actual_065283 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065283) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_065283
    g32p_supplierForest_actual_047213

def g32p_supplierForest_node_065329 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065329 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065329 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065069 := by
  decide +kernel

theorem g32p_supplierForest_actual_065329 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065329) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_065329
    g32p_supplierForest_actual_065069

def g32p_supplierForest_node_065337 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_065337 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065337 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063552 := by
  decide +kernel

theorem g32p_supplierForest_actual_065337 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065337) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_065337
    g32p_supplierForest_actual_063552

def g32p_supplierForest_node_065342 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_065342 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065342 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_056568 := by
  decide +kernel

theorem g32p_supplierForest_actual_065342 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065342) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 3 g32p_supplierForest_edge_065342
    g32p_supplierForest_actual_056568

def g32p_supplierForest_node_065348 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_065348 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065348 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132259 := by
  decide +kernel

theorem g32p_supplierForest_actual_065348 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065348) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_065348
    g32p_supplierForest_actual_132259

def g32p_supplierForest_node_065384 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065384 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065384 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068348 := by
  decide +kernel

theorem g32p_supplierForest_actual_065384 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065384) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_065384
    g32p_supplierForest_actual_068348

def g32p_supplierForest_node_065404 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065404 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065404 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068388 := by
  decide +kernel

theorem g32p_supplierForest_actual_065404 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065404) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_065404
    g32p_supplierForest_actual_068388

def g32p_supplierForest_node_065451 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_065451 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065451 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_063202 := by
  decide +kernel

theorem g32p_supplierForest_actual_065451 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065451) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_065451
    g32p_supplierForest_actual_063202

def g32p_supplierForest_node_065459 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065459 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065459 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132363 := by
  decide +kernel

theorem g32p_supplierForest_actual_065459 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065459) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_065459
    g32p_supplierForest_actual_132363

def g32p_supplierForest_node_065465 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065465 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065465 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_052905 := by
  decide +kernel

theorem g32p_supplierForest_actual_065465 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065465) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_065465
    g32p_supplierForest_actual_052905

def g32p_supplierForest_node_065487 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_065487 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065487 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_063746 := by
  decide +kernel

theorem g32p_supplierForest_actual_065487 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065487) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_065487
    g32p_supplierForest_actual_063746

def g32p_supplierForest_node_065531 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065531 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065531 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_011018 := by
  decide +kernel

theorem g32p_supplierForest_actual_065531 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065531) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_065531
    g32p_supplierForest_actual_011018

def g32p_supplierForest_node_065539 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065539 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065539 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132419 := by
  decide +kernel

theorem g32p_supplierForest_actual_065539 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065539) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_065539
    g32p_supplierForest_actual_132419

def g32p_supplierForest_node_065561 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065561 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065561 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_060300 := by
  decide +kernel

theorem g32p_supplierForest_actual_065561 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065561) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_065561
    g32p_supplierForest_actual_060300

def g32p_supplierForest_node_065573 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065573 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065573 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_056539 := by
  decide +kernel

theorem g32p_supplierForest_actual_065573 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065573) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_065573
    g32p_supplierForest_actual_056539

def g32p_supplierForest_node_065607 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065607 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065607 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132486 := by
  decide +kernel

theorem g32p_supplierForest_actual_065607 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065607) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_065607
    g32p_supplierForest_actual_132486

def g32p_supplierForest_node_065611 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_065611 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065611 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132492 := by
  decide +kernel

theorem g32p_supplierForest_actual_065611 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065611) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_065611
    g32p_supplierForest_actual_132492

def g32p_supplierForest_node_065647 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065647 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065647 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067683 := by
  decide +kernel

theorem g32p_supplierForest_actual_065647 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065647) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_065647
    g32p_supplierForest_actual_067683

def g32p_supplierForest_node_065666 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_065666 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065666 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132530 := by
  decide +kernel

theorem g32p_supplierForest_actual_065666 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065666) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 0 g32p_supplierForest_edge_065666
    g32p_supplierForest_actual_132530

def g32p_supplierForest_node_065683 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065683 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065683 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_068075 := by
  decide +kernel

theorem g32p_supplierForest_actual_065683 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065683) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_065683
    g32p_supplierForest_actual_068075

def g32p_supplierForest_node_065693 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065693 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065693 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_055182 := by
  decide +kernel

theorem g32p_supplierForest_actual_065693 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065693) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_065693
    g32p_supplierForest_actual_055182

def g32p_supplierForest_node_065694 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065694 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065694 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068927 := by
  decide +kernel

theorem g32p_supplierForest_actual_065694 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065694) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_065694
    g32p_supplierForest_actual_068927

def g32p_supplierForest_node_065714 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_065714 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065714 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_131901 := by
  decide +kernel

theorem g32p_supplierForest_actual_065714 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065714) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 0 g32p_supplierForest_edge_065714
    g32p_supplierForest_actual_131901

def g32p_supplierForest_node_065732 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065732 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065732 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_142663 := by
  decide +kernel

theorem g32p_supplierForest_actual_065732 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065732) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_065732
    g32p_supplierForest_actual_142663

def g32p_supplierForest_node_065743 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_065743 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065743 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132594 := by
  decide +kernel

theorem g32p_supplierForest_actual_065743 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065743) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 0 g32p_supplierForest_edge_065743
    g32p_supplierForest_actual_132594

def g32p_supplierForest_node_065758 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065758 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065758 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_068530 := by
  decide +kernel

theorem g32p_supplierForest_actual_065758 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065758) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_065758
    g32p_supplierForest_actual_068530

def g32p_supplierForest_node_065759 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_065759 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065759 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065562 := by
  decide +kernel

theorem g32p_supplierForest_actual_065759 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065759) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_065759
    g32p_supplierForest_actual_065562

def g32p_supplierForest_node_065769 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_065769 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065769 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_130466 := by
  decide +kernel

theorem g32p_supplierForest_actual_065769 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065769) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 2 g32p_supplierForest_edge_065769
    g32p_supplierForest_actual_130466

def g32p_supplierForest_node_065782 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065782 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065782 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132627 := by
  decide +kernel

theorem g32p_supplierForest_actual_065782 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065782) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 0 g32p_supplierForest_edge_065782
    g32p_supplierForest_actual_132627

def g32p_supplierForest_node_065793 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065793 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065793 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064116 := by
  decide +kernel

theorem g32p_supplierForest_actual_065793 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065793) ∧
        IsConj g (g32p_literalRepresentative 18) := by
  exact g32p_archive_step_lift _ _ 18 3 g32p_supplierForest_edge_065793
    g32p_supplierForest_actual_064116

def g32p_supplierForest_node_065794 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065794 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065794 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_143531 := by
  decide +kernel

theorem g32p_supplierForest_actual_065794 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065794) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_065794
    g32p_supplierForest_actual_143531

def g32p_supplierForest_node_065801 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065801 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065801 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_045764 := by
  decide +kernel

theorem g32p_supplierForest_actual_065801 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065801) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_065801
    g32p_supplierForest_actual_045764

def g32p_supplierForest_node_065830 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_065830 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065830 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_009367 := by
  decide +kernel

theorem g32p_supplierForest_actual_065830 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065830) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_065830
    g32p_supplierForest_actual_009367

def g32p_supplierForest_node_065843 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_065843 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065843 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_048990 := by
  decide +kernel

theorem g32p_supplierForest_actual_065843 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065843) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 1 g32p_supplierForest_edge_065843
    g32p_supplierForest_actual_048990

def g32p_supplierForest_node_065849 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065849 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065849 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132677 := by
  decide +kernel

theorem g32p_supplierForest_actual_065849 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065849) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 0 g32p_supplierForest_edge_065849
    g32p_supplierForest_actual_132677

def g32p_supplierForest_node_065862 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065862 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065862 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_069182 := by
  decide +kernel

theorem g32p_supplierForest_actual_065862 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065862) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_065862
    g32p_supplierForest_actual_069182

def g32p_supplierForest_node_065875 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065875 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065875 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128882 := by
  decide +kernel

theorem g32p_supplierForest_actual_065875 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065875) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 0 g32p_supplierForest_edge_065875
    g32p_supplierForest_actual_128882

def g32p_supplierForest_node_065878 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065878 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065878 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_069562 := by
  decide +kernel

theorem g32p_supplierForest_actual_065878 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065878) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_065878
    g32p_supplierForest_actual_069562

def g32p_supplierForest_node_065931 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065931 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065931 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132750 := by
  decide +kernel

theorem g32p_supplierForest_actual_065931 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065931) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_065931
    g32p_supplierForest_actual_132750

def g32p_supplierForest_node_065946 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065946 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065946 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_066285 := by
  decide +kernel

theorem g32p_supplierForest_actual_065946 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065946) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_065946
    g32p_supplierForest_actual_066285

def g32p_supplierForest_node_065969 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065969 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065969 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065279 := by
  decide +kernel

theorem g32p_supplierForest_actual_065969 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065969) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_065969
    g32p_supplierForest_actual_065279

def g32p_supplierForest_node_065979 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_065979 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065979 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_047249 := by
  decide +kernel

theorem g32p_supplierForest_actual_065979 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065979) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_065979
    g32p_supplierForest_actual_047249

def g32p_supplierForest_node_065993 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065993 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065993 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_059192 := by
  decide +kernel

theorem g32p_supplierForest_actual_065993 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065993) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_065993
    g32p_supplierForest_actual_059192

def g32p_supplierForest_node_066012 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066012 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066012 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_061618 := by
  decide +kernel

theorem g32p_supplierForest_actual_066012 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066012) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_066012
    g32p_supplierForest_actual_061618

def g32p_supplierForest_node_066018 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066018 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066018 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_069513 := by
  decide +kernel

theorem g32p_supplierForest_actual_066018 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066018) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 1 g32p_supplierForest_edge_066018
    g32p_supplierForest_actual_069513

def g32p_supplierForest_node_066059 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066059 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066059 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_069552 := by
  decide +kernel

theorem g32p_supplierForest_actual_066059 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066059) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_066059
    g32p_supplierForest_actual_069552

def g32p_supplierForest_node_066070 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066070 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066070 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128242 := by
  decide +kernel

theorem g32p_supplierForest_actual_066070 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066070) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_066070
    g32p_supplierForest_actual_128242

def g32p_supplierForest_node_066136 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066136 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066136 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048666 := by
  decide +kernel

theorem g32p_supplierForest_actual_066136 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066136) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 3 g32p_supplierForest_edge_066136
    g32p_supplierForest_actual_048666

def g32p_supplierForest_node_066142 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066142 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066142 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132931 := by
  decide +kernel

theorem g32p_supplierForest_actual_066142 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066142) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_066142
    g32p_supplierForest_actual_132931

def g32p_supplierForest_node_066157 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066157 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066157 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_070781 := by
  decide +kernel

theorem g32p_supplierForest_actual_066157 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066157) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_066157
    g32p_supplierForest_actual_070781

def g32p_supplierForest_node_066171 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_066171 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066171 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_050942 := by
  decide +kernel

theorem g32p_supplierForest_actual_066171 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066171) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_066171
    g32p_supplierForest_actual_050942

def g32p_supplierForest_node_066172 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066172 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066172 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_066862 := by
  decide +kernel

theorem g32p_supplierForest_actual_066172 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066172) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 1 g32p_supplierForest_edge_066172
    g32p_supplierForest_actual_066862

def g32p_supplierForest_node_066182 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066182 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066182 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_045178 := by
  decide +kernel

theorem g32p_supplierForest_actual_066182 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066182) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 1 g32p_supplierForest_edge_066182
    g32p_supplierForest_actual_045178

def g32p_supplierForest_node_066195 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_066195 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066195 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_069776 := by
  decide +kernel

theorem g32p_supplierForest_actual_066195 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066195) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_066195
    g32p_supplierForest_actual_069776

def g32p_supplierForest_node_066248 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066248 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066248 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_063995 := by
  decide +kernel

theorem g32p_supplierForest_actual_066248 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066248) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_066248
    g32p_supplierForest_actual_063995

def g32p_supplierForest_node_066303 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066303 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066303 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_048284 := by
  decide +kernel

theorem g32p_supplierForest_actual_066303 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066303) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_066303
    g32p_supplierForest_actual_048284

def g32p_supplierForest_node_066312 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066312 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066312 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_140134 := by
  decide +kernel

theorem g32p_supplierForest_actual_066312 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066312) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_066312
    g32p_supplierForest_actual_140134

def g32p_supplierForest_node_066327 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066327 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066327 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067348 := by
  decide +kernel

theorem g32p_supplierForest_actual_066327 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066327) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_066327
    g32p_supplierForest_actual_067348

def g32p_supplierForest_node_066351 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_066351 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066351 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_070088 := by
  decide +kernel

theorem g32p_supplierForest_actual_066351 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066351) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_066351
    g32p_supplierForest_actual_070088

def g32p_supplierForest_node_066357 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066357 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066357 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_133096 := by
  decide +kernel

theorem g32p_supplierForest_actual_066357 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066357) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_066357
    g32p_supplierForest_actual_133096

def g32p_supplierForest_node_066366 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_066366 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066366 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064077 := by
  decide +kernel

theorem g32p_supplierForest_actual_066366 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066366) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_066366
    g32p_supplierForest_actual_064077

def g32p_supplierForest_node_066390 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_066390 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066390 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_070146 := by
  decide +kernel

theorem g32p_supplierForest_actual_066390 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066390) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_066390
    g32p_supplierForest_actual_070146

def g32p_supplierForest_node_066415 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_066415 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066415 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_045721 := by
  decide +kernel

theorem g32p_supplierForest_actual_066415 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066415) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_066415
    g32p_supplierForest_actual_045721

def g32p_supplierForest_node_066417 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066417 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066417 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_046089 := by
  decide +kernel

theorem g32p_supplierForest_actual_066417 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066417) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 1 g32p_supplierForest_edge_066417
    g32p_supplierForest_actual_046089

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_088 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_019089 else g32p_supplierForest_node_019097) else (if i.val < 3 then g32p_supplierForest_node_019109 else g32p_supplierForest_node_019147)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_019152 else g32p_supplierForest_node_019163) else (if i.val < 7 then g32p_supplierForest_node_019217 else g32p_supplierForest_node_019239))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_019285 else g32p_supplierForest_node_019290) else (if i.val < 11 then g32p_supplierForest_node_019296 else g32p_supplierForest_node_019303)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_019327 else g32p_supplierForest_node_019348) else (if i.val < 15 then g32p_supplierForest_node_019351 else g32p_supplierForest_node_019383)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_019396 else g32p_supplierForest_node_019405) else (if i.val < 19 then g32p_supplierForest_node_019419 else g32p_supplierForest_node_019498)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_019502 else g32p_supplierForest_node_019504) else (if i.val < 23 then g32p_supplierForest_node_019538 else g32p_supplierForest_node_019620))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_019715 else g32p_supplierForest_node_019751) else (if i.val < 27 then g32p_supplierForest_node_019798 else g32p_supplierForest_node_019801)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_019865 else g32p_supplierForest_node_019880) else (if i.val < 31 then g32p_supplierForest_node_019884 else g32p_supplierForest_node_019907))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_019965 else g32p_supplierForest_node_019990) else (if i.val < 35 then g32p_supplierForest_node_020019 else g32p_supplierForest_node_020054)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_020061 else g32p_supplierForest_node_020134) else (if i.val < 39 then g32p_supplierForest_node_020151 else g32p_supplierForest_node_020213))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_020270 else g32p_supplierForest_node_020315) else (if i.val < 43 then g32p_supplierForest_node_020327 else g32p_supplierForest_node_020352)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_020360 else g32p_supplierForest_node_020370) else (if i.val < 47 then g32p_supplierForest_node_020420 else g32p_supplierForest_node_020442)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_020467 else g32p_supplierForest_node_020470) else (if i.val < 51 then g32p_supplierForest_node_020488 else g32p_supplierForest_node_020496)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_020536 else g32p_supplierForest_node_020543) else (if i.val < 55 then g32p_supplierForest_node_020547 else g32p_supplierForest_node_020560))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_020576 else g32p_supplierForest_node_020592) else (if i.val < 59 then g32p_supplierForest_node_020613 else g32p_supplierForest_node_020673)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_020682 else g32p_supplierForest_node_020696) else (if i.val < 63 then g32p_supplierForest_node_020711 else g32p_supplierForest_node_020728)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_020739 else g32p_supplierForest_node_020749) else (if i.val < 67 then g32p_supplierForest_node_020771 else g32p_supplierForest_node_020796)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_020807 else g32p_supplierForest_node_020824) else (if i.val < 71 then g32p_supplierForest_node_020828 else g32p_supplierForest_node_020919))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_020939 else g32p_supplierForest_node_021117) else (if i.val < 75 then g32p_supplierForest_node_021135 else g32p_supplierForest_node_021174)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_021219 else g32p_supplierForest_node_021233) else (if i.val < 79 then g32p_supplierForest_node_021236 else g32p_supplierForest_node_021277)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_021316 else g32p_supplierForest_node_021343) else (if i.val < 83 then g32p_supplierForest_node_021368 else g32p_supplierForest_node_021408)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_021413 else g32p_supplierForest_node_021427) else (if i.val < 87 then g32p_supplierForest_node_021458 else g32p_supplierForest_node_021462))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_021467 else g32p_supplierForest_node_021484) else (if i.val < 91 then g32p_supplierForest_node_021522 else g32p_supplierForest_node_021591)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_021619 else g32p_supplierForest_node_021629) else (if i.val < 95 then g32p_supplierForest_node_021647 else g32p_supplierForest_node_021671))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_021680 else g32p_supplierForest_node_021769) else (if i.val < 99 then g32p_supplierForest_node_021773 else g32p_supplierForest_node_021783)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_021796 else g32p_supplierForest_node_021800) else (if i.val < 103 then g32p_supplierForest_node_021817 else g32p_supplierForest_node_021825))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_021830 else g32p_supplierForest_node_021858) else (if i.val < 107 then g32p_supplierForest_node_021908 else g32p_supplierForest_node_021956)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_021980 else g32p_supplierForest_node_021995) else (if i.val < 111 then g32p_supplierForest_node_022000 else g32p_supplierForest_node_022010)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_022048 else g32p_supplierForest_node_022075) else (if i.val < 115 then g32p_supplierForest_node_022082 else g32p_supplierForest_node_022130)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_022206 else g32p_supplierForest_node_022237) else (if i.val < 119 then g32p_supplierForest_node_022280 else g32p_supplierForest_node_022300))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_022317 else g32p_supplierForest_node_022338) else (if i.val < 123 then g32p_supplierForest_node_022408 else g32p_supplierForest_node_022440)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_022442 else g32p_supplierForest_node_022450) else (if i.val < 127 then g32p_supplierForest_node_022484 else g32p_supplierForest_node_022500))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_022522 else g32p_supplierForest_node_022530) else (if i.val < 131 then g32p_supplierForest_node_022541 else g32p_supplierForest_node_022572)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_022606 else g32p_supplierForest_node_022634) else (if i.val < 135 then g32p_supplierForest_node_022672 else g32p_supplierForest_node_022725))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_022756 else g32p_supplierForest_node_022802) else (if i.val < 139 then g32p_supplierForest_node_022905 else g32p_supplierForest_node_023028)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_023079 else g32p_supplierForest_node_023083) else (if i.val < 143 then g32p_supplierForest_node_023130 else g32p_supplierForest_node_023193)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_023244 else g32p_supplierForest_node_023255) else (if i.val < 147 then g32p_supplierForest_node_023262 else g32p_supplierForest_node_023281)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_023296 else g32p_supplierForest_node_023411) else (if i.val < 151 then g32p_supplierForest_node_023414 else g32p_supplierForest_node_023430))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_023433 else g32p_supplierForest_node_023436) else (if i.val < 155 then g32p_supplierForest_node_023481 else g32p_supplierForest_node_023502)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_023552 else g32p_supplierForest_node_023582) else (if i.val < 159 then g32p_supplierForest_node_023593 else g32p_supplierForest_node_023684))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_023718 else g32p_supplierForest_node_023723) else (if i.val < 163 then g32p_supplierForest_node_023792 else g32p_supplierForest_node_023801)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_023809 else g32p_supplierForest_node_023814) else (if i.val < 167 then g32p_supplierForest_node_023850 else g32p_supplierForest_node_023854))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_023878 else g32p_supplierForest_node_023918) else (if i.val < 171 then g32p_supplierForest_node_023940 else g32p_supplierForest_node_023959)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_023977 else g32p_supplierForest_node_023992) else (if i.val < 175 then g32p_supplierForest_node_024003 else g32p_supplierForest_node_024041)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_024170 else g32p_supplierForest_node_024171) else (if i.val < 179 then g32p_supplierForest_node_024299 else g32p_supplierForest_node_024315)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_024362 else g32p_supplierForest_node_024372) else (if i.val < 183 then g32p_supplierForest_node_024394 else g32p_supplierForest_node_024430))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_024433 else g32p_supplierForest_node_024457) else (if i.val < 187 then g32p_supplierForest_node_024468 else g32p_supplierForest_node_024520)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_024547 else g32p_supplierForest_node_024562) else (if i.val < 191 then g32p_supplierForest_node_024567 else g32p_supplierForest_node_024595)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_024618 else g32p_supplierForest_node_024631) else (if i.val < 195 then g32p_supplierForest_node_024634 else g32p_supplierForest_node_024664)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_024677 else g32p_supplierForest_node_024701) else (if i.val < 199 then g32p_supplierForest_node_024783 else g32p_supplierForest_node_024798))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_024826 else g32p_supplierForest_node_024832) else (if i.val < 203 then g32p_supplierForest_node_024893 else g32p_supplierForest_node_024896)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_024901 else g32p_supplierForest_node_024939) else (if i.val < 207 then g32p_supplierForest_node_024946 else g32p_supplierForest_node_024968)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_025022 else g32p_supplierForest_node_025045) else (if i.val < 211 then g32p_supplierForest_node_025046 else g32p_supplierForest_node_025054)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_025069 else g32p_supplierForest_node_025179) else (if i.val < 215 then g32p_supplierForest_node_025213 else g32p_supplierForest_node_025243))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_025267 else g32p_supplierForest_node_025282) else (if i.val < 219 then g32p_supplierForest_node_025304 else g32p_supplierForest_node_025309)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_025339 else g32p_supplierForest_node_025341) else (if i.val < 223 then g32p_supplierForest_node_025361 else g32p_supplierForest_node_025365))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_025387 else g32p_supplierForest_node_025410) else (if i.val < 227 then g32p_supplierForest_node_025418 else g32p_supplierForest_node_025436)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_025437 else g32p_supplierForest_node_025457) else (if i.val < 231 then g32p_supplierForest_node_025527 else g32p_supplierForest_node_025565))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_025577 else g32p_supplierForest_node_025585) else (if i.val < 235 then g32p_supplierForest_node_025591 else g32p_supplierForest_node_025597)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_025603 else g32p_supplierForest_node_025623) else (if i.val < 239 then g32p_supplierForest_node_025648 else g32p_supplierForest_node_025652)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_025710 else g32p_supplierForest_node_025712) else (if i.val < 243 then g32p_supplierForest_node_025772 else g32p_supplierForest_node_025786)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_025815 else g32p_supplierForest_node_025823) else (if i.val < 247 then g32p_supplierForest_node_025828 else g32p_supplierForest_node_025942))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_025943 else g32p_supplierForest_node_025967) else (if i.val < 251 then g32p_supplierForest_node_026002 else g32p_supplierForest_node_026019)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_026029 else g32p_supplierForest_node_026049) else (if i.val < 255 then g32p_supplierForest_node_026050 else g32p_supplierForest_node_026111))))))))

def g32p_supplierForest_classes_088 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 46 else 49) else (if i.val < 3 then 12 else 26)) else (if i.val < 6 then (if i.val < 5 then 27 else 46) else (if i.val < 7 then 12 else 10))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 49 else 10) else (if i.val < 11 then 50 else 50)) else (if i.val < 14 then (if i.val < 13 then 46 else 9) else (if i.val < 15 then 48 else 26)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 47 else 26) else (if i.val < 19 then 45 else 25)) else (if i.val < 22 then (if i.val < 21 then 49 else 25) else (if i.val < 23 then 26 else 10))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 9 else 48) else (if i.val < 27 then 9 else 8)) else (if i.val < 30 then (if i.val < 29 then 25 else 10) else (if i.val < 31 then 26 else 26))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 48 else 10) else (if i.val < 35 then 49 else 47)) else (if i.val < 38 then (if i.val < 37 then 47 else 46) else (if i.val < 39 then 46 else 46))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 47 else 10) else (if i.val < 43 then 27 else 50)) else (if i.val < 46 then (if i.val < 45 then 27 else 45) else (if i.val < 47 then 10 else 49)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 12 else 49) else (if i.val < 51 then 47 else 47)) else (if i.val < 54 then (if i.val < 53 then 49 else 50) else (if i.val < 55 then 49 else 49))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 10 else 47) else (if i.val < 59 then 10 else 48)) else (if i.val < 62 then (if i.val < 61 then 49 else 10) else (if i.val < 63 then 27 else 49)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 25 else 27) else (if i.val < 67 then 26 else 48)) else (if i.val < 70 then (if i.val < 69 then 26 else 49) else (if i.val < 71 then 50 else 48))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 10 else 49) else (if i.val < 75 then 49 else 46)) else (if i.val < 78 then (if i.val < 77 then 25 else 49) else (if i.val < 79 then 12 else 50)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 49 else 48) else (if i.val < 83 then 49 else 27)) else (if i.val < 86 then (if i.val < 85 then 49 else 48) else (if i.val < 87 then 49 else 26))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 48 else 49) else (if i.val < 91 then 25 else 25)) else (if i.val < 94 then (if i.val < 93 then 49 else 49) else (if i.val < 95 then 46 else 46))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 9 else 47) else (if i.val < 99 then 50 else 25)) else (if i.val < 102 then (if i.val < 101 then 49 else 25) else (if i.val < 103 then 48 else 49))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 47 else 27) else (if i.val < 107 then 26 else 46)) else (if i.val < 110 then (if i.val < 109 then 49 else 45) else (if i.val < 111 then 26 else 49)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 25 else 49) else (if i.val < 115 then 48 else 25)) else (if i.val < 118 then (if i.val < 117 then 48 else 50) else (if i.val < 119 then 48 else 50))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 49 else 50) else (if i.val < 123 then 49 else 25)) else (if i.val < 126 then (if i.val < 125 then 8 else 27) else (if i.val < 127 then 26 else 12))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 26 else 26) else (if i.val < 131 then 26 else 10)) else (if i.val < 134 then (if i.val < 133 then 12 else 9) else (if i.val < 135 then 49 else 50))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 25 else 26) else (if i.val < 139 then 49 else 47)) else (if i.val < 142 then (if i.val < 141 then 27 else 47) else (if i.val < 143 then 48 else 10)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 9 else 47) else (if i.val < 147 then 46 else 49)) else (if i.val < 150 then (if i.val < 149 then 25 else 46) else (if i.val < 151 then 10 else 49))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 49 else 49) else (if i.val < 155 then 46 else 49)) else (if i.val < 158 then (if i.val < 157 then 9 else 47) else (if i.val < 159 then 10 else 47))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 49 else 9) else (if i.val < 163 then 50 else 46)) else (if i.val < 166 then (if i.val < 165 then 9 else 26) else (if i.val < 167 then 25 else 27))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 49 else 56) else (if i.val < 171 then 48 else 46)) else (if i.val < 174 then (if i.val < 173 then 49 else 27) else (if i.val < 175 then 27 else 48)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 49 else 46) else (if i.val < 179 then 26 else 26)) else (if i.val < 182 then (if i.val < 181 then 25 else 49) else (if i.val < 183 then 26 else 49))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 49 else 49) else (if i.val < 187 then 12 else 33)) else (if i.val < 190 then (if i.val < 189 then 36 else 15) else (if i.val < 191 then 17 else 17)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 14 else 16) else (if i.val < 195 then 30 else 30)) else (if i.val < 198 then (if i.val < 197 then 30 else 31) else (if i.val < 199 then 16 else 16))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 57 else 57) else (if i.val < 203 then 57 else 30)) else (if i.val < 206 then (if i.val < 205 then 32 else 32) else (if i.val < 207 then 57 else 59)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 14 else 57) else (if i.val < 211 then 17 else 30)) else (if i.val < 214 then (if i.val < 213 then 57 else 57) else (if i.val < 215 then 16 else 29))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 15 else 57) else (if i.val < 219 then 57 else 14)) else (if i.val < 222 then (if i.val < 221 then 57 else 15) else (if i.val < 223 then 14 else 57))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 29 else 16) else (if i.val < 227 then 16 else 14)) else (if i.val < 230 then (if i.val < 229 then 15 else 33) else (if i.val < 231 then 14 else 57))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 57 else 57) else (if i.val < 235 then 33 else 29)) else (if i.val < 238 then (if i.val < 237 then 17 else 57) else (if i.val < 239 then 61 else 30)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 57 else 17) else (if i.val < 243 then 16 else 15)) else (if i.val < 246 then (if i.val < 245 then 30 else 57) else (if i.val < 247 then 32 else 57))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 15 else 30) else (if i.val < 251 then 30 else 16)) else (if i.val < 254 then (if i.val < 253 then 30 else 15) else (if i.val < 255 then 57 else 57))))))))

theorem g32p_supplierForest_actual_088 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_088 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_088 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_019089
  · exact g32p_supplierForest_actual_019097
  · exact g32p_supplierForest_actual_019109
  · exact g32p_supplierForest_actual_019147
  · exact g32p_supplierForest_actual_019152
  · exact g32p_supplierForest_actual_019163
  · exact g32p_supplierForest_actual_019217
  · exact g32p_supplierForest_actual_019239
  · exact g32p_supplierForest_actual_019285
  · exact g32p_supplierForest_actual_019290
  · exact g32p_supplierForest_actual_019296
  · exact g32p_supplierForest_actual_019303
  · exact g32p_supplierForest_actual_019327
  · exact g32p_supplierForest_actual_019348
  · exact g32p_supplierForest_actual_019351
  · exact g32p_supplierForest_actual_019383
  · exact g32p_supplierForest_actual_019396
  · exact g32p_supplierForest_actual_019405
  · exact g32p_supplierForest_actual_019419
  · exact g32p_supplierForest_actual_019498
  · exact g32p_supplierForest_actual_019502
  · exact g32p_supplierForest_actual_019504
  · exact g32p_supplierForest_actual_019538
  · exact g32p_supplierForest_actual_019620
  · exact g32p_supplierForest_actual_019715
  · exact g32p_supplierForest_actual_019751
  · exact g32p_supplierForest_actual_019798
  · exact g32p_supplierForest_actual_019801
  · exact g32p_supplierForest_actual_019865
  · exact g32p_supplierForest_actual_019880
  · exact g32p_supplierForest_actual_019884
  · exact g32p_supplierForest_actual_019907
  · exact g32p_supplierForest_actual_019965
  · exact g32p_supplierForest_actual_019990
  · exact g32p_supplierForest_actual_020019
  · exact g32p_supplierForest_actual_020054
  · exact g32p_supplierForest_actual_020061
  · exact g32p_supplierForest_actual_020134
  · exact g32p_supplierForest_actual_020151
  · exact g32p_supplierForest_actual_020213
  · exact g32p_supplierForest_actual_020270
  · exact g32p_supplierForest_actual_020315
  · exact g32p_supplierForest_actual_020327
  · exact g32p_supplierForest_actual_020352
  · exact g32p_supplierForest_actual_020360
  · exact g32p_supplierForest_actual_020370
  · exact g32p_supplierForest_actual_020420
  · exact g32p_supplierForest_actual_020442
  · exact g32p_supplierForest_actual_020467
  · exact g32p_supplierForest_actual_020470
  · exact g32p_supplierForest_actual_020488
  · exact g32p_supplierForest_actual_020496
  · exact g32p_supplierForest_actual_020536
  · exact g32p_supplierForest_actual_020543
  · exact g32p_supplierForest_actual_020547
  · exact g32p_supplierForest_actual_020560
  · exact g32p_supplierForest_actual_020576
  · exact g32p_supplierForest_actual_020592
  · exact g32p_supplierForest_actual_020613
  · exact g32p_supplierForest_actual_020673
  · exact g32p_supplierForest_actual_020682
  · exact g32p_supplierForest_actual_020696
  · exact g32p_supplierForest_actual_020711
  · exact g32p_supplierForest_actual_020728
  · exact g32p_supplierForest_actual_020739
  · exact g32p_supplierForest_actual_020749
  · exact g32p_supplierForest_actual_020771
  · exact g32p_supplierForest_actual_020796
  · exact g32p_supplierForest_actual_020807
  · exact g32p_supplierForest_actual_020824
  · exact g32p_supplierForest_actual_020828
  · exact g32p_supplierForest_actual_020919
  · exact g32p_supplierForest_actual_020939
  · exact g32p_supplierForest_actual_021117
  · exact g32p_supplierForest_actual_021135
  · exact g32p_supplierForest_actual_021174
  · exact g32p_supplierForest_actual_021219
  · exact g32p_supplierForest_actual_021233
  · exact g32p_supplierForest_actual_021236
  · exact g32p_supplierForest_actual_021277
  · exact g32p_supplierForest_actual_021316
  · exact g32p_supplierForest_actual_021343
  · exact g32p_supplierForest_actual_021368
  · exact g32p_supplierForest_actual_021408
  · exact g32p_supplierForest_actual_021413
  · exact g32p_supplierForest_actual_021427
  · exact g32p_supplierForest_actual_021458
  · exact g32p_supplierForest_actual_021462
  · exact g32p_supplierForest_actual_021467
  · exact g32p_supplierForest_actual_021484
  · exact g32p_supplierForest_actual_021522
  · exact g32p_supplierForest_actual_021591
  · exact g32p_supplierForest_actual_021619
  · exact g32p_supplierForest_actual_021629
  · exact g32p_supplierForest_actual_021647
  · exact g32p_supplierForest_actual_021671
  · exact g32p_supplierForest_actual_021680
  · exact g32p_supplierForest_actual_021769
  · exact g32p_supplierForest_actual_021773
  · exact g32p_supplierForest_actual_021783
  · exact g32p_supplierForest_actual_021796
  · exact g32p_supplierForest_actual_021800
  · exact g32p_supplierForest_actual_021817
  · exact g32p_supplierForest_actual_021825
  · exact g32p_supplierForest_actual_021830
  · exact g32p_supplierForest_actual_021858
  · exact g32p_supplierForest_actual_021908
  · exact g32p_supplierForest_actual_021956
  · exact g32p_supplierForest_actual_021980
  · exact g32p_supplierForest_actual_021995
  · exact g32p_supplierForest_actual_022000
  · exact g32p_supplierForest_actual_022010
  · exact g32p_supplierForest_actual_022048
  · exact g32p_supplierForest_actual_022075
  · exact g32p_supplierForest_actual_022082
  · exact g32p_supplierForest_actual_022130
  · exact g32p_supplierForest_actual_022206
  · exact g32p_supplierForest_actual_022237
  · exact g32p_supplierForest_actual_022280
  · exact g32p_supplierForest_actual_022300
  · exact g32p_supplierForest_actual_022317
  · exact g32p_supplierForest_actual_022338
  · exact g32p_supplierForest_actual_022408
  · exact g32p_supplierForest_actual_022440
  · exact g32p_supplierForest_actual_022442
  · exact g32p_supplierForest_actual_022450
  · exact g32p_supplierForest_actual_022484
  · exact g32p_supplierForest_actual_022500
  · exact g32p_supplierForest_actual_022522
  · exact g32p_supplierForest_actual_022530
  · exact g32p_supplierForest_actual_022541
  · exact g32p_supplierForest_actual_022572
  · exact g32p_supplierForest_actual_022606
  · exact g32p_supplierForest_actual_022634
  · exact g32p_supplierForest_actual_022672
  · exact g32p_supplierForest_actual_022725
  · exact g32p_supplierForest_actual_022756
  · exact g32p_supplierForest_actual_022802
  · exact g32p_supplierForest_actual_022905
  · exact g32p_supplierForest_actual_023028
  · exact g32p_supplierForest_actual_023079
  · exact g32p_supplierForest_actual_023083
  · exact g32p_supplierForest_actual_023130
  · exact g32p_supplierForest_actual_023193
  · exact g32p_supplierForest_actual_023244
  · exact g32p_supplierForest_actual_023255
  · exact g32p_supplierForest_actual_023262
  · exact g32p_supplierForest_actual_023281
  · exact g32p_supplierForest_actual_023296
  · exact g32p_supplierForest_actual_023411
  · exact g32p_supplierForest_actual_023414
  · exact g32p_supplierForest_actual_023430
  · exact g32p_supplierForest_actual_023433
  · exact g32p_supplierForest_actual_023436
  · exact g32p_supplierForest_actual_023481
  · exact g32p_supplierForest_actual_023502
  · exact g32p_supplierForest_actual_023552
  · exact g32p_supplierForest_actual_023582
  · exact g32p_supplierForest_actual_023593
  · exact g32p_supplierForest_actual_023684
  · exact g32p_supplierForest_actual_023718
  · exact g32p_supplierForest_actual_023723
  · exact g32p_supplierForest_actual_023792
  · exact g32p_supplierForest_actual_023801
  · exact g32p_supplierForest_actual_023809
  · exact g32p_supplierForest_actual_023814
  · exact g32p_supplierForest_actual_023850
  · exact g32p_supplierForest_actual_023854
  · exact g32p_supplierForest_actual_023878
  · exact g32p_supplierForest_actual_023918
  · exact g32p_supplierForest_actual_023940
  · exact g32p_supplierForest_actual_023959
  · exact g32p_supplierForest_actual_023977
  · exact g32p_supplierForest_actual_023992
  · exact g32p_supplierForest_actual_024003
  · exact g32p_supplierForest_actual_024041
  · exact g32p_supplierForest_actual_024170
  · exact g32p_supplierForest_actual_024171
  · exact g32p_supplierForest_actual_024299
  · exact g32p_supplierForest_actual_024315
  · exact g32p_supplierForest_actual_024362
  · exact g32p_supplierForest_actual_024372
  · exact g32p_supplierForest_actual_024394
  · exact g32p_supplierForest_actual_024430
  · exact g32p_supplierForest_actual_024433
  · exact g32p_supplierForest_actual_024457
  · exact g32p_supplierForest_actual_024468
  · exact g32p_supplierForest_actual_024520
  · exact g32p_supplierForest_actual_024547
  · exact g32p_supplierForest_actual_024562
  · exact g32p_supplierForest_actual_024567
  · exact g32p_supplierForest_actual_024595
  · exact g32p_supplierForest_actual_024618
  · exact g32p_supplierForest_actual_024631
  · exact g32p_supplierForest_actual_024634
  · exact g32p_supplierForest_actual_024664
  · exact g32p_supplierForest_actual_024677
  · exact g32p_supplierForest_actual_024701
  · exact g32p_supplierForest_actual_024783
  · exact g32p_supplierForest_actual_024798
  · exact g32p_supplierForest_actual_024826
  · exact g32p_supplierForest_actual_024832
  · exact g32p_supplierForest_actual_024893
  · exact g32p_supplierForest_actual_024896
  · exact g32p_supplierForest_actual_024901
  · exact g32p_supplierForest_actual_024939
  · exact g32p_supplierForest_actual_024946
  · exact g32p_supplierForest_actual_024968
  · exact g32p_supplierForest_actual_025022
  · exact g32p_supplierForest_actual_025045
  · exact g32p_supplierForest_actual_025046
  · exact g32p_supplierForest_actual_025054
  · exact g32p_supplierForest_actual_025069
  · exact g32p_supplierForest_actual_025179
  · exact g32p_supplierForest_actual_025213
  · exact g32p_supplierForest_actual_025243
  · exact g32p_supplierForest_actual_025267
  · exact g32p_supplierForest_actual_025282
  · exact g32p_supplierForest_actual_025304
  · exact g32p_supplierForest_actual_025309
  · exact g32p_supplierForest_actual_025339
  · exact g32p_supplierForest_actual_025341
  · exact g32p_supplierForest_actual_025361
  · exact g32p_supplierForest_actual_025365
  · exact g32p_supplierForest_actual_025387
  · exact g32p_supplierForest_actual_025410
  · exact g32p_supplierForest_actual_025418
  · exact g32p_supplierForest_actual_025436
  · exact g32p_supplierForest_actual_025437
  · exact g32p_supplierForest_actual_025457
  · exact g32p_supplierForest_actual_025527
  · exact g32p_supplierForest_actual_025565
  · exact g32p_supplierForest_actual_025577
  · exact g32p_supplierForest_actual_025585
  · exact g32p_supplierForest_actual_025591
  · exact g32p_supplierForest_actual_025597
  · exact g32p_supplierForest_actual_025603
  · exact g32p_supplierForest_actual_025623
  · exact g32p_supplierForest_actual_025648
  · exact g32p_supplierForest_actual_025652
  · exact g32p_supplierForest_actual_025710
  · exact g32p_supplierForest_actual_025712
  · exact g32p_supplierForest_actual_025772
  · exact g32p_supplierForest_actual_025786
  · exact g32p_supplierForest_actual_025815
  · exact g32p_supplierForest_actual_025823
  · exact g32p_supplierForest_actual_025828
  · exact g32p_supplierForest_actual_025942
  · exact g32p_supplierForest_actual_025943
  · exact g32p_supplierForest_actual_025967
  · exact g32p_supplierForest_actual_026002
  · exact g32p_supplierForest_actual_026019
  · exact g32p_supplierForest_actual_026029
  · exact g32p_supplierForest_actual_026049
  · exact g32p_supplierForest_actual_026050
  · exact g32p_supplierForest_actual_026111

def g32p_supplierForest_nodes_089 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_026186 else g32p_supplierForest_node_026197) else (if i.val < 3 then g32p_supplierForest_node_026212 else g32p_supplierForest_node_026241)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_026281 else g32p_supplierForest_node_026300) else (if i.val < 7 then g32p_supplierForest_node_026308 else g32p_supplierForest_node_026340))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_026367 else g32p_supplierForest_node_026372) else (if i.val < 11 then g32p_supplierForest_node_026389 else g32p_supplierForest_node_026407)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_026419 else g32p_supplierForest_node_026420) else (if i.val < 15 then g32p_supplierForest_node_026427 else g32p_supplierForest_node_026522)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_026526 else g32p_supplierForest_node_026564) else (if i.val < 19 then g32p_supplierForest_node_026574 else g32p_supplierForest_node_026645)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_026663 else g32p_supplierForest_node_026683) else (if i.val < 23 then g32p_supplierForest_node_026723 else g32p_supplierForest_node_026741))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_026765 else g32p_supplierForest_node_026797) else (if i.val < 27 then g32p_supplierForest_node_026856 else g32p_supplierForest_node_026897)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_026906 else g32p_supplierForest_node_026943) else (if i.val < 31 then g32p_supplierForest_node_026946 else g32p_supplierForest_node_026948))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_026969 else g32p_supplierForest_node_027018) else (if i.val < 35 then g32p_supplierForest_node_027024 else g32p_supplierForest_node_027050)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_027098 else g32p_supplierForest_node_027119) else (if i.val < 39 then g32p_supplierForest_node_027148 else g32p_supplierForest_node_027195))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_027226 else g32p_supplierForest_node_027230) else (if i.val < 43 then g32p_supplierForest_node_027232 else g32p_supplierForest_node_027289)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_027461 else g32p_supplierForest_node_027477) else (if i.val < 47 then g32p_supplierForest_node_027574 else g32p_supplierForest_node_027598)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_027600 else g32p_supplierForest_node_027602) else (if i.val < 51 then g32p_supplierForest_node_027630 else g32p_supplierForest_node_027641)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_027667 else g32p_supplierForest_node_027709) else (if i.val < 55 then g32p_supplierForest_node_027742 else g32p_supplierForest_node_027747))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_027811 else g32p_supplierForest_node_027812) else (if i.val < 59 then g32p_supplierForest_node_027828 else g32p_supplierForest_node_027834)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_027839 else g32p_supplierForest_node_027841) else (if i.val < 63 then g32p_supplierForest_node_027909 else g32p_supplierForest_node_027915)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_027936 else g32p_supplierForest_node_027942) else (if i.val < 67 then g32p_supplierForest_node_027974 else g32p_supplierForest_node_028033)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_028047 else g32p_supplierForest_node_028075) else (if i.val < 71 then g32p_supplierForest_node_028110 else g32p_supplierForest_node_028117))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_028130 else g32p_supplierForest_node_028135) else (if i.val < 75 then g32p_supplierForest_node_028145 else g32p_supplierForest_node_028156)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_028157 else g32p_supplierForest_node_028168) else (if i.val < 79 then g32p_supplierForest_node_028189 else g32p_supplierForest_node_028211)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_028259 else g32p_supplierForest_node_028278) else (if i.val < 83 then g32p_supplierForest_node_028318 else g32p_supplierForest_node_028337)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_028351 else g32p_supplierForest_node_028397) else (if i.val < 87 then g32p_supplierForest_node_028402 else g32p_supplierForest_node_028442))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_028499 else g32p_supplierForest_node_028507) else (if i.val < 91 then g32p_supplierForest_node_028516 else g32p_supplierForest_node_028526)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_028535 else g32p_supplierForest_node_028575) else (if i.val < 95 then g32p_supplierForest_node_028584 else g32p_supplierForest_node_028608))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_028639 else g32p_supplierForest_node_028684) else (if i.val < 99 then g32p_supplierForest_node_028686 else g32p_supplierForest_node_028701)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_028704 else g32p_supplierForest_node_028706) else (if i.val < 103 then g32p_supplierForest_node_028708 else g32p_supplierForest_node_028710))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_028724 else g32p_supplierForest_node_028741) else (if i.val < 107 then g32p_supplierForest_node_028751 else g32p_supplierForest_node_028807)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_028833 else g32p_supplierForest_node_028846) else (if i.val < 111 then g32p_supplierForest_node_028859 else g32p_supplierForest_node_028880)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_028882 else g32p_supplierForest_node_028889) else (if i.val < 115 then g32p_supplierForest_node_028909 else g32p_supplierForest_node_028911)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_028948 else g32p_supplierForest_node_028957) else (if i.val < 119 then g32p_supplierForest_node_028965 else g32p_supplierForest_node_028983))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_028999 else g32p_supplierForest_node_029015) else (if i.val < 123 then g32p_supplierForest_node_029021 else g32p_supplierForest_node_029124)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_029137 else g32p_supplierForest_node_029174) else (if i.val < 127 then g32p_supplierForest_node_029179 else g32p_supplierForest_node_029204))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_029218 else g32p_supplierForest_node_029258) else (if i.val < 131 then g32p_supplierForest_node_029281 else g32p_supplierForest_node_029301)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_029330 else g32p_supplierForest_node_029334) else (if i.val < 135 then g32p_supplierForest_node_029370 else g32p_supplierForest_node_029374))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_029402 else g32p_supplierForest_node_029430) else (if i.val < 139 then g32p_supplierForest_node_029440 else g32p_supplierForest_node_029454)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_029459 else g32p_supplierForest_node_029494) else (if i.val < 143 then g32p_supplierForest_node_029529 else g32p_supplierForest_node_029546)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_029552 else g32p_supplierForest_node_029589) else (if i.val < 147 then g32p_supplierForest_node_029609 else g32p_supplierForest_node_029617)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_029620 else g32p_supplierForest_node_029626) else (if i.val < 151 then g32p_supplierForest_node_029636 else g32p_supplierForest_node_029652))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_029670 else g32p_supplierForest_node_029711) else (if i.val < 155 then g32p_supplierForest_node_029762 else g32p_supplierForest_node_029779)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_029786 else g32p_supplierForest_node_029788) else (if i.val < 159 then g32p_supplierForest_node_029792 else g32p_supplierForest_node_029798))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_029836 else g32p_supplierForest_node_029892) else (if i.val < 163 then g32p_supplierForest_node_029908 else g32p_supplierForest_node_029931)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_029942 else g32p_supplierForest_node_029950) else (if i.val < 167 then g32p_supplierForest_node_029995 else g32p_supplierForest_node_029997))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_030031 else g32p_supplierForest_node_030051) else (if i.val < 171 then g32p_supplierForest_node_030078 else g32p_supplierForest_node_030095)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_030108 else g32p_supplierForest_node_030129) else (if i.val < 175 then g32p_supplierForest_node_030137 else g32p_supplierForest_node_030144)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_030147 else g32p_supplierForest_node_030168) else (if i.val < 179 then g32p_supplierForest_node_030170 else g32p_supplierForest_node_030176)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_030199 else g32p_supplierForest_node_030222) else (if i.val < 183 then g32p_supplierForest_node_030229 else g32p_supplierForest_node_030230))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_030247 else g32p_supplierForest_node_030295) else (if i.val < 187 then g32p_supplierForest_node_030297 else g32p_supplierForest_node_030302)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_030321 else g32p_supplierForest_node_030329) else (if i.val < 191 then g32p_supplierForest_node_030336 else g32p_supplierForest_node_030351)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_030396 else g32p_supplierForest_node_030436) else (if i.val < 195 then g32p_supplierForest_node_030450 else g32p_supplierForest_node_030481)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_030492 else g32p_supplierForest_node_030514) else (if i.val < 199 then g32p_supplierForest_node_030525 else g32p_supplierForest_node_030539))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_030567 else g32p_supplierForest_node_030574) else (if i.val < 203 then g32p_supplierForest_node_030610 else g32p_supplierForest_node_030628)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_030652 else g32p_supplierForest_node_030691) else (if i.val < 207 then g32p_supplierForest_node_030697 else g32p_supplierForest_node_030703)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_030704 else g32p_supplierForest_node_030738) else (if i.val < 211 then g32p_supplierForest_node_030818 else g32p_supplierForest_node_030824)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_030828 else g32p_supplierForest_node_030836) else (if i.val < 215 then g32p_supplierForest_node_030858 else g32p_supplierForest_node_030870))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_030884 else g32p_supplierForest_node_030892) else (if i.val < 219 then g32p_supplierForest_node_030900 else g32p_supplierForest_node_030904)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_030949 else g32p_supplierForest_node_030966) else (if i.val < 223 then g32p_supplierForest_node_030977 else g32p_supplierForest_node_031083))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_031133 else g32p_supplierForest_node_031176) else (if i.val < 227 then g32p_supplierForest_node_031283 else g32p_supplierForest_node_031290)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_031336 else g32p_supplierForest_node_031368) else (if i.val < 231 then g32p_supplierForest_node_031388 else g32p_supplierForest_node_031391))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_031413 else g32p_supplierForest_node_031481) else (if i.val < 235 then g32p_supplierForest_node_031544 else g32p_supplierForest_node_031566)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_031590 else g32p_supplierForest_node_031594) else (if i.val < 239 then g32p_supplierForest_node_031646 else g32p_supplierForest_node_031697)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_031706 else g32p_supplierForest_node_031765) else (if i.val < 243 then g32p_supplierForest_node_031773 else g32p_supplierForest_node_031774)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_031783 else g32p_supplierForest_node_031787) else (if i.val < 247 then g32p_supplierForest_node_031792 else g32p_supplierForest_node_031798))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_031812 else g32p_supplierForest_node_031823) else (if i.val < 251 then g32p_supplierForest_node_031825 else g32p_supplierForest_node_031896)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_031913 else g32p_supplierForest_node_031917) else (if i.val < 255 then g32p_supplierForest_node_031920 else g32p_supplierForest_node_031930))))))))

def g32p_supplierForest_classes_089 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 14 else 15) else (if i.val < 3 then 60 else 63)) else (if i.val < 6 then (if i.val < 5 then 16 else 17) else (if i.val < 7 then 16 else 57))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 57 else 16) else (if i.val < 11 then 30 else 15)) else (if i.val < 14 then (if i.val < 13 then 35 else 30) else (if i.val < 15 then 15 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 57) else (if i.val < 19 then 16 else 15)) else (if i.val < 22 then (if i.val < 21 then 30 else 59) else (if i.val < 23 then 16 else 15))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 57 else 17) else (if i.val < 27 then 16 else 30)) else (if i.val < 30 then (if i.val < 29 then 29 else 17) else (if i.val < 31 then 35 else 14))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 17 else 57) else (if i.val < 35 then 17 else 30)) else (if i.val < 38 then (if i.val < 37 then 57 else 36) else (if i.val < 39 then 29 else 29))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 15 else 15) else (if i.val < 43 then 15 else 31)) else (if i.val < 46 then (if i.val < 45 then 29 else 29) else (if i.val < 47 then 15 else 30)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 30 else 32) else (if i.val < 51 then 16 else 29)) else (if i.val < 54 then (if i.val < 53 then 59 else 17) else (if i.val < 55 then 57 else 57))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 17 else 30) else (if i.val < 59 then 30 else 14)) else (if i.val < 62 then (if i.val < 61 then 31 else 32) else (if i.val < 63 then 30 else 57)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 35 else 30) else (if i.val < 67 then 57 else 14)) else (if i.val < 70 then (if i.val < 69 then 30 else 57) else (if i.val < 71 then 15 else 16))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 57 else 14) else (if i.val < 75 then 30 else 14)) else (if i.val < 78 then (if i.val < 77 then 59 else 16) else (if i.val < 79 then 57 else 16)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 32 else 30) else (if i.val < 83 then 34 else 4)) else (if i.val < 86 then (if i.val < 85 then 57 else 17) else (if i.val < 87 then 4 else 57))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 57 else 16) else (if i.val < 91 then 33 else 30)) else (if i.val < 94 then (if i.val < 93 then 16 else 32) else (if i.val < 95 then 57 else 29))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 57 else 17) else (if i.val < 99 then 58 else 30)) else (if i.val < 102 then (if i.val < 101 then 14 else 57) else (if i.val < 103 then 30 else 32))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 16 else 17) else (if i.val < 107 then 16 else 14)) else (if i.val < 110 then (if i.val < 109 then 60 else 57) else (if i.val < 111 then 57 else 30)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 30 else 64) else (if i.val < 115 then 17 else 30)) else (if i.val < 118 then (if i.val < 117 then 17 else 63) else (if i.val < 119 then 57 else 30))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 30 else 30) else (if i.val < 123 then 16 else 3)) else (if i.val < 126 then (if i.val < 125 then 30 else 30) else (if i.val < 127 then 32 else 15))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 63 else 15) else (if i.val < 131 then 59 else 57)) else (if i.val < 134 then (if i.val < 133 then 63 else 30) else (if i.val < 135 then 57 else 59))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 57 else 15) else (if i.val < 139 then 57 else 30)) else (if i.val < 142 then (if i.val < 141 then 30 else 58) else (if i.val < 143 then 16 else 60)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 59 else 57) else (if i.val < 147 then 16 else 14)) else (if i.val < 150 then (if i.val < 149 then 15 else 57) else (if i.val < 151 then 15 else 30))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 57 else 57) else (if i.val < 155 then 57 else 57)) else (if i.val < 158 then (if i.val < 157 then 60 else 58) else (if i.val < 159 then 57 else 30))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 15 else 30) else (if i.val < 163 then 33 else 30)) else (if i.val < 166 then (if i.val < 165 then 17 else 57) else (if i.val < 167 then 57 else 30))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 16 else 14) else (if i.val < 171 then 15 else 57)) else (if i.val < 174 then (if i.val < 173 then 30 else 16) else (if i.val < 175 then 33 else 30)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 57 else 57) else (if i.val < 179 then 17 else 57)) else (if i.val < 182 then (if i.val < 181 then 59 else 59) else (if i.val < 183 then 57 else 57))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 16 else 64) else (if i.val < 187 then 17 else 64)) else (if i.val < 190 then (if i.val < 189 then 63 else 57) else (if i.val < 191 then 30 else 61)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 57 else 16) else (if i.val < 195 then 57 else 57)) else (if i.val < 198 then (if i.val < 197 then 30 else 57) else (if i.val < 199 then 66 else 57))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 57 else 16) else (if i.val < 203 then 57 else 15)) else (if i.val < 206 then (if i.val < 205 then 4 else 29) else (if i.val < 207 then 57 else 30)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 61 else 61) else (if i.val < 211 then 30 else 35)) else (if i.val < 214 then (if i.val < 213 then 29 else 30) else (if i.val < 215 then 15 else 15))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 57 else 15) else (if i.val < 219 then 32 else 30)) else (if i.val < 222 then (if i.val < 221 then 16 else 33) else (if i.val < 223 then 17 else 57))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 64 else 63) else (if i.val < 227 then 30 else 61)) else (if i.val < 230 then (if i.val < 229 then 63 else 59) else (if i.val < 231 then 57 else 57))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 59 else 57) else (if i.val < 235 then 57 else 30)) else (if i.val < 238 then (if i.val < 237 then 30 else 16) else (if i.val < 239 then 57 else 30)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 62 else 59) else (if i.val < 243 then 30 else 30)) else (if i.val < 246 then (if i.val < 245 then 16 else 32) else (if i.val < 247 then 30 else 59))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 16 else 57) else (if i.val < 251 then 64 else 32)) else (if i.val < 254 then (if i.val < 253 then 16 else 30) else (if i.val < 255 then 30 else 16))))))))

theorem g32p_supplierForest_actual_089 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_089 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_089 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_026186
  · exact g32p_supplierForest_actual_026197
  · exact g32p_supplierForest_actual_026212
  · exact g32p_supplierForest_actual_026241
  · exact g32p_supplierForest_actual_026281
  · exact g32p_supplierForest_actual_026300
  · exact g32p_supplierForest_actual_026308
  · exact g32p_supplierForest_actual_026340
  · exact g32p_supplierForest_actual_026367
  · exact g32p_supplierForest_actual_026372
  · exact g32p_supplierForest_actual_026389
  · exact g32p_supplierForest_actual_026407
  · exact g32p_supplierForest_actual_026419
  · exact g32p_supplierForest_actual_026420
  · exact g32p_supplierForest_actual_026427
  · exact g32p_supplierForest_actual_026522
  · exact g32p_supplierForest_actual_026526
  · exact g32p_supplierForest_actual_026564
  · exact g32p_supplierForest_actual_026574
  · exact g32p_supplierForest_actual_026645
  · exact g32p_supplierForest_actual_026663
  · exact g32p_supplierForest_actual_026683
  · exact g32p_supplierForest_actual_026723
  · exact g32p_supplierForest_actual_026741
  · exact g32p_supplierForest_actual_026765
  · exact g32p_supplierForest_actual_026797
  · exact g32p_supplierForest_actual_026856
  · exact g32p_supplierForest_actual_026897
  · exact g32p_supplierForest_actual_026906
  · exact g32p_supplierForest_actual_026943
  · exact g32p_supplierForest_actual_026946
  · exact g32p_supplierForest_actual_026948
  · exact g32p_supplierForest_actual_026969
  · exact g32p_supplierForest_actual_027018
  · exact g32p_supplierForest_actual_027024
  · exact g32p_supplierForest_actual_027050
  · exact g32p_supplierForest_actual_027098
  · exact g32p_supplierForest_actual_027119
  · exact g32p_supplierForest_actual_027148
  · exact g32p_supplierForest_actual_027195
  · exact g32p_supplierForest_actual_027226
  · exact g32p_supplierForest_actual_027230
  · exact g32p_supplierForest_actual_027232
  · exact g32p_supplierForest_actual_027289
  · exact g32p_supplierForest_actual_027461
  · exact g32p_supplierForest_actual_027477
  · exact g32p_supplierForest_actual_027574
  · exact g32p_supplierForest_actual_027598
  · exact g32p_supplierForest_actual_027600
  · exact g32p_supplierForest_actual_027602
  · exact g32p_supplierForest_actual_027630
  · exact g32p_supplierForest_actual_027641
  · exact g32p_supplierForest_actual_027667
  · exact g32p_supplierForest_actual_027709
  · exact g32p_supplierForest_actual_027742
  · exact g32p_supplierForest_actual_027747
  · exact g32p_supplierForest_actual_027811
  · exact g32p_supplierForest_actual_027812
  · exact g32p_supplierForest_actual_027828
  · exact g32p_supplierForest_actual_027834
  · exact g32p_supplierForest_actual_027839
  · exact g32p_supplierForest_actual_027841
  · exact g32p_supplierForest_actual_027909
  · exact g32p_supplierForest_actual_027915
  · exact g32p_supplierForest_actual_027936
  · exact g32p_supplierForest_actual_027942
  · exact g32p_supplierForest_actual_027974
  · exact g32p_supplierForest_actual_028033
  · exact g32p_supplierForest_actual_028047
  · exact g32p_supplierForest_actual_028075
  · exact g32p_supplierForest_actual_028110
  · exact g32p_supplierForest_actual_028117
  · exact g32p_supplierForest_actual_028130
  · exact g32p_supplierForest_actual_028135
  · exact g32p_supplierForest_actual_028145
  · exact g32p_supplierForest_actual_028156
  · exact g32p_supplierForest_actual_028157
  · exact g32p_supplierForest_actual_028168
  · exact g32p_supplierForest_actual_028189
  · exact g32p_supplierForest_actual_028211
  · exact g32p_supplierForest_actual_028259
  · exact g32p_supplierForest_actual_028278
  · exact g32p_supplierForest_actual_028318
  · exact g32p_supplierForest_actual_028337
  · exact g32p_supplierForest_actual_028351
  · exact g32p_supplierForest_actual_028397
  · exact g32p_supplierForest_actual_028402
  · exact g32p_supplierForest_actual_028442
  · exact g32p_supplierForest_actual_028499
  · exact g32p_supplierForest_actual_028507
  · exact g32p_supplierForest_actual_028516
  · exact g32p_supplierForest_actual_028526
  · exact g32p_supplierForest_actual_028535
  · exact g32p_supplierForest_actual_028575
  · exact g32p_supplierForest_actual_028584
  · exact g32p_supplierForest_actual_028608
  · exact g32p_supplierForest_actual_028639
  · exact g32p_supplierForest_actual_028684
  · exact g32p_supplierForest_actual_028686
  · exact g32p_supplierForest_actual_028701
  · exact g32p_supplierForest_actual_028704
  · exact g32p_supplierForest_actual_028706
  · exact g32p_supplierForest_actual_028708
  · exact g32p_supplierForest_actual_028710
  · exact g32p_supplierForest_actual_028724
  · exact g32p_supplierForest_actual_028741
  · exact g32p_supplierForest_actual_028751
  · exact g32p_supplierForest_actual_028807
  · exact g32p_supplierForest_actual_028833
  · exact g32p_supplierForest_actual_028846
  · exact g32p_supplierForest_actual_028859
  · exact g32p_supplierForest_actual_028880
  · exact g32p_supplierForest_actual_028882
  · exact g32p_supplierForest_actual_028889
  · exact g32p_supplierForest_actual_028909
  · exact g32p_supplierForest_actual_028911
  · exact g32p_supplierForest_actual_028948
  · exact g32p_supplierForest_actual_028957
  · exact g32p_supplierForest_actual_028965
  · exact g32p_supplierForest_actual_028983
  · exact g32p_supplierForest_actual_028999
  · exact g32p_supplierForest_actual_029015
  · exact g32p_supplierForest_actual_029021
  · exact g32p_supplierForest_actual_029124
  · exact g32p_supplierForest_actual_029137
  · exact g32p_supplierForest_actual_029174
  · exact g32p_supplierForest_actual_029179
  · exact g32p_supplierForest_actual_029204
  · exact g32p_supplierForest_actual_029218
  · exact g32p_supplierForest_actual_029258
  · exact g32p_supplierForest_actual_029281
  · exact g32p_supplierForest_actual_029301
  · exact g32p_supplierForest_actual_029330
  · exact g32p_supplierForest_actual_029334
  · exact g32p_supplierForest_actual_029370
  · exact g32p_supplierForest_actual_029374
  · exact g32p_supplierForest_actual_029402
  · exact g32p_supplierForest_actual_029430
  · exact g32p_supplierForest_actual_029440
  · exact g32p_supplierForest_actual_029454
  · exact g32p_supplierForest_actual_029459
  · exact g32p_supplierForest_actual_029494
  · exact g32p_supplierForest_actual_029529
  · exact g32p_supplierForest_actual_029546
  · exact g32p_supplierForest_actual_029552
  · exact g32p_supplierForest_actual_029589
  · exact g32p_supplierForest_actual_029609
  · exact g32p_supplierForest_actual_029617
  · exact g32p_supplierForest_actual_029620
  · exact g32p_supplierForest_actual_029626
  · exact g32p_supplierForest_actual_029636
  · exact g32p_supplierForest_actual_029652
  · exact g32p_supplierForest_actual_029670
  · exact g32p_supplierForest_actual_029711
  · exact g32p_supplierForest_actual_029762
  · exact g32p_supplierForest_actual_029779
  · exact g32p_supplierForest_actual_029786
  · exact g32p_supplierForest_actual_029788
  · exact g32p_supplierForest_actual_029792
  · exact g32p_supplierForest_actual_029798
  · exact g32p_supplierForest_actual_029836
  · exact g32p_supplierForest_actual_029892
  · exact g32p_supplierForest_actual_029908
  · exact g32p_supplierForest_actual_029931
  · exact g32p_supplierForest_actual_029942
  · exact g32p_supplierForest_actual_029950
  · exact g32p_supplierForest_actual_029995
  · exact g32p_supplierForest_actual_029997
  · exact g32p_supplierForest_actual_030031
  · exact g32p_supplierForest_actual_030051
  · exact g32p_supplierForest_actual_030078
  · exact g32p_supplierForest_actual_030095
  · exact g32p_supplierForest_actual_030108
  · exact g32p_supplierForest_actual_030129
  · exact g32p_supplierForest_actual_030137
  · exact g32p_supplierForest_actual_030144
  · exact g32p_supplierForest_actual_030147
  · exact g32p_supplierForest_actual_030168
  · exact g32p_supplierForest_actual_030170
  · exact g32p_supplierForest_actual_030176
  · exact g32p_supplierForest_actual_030199
  · exact g32p_supplierForest_actual_030222
  · exact g32p_supplierForest_actual_030229
  · exact g32p_supplierForest_actual_030230
  · exact g32p_supplierForest_actual_030247
  · exact g32p_supplierForest_actual_030295
  · exact g32p_supplierForest_actual_030297
  · exact g32p_supplierForest_actual_030302
  · exact g32p_supplierForest_actual_030321
  · exact g32p_supplierForest_actual_030329
  · exact g32p_supplierForest_actual_030336
  · exact g32p_supplierForest_actual_030351
  · exact g32p_supplierForest_actual_030396
  · exact g32p_supplierForest_actual_030436
  · exact g32p_supplierForest_actual_030450
  · exact g32p_supplierForest_actual_030481
  · exact g32p_supplierForest_actual_030492
  · exact g32p_supplierForest_actual_030514
  · exact g32p_supplierForest_actual_030525
  · exact g32p_supplierForest_actual_030539
  · exact g32p_supplierForest_actual_030567
  · exact g32p_supplierForest_actual_030574
  · exact g32p_supplierForest_actual_030610
  · exact g32p_supplierForest_actual_030628
  · exact g32p_supplierForest_actual_030652
  · exact g32p_supplierForest_actual_030691
  · exact g32p_supplierForest_actual_030697
  · exact g32p_supplierForest_actual_030703
  · exact g32p_supplierForest_actual_030704
  · exact g32p_supplierForest_actual_030738
  · exact g32p_supplierForest_actual_030818
  · exact g32p_supplierForest_actual_030824
  · exact g32p_supplierForest_actual_030828
  · exact g32p_supplierForest_actual_030836
  · exact g32p_supplierForest_actual_030858
  · exact g32p_supplierForest_actual_030870
  · exact g32p_supplierForest_actual_030884
  · exact g32p_supplierForest_actual_030892
  · exact g32p_supplierForest_actual_030900
  · exact g32p_supplierForest_actual_030904
  · exact g32p_supplierForest_actual_030949
  · exact g32p_supplierForest_actual_030966
  · exact g32p_supplierForest_actual_030977
  · exact g32p_supplierForest_actual_031083
  · exact g32p_supplierForest_actual_031133
  · exact g32p_supplierForest_actual_031176
  · exact g32p_supplierForest_actual_031283
  · exact g32p_supplierForest_actual_031290
  · exact g32p_supplierForest_actual_031336
  · exact g32p_supplierForest_actual_031368
  · exact g32p_supplierForest_actual_031388
  · exact g32p_supplierForest_actual_031391
  · exact g32p_supplierForest_actual_031413
  · exact g32p_supplierForest_actual_031481
  · exact g32p_supplierForest_actual_031544
  · exact g32p_supplierForest_actual_031566
  · exact g32p_supplierForest_actual_031590
  · exact g32p_supplierForest_actual_031594
  · exact g32p_supplierForest_actual_031646
  · exact g32p_supplierForest_actual_031697
  · exact g32p_supplierForest_actual_031706
  · exact g32p_supplierForest_actual_031765
  · exact g32p_supplierForest_actual_031773
  · exact g32p_supplierForest_actual_031774
  · exact g32p_supplierForest_actual_031783
  · exact g32p_supplierForest_actual_031787
  · exact g32p_supplierForest_actual_031792
  · exact g32p_supplierForest_actual_031798
  · exact g32p_supplierForest_actual_031812
  · exact g32p_supplierForest_actual_031823
  · exact g32p_supplierForest_actual_031825
  · exact g32p_supplierForest_actual_031896
  · exact g32p_supplierForest_actual_031913
  · exact g32p_supplierForest_actual_031917
  · exact g32p_supplierForest_actual_031920
  · exact g32p_supplierForest_actual_031930

def g32p_supplierForest_nodes_090 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_032013 else g32p_supplierForest_node_032039) else (if i.val < 3 then g32p_supplierForest_node_032041 else g32p_supplierForest_node_032080)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_032081 else g32p_supplierForest_node_032130) else (if i.val < 7 then g32p_supplierForest_node_032146 else g32p_supplierForest_node_032161))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_032171 else g32p_supplierForest_node_032185) else (if i.val < 11 then g32p_supplierForest_node_032204 else g32p_supplierForest_node_032238)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_032288 else g32p_supplierForest_node_032296) else (if i.val < 15 then g32p_supplierForest_node_032396 else g32p_supplierForest_node_032412)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_032418 else g32p_supplierForest_node_032438) else (if i.val < 19 then g32p_supplierForest_node_032492 else g32p_supplierForest_node_032510)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_032511 else g32p_supplierForest_node_032533) else (if i.val < 23 then g32p_supplierForest_node_032552 else g32p_supplierForest_node_032554))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_032557 else g32p_supplierForest_node_032563) else (if i.val < 27 then g32p_supplierForest_node_032569 else g32p_supplierForest_node_032578)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_032608 else g32p_supplierForest_node_032619) else (if i.val < 31 then g32p_supplierForest_node_032640 else g32p_supplierForest_node_032644))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_032650 else g32p_supplierForest_node_032730) else (if i.val < 35 then g32p_supplierForest_node_032731 else g32p_supplierForest_node_032760)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_032791 else g32p_supplierForest_node_032841) else (if i.val < 39 then g32p_supplierForest_node_032907 else g32p_supplierForest_node_032911))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_032916 else g32p_supplierForest_node_032934) else (if i.val < 43 then g32p_supplierForest_node_032953 else g32p_supplierForest_node_032985)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_032998 else g32p_supplierForest_node_033068) else (if i.val < 47 then g32p_supplierForest_node_033071 else g32p_supplierForest_node_033074)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_033093 else g32p_supplierForest_node_033108) else (if i.val < 51 then g32p_supplierForest_node_033148 else g32p_supplierForest_node_033153)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_033176 else g32p_supplierForest_node_033186) else (if i.val < 55 then g32p_supplierForest_node_033223 else g32p_supplierForest_node_033257))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_033261 else g32p_supplierForest_node_033283) else (if i.val < 59 then g32p_supplierForest_node_033284 else g32p_supplierForest_node_033307)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_033351 else g32p_supplierForest_node_033405) else (if i.val < 63 then g32p_supplierForest_node_033464 else g32p_supplierForest_node_033474)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_033552 else g32p_supplierForest_node_033562) else (if i.val < 67 then g32p_supplierForest_node_033636 else g32p_supplierForest_node_033666)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_033667 else g32p_supplierForest_node_033736) else (if i.val < 71 then g32p_supplierForest_node_033770 else g32p_supplierForest_node_033786))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_033788 else g32p_supplierForest_node_033810) else (if i.val < 75 then g32p_supplierForest_node_033903 else g32p_supplierForest_node_033908)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_033911 else g32p_supplierForest_node_033921) else (if i.val < 79 then g32p_supplierForest_node_033928 else g32p_supplierForest_node_033938)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_033940 else g32p_supplierForest_node_033941) else (if i.val < 83 then g32p_supplierForest_node_033976 else g32p_supplierForest_node_033978)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_034061 else g32p_supplierForest_node_034068) else (if i.val < 87 then g32p_supplierForest_node_034069 else g32p_supplierForest_node_034082))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_034128 else g32p_supplierForest_node_034153) else (if i.val < 91 then g32p_supplierForest_node_034194 else g32p_supplierForest_node_034203)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_034243 else g32p_supplierForest_node_034280) else (if i.val < 95 then g32p_supplierForest_node_034321 else g32p_supplierForest_node_034353))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_034389 else g32p_supplierForest_node_034392) else (if i.val < 99 then g32p_supplierForest_node_034395 else g32p_supplierForest_node_034431)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_034437 else g32p_supplierForest_node_034459) else (if i.val < 103 then g32p_supplierForest_node_034461 else g32p_supplierForest_node_034465))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_034545 else g32p_supplierForest_node_034549) else (if i.val < 107 then g32p_supplierForest_node_034560 else g32p_supplierForest_node_034572)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_034584 else g32p_supplierForest_node_034602) else (if i.val < 111 then g32p_supplierForest_node_034615 else g32p_supplierForest_node_034616)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_034639 else g32p_supplierForest_node_034666) else (if i.val < 115 then g32p_supplierForest_node_034690 else g32p_supplierForest_node_034694)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_034701 else g32p_supplierForest_node_034737) else (if i.val < 119 then g32p_supplierForest_node_034765 else g32p_supplierForest_node_034773))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_034823 else g32p_supplierForest_node_034826) else (if i.val < 123 then g32p_supplierForest_node_034841 else g32p_supplierForest_node_034857)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_034868 else g32p_supplierForest_node_034874) else (if i.val < 127 then g32p_supplierForest_node_034876 else g32p_supplierForest_node_034893))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_034905 else g32p_supplierForest_node_034906) else (if i.val < 131 then g32p_supplierForest_node_034999 else g32p_supplierForest_node_035008)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_035011 else g32p_supplierForest_node_035017) else (if i.val < 135 then g32p_supplierForest_node_035040 else g32p_supplierForest_node_035061))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_035080 else g32p_supplierForest_node_035113) else (if i.val < 139 then g32p_supplierForest_node_035117 else g32p_supplierForest_node_035140)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_035145 else g32p_supplierForest_node_035156) else (if i.val < 143 then g32p_supplierForest_node_035179 else g32p_supplierForest_node_035193)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_035209 else g32p_supplierForest_node_035263) else (if i.val < 147 then g32p_supplierForest_node_035293 else g32p_supplierForest_node_035338)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_035343 else g32p_supplierForest_node_035356) else (if i.val < 151 then g32p_supplierForest_node_035383 else g32p_supplierForest_node_035388))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_035453 else g32p_supplierForest_node_035473) else (if i.val < 155 then g32p_supplierForest_node_035538 else g32p_supplierForest_node_035567)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_035596 else g32p_supplierForest_node_035608) else (if i.val < 159 then g32p_supplierForest_node_035610 else g32p_supplierForest_node_035678))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_035761 else g32p_supplierForest_node_035777) else (if i.val < 163 then g32p_supplierForest_node_035865 else g32p_supplierForest_node_035882)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_035893 else g32p_supplierForest_node_035900) else (if i.val < 167 then g32p_supplierForest_node_035908 else g32p_supplierForest_node_035910))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_035932 else g32p_supplierForest_node_035951) else (if i.val < 171 then g32p_supplierForest_node_035993 else g32p_supplierForest_node_036023)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_036045 else g32p_supplierForest_node_036049) else (if i.val < 175 then g32p_supplierForest_node_036062 else g32p_supplierForest_node_036065)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_036070 else g32p_supplierForest_node_036080) else (if i.val < 179 then g32p_supplierForest_node_036106 else g32p_supplierForest_node_036126)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_036140 else g32p_supplierForest_node_036146) else (if i.val < 183 then g32p_supplierForest_node_036149 else g32p_supplierForest_node_036216))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_036235 else g32p_supplierForest_node_036276) else (if i.val < 187 then g32p_supplierForest_node_036278 else g32p_supplierForest_node_036306)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_036346 else g32p_supplierForest_node_036367) else (if i.val < 191 then g32p_supplierForest_node_036427 else g32p_supplierForest_node_036443)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_036444 else g32p_supplierForest_node_036453) else (if i.val < 195 then g32p_supplierForest_node_036454 else g32p_supplierForest_node_036462)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_036509 else g32p_supplierForest_node_036525) else (if i.val < 199 then g32p_supplierForest_node_036556 else g32p_supplierForest_node_036585))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_036654 else g32p_supplierForest_node_036657) else (if i.val < 203 then g32p_supplierForest_node_036689 else g32p_supplierForest_node_036759)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_036763 else g32p_supplierForest_node_036782) else (if i.val < 207 then g32p_supplierForest_node_036801 else g32p_supplierForest_node_036830)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_036833 else g32p_supplierForest_node_036848) else (if i.val < 211 then g32p_supplierForest_node_036858 else g32p_supplierForest_node_036859)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_036901 else g32p_supplierForest_node_036905) else (if i.val < 215 then g32p_supplierForest_node_036939 else g32p_supplierForest_node_036953))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_036974 else g32p_supplierForest_node_036996) else (if i.val < 219 then g32p_supplierForest_node_037019 else g32p_supplierForest_node_037080)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_037101 else g32p_supplierForest_node_037132) else (if i.val < 223 then g32p_supplierForest_node_037162 else g32p_supplierForest_node_037192))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_037194 else g32p_supplierForest_node_037208) else (if i.val < 227 then g32p_supplierForest_node_037242 else g32p_supplierForest_node_037266)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_037270 else g32p_supplierForest_node_037311) else (if i.val < 231 then g32p_supplierForest_node_037404 else g32p_supplierForest_node_037438))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_037461 else g32p_supplierForest_node_037469) else (if i.val < 235 then g32p_supplierForest_node_037509 else g32p_supplierForest_node_037516)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_037542 else g32p_supplierForest_node_037623) else (if i.val < 239 then g32p_supplierForest_node_037712 else g32p_supplierForest_node_037713)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_037788 else g32p_supplierForest_node_037806) else (if i.val < 243 then g32p_supplierForest_node_037842 else g32p_supplierForest_node_037866)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_037887 else g32p_supplierForest_node_037888) else (if i.val < 247 then g32p_supplierForest_node_037896 else g32p_supplierForest_node_037932))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_037944 else g32p_supplierForest_node_037959) else (if i.val < 251 then g32p_supplierForest_node_037971 else g32p_supplierForest_node_037999)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_038010 else g32p_supplierForest_node_038013) else (if i.val < 255 then g32p_supplierForest_node_038045 else g32p_supplierForest_node_038059))))))))

def g32p_supplierForest_classes_090 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 63 else 30) else (if i.val < 3 then 57 else 58)) else (if i.val < 6 then (if i.val < 5 then 60 else 16) else (if i.val < 7 then 57 else 58))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 29 else 57) else (if i.val < 11 then 60 else 59)) else (if i.val < 14 then (if i.val < 13 then 63 else 59) else (if i.val < 15 then 58 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 62 else 30) else (if i.val < 19 then 4 else 4)) else (if i.val < 22 then (if i.val < 21 then 64 else 57) else (if i.val < 23 then 57 else 16))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 57 else 57) else (if i.val < 27 then 63 else 30)) else (if i.val < 30 then (if i.val < 29 then 59 else 57) else (if i.val < 31 then 30 else 30))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 57 else 29) else (if i.val < 35 then 15 else 57)) else (if i.val < 38 then (if i.val < 37 then 59 else 63) else (if i.val < 39 then 15 else 14))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 16 else 57) else (if i.val < 43 then 62 else 30)) else (if i.val < 46 then (if i.val < 45 then 57 else 14) else (if i.val < 47 then 29 else 14)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 59 else 59) else (if i.val < 51 then 17 else 30)) else (if i.val < 54 then (if i.val < 53 then 30 else 57) else (if i.val < 55 then 57 else 63))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 59 else 16) else (if i.val < 59 then 66 else 31)) else (if i.val < 62 then (if i.val < 61 then 30 else 30) else (if i.val < 63 then 32 else 31)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 29 else 59) else (if i.val < 67 then 30 else 32)) else (if i.val < 70 then (if i.val < 69 then 16 else 57) else (if i.val < 71 then 16 else 16))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 30 else 15) else (if i.val < 75 then 14 else 33)) else (if i.val < 78 then (if i.val < 77 then 34 else 30) else (if i.val < 79 then 30 else 16)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 17 else 57) else (if i.val < 83 then 16 else 30)) else (if i.val < 86 then (if i.val < 85 then 14 else 15) else (if i.val < 87 then 57 else 57))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 57 else 59) else (if i.val < 91 then 30 else 36)) else (if i.val < 94 then (if i.val < 93 then 57 else 32) else (if i.val < 95 then 16 else 62))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 57 else 16) else (if i.val < 99 then 30 else 32)) else (if i.val < 102 then (if i.val < 101 then 30 else 35) else (if i.val < 103 then 30 else 30))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 62 else 57) else (if i.val < 107 then 57 else 57)) else (if i.val < 110 then (if i.val < 109 then 57 else 57) else (if i.val < 111 then 35 else 29)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 33 else 33) else (if i.val < 115 then 30 else 57)) else (if i.val < 118 then (if i.val < 117 then 57 else 17) else (if i.val < 119 then 57 else 57))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 59 else 60) else (if i.val < 123 then 16 else 35)) else (if i.val < 126 then (if i.val < 125 then 16 else 57) else (if i.val < 127 then 30 else 57))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 57 else 30) else (if i.val < 131 then 17 else 58)) else (if i.val < 134 then (if i.val < 133 then 16 else 16) else (if i.val < 135 then 16 else 57))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 57 else 14) else (if i.val < 139 then 63 else 62)) else (if i.val < 142 then (if i.val < 141 then 57 else 63) else (if i.val < 143 then 30 else 30)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 57 else 57) else (if i.val < 147 then 57 else 16)) else (if i.val < 150 then (if i.val < 149 then 62 else 57) else (if i.val < 151 then 30 else 29))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 30 else 57) else (if i.val < 155 then 17 else 17)) else (if i.val < 158 then (if i.val < 157 then 60 else 16) else (if i.val < 159 then 16 else 57))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 59 else 57) else (if i.val < 163 then 63 else 30)) else (if i.val < 166 then (if i.val < 165 then 16 else 30) else (if i.val < 167 then 14 else 29))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 57 else 57) else (if i.val < 171 then 30 else 57)) else (if i.val < 174 then (if i.val < 173 then 16 else 57) else (if i.val < 175 then 57 else 30)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 30 else 30) else (if i.val < 179 then 57 else 30)) else (if i.val < 182 then (if i.val < 181 then 57 else 57) else (if i.val < 183 then 30 else 57))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 36 else 57) else (if i.val < 187 then 30 else 30)) else (if i.val < 190 then (if i.val < 189 then 30 else 57) else (if i.val < 191 then 57 else 30)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 59 else 57) else (if i.val < 195 then 15 else 57)) else (if i.val < 198 then (if i.val < 197 then 32 else 57) else (if i.val < 199 then 57 else 35))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 15 else 15) else (if i.val < 203 then 57 else 29)) else (if i.val < 206 then (if i.val < 205 then 15 else 15) else (if i.val < 207 then 16 else 60)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 31 else 57) else (if i.val < 211 then 14 else 57)) else (if i.val < 214 then (if i.val < 213 then 14 else 15) else (if i.val < 215 then 58 else 29))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 30 else 30) else (if i.val < 219 then 35 else 16)) else (if i.val < 222 then (if i.val < 221 then 57 else 16) else (if i.val < 223 then 30 else 16))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 15 else 30) else (if i.val < 227 then 17 else 16)) else (if i.val < 230 then (if i.val < 229 then 57 else 15) else (if i.val < 231 then 16 else 30))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 30 else 14) else (if i.val < 235 then 14 else 14)) else (if i.val < 238 then (if i.val < 237 then 58 else 30) else (if i.val < 239 then 30 else 59)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 57 else 33) else (if i.val < 243 then 57 else 16)) else (if i.val < 246 then (if i.val < 245 then 58 else 29) else (if i.val < 247 then 15 else 30))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 36 else 64) else (if i.val < 251 then 57 else 30)) else (if i.val < 254 then (if i.val < 253 then 34 else 35) else (if i.val < 255 then 57 else 30))))))))

theorem g32p_supplierForest_actual_090 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_090 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_090 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_032013
  · exact g32p_supplierForest_actual_032039
  · exact g32p_supplierForest_actual_032041
  · exact g32p_supplierForest_actual_032080
  · exact g32p_supplierForest_actual_032081
  · exact g32p_supplierForest_actual_032130
  · exact g32p_supplierForest_actual_032146
  · exact g32p_supplierForest_actual_032161
  · exact g32p_supplierForest_actual_032171
  · exact g32p_supplierForest_actual_032185
  · exact g32p_supplierForest_actual_032204
  · exact g32p_supplierForest_actual_032238
  · exact g32p_supplierForest_actual_032288
  · exact g32p_supplierForest_actual_032296
  · exact g32p_supplierForest_actual_032396
  · exact g32p_supplierForest_actual_032412
  · exact g32p_supplierForest_actual_032418
  · exact g32p_supplierForest_actual_032438
  · exact g32p_supplierForest_actual_032492
  · exact g32p_supplierForest_actual_032510
  · exact g32p_supplierForest_actual_032511
  · exact g32p_supplierForest_actual_032533
  · exact g32p_supplierForest_actual_032552
  · exact g32p_supplierForest_actual_032554
  · exact g32p_supplierForest_actual_032557
  · exact g32p_supplierForest_actual_032563
  · exact g32p_supplierForest_actual_032569
  · exact g32p_supplierForest_actual_032578
  · exact g32p_supplierForest_actual_032608
  · exact g32p_supplierForest_actual_032619
  · exact g32p_supplierForest_actual_032640
  · exact g32p_supplierForest_actual_032644
  · exact g32p_supplierForest_actual_032650
  · exact g32p_supplierForest_actual_032730
  · exact g32p_supplierForest_actual_032731
  · exact g32p_supplierForest_actual_032760
  · exact g32p_supplierForest_actual_032791
  · exact g32p_supplierForest_actual_032841
  · exact g32p_supplierForest_actual_032907
  · exact g32p_supplierForest_actual_032911
  · exact g32p_supplierForest_actual_032916
  · exact g32p_supplierForest_actual_032934
  · exact g32p_supplierForest_actual_032953
  · exact g32p_supplierForest_actual_032985
  · exact g32p_supplierForest_actual_032998
  · exact g32p_supplierForest_actual_033068
  · exact g32p_supplierForest_actual_033071
  · exact g32p_supplierForest_actual_033074
  · exact g32p_supplierForest_actual_033093
  · exact g32p_supplierForest_actual_033108
  · exact g32p_supplierForest_actual_033148
  · exact g32p_supplierForest_actual_033153
  · exact g32p_supplierForest_actual_033176
  · exact g32p_supplierForest_actual_033186
  · exact g32p_supplierForest_actual_033223
  · exact g32p_supplierForest_actual_033257
  · exact g32p_supplierForest_actual_033261
  · exact g32p_supplierForest_actual_033283
  · exact g32p_supplierForest_actual_033284
  · exact g32p_supplierForest_actual_033307
  · exact g32p_supplierForest_actual_033351
  · exact g32p_supplierForest_actual_033405
  · exact g32p_supplierForest_actual_033464
  · exact g32p_supplierForest_actual_033474
  · exact g32p_supplierForest_actual_033552
  · exact g32p_supplierForest_actual_033562
  · exact g32p_supplierForest_actual_033636
  · exact g32p_supplierForest_actual_033666
  · exact g32p_supplierForest_actual_033667
  · exact g32p_supplierForest_actual_033736
  · exact g32p_supplierForest_actual_033770
  · exact g32p_supplierForest_actual_033786
  · exact g32p_supplierForest_actual_033788
  · exact g32p_supplierForest_actual_033810
  · exact g32p_supplierForest_actual_033903
  · exact g32p_supplierForest_actual_033908
  · exact g32p_supplierForest_actual_033911
  · exact g32p_supplierForest_actual_033921
  · exact g32p_supplierForest_actual_033928
  · exact g32p_supplierForest_actual_033938
  · exact g32p_supplierForest_actual_033940
  · exact g32p_supplierForest_actual_033941
  · exact g32p_supplierForest_actual_033976
  · exact g32p_supplierForest_actual_033978
  · exact g32p_supplierForest_actual_034061
  · exact g32p_supplierForest_actual_034068
  · exact g32p_supplierForest_actual_034069
  · exact g32p_supplierForest_actual_034082
  · exact g32p_supplierForest_actual_034128
  · exact g32p_supplierForest_actual_034153
  · exact g32p_supplierForest_actual_034194
  · exact g32p_supplierForest_actual_034203
  · exact g32p_supplierForest_actual_034243
  · exact g32p_supplierForest_actual_034280
  · exact g32p_supplierForest_actual_034321
  · exact g32p_supplierForest_actual_034353
  · exact g32p_supplierForest_actual_034389
  · exact g32p_supplierForest_actual_034392
  · exact g32p_supplierForest_actual_034395
  · exact g32p_supplierForest_actual_034431
  · exact g32p_supplierForest_actual_034437
  · exact g32p_supplierForest_actual_034459
  · exact g32p_supplierForest_actual_034461
  · exact g32p_supplierForest_actual_034465
  · exact g32p_supplierForest_actual_034545
  · exact g32p_supplierForest_actual_034549
  · exact g32p_supplierForest_actual_034560
  · exact g32p_supplierForest_actual_034572
  · exact g32p_supplierForest_actual_034584
  · exact g32p_supplierForest_actual_034602
  · exact g32p_supplierForest_actual_034615
  · exact g32p_supplierForest_actual_034616
  · exact g32p_supplierForest_actual_034639
  · exact g32p_supplierForest_actual_034666
  · exact g32p_supplierForest_actual_034690
  · exact g32p_supplierForest_actual_034694
  · exact g32p_supplierForest_actual_034701
  · exact g32p_supplierForest_actual_034737
  · exact g32p_supplierForest_actual_034765
  · exact g32p_supplierForest_actual_034773
  · exact g32p_supplierForest_actual_034823
  · exact g32p_supplierForest_actual_034826
  · exact g32p_supplierForest_actual_034841
  · exact g32p_supplierForest_actual_034857
  · exact g32p_supplierForest_actual_034868
  · exact g32p_supplierForest_actual_034874
  · exact g32p_supplierForest_actual_034876
  · exact g32p_supplierForest_actual_034893
  · exact g32p_supplierForest_actual_034905
  · exact g32p_supplierForest_actual_034906
  · exact g32p_supplierForest_actual_034999
  · exact g32p_supplierForest_actual_035008
  · exact g32p_supplierForest_actual_035011
  · exact g32p_supplierForest_actual_035017
  · exact g32p_supplierForest_actual_035040
  · exact g32p_supplierForest_actual_035061
  · exact g32p_supplierForest_actual_035080
  · exact g32p_supplierForest_actual_035113
  · exact g32p_supplierForest_actual_035117
  · exact g32p_supplierForest_actual_035140
  · exact g32p_supplierForest_actual_035145
  · exact g32p_supplierForest_actual_035156
  · exact g32p_supplierForest_actual_035179
  · exact g32p_supplierForest_actual_035193
  · exact g32p_supplierForest_actual_035209
  · exact g32p_supplierForest_actual_035263
  · exact g32p_supplierForest_actual_035293
  · exact g32p_supplierForest_actual_035338
  · exact g32p_supplierForest_actual_035343
  · exact g32p_supplierForest_actual_035356
  · exact g32p_supplierForest_actual_035383
  · exact g32p_supplierForest_actual_035388
  · exact g32p_supplierForest_actual_035453
  · exact g32p_supplierForest_actual_035473
  · exact g32p_supplierForest_actual_035538
  · exact g32p_supplierForest_actual_035567
  · exact g32p_supplierForest_actual_035596
  · exact g32p_supplierForest_actual_035608
  · exact g32p_supplierForest_actual_035610
  · exact g32p_supplierForest_actual_035678
  · exact g32p_supplierForest_actual_035761
  · exact g32p_supplierForest_actual_035777
  · exact g32p_supplierForest_actual_035865
  · exact g32p_supplierForest_actual_035882
  · exact g32p_supplierForest_actual_035893
  · exact g32p_supplierForest_actual_035900
  · exact g32p_supplierForest_actual_035908
  · exact g32p_supplierForest_actual_035910
  · exact g32p_supplierForest_actual_035932
  · exact g32p_supplierForest_actual_035951
  · exact g32p_supplierForest_actual_035993
  · exact g32p_supplierForest_actual_036023
  · exact g32p_supplierForest_actual_036045
  · exact g32p_supplierForest_actual_036049
  · exact g32p_supplierForest_actual_036062
  · exact g32p_supplierForest_actual_036065
  · exact g32p_supplierForest_actual_036070
  · exact g32p_supplierForest_actual_036080
  · exact g32p_supplierForest_actual_036106
  · exact g32p_supplierForest_actual_036126
  · exact g32p_supplierForest_actual_036140
  · exact g32p_supplierForest_actual_036146
  · exact g32p_supplierForest_actual_036149
  · exact g32p_supplierForest_actual_036216
  · exact g32p_supplierForest_actual_036235
  · exact g32p_supplierForest_actual_036276
  · exact g32p_supplierForest_actual_036278
  · exact g32p_supplierForest_actual_036306
  · exact g32p_supplierForest_actual_036346
  · exact g32p_supplierForest_actual_036367
  · exact g32p_supplierForest_actual_036427
  · exact g32p_supplierForest_actual_036443
  · exact g32p_supplierForest_actual_036444
  · exact g32p_supplierForest_actual_036453
  · exact g32p_supplierForest_actual_036454
  · exact g32p_supplierForest_actual_036462
  · exact g32p_supplierForest_actual_036509
  · exact g32p_supplierForest_actual_036525
  · exact g32p_supplierForest_actual_036556
  · exact g32p_supplierForest_actual_036585
  · exact g32p_supplierForest_actual_036654
  · exact g32p_supplierForest_actual_036657
  · exact g32p_supplierForest_actual_036689
  · exact g32p_supplierForest_actual_036759
  · exact g32p_supplierForest_actual_036763
  · exact g32p_supplierForest_actual_036782
  · exact g32p_supplierForest_actual_036801
  · exact g32p_supplierForest_actual_036830
  · exact g32p_supplierForest_actual_036833
  · exact g32p_supplierForest_actual_036848
  · exact g32p_supplierForest_actual_036858
  · exact g32p_supplierForest_actual_036859
  · exact g32p_supplierForest_actual_036901
  · exact g32p_supplierForest_actual_036905
  · exact g32p_supplierForest_actual_036939
  · exact g32p_supplierForest_actual_036953
  · exact g32p_supplierForest_actual_036974
  · exact g32p_supplierForest_actual_036996
  · exact g32p_supplierForest_actual_037019
  · exact g32p_supplierForest_actual_037080
  · exact g32p_supplierForest_actual_037101
  · exact g32p_supplierForest_actual_037132
  · exact g32p_supplierForest_actual_037162
  · exact g32p_supplierForest_actual_037192
  · exact g32p_supplierForest_actual_037194
  · exact g32p_supplierForest_actual_037208
  · exact g32p_supplierForest_actual_037242
  · exact g32p_supplierForest_actual_037266
  · exact g32p_supplierForest_actual_037270
  · exact g32p_supplierForest_actual_037311
  · exact g32p_supplierForest_actual_037404
  · exact g32p_supplierForest_actual_037438
  · exact g32p_supplierForest_actual_037461
  · exact g32p_supplierForest_actual_037469
  · exact g32p_supplierForest_actual_037509
  · exact g32p_supplierForest_actual_037516
  · exact g32p_supplierForest_actual_037542
  · exact g32p_supplierForest_actual_037623
  · exact g32p_supplierForest_actual_037712
  · exact g32p_supplierForest_actual_037713
  · exact g32p_supplierForest_actual_037788
  · exact g32p_supplierForest_actual_037806
  · exact g32p_supplierForest_actual_037842
  · exact g32p_supplierForest_actual_037866
  · exact g32p_supplierForest_actual_037887
  · exact g32p_supplierForest_actual_037888
  · exact g32p_supplierForest_actual_037896
  · exact g32p_supplierForest_actual_037932
  · exact g32p_supplierForest_actual_037944
  · exact g32p_supplierForest_actual_037959
  · exact g32p_supplierForest_actual_037971
  · exact g32p_supplierForest_actual_037999
  · exact g32p_supplierForest_actual_038010
  · exact g32p_supplierForest_actual_038013
  · exact g32p_supplierForest_actual_038045
  · exact g32p_supplierForest_actual_038059

def g32p_supplierForest_nodes_091 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_038062 else g32p_supplierForest_node_038084) else (if i.val < 3 then g32p_supplierForest_node_038172 else g32p_supplierForest_node_038180)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_038196 else g32p_supplierForest_node_038219) else (if i.val < 7 then g32p_supplierForest_node_038231 else g32p_supplierForest_node_038302))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_038311 else g32p_supplierForest_node_038314) else (if i.val < 11 then g32p_supplierForest_node_038328 else g32p_supplierForest_node_038340)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_038343 else g32p_supplierForest_node_038355) else (if i.val < 15 then g32p_supplierForest_node_038381 else g32p_supplierForest_node_038399)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_038413 else g32p_supplierForest_node_038451) else (if i.val < 19 then g32p_supplierForest_node_038476 else g32p_supplierForest_node_038554)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_038582 else g32p_supplierForest_node_038610) else (if i.val < 23 then g32p_supplierForest_node_038630 else g32p_supplierForest_node_038644))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_038651 else g32p_supplierForest_node_038672) else (if i.val < 27 then g32p_supplierForest_node_038720 else g32p_supplierForest_node_038726)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_038807 else g32p_supplierForest_node_038838) else (if i.val < 31 then g32p_supplierForest_node_038843 else g32p_supplierForest_node_038852))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_038858 else g32p_supplierForest_node_038900) else (if i.val < 35 then g32p_supplierForest_node_038945 else g32p_supplierForest_node_038974)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_038980 else g32p_supplierForest_node_038982) else (if i.val < 39 then g32p_supplierForest_node_038998 else g32p_supplierForest_node_039057))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_039058 else g32p_supplierForest_node_039123) else (if i.val < 43 then g32p_supplierForest_node_039137 else g32p_supplierForest_node_039157)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_039159 else g32p_supplierForest_node_039164) else (if i.val < 47 then g32p_supplierForest_node_039180 else g32p_supplierForest_node_039187)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_039188 else g32p_supplierForest_node_039231) else (if i.val < 51 then g32p_supplierForest_node_039268 else g32p_supplierForest_node_039290)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_039298 else g32p_supplierForest_node_039300) else (if i.val < 55 then g32p_supplierForest_node_039310 else g32p_supplierForest_node_039393))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_039394 else g32p_supplierForest_node_039416) else (if i.val < 59 then g32p_supplierForest_node_039422 else g32p_supplierForest_node_039433)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_039436 else g32p_supplierForest_node_039440) else (if i.val < 63 then g32p_supplierForest_node_039461 else g32p_supplierForest_node_039462)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_039503 else g32p_supplierForest_node_039531) else (if i.val < 67 then g32p_supplierForest_node_039538 else g32p_supplierForest_node_039540)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_039550 else g32p_supplierForest_node_039551) else (if i.val < 71 then g32p_supplierForest_node_039593 else g32p_supplierForest_node_039654))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_039656 else g32p_supplierForest_node_039659) else (if i.val < 75 then g32p_supplierForest_node_039667 else g32p_supplierForest_node_039709)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_039767 else g32p_supplierForest_node_039768) else (if i.val < 79 then g32p_supplierForest_node_039805 else g32p_supplierForest_node_039817)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_039874 else g32p_supplierForest_node_039886) else (if i.val < 83 then g32p_supplierForest_node_039908 else g32p_supplierForest_node_039968)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_039969 else g32p_supplierForest_node_039980) else (if i.val < 87 then g32p_supplierForest_node_040004 else g32p_supplierForest_node_040018))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_040023 else g32p_supplierForest_node_040030) else (if i.val < 91 then g32p_supplierForest_node_040077 else g32p_supplierForest_node_040090)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_040132 else g32p_supplierForest_node_040139) else (if i.val < 95 then g32p_supplierForest_node_040165 else g32p_supplierForest_node_040232))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_040260 else g32p_supplierForest_node_040297) else (if i.val < 99 then g32p_supplierForest_node_040300 else g32p_supplierForest_node_040301)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_040314 else g32p_supplierForest_node_040324) else (if i.val < 103 then g32p_supplierForest_node_040355 else g32p_supplierForest_node_040361))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_040386 else g32p_supplierForest_node_040387) else (if i.val < 107 then g32p_supplierForest_node_040393 else g32p_supplierForest_node_040405)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_040418 else g32p_supplierForest_node_040435) else (if i.val < 111 then g32p_supplierForest_node_040447 else g32p_supplierForest_node_040463)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_040583 else g32p_supplierForest_node_040602) else (if i.val < 115 then g32p_supplierForest_node_040620 else g32p_supplierForest_node_040629)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_040661 else g32p_supplierForest_node_040666) else (if i.val < 119 then g32p_supplierForest_node_040683 else g32p_supplierForest_node_040688))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_040689 else g32p_supplierForest_node_040698) else (if i.val < 123 then g32p_supplierForest_node_040703 else g32p_supplierForest_node_040733)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_040737 else g32p_supplierForest_node_040870) else (if i.val < 127 then g32p_supplierForest_node_040900 else g32p_supplierForest_node_040909))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_040910 else g32p_supplierForest_node_040979) else (if i.val < 131 then g32p_supplierForest_node_041002 else g32p_supplierForest_node_041022)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_041053 else g32p_supplierForest_node_041062) else (if i.val < 135 then g32p_supplierForest_node_041136 else g32p_supplierForest_node_041195))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_041196 else g32p_supplierForest_node_041217) else (if i.val < 139 then g32p_supplierForest_node_041223 else g32p_supplierForest_node_041282)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_041283 else g32p_supplierForest_node_041306) else (if i.val < 143 then g32p_supplierForest_node_041345 else g32p_supplierForest_node_041379)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_041382 else g32p_supplierForest_node_041461) else (if i.val < 147 then g32p_supplierForest_node_041480 else g32p_supplierForest_node_041491)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_041581 else g32p_supplierForest_node_041583) else (if i.val < 151 then g32p_supplierForest_node_041602 else g32p_supplierForest_node_041624))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_041635 else g32p_supplierForest_node_041646) else (if i.val < 155 then g32p_supplierForest_node_041647 else g32p_supplierForest_node_041654)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_041660 else g32p_supplierForest_node_041687) else (if i.val < 159 then g32p_supplierForest_node_041693 else g32p_supplierForest_node_041704))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_041708 else g32p_supplierForest_node_041802) else (if i.val < 163 then g32p_supplierForest_node_041864 else g32p_supplierForest_node_041881)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_041900 else g32p_supplierForest_node_041939) else (if i.val < 167 then g32p_supplierForest_node_041985 else g32p_supplierForest_node_042022))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_042049 else g32p_supplierForest_node_042101) else (if i.val < 171 then g32p_supplierForest_node_042105 else g32p_supplierForest_node_042124)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_042134 else g32p_supplierForest_node_042142) else (if i.val < 175 then g32p_supplierForest_node_042150 else g32p_supplierForest_node_042199)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_042201 else g32p_supplierForest_node_042204) else (if i.val < 179 then g32p_supplierForest_node_042241 else g32p_supplierForest_node_042281)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_042288 else g32p_supplierForest_node_042356) else (if i.val < 183 then g32p_supplierForest_node_042364 else g32p_supplierForest_node_042383))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_042441 else g32p_supplierForest_node_042481) else (if i.val < 187 then g32p_supplierForest_node_042490 else g32p_supplierForest_node_042510)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_042511 else g32p_supplierForest_node_042522) else (if i.val < 191 then g32p_supplierForest_node_042604 else g32p_supplierForest_node_042618)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_042647 else g32p_supplierForest_node_042668) else (if i.val < 195 then g32p_supplierForest_node_042674 else g32p_supplierForest_node_042691)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_042758 else g32p_supplierForest_node_042760) else (if i.val < 199 then g32p_supplierForest_node_042809 else g32p_supplierForest_node_042822))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_042826 else g32p_supplierForest_node_042829) else (if i.val < 203 then g32p_supplierForest_node_042838 else g32p_supplierForest_node_042876)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_042919 else g32p_supplierForest_node_042920) else (if i.val < 207 then g32p_supplierForest_node_042928 else g32p_supplierForest_node_043001)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_043023 else g32p_supplierForest_node_043045) else (if i.val < 211 then g32p_supplierForest_node_043118 else g32p_supplierForest_node_043189)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_043233 else g32p_supplierForest_node_043243) else (if i.val < 215 then g32p_supplierForest_node_043280 else g32p_supplierForest_node_043291))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_043322 else g32p_supplierForest_node_043324) else (if i.val < 219 then g32p_supplierForest_node_043333 else g32p_supplierForest_node_043362)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_043400 else g32p_supplierForest_node_043425) else (if i.val < 223 then g32p_supplierForest_node_043463 else g32p_supplierForest_node_043521))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_043526 else g32p_supplierForest_node_043555) else (if i.val < 227 then g32p_supplierForest_node_043589 else g32p_supplierForest_node_043600)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_043621 else g32p_supplierForest_node_043631) else (if i.val < 231 then g32p_supplierForest_node_043676 else g32p_supplierForest_node_043706))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_043737 else g32p_supplierForest_node_043760) else (if i.val < 235 then g32p_supplierForest_node_043849 else g32p_supplierForest_node_043923)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_043960 else g32p_supplierForest_node_043969) else (if i.val < 239 then g32p_supplierForest_node_043980 else g32p_supplierForest_node_043991)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_043999 else g32p_supplierForest_node_044006) else (if i.val < 243 then g32p_supplierForest_node_044021 else g32p_supplierForest_node_044054)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_044115 else g32p_supplierForest_node_044165) else (if i.val < 247 then g32p_supplierForest_node_044203 else g32p_supplierForest_node_044208))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_044226 else g32p_supplierForest_node_044227) else (if i.val < 251 then g32p_supplierForest_node_044236 else g32p_supplierForest_node_044247)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_044248 else g32p_supplierForest_node_044251) else (if i.val < 255 then g32p_supplierForest_node_044262 else g32p_supplierForest_node_044304))))))))

def g32p_supplierForest_classes_091 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 32 else 61) else (if i.val < 3 then 57 else 16)) else (if i.val < 6 then (if i.val < 5 then 14 else 57) else (if i.val < 7 then 30 else 57))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 30 else 30) else (if i.val < 11 then 32 else 16)) else (if i.val < 14 then (if i.val < 13 then 30 else 57) else (if i.val < 15 then 34 else 57)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 15) else (if i.val < 19 then 33 else 57)) else (if i.val < 22 then (if i.val < 21 then 57 else 30) else (if i.val < 23 then 36 else 59))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 57 else 16) else (if i.val < 27 then 57 else 30)) else (if i.val < 30 then (if i.val < 29 then 57 else 57) else (if i.val < 31 then 15 else 59))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 57 else 30) else (if i.val < 35 then 57 else 57)) else (if i.val < 38 then (if i.val < 37 then 59 else 17) else (if i.val < 39 then 33 else 29))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 30 else 30) else (if i.val < 43 then 32 else 15)) else (if i.val < 46 then (if i.val < 45 then 63 else 16) else (if i.val < 47 then 61 else 59)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 30 else 30) else (if i.val < 51 then 32 else 32)) else (if i.val < 54 then (if i.val < 53 then 57 else 16) else (if i.val < 55 then 16 else 57))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 57 else 30) else (if i.val < 59 then 57 else 32)) else (if i.val < 62 then (if i.val < 61 then 30 else 30) else (if i.val < 63 then 57 else 29)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 17 else 63) else (if i.val < 67 then 59 else 57)) else (if i.val < 70 then (if i.val < 69 then 33 else 29) else (if i.val < 71 then 60 else 30))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 16 else 63) else (if i.val < 75 then 59 else 57)) else (if i.val < 78 then (if i.val < 77 then 62 else 29) else (if i.val < 79 then 63 else 63)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 34 else 63) else (if i.val < 83 then 63 else 34)) else (if i.val < 86 then (if i.val < 85 then 16 else 30) else (if i.val < 87 then 32 else 30))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 59 else 33) else (if i.val < 91 then 17 else 59)) else (if i.val < 94 then (if i.val < 93 then 30 else 59) else (if i.val < 95 then 16 else 57))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 30 else 57) else (if i.val < 99 then 35 else 34)) else (if i.val < 102 then (if i.val < 101 then 32 else 16) else (if i.val < 103 then 62 else 35))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 29 else 57) else (if i.val < 107 then 62 else 30)) else (if i.val < 110 then (if i.val < 109 then 36 else 57) else (if i.val < 111 then 30 else 30)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 57 else 14) else (if i.val < 115 then 57 else 30)) else (if i.val < 118 then (if i.val < 117 then 64 else 30) else (if i.val < 119 then 16 else 29))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 16 else 29) else (if i.val < 123 then 30 else 57)) else (if i.val < 126 then (if i.val < 125 then 57 else 33) else (if i.val < 127 then 36 else 59))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 16 else 63) else (if i.val < 131 then 57 else 64)) else (if i.val < 134 then (if i.val < 133 then 57 else 58) else (if i.val < 135 then 30 else 57))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 60 else 63) else (if i.val < 139 then 63 else 16)) else (if i.val < 142 then (if i.val < 141 then 57 else 16) else (if i.val < 143 then 59 else 57)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 57 else 30) else (if i.val < 147 then 29 else 30)) else (if i.val < 150 then (if i.val < 149 then 29 else 29) else (if i.val < 151 then 29 else 15))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 29 else 16) else (if i.val < 155 then 30 else 58)) else (if i.val < 158 then (if i.val < 157 then 14 else 29) else (if i.val < 159 then 59 else 15))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 30 else 57) else (if i.val < 163 then 29 else 30)) else (if i.val < 166 then (if i.val < 165 then 30 else 33) else (if i.val < 167 then 57 else 14))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 59 else 29) else (if i.val < 171 then 15 else 33)) else (if i.val < 174 then (if i.val < 173 then 15 else 57) else (if i.val < 175 then 33 else 32)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 59 else 30) else (if i.val < 179 then 57 else 57)) else (if i.val < 182 then (if i.val < 181 then 57 else 62) else (if i.val < 183 then 16 else 66))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 57 else 30) else (if i.val < 187 then 34 else 57)) else (if i.val < 190 then (if i.val < 189 then 57 else 63) else (if i.val < 191 then 14 else 63)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 14 else 30) else (if i.val < 195 then 17 else 14)) else (if i.val < 198 then (if i.val < 197 then 57 else 30) else (if i.val < 199 then 30 else 16))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 59 else 57) else (if i.val < 203 then 30 else 30)) else (if i.val < 206 then (if i.val < 205 then 17 else 57) else (if i.val < 207 then 60 else 30)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 30 else 57) else (if i.val < 211 then 63 else 60)) else (if i.val < 214 then (if i.val < 213 then 15 else 35) else (if i.val < 215 then 57 else 30))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 30 else 59) else (if i.val < 219 then 57 else 30)) else (if i.val < 222 then (if i.val < 221 then 30 else 57) else (if i.val < 223 then 57 else 62))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 57 else 16) else (if i.val < 227 then 57 else 16)) else (if i.val < 230 then (if i.val < 229 then 16 else 57) else (if i.val < 231 then 57 else 30))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 59 else 16) else (if i.val < 235 then 57 else 35)) else (if i.val < 238 then (if i.val < 237 then 57 else 14) else (if i.val < 239 then 57 else 59)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 57 else 58) else (if i.val < 243 then 59 else 57)) else (if i.val < 246 then (if i.val < 245 then 15 else 30) else (if i.val < 247 then 16 else 57))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 61 else 57) else (if i.val < 251 then 35 else 57)) else (if i.val < 254 then (if i.val < 253 then 30 else 60) else (if i.val < 255 then 60 else 57))))))))

theorem g32p_supplierForest_actual_091 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_091 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_091 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_038062
  · exact g32p_supplierForest_actual_038084
  · exact g32p_supplierForest_actual_038172
  · exact g32p_supplierForest_actual_038180
  · exact g32p_supplierForest_actual_038196
  · exact g32p_supplierForest_actual_038219
  · exact g32p_supplierForest_actual_038231
  · exact g32p_supplierForest_actual_038302
  · exact g32p_supplierForest_actual_038311
  · exact g32p_supplierForest_actual_038314
  · exact g32p_supplierForest_actual_038328
  · exact g32p_supplierForest_actual_038340
  · exact g32p_supplierForest_actual_038343
  · exact g32p_supplierForest_actual_038355
  · exact g32p_supplierForest_actual_038381
  · exact g32p_supplierForest_actual_038399
  · exact g32p_supplierForest_actual_038413
  · exact g32p_supplierForest_actual_038451
  · exact g32p_supplierForest_actual_038476
  · exact g32p_supplierForest_actual_038554
  · exact g32p_supplierForest_actual_038582
  · exact g32p_supplierForest_actual_038610
  · exact g32p_supplierForest_actual_038630
  · exact g32p_supplierForest_actual_038644
  · exact g32p_supplierForest_actual_038651
  · exact g32p_supplierForest_actual_038672
  · exact g32p_supplierForest_actual_038720
  · exact g32p_supplierForest_actual_038726
  · exact g32p_supplierForest_actual_038807
  · exact g32p_supplierForest_actual_038838
  · exact g32p_supplierForest_actual_038843
  · exact g32p_supplierForest_actual_038852
  · exact g32p_supplierForest_actual_038858
  · exact g32p_supplierForest_actual_038900
  · exact g32p_supplierForest_actual_038945
  · exact g32p_supplierForest_actual_038974
  · exact g32p_supplierForest_actual_038980
  · exact g32p_supplierForest_actual_038982
  · exact g32p_supplierForest_actual_038998
  · exact g32p_supplierForest_actual_039057
  · exact g32p_supplierForest_actual_039058
  · exact g32p_supplierForest_actual_039123
  · exact g32p_supplierForest_actual_039137
  · exact g32p_supplierForest_actual_039157
  · exact g32p_supplierForest_actual_039159
  · exact g32p_supplierForest_actual_039164
  · exact g32p_supplierForest_actual_039180
  · exact g32p_supplierForest_actual_039187
  · exact g32p_supplierForest_actual_039188
  · exact g32p_supplierForest_actual_039231
  · exact g32p_supplierForest_actual_039268
  · exact g32p_supplierForest_actual_039290
  · exact g32p_supplierForest_actual_039298
  · exact g32p_supplierForest_actual_039300
  · exact g32p_supplierForest_actual_039310
  · exact g32p_supplierForest_actual_039393
  · exact g32p_supplierForest_actual_039394
  · exact g32p_supplierForest_actual_039416
  · exact g32p_supplierForest_actual_039422
  · exact g32p_supplierForest_actual_039433
  · exact g32p_supplierForest_actual_039436
  · exact g32p_supplierForest_actual_039440
  · exact g32p_supplierForest_actual_039461
  · exact g32p_supplierForest_actual_039462
  · exact g32p_supplierForest_actual_039503
  · exact g32p_supplierForest_actual_039531
  · exact g32p_supplierForest_actual_039538
  · exact g32p_supplierForest_actual_039540
  · exact g32p_supplierForest_actual_039550
  · exact g32p_supplierForest_actual_039551
  · exact g32p_supplierForest_actual_039593
  · exact g32p_supplierForest_actual_039654
  · exact g32p_supplierForest_actual_039656
  · exact g32p_supplierForest_actual_039659
  · exact g32p_supplierForest_actual_039667
  · exact g32p_supplierForest_actual_039709
  · exact g32p_supplierForest_actual_039767
  · exact g32p_supplierForest_actual_039768
  · exact g32p_supplierForest_actual_039805
  · exact g32p_supplierForest_actual_039817
  · exact g32p_supplierForest_actual_039874
  · exact g32p_supplierForest_actual_039886
  · exact g32p_supplierForest_actual_039908
  · exact g32p_supplierForest_actual_039968
  · exact g32p_supplierForest_actual_039969
  · exact g32p_supplierForest_actual_039980
  · exact g32p_supplierForest_actual_040004
  · exact g32p_supplierForest_actual_040018
  · exact g32p_supplierForest_actual_040023
  · exact g32p_supplierForest_actual_040030
  · exact g32p_supplierForest_actual_040077
  · exact g32p_supplierForest_actual_040090
  · exact g32p_supplierForest_actual_040132
  · exact g32p_supplierForest_actual_040139
  · exact g32p_supplierForest_actual_040165
  · exact g32p_supplierForest_actual_040232
  · exact g32p_supplierForest_actual_040260
  · exact g32p_supplierForest_actual_040297
  · exact g32p_supplierForest_actual_040300
  · exact g32p_supplierForest_actual_040301
  · exact g32p_supplierForest_actual_040314
  · exact g32p_supplierForest_actual_040324
  · exact g32p_supplierForest_actual_040355
  · exact g32p_supplierForest_actual_040361
  · exact g32p_supplierForest_actual_040386
  · exact g32p_supplierForest_actual_040387
  · exact g32p_supplierForest_actual_040393
  · exact g32p_supplierForest_actual_040405
  · exact g32p_supplierForest_actual_040418
  · exact g32p_supplierForest_actual_040435
  · exact g32p_supplierForest_actual_040447
  · exact g32p_supplierForest_actual_040463
  · exact g32p_supplierForest_actual_040583
  · exact g32p_supplierForest_actual_040602
  · exact g32p_supplierForest_actual_040620
  · exact g32p_supplierForest_actual_040629
  · exact g32p_supplierForest_actual_040661
  · exact g32p_supplierForest_actual_040666
  · exact g32p_supplierForest_actual_040683
  · exact g32p_supplierForest_actual_040688
  · exact g32p_supplierForest_actual_040689
  · exact g32p_supplierForest_actual_040698
  · exact g32p_supplierForest_actual_040703
  · exact g32p_supplierForest_actual_040733
  · exact g32p_supplierForest_actual_040737
  · exact g32p_supplierForest_actual_040870
  · exact g32p_supplierForest_actual_040900
  · exact g32p_supplierForest_actual_040909
  · exact g32p_supplierForest_actual_040910
  · exact g32p_supplierForest_actual_040979
  · exact g32p_supplierForest_actual_041002
  · exact g32p_supplierForest_actual_041022
  · exact g32p_supplierForest_actual_041053
  · exact g32p_supplierForest_actual_041062
  · exact g32p_supplierForest_actual_041136
  · exact g32p_supplierForest_actual_041195
  · exact g32p_supplierForest_actual_041196
  · exact g32p_supplierForest_actual_041217
  · exact g32p_supplierForest_actual_041223
  · exact g32p_supplierForest_actual_041282
  · exact g32p_supplierForest_actual_041283
  · exact g32p_supplierForest_actual_041306
  · exact g32p_supplierForest_actual_041345
  · exact g32p_supplierForest_actual_041379
  · exact g32p_supplierForest_actual_041382
  · exact g32p_supplierForest_actual_041461
  · exact g32p_supplierForest_actual_041480
  · exact g32p_supplierForest_actual_041491
  · exact g32p_supplierForest_actual_041581
  · exact g32p_supplierForest_actual_041583
  · exact g32p_supplierForest_actual_041602
  · exact g32p_supplierForest_actual_041624
  · exact g32p_supplierForest_actual_041635
  · exact g32p_supplierForest_actual_041646
  · exact g32p_supplierForest_actual_041647
  · exact g32p_supplierForest_actual_041654
  · exact g32p_supplierForest_actual_041660
  · exact g32p_supplierForest_actual_041687
  · exact g32p_supplierForest_actual_041693
  · exact g32p_supplierForest_actual_041704
  · exact g32p_supplierForest_actual_041708
  · exact g32p_supplierForest_actual_041802
  · exact g32p_supplierForest_actual_041864
  · exact g32p_supplierForest_actual_041881
  · exact g32p_supplierForest_actual_041900
  · exact g32p_supplierForest_actual_041939
  · exact g32p_supplierForest_actual_041985
  · exact g32p_supplierForest_actual_042022
  · exact g32p_supplierForest_actual_042049
  · exact g32p_supplierForest_actual_042101
  · exact g32p_supplierForest_actual_042105
  · exact g32p_supplierForest_actual_042124
  · exact g32p_supplierForest_actual_042134
  · exact g32p_supplierForest_actual_042142
  · exact g32p_supplierForest_actual_042150
  · exact g32p_supplierForest_actual_042199
  · exact g32p_supplierForest_actual_042201
  · exact g32p_supplierForest_actual_042204
  · exact g32p_supplierForest_actual_042241
  · exact g32p_supplierForest_actual_042281
  · exact g32p_supplierForest_actual_042288
  · exact g32p_supplierForest_actual_042356
  · exact g32p_supplierForest_actual_042364
  · exact g32p_supplierForest_actual_042383
  · exact g32p_supplierForest_actual_042441
  · exact g32p_supplierForest_actual_042481
  · exact g32p_supplierForest_actual_042490
  · exact g32p_supplierForest_actual_042510
  · exact g32p_supplierForest_actual_042511
  · exact g32p_supplierForest_actual_042522
  · exact g32p_supplierForest_actual_042604
  · exact g32p_supplierForest_actual_042618
  · exact g32p_supplierForest_actual_042647
  · exact g32p_supplierForest_actual_042668
  · exact g32p_supplierForest_actual_042674
  · exact g32p_supplierForest_actual_042691
  · exact g32p_supplierForest_actual_042758
  · exact g32p_supplierForest_actual_042760
  · exact g32p_supplierForest_actual_042809
  · exact g32p_supplierForest_actual_042822
  · exact g32p_supplierForest_actual_042826
  · exact g32p_supplierForest_actual_042829
  · exact g32p_supplierForest_actual_042838
  · exact g32p_supplierForest_actual_042876
  · exact g32p_supplierForest_actual_042919
  · exact g32p_supplierForest_actual_042920
  · exact g32p_supplierForest_actual_042928
  · exact g32p_supplierForest_actual_043001
  · exact g32p_supplierForest_actual_043023
  · exact g32p_supplierForest_actual_043045
  · exact g32p_supplierForest_actual_043118
  · exact g32p_supplierForest_actual_043189
  · exact g32p_supplierForest_actual_043233
  · exact g32p_supplierForest_actual_043243
  · exact g32p_supplierForest_actual_043280
  · exact g32p_supplierForest_actual_043291
  · exact g32p_supplierForest_actual_043322
  · exact g32p_supplierForest_actual_043324
  · exact g32p_supplierForest_actual_043333
  · exact g32p_supplierForest_actual_043362
  · exact g32p_supplierForest_actual_043400
  · exact g32p_supplierForest_actual_043425
  · exact g32p_supplierForest_actual_043463
  · exact g32p_supplierForest_actual_043521
  · exact g32p_supplierForest_actual_043526
  · exact g32p_supplierForest_actual_043555
  · exact g32p_supplierForest_actual_043589
  · exact g32p_supplierForest_actual_043600
  · exact g32p_supplierForest_actual_043621
  · exact g32p_supplierForest_actual_043631
  · exact g32p_supplierForest_actual_043676
  · exact g32p_supplierForest_actual_043706
  · exact g32p_supplierForest_actual_043737
  · exact g32p_supplierForest_actual_043760
  · exact g32p_supplierForest_actual_043849
  · exact g32p_supplierForest_actual_043923
  · exact g32p_supplierForest_actual_043960
  · exact g32p_supplierForest_actual_043969
  · exact g32p_supplierForest_actual_043980
  · exact g32p_supplierForest_actual_043991
  · exact g32p_supplierForest_actual_043999
  · exact g32p_supplierForest_actual_044006
  · exact g32p_supplierForest_actual_044021
  · exact g32p_supplierForest_actual_044054
  · exact g32p_supplierForest_actual_044115
  · exact g32p_supplierForest_actual_044165
  · exact g32p_supplierForest_actual_044203
  · exact g32p_supplierForest_actual_044208
  · exact g32p_supplierForest_actual_044226
  · exact g32p_supplierForest_actual_044227
  · exact g32p_supplierForest_actual_044236
  · exact g32p_supplierForest_actual_044247
  · exact g32p_supplierForest_actual_044248
  · exact g32p_supplierForest_actual_044251
  · exact g32p_supplierForest_actual_044262
  · exact g32p_supplierForest_actual_044304

def g32p_supplierForest_nodes_092 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_044383 else g32p_supplierForest_node_044393) else (if i.val < 3 then g32p_supplierForest_node_044400 else g32p_supplierForest_node_044416)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_044417 else g32p_supplierForest_node_044422) else (if i.val < 7 then g32p_supplierForest_node_044451 else g32p_supplierForest_node_044458))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_044497 else g32p_supplierForest_node_044499) else (if i.val < 11 then g32p_supplierForest_node_044507 else g32p_supplierForest_node_044517)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_044533 else g32p_supplierForest_node_044553) else (if i.val < 15 then g32p_supplierForest_node_044601 else g32p_supplierForest_node_044645)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_044659 else g32p_supplierForest_node_044661) else (if i.val < 19 then g32p_supplierForest_node_044670 else g32p_supplierForest_node_044672)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_044679 else g32p_supplierForest_node_044680) else (if i.val < 23 then g32p_supplierForest_node_044694 else g32p_supplierForest_node_044725))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_044728 else g32p_supplierForest_node_044750) else (if i.val < 27 then g32p_supplierForest_node_044796 else g32p_supplierForest_node_044841)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_044855 else g32p_supplierForest_node_044861) else (if i.val < 31 then g32p_supplierForest_node_044882 else g32p_supplierForest_node_044905))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_044928 else g32p_supplierForest_node_044960) else (if i.val < 35 then g32p_supplierForest_node_044974 else g32p_supplierForest_node_044984)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_044988 else g32p_supplierForest_node_044989) else (if i.val < 39 then g32p_supplierForest_node_044995 else g32p_supplierForest_node_045000))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_045026 else g32p_supplierForest_node_045035) else (if i.val < 43 then g32p_supplierForest_node_045049 else g32p_supplierForest_node_045051)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_045070 else g32p_supplierForest_node_045097) else (if i.val < 47 then g32p_supplierForest_node_045121 else g32p_supplierForest_node_045130)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_045149 else g32p_supplierForest_node_045181) else (if i.val < 51 then g32p_supplierForest_node_045218 else g32p_supplierForest_node_045259)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_045266 else g32p_supplierForest_node_045291) else (if i.val < 55 then g32p_supplierForest_node_045359 else g32p_supplierForest_node_045427))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_045471 else g32p_supplierForest_node_045479) else (if i.val < 59 then g32p_supplierForest_node_045498 else g32p_supplierForest_node_045524)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_045529 else g32p_supplierForest_node_045538) else (if i.val < 63 then g32p_supplierForest_node_045574 else g32p_supplierForest_node_045609)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_045630 else g32p_supplierForest_node_045634) else (if i.val < 67 then g32p_supplierForest_node_045714 else g32p_supplierForest_node_045729)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_045797 else g32p_supplierForest_node_045849) else (if i.val < 71 then g32p_supplierForest_node_045867 else g32p_supplierForest_node_045870))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_045888 else g32p_supplierForest_node_045907) else (if i.val < 75 then g32p_supplierForest_node_045920 else g32p_supplierForest_node_045924)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_045946 else g32p_supplierForest_node_045996) else (if i.val < 79 then g32p_supplierForest_node_046002 else g32p_supplierForest_node_046081)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_046095 else g32p_supplierForest_node_046125) else (if i.val < 83 then g32p_supplierForest_node_046134 else g32p_supplierForest_node_046137)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_046195 else g32p_supplierForest_node_046204) else (if i.val < 87 then g32p_supplierForest_node_046211 else g32p_supplierForest_node_046229))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_046243 else g32p_supplierForest_node_046244) else (if i.val < 91 then g32p_supplierForest_node_046256 else g32p_supplierForest_node_046266)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_046271 else g32p_supplierForest_node_046295) else (if i.val < 95 then g32p_supplierForest_node_046319 else g32p_supplierForest_node_046357))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_046373 else g32p_supplierForest_node_046428) else (if i.val < 99 then g32p_supplierForest_node_046482 else g32p_supplierForest_node_046487)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_046505 else g32p_supplierForest_node_046510) else (if i.val < 103 then g32p_supplierForest_node_046532 else g32p_supplierForest_node_046541))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_046562 else g32p_supplierForest_node_046563) else (if i.val < 107 then g32p_supplierForest_node_046580 else g32p_supplierForest_node_046612)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_046673 else g32p_supplierForest_node_046682) else (if i.val < 111 then g32p_supplierForest_node_046688 else g32p_supplierForest_node_046705)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_046731 else g32p_supplierForest_node_046752) else (if i.val < 115 then g32p_supplierForest_node_046782 else g32p_supplierForest_node_046832)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_046844 else g32p_supplierForest_node_046872) else (if i.val < 119 then g32p_supplierForest_node_046889 else g32p_supplierForest_node_046939))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_046959 else g32p_supplierForest_node_047064) else (if i.val < 123 then g32p_supplierForest_node_047098 else g32p_supplierForest_node_047126)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_047157 else g32p_supplierForest_node_047165) else (if i.val < 127 then g32p_supplierForest_node_047172 else g32p_supplierForest_node_047180))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_047220 else g32p_supplierForest_node_047245) else (if i.val < 131 then g32p_supplierForest_node_047261 else g32p_supplierForest_node_047298)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_047307 else g32p_supplierForest_node_047334) else (if i.val < 135 then g32p_supplierForest_node_047335 else g32p_supplierForest_node_047337))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_047353 else g32p_supplierForest_node_047356) else (if i.val < 139 then g32p_supplierForest_node_047417 else g32p_supplierForest_node_047425)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_047439 else g32p_supplierForest_node_047461) else (if i.val < 143 then g32p_supplierForest_node_047502 else g32p_supplierForest_node_047508)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_047512 else g32p_supplierForest_node_047523) else (if i.val < 147 then g32p_supplierForest_node_047547 else g32p_supplierForest_node_047576)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_047601 else g32p_supplierForest_node_047605) else (if i.val < 151 then g32p_supplierForest_node_047644 else g32p_supplierForest_node_047651))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_047665 else g32p_supplierForest_node_047679) else (if i.val < 155 then g32p_supplierForest_node_047682 else g32p_supplierForest_node_047697)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_047735 else g32p_supplierForest_node_047784) else (if i.val < 159 then g32p_supplierForest_node_047804 else g32p_supplierForest_node_047847))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_047872 else g32p_supplierForest_node_047897) else (if i.val < 163 then g32p_supplierForest_node_047935 else g32p_supplierForest_node_047981)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_047985 else g32p_supplierForest_node_047996) else (if i.val < 167 then g32p_supplierForest_node_048032 else g32p_supplierForest_node_048053))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_048070 else g32p_supplierForest_node_048073) else (if i.val < 171 then g32p_supplierForest_node_048095 else g32p_supplierForest_node_048161)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_048169 else g32p_supplierForest_node_048183) else (if i.val < 175 then g32p_supplierForest_node_048200 else g32p_supplierForest_node_048223)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_048233 else g32p_supplierForest_node_048245) else (if i.val < 179 then g32p_supplierForest_node_048247 else g32p_supplierForest_node_048289)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_048293 else g32p_supplierForest_node_048310) else (if i.val < 183 then g32p_supplierForest_node_048316 else g32p_supplierForest_node_048338))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_048339 else g32p_supplierForest_node_048350) else (if i.val < 187 then g32p_supplierForest_node_048352 else g32p_supplierForest_node_048359)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_048408 else g32p_supplierForest_node_048418) else (if i.val < 191 then g32p_supplierForest_node_048442 else g32p_supplierForest_node_048487)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_048497 else g32p_supplierForest_node_048544) else (if i.val < 195 then g32p_supplierForest_node_048549 else g32p_supplierForest_node_048554)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_048668 else g32p_supplierForest_node_048682) else (if i.val < 199 then g32p_supplierForest_node_048695 else g32p_supplierForest_node_048714))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_048716 else g32p_supplierForest_node_048717) else (if i.val < 203 then g32p_supplierForest_node_048718 else g32p_supplierForest_node_048756)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_048786 else g32p_supplierForest_node_048849) else (if i.val < 207 then g32p_supplierForest_node_048855 else g32p_supplierForest_node_048889)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_048917 else g32p_supplierForest_node_048931) else (if i.val < 211 then g32p_supplierForest_node_048956 else g32p_supplierForest_node_049003)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_049004 else g32p_supplierForest_node_049029) else (if i.val < 215 then g32p_supplierForest_node_049054 else g32p_supplierForest_node_049152))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_049169 else g32p_supplierForest_node_049212) else (if i.val < 219 then g32p_supplierForest_node_049265 else g32p_supplierForest_node_049292)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_049355 else g32p_supplierForest_node_049389) else (if i.val < 223 then g32p_supplierForest_node_049392 else g32p_supplierForest_node_049436))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_049455 else g32p_supplierForest_node_049466) else (if i.val < 227 then g32p_supplierForest_node_049528 else g32p_supplierForest_node_049532)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_049539 else g32p_supplierForest_node_049594) else (if i.val < 231 then g32p_supplierForest_node_049638 else g32p_supplierForest_node_049639))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_049652 else g32p_supplierForest_node_049662) else (if i.val < 235 then g32p_supplierForest_node_049689 else g32p_supplierForest_node_049696)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_049723 else g32p_supplierForest_node_049796) else (if i.val < 239 then g32p_supplierForest_node_049838 else g32p_supplierForest_node_049872)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_049879 else g32p_supplierForest_node_049883) else (if i.val < 243 then g32p_supplierForest_node_049903 else g32p_supplierForest_node_049914)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_049916 else g32p_supplierForest_node_049956) else (if i.val < 247 then g32p_supplierForest_node_049958 else g32p_supplierForest_node_050022))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_050024 else g32p_supplierForest_node_050031) else (if i.val < 251 then g32p_supplierForest_node_050073 else g32p_supplierForest_node_050089)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_050108 else g32p_supplierForest_node_050111) else (if i.val < 255 then g32p_supplierForest_node_050138 else g32p_supplierForest_node_050144))))))))

def g32p_supplierForest_classes_092 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 30 else 30) else (if i.val < 3 then 16 else 15)) else (if i.val < 6 then (if i.val < 5 then 33 else 22) else (if i.val < 7 then 43 else 39))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 22 else 22) else (if i.val < 11 then 43 else 21)) else (if i.val < 14 then (if i.val < 13 then 39 else 43) else (if i.val < 15 then 22 else 41)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 22 else 43) else (if i.val < 19 then 38 else 21)) else (if i.val < 22 then (if i.val < 21 then 21 else 38) else (if i.val < 23 then 21 else 21))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 7 else 6) else (if i.val < 27 then 38 else 22)) else (if i.val < 30 then (if i.val < 29 then 38 else 20) else (if i.val < 31 then 39 else 6))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 40 else 22) else (if i.val < 35 then 21 else 43)) else (if i.val < 38 then (if i.val < 37 then 40 else 40) else (if i.val < 39 then 21 else 22))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 22 else 22) else (if i.val < 43 then 38 else 22)) else (if i.val < 46 then (if i.val < 45 then 21 else 24) else (if i.val < 47 then 38 else 20)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 39 else 68) else (if i.val < 51 then 38 else 40)) else (if i.val < 54 then (if i.val < 53 then 6 else 38) else (if i.val < 55 then 39 else 38))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 71 else 38) else (if i.val < 59 then 38 else 21)) else (if i.val < 62 then (if i.val < 61 then 68 else 74) else (if i.val < 63 then 22 else 20)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 70 else 20) else (if i.val < 67 then 42 else 72)) else (if i.val < 70 then (if i.val < 69 then 39 else 70) else (if i.val < 71 then 70 else 7))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 21 else 6) else (if i.val < 75 then 74 else 74)) else (if i.val < 78 then (if i.val < 77 then 38 else 72) else (if i.val < 79 then 41 else 43)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 6 else 21) else (if i.val < 83 then 39 else 6)) else (if i.val < 86 then (if i.val < 85 then 6 else 38) else (if i.val < 87 then 38 else 38))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 20 else 5) else (if i.val < 91 then 5 else 38)) else (if i.val < 94 then (if i.val < 93 then 38 else 38) else (if i.val < 95 then 7 else 5))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 21 else 74) else (if i.val < 99 then 40 else 7)) else (if i.val < 102 then (if i.val < 101 then 73 else 74) else (if i.val < 103 then 38 else 72))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 21 else 22) else (if i.val < 107 then 21 else 19)) else (if i.val < 110 then (if i.val < 109 then 40 else 43) else (if i.val < 111 then 22 else 38)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 38 else 38) else (if i.val < 115 then 70 else 38)) else (if i.val < 118 then (if i.val < 117 then 21 else 68) else (if i.val < 119 then 38 else 40))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 43 else 38) else (if i.val < 123 then 73 else 21)) else (if i.val < 126 then (if i.val < 125 then 38 else 73) else (if i.val < 127 then 38 else 42))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 38 else 38) else (if i.val < 131 then 74 else 39)) else (if i.val < 134 then (if i.val < 133 then 21 else 21) else (if i.val < 135 then 75 else 38))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 74 else 74) else (if i.val < 139 then 42 else 38)) else (if i.val < 142 then (if i.val < 141 then 38 else 74) else (if i.val < 143 then 23 else 21)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 42 else 21) else (if i.val < 147 then 21 else 74)) else (if i.val < 150 then (if i.val < 149 then 21 else 22) else (if i.val < 151 then 20 else 21))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 21 else 40) else (if i.val < 155 then 40 else 40)) else (if i.val < 158 then (if i.val < 157 then 74 else 38) else (if i.val < 159 then 68 else 7))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 21 else 42) else (if i.val < 163 then 7 else 74)) else (if i.val < 166 then (if i.val < 165 then 74 else 38) else (if i.val < 167 then 69 else 6))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 21 else 38) else (if i.val < 171 then 21 else 68)) else (if i.val < 174 then (if i.val < 173 then 39 else 22) else (if i.val < 175 then 19 else 38)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 6 else 68) else (if i.val < 179 then 38 else 22)) else (if i.val < 182 then (if i.val < 181 then 7 else 21) else (if i.val < 183 then 20 else 38))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 22 else 70) else (if i.val < 187 then 70 else 22)) else (if i.val < 190 then (if i.val < 189 then 72 else 68) else (if i.val < 191 then 22 else 22)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 21 else 43) else (if i.val < 195 then 38 else 6)) else (if i.val < 198 then (if i.val < 197 then 21 else 40) else (if i.val < 199 then 73 else 40))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 73 else 38) else (if i.val < 203 then 73 else 70)) else (if i.val < 206 then (if i.val < 205 then 74 else 6) else (if i.val < 207 then 38 else 20)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 38 else 20) else (if i.val < 211 then 22 else 21)) else (if i.val < 214 then (if i.val < 213 then 38 else 68) else (if i.val < 215 then 21 else 38))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 38 else 21) else (if i.val < 219 then 22 else 22)) else (if i.val < 222 then (if i.val < 221 then 41 else 43) else (if i.val < 223 then 21 else 21))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 38 else 22) else (if i.val < 227 then 21 else 21)) else (if i.val < 230 then (if i.val < 229 then 41 else 39) else (if i.val < 231 then 22 else 22))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 38 else 43) else (if i.val < 235 then 6 else 38)) else (if i.val < 238 then (if i.val < 237 then 21 else 21) else (if i.val < 239 then 23 else 6)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 38 else 69) else (if i.val < 243 then 38 else 38)) else (if i.val < 246 then (if i.val < 245 then 38 else 43) else (if i.val < 247 then 38 else 40))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 40 else 21) else (if i.val < 251 then 21 else 22)) else (if i.val < 254 then (if i.val < 253 then 38 else 39) else (if i.val < 255 then 7 else 22))))))))

theorem g32p_supplierForest_actual_092 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_092 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_092 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_044383
  · exact g32p_supplierForest_actual_044393
  · exact g32p_supplierForest_actual_044400
  · exact g32p_supplierForest_actual_044416
  · exact g32p_supplierForest_actual_044417
  · exact g32p_supplierForest_actual_044422
  · exact g32p_supplierForest_actual_044451
  · exact g32p_supplierForest_actual_044458
  · exact g32p_supplierForest_actual_044497
  · exact g32p_supplierForest_actual_044499
  · exact g32p_supplierForest_actual_044507
  · exact g32p_supplierForest_actual_044517
  · exact g32p_supplierForest_actual_044533
  · exact g32p_supplierForest_actual_044553
  · exact g32p_supplierForest_actual_044601
  · exact g32p_supplierForest_actual_044645
  · exact g32p_supplierForest_actual_044659
  · exact g32p_supplierForest_actual_044661
  · exact g32p_supplierForest_actual_044670
  · exact g32p_supplierForest_actual_044672
  · exact g32p_supplierForest_actual_044679
  · exact g32p_supplierForest_actual_044680
  · exact g32p_supplierForest_actual_044694
  · exact g32p_supplierForest_actual_044725
  · exact g32p_supplierForest_actual_044728
  · exact g32p_supplierForest_actual_044750
  · exact g32p_supplierForest_actual_044796
  · exact g32p_supplierForest_actual_044841
  · exact g32p_supplierForest_actual_044855
  · exact g32p_supplierForest_actual_044861
  · exact g32p_supplierForest_actual_044882
  · exact g32p_supplierForest_actual_044905
  · exact g32p_supplierForest_actual_044928
  · exact g32p_supplierForest_actual_044960
  · exact g32p_supplierForest_actual_044974
  · exact g32p_supplierForest_actual_044984
  · exact g32p_supplierForest_actual_044988
  · exact g32p_supplierForest_actual_044989
  · exact g32p_supplierForest_actual_044995
  · exact g32p_supplierForest_actual_045000
  · exact g32p_supplierForest_actual_045026
  · exact g32p_supplierForest_actual_045035
  · exact g32p_supplierForest_actual_045049
  · exact g32p_supplierForest_actual_045051
  · exact g32p_supplierForest_actual_045070
  · exact g32p_supplierForest_actual_045097
  · exact g32p_supplierForest_actual_045121
  · exact g32p_supplierForest_actual_045130
  · exact g32p_supplierForest_actual_045149
  · exact g32p_supplierForest_actual_045181
  · exact g32p_supplierForest_actual_045218
  · exact g32p_supplierForest_actual_045259
  · exact g32p_supplierForest_actual_045266
  · exact g32p_supplierForest_actual_045291
  · exact g32p_supplierForest_actual_045359
  · exact g32p_supplierForest_actual_045427
  · exact g32p_supplierForest_actual_045471
  · exact g32p_supplierForest_actual_045479
  · exact g32p_supplierForest_actual_045498
  · exact g32p_supplierForest_actual_045524
  · exact g32p_supplierForest_actual_045529
  · exact g32p_supplierForest_actual_045538
  · exact g32p_supplierForest_actual_045574
  · exact g32p_supplierForest_actual_045609
  · exact g32p_supplierForest_actual_045630
  · exact g32p_supplierForest_actual_045634
  · exact g32p_supplierForest_actual_045714
  · exact g32p_supplierForest_actual_045729
  · exact g32p_supplierForest_actual_045797
  · exact g32p_supplierForest_actual_045849
  · exact g32p_supplierForest_actual_045867
  · exact g32p_supplierForest_actual_045870
  · exact g32p_supplierForest_actual_045888
  · exact g32p_supplierForest_actual_045907
  · exact g32p_supplierForest_actual_045920
  · exact g32p_supplierForest_actual_045924
  · exact g32p_supplierForest_actual_045946
  · exact g32p_supplierForest_actual_045996
  · exact g32p_supplierForest_actual_046002
  · exact g32p_supplierForest_actual_046081
  · exact g32p_supplierForest_actual_046095
  · exact g32p_supplierForest_actual_046125
  · exact g32p_supplierForest_actual_046134
  · exact g32p_supplierForest_actual_046137
  · exact g32p_supplierForest_actual_046195
  · exact g32p_supplierForest_actual_046204
  · exact g32p_supplierForest_actual_046211
  · exact g32p_supplierForest_actual_046229
  · exact g32p_supplierForest_actual_046243
  · exact g32p_supplierForest_actual_046244
  · exact g32p_supplierForest_actual_046256
  · exact g32p_supplierForest_actual_046266
  · exact g32p_supplierForest_actual_046271
  · exact g32p_supplierForest_actual_046295
  · exact g32p_supplierForest_actual_046319
  · exact g32p_supplierForest_actual_046357
  · exact g32p_supplierForest_actual_046373
  · exact g32p_supplierForest_actual_046428
  · exact g32p_supplierForest_actual_046482
  · exact g32p_supplierForest_actual_046487
  · exact g32p_supplierForest_actual_046505
  · exact g32p_supplierForest_actual_046510
  · exact g32p_supplierForest_actual_046532
  · exact g32p_supplierForest_actual_046541
  · exact g32p_supplierForest_actual_046562
  · exact g32p_supplierForest_actual_046563
  · exact g32p_supplierForest_actual_046580
  · exact g32p_supplierForest_actual_046612
  · exact g32p_supplierForest_actual_046673
  · exact g32p_supplierForest_actual_046682
  · exact g32p_supplierForest_actual_046688
  · exact g32p_supplierForest_actual_046705
  · exact g32p_supplierForest_actual_046731
  · exact g32p_supplierForest_actual_046752
  · exact g32p_supplierForest_actual_046782
  · exact g32p_supplierForest_actual_046832
  · exact g32p_supplierForest_actual_046844
  · exact g32p_supplierForest_actual_046872
  · exact g32p_supplierForest_actual_046889
  · exact g32p_supplierForest_actual_046939
  · exact g32p_supplierForest_actual_046959
  · exact g32p_supplierForest_actual_047064
  · exact g32p_supplierForest_actual_047098
  · exact g32p_supplierForest_actual_047126
  · exact g32p_supplierForest_actual_047157
  · exact g32p_supplierForest_actual_047165
  · exact g32p_supplierForest_actual_047172
  · exact g32p_supplierForest_actual_047180
  · exact g32p_supplierForest_actual_047220
  · exact g32p_supplierForest_actual_047245
  · exact g32p_supplierForest_actual_047261
  · exact g32p_supplierForest_actual_047298
  · exact g32p_supplierForest_actual_047307
  · exact g32p_supplierForest_actual_047334
  · exact g32p_supplierForest_actual_047335
  · exact g32p_supplierForest_actual_047337
  · exact g32p_supplierForest_actual_047353
  · exact g32p_supplierForest_actual_047356
  · exact g32p_supplierForest_actual_047417
  · exact g32p_supplierForest_actual_047425
  · exact g32p_supplierForest_actual_047439
  · exact g32p_supplierForest_actual_047461
  · exact g32p_supplierForest_actual_047502
  · exact g32p_supplierForest_actual_047508
  · exact g32p_supplierForest_actual_047512
  · exact g32p_supplierForest_actual_047523
  · exact g32p_supplierForest_actual_047547
  · exact g32p_supplierForest_actual_047576
  · exact g32p_supplierForest_actual_047601
  · exact g32p_supplierForest_actual_047605
  · exact g32p_supplierForest_actual_047644
  · exact g32p_supplierForest_actual_047651
  · exact g32p_supplierForest_actual_047665
  · exact g32p_supplierForest_actual_047679
  · exact g32p_supplierForest_actual_047682
  · exact g32p_supplierForest_actual_047697
  · exact g32p_supplierForest_actual_047735
  · exact g32p_supplierForest_actual_047784
  · exact g32p_supplierForest_actual_047804
  · exact g32p_supplierForest_actual_047847
  · exact g32p_supplierForest_actual_047872
  · exact g32p_supplierForest_actual_047897
  · exact g32p_supplierForest_actual_047935
  · exact g32p_supplierForest_actual_047981
  · exact g32p_supplierForest_actual_047985
  · exact g32p_supplierForest_actual_047996
  · exact g32p_supplierForest_actual_048032
  · exact g32p_supplierForest_actual_048053
  · exact g32p_supplierForest_actual_048070
  · exact g32p_supplierForest_actual_048073
  · exact g32p_supplierForest_actual_048095
  · exact g32p_supplierForest_actual_048161
  · exact g32p_supplierForest_actual_048169
  · exact g32p_supplierForest_actual_048183
  · exact g32p_supplierForest_actual_048200
  · exact g32p_supplierForest_actual_048223
  · exact g32p_supplierForest_actual_048233
  · exact g32p_supplierForest_actual_048245
  · exact g32p_supplierForest_actual_048247
  · exact g32p_supplierForest_actual_048289
  · exact g32p_supplierForest_actual_048293
  · exact g32p_supplierForest_actual_048310
  · exact g32p_supplierForest_actual_048316
  · exact g32p_supplierForest_actual_048338
  · exact g32p_supplierForest_actual_048339
  · exact g32p_supplierForest_actual_048350
  · exact g32p_supplierForest_actual_048352
  · exact g32p_supplierForest_actual_048359
  · exact g32p_supplierForest_actual_048408
  · exact g32p_supplierForest_actual_048418
  · exact g32p_supplierForest_actual_048442
  · exact g32p_supplierForest_actual_048487
  · exact g32p_supplierForest_actual_048497
  · exact g32p_supplierForest_actual_048544
  · exact g32p_supplierForest_actual_048549
  · exact g32p_supplierForest_actual_048554
  · exact g32p_supplierForest_actual_048668
  · exact g32p_supplierForest_actual_048682
  · exact g32p_supplierForest_actual_048695
  · exact g32p_supplierForest_actual_048714
  · exact g32p_supplierForest_actual_048716
  · exact g32p_supplierForest_actual_048717
  · exact g32p_supplierForest_actual_048718
  · exact g32p_supplierForest_actual_048756
  · exact g32p_supplierForest_actual_048786
  · exact g32p_supplierForest_actual_048849
  · exact g32p_supplierForest_actual_048855
  · exact g32p_supplierForest_actual_048889
  · exact g32p_supplierForest_actual_048917
  · exact g32p_supplierForest_actual_048931
  · exact g32p_supplierForest_actual_048956
  · exact g32p_supplierForest_actual_049003
  · exact g32p_supplierForest_actual_049004
  · exact g32p_supplierForest_actual_049029
  · exact g32p_supplierForest_actual_049054
  · exact g32p_supplierForest_actual_049152
  · exact g32p_supplierForest_actual_049169
  · exact g32p_supplierForest_actual_049212
  · exact g32p_supplierForest_actual_049265
  · exact g32p_supplierForest_actual_049292
  · exact g32p_supplierForest_actual_049355
  · exact g32p_supplierForest_actual_049389
  · exact g32p_supplierForest_actual_049392
  · exact g32p_supplierForest_actual_049436
  · exact g32p_supplierForest_actual_049455
  · exact g32p_supplierForest_actual_049466
  · exact g32p_supplierForest_actual_049528
  · exact g32p_supplierForest_actual_049532
  · exact g32p_supplierForest_actual_049539
  · exact g32p_supplierForest_actual_049594
  · exact g32p_supplierForest_actual_049638
  · exact g32p_supplierForest_actual_049639
  · exact g32p_supplierForest_actual_049652
  · exact g32p_supplierForest_actual_049662
  · exact g32p_supplierForest_actual_049689
  · exact g32p_supplierForest_actual_049696
  · exact g32p_supplierForest_actual_049723
  · exact g32p_supplierForest_actual_049796
  · exact g32p_supplierForest_actual_049838
  · exact g32p_supplierForest_actual_049872
  · exact g32p_supplierForest_actual_049879
  · exact g32p_supplierForest_actual_049883
  · exact g32p_supplierForest_actual_049903
  · exact g32p_supplierForest_actual_049914
  · exact g32p_supplierForest_actual_049916
  · exact g32p_supplierForest_actual_049956
  · exact g32p_supplierForest_actual_049958
  · exact g32p_supplierForest_actual_050022
  · exact g32p_supplierForest_actual_050024
  · exact g32p_supplierForest_actual_050031
  · exact g32p_supplierForest_actual_050073
  · exact g32p_supplierForest_actual_050089
  · exact g32p_supplierForest_actual_050108
  · exact g32p_supplierForest_actual_050111
  · exact g32p_supplierForest_actual_050138
  · exact g32p_supplierForest_actual_050144

def g32p_supplierForest_nodes_093 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_050150 else g32p_supplierForest_node_050158) else (if i.val < 3 then g32p_supplierForest_node_050166 else g32p_supplierForest_node_050187)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_050209 else g32p_supplierForest_node_050227) else (if i.val < 7 then g32p_supplierForest_node_050277 else g32p_supplierForest_node_050282))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_050286 else g32p_supplierForest_node_050305) else (if i.val < 11 then g32p_supplierForest_node_050325 else g32p_supplierForest_node_050328)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_050349 else g32p_supplierForest_node_050366) else (if i.val < 15 then g32p_supplierForest_node_050376 else g32p_supplierForest_node_050399)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_050428 else g32p_supplierForest_node_050436) else (if i.val < 19 then g32p_supplierForest_node_050473 else g32p_supplierForest_node_050484)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_050494 else g32p_supplierForest_node_050501) else (if i.val < 23 then g32p_supplierForest_node_050507 else g32p_supplierForest_node_050531))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_050540 else g32p_supplierForest_node_050556) else (if i.val < 27 then g32p_supplierForest_node_050575 else g32p_supplierForest_node_050613)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_050633 else g32p_supplierForest_node_050650) else (if i.val < 31 then g32p_supplierForest_node_050663 else g32p_supplierForest_node_050688))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_050740 else g32p_supplierForest_node_050761) else (if i.val < 35 then g32p_supplierForest_node_050811 else g32p_supplierForest_node_050866)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_050884 else g32p_supplierForest_node_050889) else (if i.val < 39 then g32p_supplierForest_node_050893 else g32p_supplierForest_node_050925))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_050932 else g32p_supplierForest_node_050941) else (if i.val < 43 then g32p_supplierForest_node_050951 else g32p_supplierForest_node_050955)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_050965 else g32p_supplierForest_node_050976) else (if i.val < 47 then g32p_supplierForest_node_050982 else g32p_supplierForest_node_051004)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_051014 else g32p_supplierForest_node_051022) else (if i.val < 51 then g32p_supplierForest_node_051096 else g32p_supplierForest_node_051141)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_051168 else g32p_supplierForest_node_051186) else (if i.val < 55 then g32p_supplierForest_node_051223 else g32p_supplierForest_node_051242))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_051248 else g32p_supplierForest_node_051281) else (if i.val < 59 then g32p_supplierForest_node_051318 else g32p_supplierForest_node_051319)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_051334 else g32p_supplierForest_node_051369) else (if i.val < 63 then g32p_supplierForest_node_051370 else g32p_supplierForest_node_051390)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_051455 else g32p_supplierForest_node_051467) else (if i.val < 67 then g32p_supplierForest_node_051475 else g32p_supplierForest_node_051521)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_051526 else g32p_supplierForest_node_051553) else (if i.val < 71 then g32p_supplierForest_node_051555 else g32p_supplierForest_node_051583))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_051602 else g32p_supplierForest_node_051626) else (if i.val < 75 then g32p_supplierForest_node_051634 else g32p_supplierForest_node_051690)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_051717 else g32p_supplierForest_node_051726) else (if i.val < 79 then g32p_supplierForest_node_051775 else g32p_supplierForest_node_051778)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_051787 else g32p_supplierForest_node_051817) else (if i.val < 83 then g32p_supplierForest_node_051825 else g32p_supplierForest_node_051831)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_051832 else g32p_supplierForest_node_051841) else (if i.val < 87 then g32p_supplierForest_node_051843 else g32p_supplierForest_node_051948))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_051965 else g32p_supplierForest_node_051972) else (if i.val < 91 then g32p_supplierForest_node_051974 else g32p_supplierForest_node_051976)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_051997 else g32p_supplierForest_node_052005) else (if i.val < 95 then g32p_supplierForest_node_052020 else g32p_supplierForest_node_052030))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_052074 else g32p_supplierForest_node_052076) else (if i.val < 99 then g32p_supplierForest_node_052084 else g32p_supplierForest_node_052109)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_052156 else g32p_supplierForest_node_052167) else (if i.val < 103 then g32p_supplierForest_node_052178 else g32p_supplierForest_node_052196))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_052198 else g32p_supplierForest_node_052214) else (if i.val < 107 then g32p_supplierForest_node_052241 else g32p_supplierForest_node_052251)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_052263 else g32p_supplierForest_node_052291) else (if i.val < 111 then g32p_supplierForest_node_052314 else g32p_supplierForest_node_052341)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_052348 else g32p_supplierForest_node_052415) else (if i.val < 115 then g32p_supplierForest_node_052428 else g32p_supplierForest_node_052556)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_052615 else g32p_supplierForest_node_052617) else (if i.val < 119 then g32p_supplierForest_node_052629 else g32p_supplierForest_node_052640))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_052641 else g32p_supplierForest_node_052651) else (if i.val < 123 then g32p_supplierForest_node_052666 else g32p_supplierForest_node_052724)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_052729 else g32p_supplierForest_node_052731) else (if i.val < 127 then g32p_supplierForest_node_052739 else g32p_supplierForest_node_052768))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_052774 else g32p_supplierForest_node_052775) else (if i.val < 131 then g32p_supplierForest_node_052780 else g32p_supplierForest_node_052787)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_052795 else g32p_supplierForest_node_052832) else (if i.val < 135 then g32p_supplierForest_node_052836 else g32p_supplierForest_node_052845))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_052867 else g32p_supplierForest_node_052870) else (if i.val < 139 then g32p_supplierForest_node_052907 else g32p_supplierForest_node_052914)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_052915 else g32p_supplierForest_node_052993) else (if i.val < 143 then g32p_supplierForest_node_053019 else g32p_supplierForest_node_053020)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_053058 else g32p_supplierForest_node_053062) else (if i.val < 147 then g32p_supplierForest_node_053064 else g32p_supplierForest_node_053070)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_053111 else g32p_supplierForest_node_053117) else (if i.val < 151 then g32p_supplierForest_node_053137 else g32p_supplierForest_node_053157))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_053174 else g32p_supplierForest_node_053176) else (if i.val < 155 then g32p_supplierForest_node_053181 else g32p_supplierForest_node_053331)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_053338 else g32p_supplierForest_node_053366) else (if i.val < 159 then g32p_supplierForest_node_053469 else g32p_supplierForest_node_053527))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_053566 else g32p_supplierForest_node_053576) else (if i.val < 163 then g32p_supplierForest_node_053582 else g32p_supplierForest_node_053634)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_053664 else g32p_supplierForest_node_053744) else (if i.val < 167 then g32p_supplierForest_node_053794 else g32p_supplierForest_node_053797))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_053830 else g32p_supplierForest_node_053831) else (if i.val < 171 then g32p_supplierForest_node_053839 else g32p_supplierForest_node_053857)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_053866 else g32p_supplierForest_node_053872) else (if i.val < 175 then g32p_supplierForest_node_053890 else g32p_supplierForest_node_053893)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_053948 else g32p_supplierForest_node_053955) else (if i.val < 179 then g32p_supplierForest_node_053970 else g32p_supplierForest_node_053974)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_053998 else g32p_supplierForest_node_054010) else (if i.val < 183 then g32p_supplierForest_node_054027 else g32p_supplierForest_node_054049))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_054057 else g32p_supplierForest_node_054095) else (if i.val < 187 then g32p_supplierForest_node_054117 else g32p_supplierForest_node_054139)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_054158 else g32p_supplierForest_node_054190) else (if i.val < 191 then g32p_supplierForest_node_054192 else g32p_supplierForest_node_054205)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_054213 else g32p_supplierForest_node_054274) else (if i.val < 195 then g32p_supplierForest_node_054287 else g32p_supplierForest_node_054309)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_054318 else g32p_supplierForest_node_054328) else (if i.val < 199 then g32p_supplierForest_node_054358 else g32p_supplierForest_node_054397))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_054404 else g32p_supplierForest_node_054413) else (if i.val < 203 then g32p_supplierForest_node_054440 else g32p_supplierForest_node_054444)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_054454 else g32p_supplierForest_node_054472) else (if i.val < 207 then g32p_supplierForest_node_054475 else g32p_supplierForest_node_054484)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_054516 else g32p_supplierForest_node_054535) else (if i.val < 211 then g32p_supplierForest_node_054551 else g32p_supplierForest_node_054579)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_054587 else g32p_supplierForest_node_054613) else (if i.val < 215 then g32p_supplierForest_node_054616 else g32p_supplierForest_node_054625))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_054626 else g32p_supplierForest_node_054633) else (if i.val < 219 then g32p_supplierForest_node_054657 else g32p_supplierForest_node_054683)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_054700 else g32p_supplierForest_node_054701) else (if i.val < 223 then g32p_supplierForest_node_054706 else g32p_supplierForest_node_054712))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_054762 else g32p_supplierForest_node_054783) else (if i.val < 227 then g32p_supplierForest_node_054857 else g32p_supplierForest_node_054873)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_054937 else g32p_supplierForest_node_054940) else (if i.val < 231 then g32p_supplierForest_node_054948 else g32p_supplierForest_node_054961))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_054972 else g32p_supplierForest_node_054975) else (if i.val < 235 then g32p_supplierForest_node_054984 else g32p_supplierForest_node_054987)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_054992 else g32p_supplierForest_node_054999) else (if i.val < 239 then g32p_supplierForest_node_055068 else g32p_supplierForest_node_055099)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_055101 else g32p_supplierForest_node_055111) else (if i.val < 243 then g32p_supplierForest_node_055122 else g32p_supplierForest_node_055148)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_055150 else g32p_supplierForest_node_055169) else (if i.val < 247 then g32p_supplierForest_node_055205 else g32p_supplierForest_node_055245))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_055250 else g32p_supplierForest_node_055260) else (if i.val < 251 then g32p_supplierForest_node_055293 else g32p_supplierForest_node_055297)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_055301 else g32p_supplierForest_node_055377) else (if i.val < 255 then g32p_supplierForest_node_055389 else g32p_supplierForest_node_055391))))))))

def g32p_supplierForest_classes_093 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 70 else 21) else (if i.val < 3 then 21 else 21)) else (if i.val < 6 then (if i.val < 5 then 21 else 43) else (if i.val < 7 then 21 else 21))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 38 else 40) else (if i.val < 11 then 38 else 21)) else (if i.val < 14 then (if i.val < 13 then 38 else 22) else (if i.val < 15 then 22 else 24)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 21 else 43) else (if i.val < 19 then 38 else 39)) else (if i.val < 22 then (if i.val < 21 then 22 else 75) else (if i.val < 23 then 38 else 72))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 38 else 21) else (if i.val < 27 then 43 else 43)) else (if i.val < 30 then (if i.val < 29 then 43 else 43) else (if i.val < 31 then 38 else 38))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 22 else 38) else (if i.val < 35 then 21 else 38)) else (if i.val < 38 then (if i.val < 37 then 38 else 72) else (if i.val < 39 then 7 else 20))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 22 else 40) else (if i.val < 43 then 38 else 38)) else (if i.val < 46 then (if i.val < 45 then 38 else 38) else (if i.val < 47 then 21 else 20)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 70 else 39) else (if i.val < 51 then 22 else 22)) else (if i.val < 54 then (if i.val < 53 then 21 else 21) else (if i.val < 55 then 68 else 6))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 7 else 38) else (if i.val < 59 then 6 else 21)) else (if i.val < 62 then (if i.val < 61 then 74 else 21) else (if i.val < 63 then 21 else 21)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 38 else 21) else (if i.val < 67 then 70 else 40)) else (if i.val < 70 then (if i.val < 69 then 39 else 22) else (if i.val < 71 then 43 else 21))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 39 else 43) else (if i.val < 75 then 22 else 43)) else (if i.val < 78 then (if i.val < 77 then 21 else 43) else (if i.val < 79 then 73 else 41)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 21 else 21) else (if i.val < 83 then 38 else 38)) else (if i.val < 86 then (if i.val < 85 then 39 else 38) else (if i.val < 87 then 40 else 38))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 38 else 40) else (if i.val < 91 then 22 else 38)) else (if i.val < 94 then (if i.val < 93 then 38 else 22) else (if i.val < 95 then 38 else 21))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 43 else 21) else (if i.val < 99 then 21 else 38)) else (if i.val < 102 then (if i.val < 101 then 43 else 41) else (if i.val < 103 then 40 else 38))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 43 else 74) else (if i.val < 107 then 70 else 43)) else (if i.val < 110 then (if i.val < 109 then 20 else 75) else (if i.val < 111 then 68 else 6)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 40 else 38) else (if i.val < 115 then 43 else 38)) else (if i.val < 118 then (if i.val < 117 then 43 else 38) else (if i.val < 119 then 21 else 43))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 41 else 22) else (if i.val < 123 then 74 else 74)) else (if i.val < 126 then (if i.val < 125 then 75 else 21) else (if i.val < 127 then 40 else 41))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 43 else 6) else (if i.val < 131 then 38 else 7)) else (if i.val < 134 then (if i.val < 133 then 6 else 22) else (if i.val < 135 then 7 else 5))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 38 else 38) else (if i.val < 139 then 38 else 38)) else (if i.val < 142 then (if i.val < 141 then 38 else 38) else (if i.val < 143 then 38 else 71)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 21 else 70) else (if i.val < 147 then 21 else 73)) else (if i.val < 150 then (if i.val < 149 then 41 else 21) else (if i.val < 151 then 7 else 72))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 21 else 40) else (if i.val < 155 then 43 else 74)) else (if i.val < 158 then (if i.val < 157 then 43 else 23) else (if i.val < 159 then 41 else 41))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 43 else 41) else (if i.val < 163 then 38 else 38)) else (if i.val < 166 then (if i.val < 165 then 38 else 41) else (if i.val < 167 then 21 else 21))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 22 else 23) else (if i.val < 171 then 43 else 38)) else (if i.val < 174 then (if i.val < 173 then 38 else 39) else (if i.val < 175 then 38 else 74)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 43 else 38) else (if i.val < 179 then 20 else 38)) else (if i.val < 182 then (if i.val < 181 then 74 else 74) else (if i.val < 183 then 70 else 69))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 74 else 22) else (if i.val < 187 then 43 else 38)) else (if i.val < 190 then (if i.val < 189 then 7 else 38) else (if i.val < 191 then 38 else 73)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 38 else 72) else (if i.val < 195 then 38 else 22)) else (if i.val < 198 then (if i.val < 197 then 21 else 70) else (if i.val < 199 then 73 else 21))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 21 else 38) else (if i.val < 203 then 74 else 38)) else (if i.val < 206 then (if i.val < 205 then 38 else 43) else (if i.val < 207 then 38 else 68)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 74 else 43) else (if i.val < 211 then 74 else 43)) else (if i.val < 214 then (if i.val < 213 then 75 else 21) else (if i.val < 215 then 22 else 21))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 43 else 38) else (if i.val < 219 then 21 else 22)) else (if i.val < 222 then (if i.val < 221 then 38 else 68) else (if i.val < 223 then 74 else 21))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 7 else 38) else (if i.val < 227 then 38 else 40)) else (if i.val < 230 then (if i.val < 229 then 21 else 73) else (if i.val < 231 then 72 else 21))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 72 else 38) else (if i.val < 235 then 21 else 38)) else (if i.val < 238 then (if i.val < 237 then 43 else 38) else (if i.val < 239 then 22 else 38)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 43 else 38) else (if i.val < 243 then 40 else 21)) else (if i.val < 246 then (if i.val < 245 then 38 else 73) else (if i.val < 247 then 7 else 38))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 38 else 38) else (if i.val < 251 then 38 else 43)) else (if i.val < 254 then (if i.val < 253 then 73 else 75) else (if i.val < 255 then 68 else 21))))))))

theorem g32p_supplierForest_actual_093 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_093 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_093 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_050150
  · exact g32p_supplierForest_actual_050158
  · exact g32p_supplierForest_actual_050166
  · exact g32p_supplierForest_actual_050187
  · exact g32p_supplierForest_actual_050209
  · exact g32p_supplierForest_actual_050227
  · exact g32p_supplierForest_actual_050277
  · exact g32p_supplierForest_actual_050282
  · exact g32p_supplierForest_actual_050286
  · exact g32p_supplierForest_actual_050305
  · exact g32p_supplierForest_actual_050325
  · exact g32p_supplierForest_actual_050328
  · exact g32p_supplierForest_actual_050349
  · exact g32p_supplierForest_actual_050366
  · exact g32p_supplierForest_actual_050376
  · exact g32p_supplierForest_actual_050399
  · exact g32p_supplierForest_actual_050428
  · exact g32p_supplierForest_actual_050436
  · exact g32p_supplierForest_actual_050473
  · exact g32p_supplierForest_actual_050484
  · exact g32p_supplierForest_actual_050494
  · exact g32p_supplierForest_actual_050501
  · exact g32p_supplierForest_actual_050507
  · exact g32p_supplierForest_actual_050531
  · exact g32p_supplierForest_actual_050540
  · exact g32p_supplierForest_actual_050556
  · exact g32p_supplierForest_actual_050575
  · exact g32p_supplierForest_actual_050613
  · exact g32p_supplierForest_actual_050633
  · exact g32p_supplierForest_actual_050650
  · exact g32p_supplierForest_actual_050663
  · exact g32p_supplierForest_actual_050688
  · exact g32p_supplierForest_actual_050740
  · exact g32p_supplierForest_actual_050761
  · exact g32p_supplierForest_actual_050811
  · exact g32p_supplierForest_actual_050866
  · exact g32p_supplierForest_actual_050884
  · exact g32p_supplierForest_actual_050889
  · exact g32p_supplierForest_actual_050893
  · exact g32p_supplierForest_actual_050925
  · exact g32p_supplierForest_actual_050932
  · exact g32p_supplierForest_actual_050941
  · exact g32p_supplierForest_actual_050951
  · exact g32p_supplierForest_actual_050955
  · exact g32p_supplierForest_actual_050965
  · exact g32p_supplierForest_actual_050976
  · exact g32p_supplierForest_actual_050982
  · exact g32p_supplierForest_actual_051004
  · exact g32p_supplierForest_actual_051014
  · exact g32p_supplierForest_actual_051022
  · exact g32p_supplierForest_actual_051096
  · exact g32p_supplierForest_actual_051141
  · exact g32p_supplierForest_actual_051168
  · exact g32p_supplierForest_actual_051186
  · exact g32p_supplierForest_actual_051223
  · exact g32p_supplierForest_actual_051242
  · exact g32p_supplierForest_actual_051248
  · exact g32p_supplierForest_actual_051281
  · exact g32p_supplierForest_actual_051318
  · exact g32p_supplierForest_actual_051319
  · exact g32p_supplierForest_actual_051334
  · exact g32p_supplierForest_actual_051369
  · exact g32p_supplierForest_actual_051370
  · exact g32p_supplierForest_actual_051390
  · exact g32p_supplierForest_actual_051455
  · exact g32p_supplierForest_actual_051467
  · exact g32p_supplierForest_actual_051475
  · exact g32p_supplierForest_actual_051521
  · exact g32p_supplierForest_actual_051526
  · exact g32p_supplierForest_actual_051553
  · exact g32p_supplierForest_actual_051555
  · exact g32p_supplierForest_actual_051583
  · exact g32p_supplierForest_actual_051602
  · exact g32p_supplierForest_actual_051626
  · exact g32p_supplierForest_actual_051634
  · exact g32p_supplierForest_actual_051690
  · exact g32p_supplierForest_actual_051717
  · exact g32p_supplierForest_actual_051726
  · exact g32p_supplierForest_actual_051775
  · exact g32p_supplierForest_actual_051778
  · exact g32p_supplierForest_actual_051787
  · exact g32p_supplierForest_actual_051817
  · exact g32p_supplierForest_actual_051825
  · exact g32p_supplierForest_actual_051831
  · exact g32p_supplierForest_actual_051832
  · exact g32p_supplierForest_actual_051841
  · exact g32p_supplierForest_actual_051843
  · exact g32p_supplierForest_actual_051948
  · exact g32p_supplierForest_actual_051965
  · exact g32p_supplierForest_actual_051972
  · exact g32p_supplierForest_actual_051974
  · exact g32p_supplierForest_actual_051976
  · exact g32p_supplierForest_actual_051997
  · exact g32p_supplierForest_actual_052005
  · exact g32p_supplierForest_actual_052020
  · exact g32p_supplierForest_actual_052030
  · exact g32p_supplierForest_actual_052074
  · exact g32p_supplierForest_actual_052076
  · exact g32p_supplierForest_actual_052084
  · exact g32p_supplierForest_actual_052109
  · exact g32p_supplierForest_actual_052156
  · exact g32p_supplierForest_actual_052167
  · exact g32p_supplierForest_actual_052178
  · exact g32p_supplierForest_actual_052196
  · exact g32p_supplierForest_actual_052198
  · exact g32p_supplierForest_actual_052214
  · exact g32p_supplierForest_actual_052241
  · exact g32p_supplierForest_actual_052251
  · exact g32p_supplierForest_actual_052263
  · exact g32p_supplierForest_actual_052291
  · exact g32p_supplierForest_actual_052314
  · exact g32p_supplierForest_actual_052341
  · exact g32p_supplierForest_actual_052348
  · exact g32p_supplierForest_actual_052415
  · exact g32p_supplierForest_actual_052428
  · exact g32p_supplierForest_actual_052556
  · exact g32p_supplierForest_actual_052615
  · exact g32p_supplierForest_actual_052617
  · exact g32p_supplierForest_actual_052629
  · exact g32p_supplierForest_actual_052640
  · exact g32p_supplierForest_actual_052641
  · exact g32p_supplierForest_actual_052651
  · exact g32p_supplierForest_actual_052666
  · exact g32p_supplierForest_actual_052724
  · exact g32p_supplierForest_actual_052729
  · exact g32p_supplierForest_actual_052731
  · exact g32p_supplierForest_actual_052739
  · exact g32p_supplierForest_actual_052768
  · exact g32p_supplierForest_actual_052774
  · exact g32p_supplierForest_actual_052775
  · exact g32p_supplierForest_actual_052780
  · exact g32p_supplierForest_actual_052787
  · exact g32p_supplierForest_actual_052795
  · exact g32p_supplierForest_actual_052832
  · exact g32p_supplierForest_actual_052836
  · exact g32p_supplierForest_actual_052845
  · exact g32p_supplierForest_actual_052867
  · exact g32p_supplierForest_actual_052870
  · exact g32p_supplierForest_actual_052907
  · exact g32p_supplierForest_actual_052914
  · exact g32p_supplierForest_actual_052915
  · exact g32p_supplierForest_actual_052993
  · exact g32p_supplierForest_actual_053019
  · exact g32p_supplierForest_actual_053020
  · exact g32p_supplierForest_actual_053058
  · exact g32p_supplierForest_actual_053062
  · exact g32p_supplierForest_actual_053064
  · exact g32p_supplierForest_actual_053070
  · exact g32p_supplierForest_actual_053111
  · exact g32p_supplierForest_actual_053117
  · exact g32p_supplierForest_actual_053137
  · exact g32p_supplierForest_actual_053157
  · exact g32p_supplierForest_actual_053174
  · exact g32p_supplierForest_actual_053176
  · exact g32p_supplierForest_actual_053181
  · exact g32p_supplierForest_actual_053331
  · exact g32p_supplierForest_actual_053338
  · exact g32p_supplierForest_actual_053366
  · exact g32p_supplierForest_actual_053469
  · exact g32p_supplierForest_actual_053527
  · exact g32p_supplierForest_actual_053566
  · exact g32p_supplierForest_actual_053576
  · exact g32p_supplierForest_actual_053582
  · exact g32p_supplierForest_actual_053634
  · exact g32p_supplierForest_actual_053664
  · exact g32p_supplierForest_actual_053744
  · exact g32p_supplierForest_actual_053794
  · exact g32p_supplierForest_actual_053797
  · exact g32p_supplierForest_actual_053830
  · exact g32p_supplierForest_actual_053831
  · exact g32p_supplierForest_actual_053839
  · exact g32p_supplierForest_actual_053857
  · exact g32p_supplierForest_actual_053866
  · exact g32p_supplierForest_actual_053872
  · exact g32p_supplierForest_actual_053890
  · exact g32p_supplierForest_actual_053893
  · exact g32p_supplierForest_actual_053948
  · exact g32p_supplierForest_actual_053955
  · exact g32p_supplierForest_actual_053970
  · exact g32p_supplierForest_actual_053974
  · exact g32p_supplierForest_actual_053998
  · exact g32p_supplierForest_actual_054010
  · exact g32p_supplierForest_actual_054027
  · exact g32p_supplierForest_actual_054049
  · exact g32p_supplierForest_actual_054057
  · exact g32p_supplierForest_actual_054095
  · exact g32p_supplierForest_actual_054117
  · exact g32p_supplierForest_actual_054139
  · exact g32p_supplierForest_actual_054158
  · exact g32p_supplierForest_actual_054190
  · exact g32p_supplierForest_actual_054192
  · exact g32p_supplierForest_actual_054205
  · exact g32p_supplierForest_actual_054213
  · exact g32p_supplierForest_actual_054274
  · exact g32p_supplierForest_actual_054287
  · exact g32p_supplierForest_actual_054309
  · exact g32p_supplierForest_actual_054318
  · exact g32p_supplierForest_actual_054328
  · exact g32p_supplierForest_actual_054358
  · exact g32p_supplierForest_actual_054397
  · exact g32p_supplierForest_actual_054404
  · exact g32p_supplierForest_actual_054413
  · exact g32p_supplierForest_actual_054440
  · exact g32p_supplierForest_actual_054444
  · exact g32p_supplierForest_actual_054454
  · exact g32p_supplierForest_actual_054472
  · exact g32p_supplierForest_actual_054475
  · exact g32p_supplierForest_actual_054484
  · exact g32p_supplierForest_actual_054516
  · exact g32p_supplierForest_actual_054535
  · exact g32p_supplierForest_actual_054551
  · exact g32p_supplierForest_actual_054579
  · exact g32p_supplierForest_actual_054587
  · exact g32p_supplierForest_actual_054613
  · exact g32p_supplierForest_actual_054616
  · exact g32p_supplierForest_actual_054625
  · exact g32p_supplierForest_actual_054626
  · exact g32p_supplierForest_actual_054633
  · exact g32p_supplierForest_actual_054657
  · exact g32p_supplierForest_actual_054683
  · exact g32p_supplierForest_actual_054700
  · exact g32p_supplierForest_actual_054701
  · exact g32p_supplierForest_actual_054706
  · exact g32p_supplierForest_actual_054712
  · exact g32p_supplierForest_actual_054762
  · exact g32p_supplierForest_actual_054783
  · exact g32p_supplierForest_actual_054857
  · exact g32p_supplierForest_actual_054873
  · exact g32p_supplierForest_actual_054937
  · exact g32p_supplierForest_actual_054940
  · exact g32p_supplierForest_actual_054948
  · exact g32p_supplierForest_actual_054961
  · exact g32p_supplierForest_actual_054972
  · exact g32p_supplierForest_actual_054975
  · exact g32p_supplierForest_actual_054984
  · exact g32p_supplierForest_actual_054987
  · exact g32p_supplierForest_actual_054992
  · exact g32p_supplierForest_actual_054999
  · exact g32p_supplierForest_actual_055068
  · exact g32p_supplierForest_actual_055099
  · exact g32p_supplierForest_actual_055101
  · exact g32p_supplierForest_actual_055111
  · exact g32p_supplierForest_actual_055122
  · exact g32p_supplierForest_actual_055148
  · exact g32p_supplierForest_actual_055150
  · exact g32p_supplierForest_actual_055169
  · exact g32p_supplierForest_actual_055205
  · exact g32p_supplierForest_actual_055245
  · exact g32p_supplierForest_actual_055250
  · exact g32p_supplierForest_actual_055260
  · exact g32p_supplierForest_actual_055293
  · exact g32p_supplierForest_actual_055297
  · exact g32p_supplierForest_actual_055301
  · exact g32p_supplierForest_actual_055377
  · exact g32p_supplierForest_actual_055389
  · exact g32p_supplierForest_actual_055391

def g32p_supplierForest_nodes_094 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_055404 else g32p_supplierForest_node_055428) else (if i.val < 3 then g32p_supplierForest_node_055432 else g32p_supplierForest_node_055436)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_055439 else g32p_supplierForest_node_055456) else (if i.val < 7 then g32p_supplierForest_node_055462 else g32p_supplierForest_node_055480))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_055514 else g32p_supplierForest_node_055641) else (if i.val < 11 then g32p_supplierForest_node_055645 else g32p_supplierForest_node_055647)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_055701 else g32p_supplierForest_node_055709) else (if i.val < 15 then g32p_supplierForest_node_055722 else g32p_supplierForest_node_055757)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_055759 else g32p_supplierForest_node_055766) else (if i.val < 19 then g32p_supplierForest_node_055793 else g32p_supplierForest_node_055875)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_055877 else g32p_supplierForest_node_055903) else (if i.val < 23 then g32p_supplierForest_node_055904 else g32p_supplierForest_node_055909))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_055911 else g32p_supplierForest_node_055981) else (if i.val < 27 then g32p_supplierForest_node_056000 else g32p_supplierForest_node_056051)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_056073 else g32p_supplierForest_node_056080) else (if i.val < 31 then g32p_supplierForest_node_056091 else g32p_supplierForest_node_056116))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_056129 else g32p_supplierForest_node_056148) else (if i.val < 35 then g32p_supplierForest_node_056196 else g32p_supplierForest_node_056204)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_056209 else g32p_supplierForest_node_056224) else (if i.val < 39 then g32p_supplierForest_node_056249 else g32p_supplierForest_node_056297))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_056332 else g32p_supplierForest_node_056362) else (if i.val < 43 then g32p_supplierForest_node_056393 else g32p_supplierForest_node_056400)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_056419 else g32p_supplierForest_node_056424) else (if i.val < 47 then g32p_supplierForest_node_056427 else g32p_supplierForest_node_056430)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_056525 else g32p_supplierForest_node_056546) else (if i.val < 51 then g32p_supplierForest_node_056551 else g32p_supplierForest_node_056552)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_056565 else g32p_supplierForest_node_056580) else (if i.val < 55 then g32p_supplierForest_node_056589 else g32p_supplierForest_node_056629))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_056630 else g32p_supplierForest_node_056650) else (if i.val < 59 then g32p_supplierForest_node_056654 else g32p_supplierForest_node_056661)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_056688 else g32p_supplierForest_node_056719) else (if i.val < 63 then g32p_supplierForest_node_056728 else g32p_supplierForest_node_056765)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_056768 else g32p_supplierForest_node_056771) else (if i.val < 67 then g32p_supplierForest_node_056794 else g32p_supplierForest_node_056797)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_056843 else g32p_supplierForest_node_056887) else (if i.val < 71 then g32p_supplierForest_node_056903 else g32p_supplierForest_node_056909))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_056931 else g32p_supplierForest_node_056969) else (if i.val < 75 then g32p_supplierForest_node_057004 else g32p_supplierForest_node_057018)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_057062 else g32p_supplierForest_node_057087) else (if i.val < 79 then g32p_supplierForest_node_057088 else g32p_supplierForest_node_057107)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_057125 else g32p_supplierForest_node_057135) else (if i.val < 83 then g32p_supplierForest_node_057157 else g32p_supplierForest_node_057171)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_057222 else g32p_supplierForest_node_057257) else (if i.val < 87 then g32p_supplierForest_node_057271 else g32p_supplierForest_node_057277))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_057305 else g32p_supplierForest_node_057314) else (if i.val < 91 then g32p_supplierForest_node_057347 else g32p_supplierForest_node_057382)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_057386 else g32p_supplierForest_node_057410) else (if i.val < 95 then g32p_supplierForest_node_057466 else g32p_supplierForest_node_057558))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_057577 else g32p_supplierForest_node_057582) else (if i.val < 99 then g32p_supplierForest_node_057592 else g32p_supplierForest_node_057606)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_057611 else g32p_supplierForest_node_057680) else (if i.val < 103 then g32p_supplierForest_node_057682 else g32p_supplierForest_node_057719))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_057794 else g32p_supplierForest_node_057954) else (if i.val < 107 then g32p_supplierForest_node_057957 else g32p_supplierForest_node_057974)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_057979 else g32p_supplierForest_node_057984) else (if i.val < 111 then g32p_supplierForest_node_058018 else g32p_supplierForest_node_058025)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_058064 else g32p_supplierForest_node_058068) else (if i.val < 115 then g32p_supplierForest_node_058069 else g32p_supplierForest_node_058074)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_058085 else g32p_supplierForest_node_058115) else (if i.val < 119 then g32p_supplierForest_node_058186 else g32p_supplierForest_node_058189))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_058218 else g32p_supplierForest_node_058236) else (if i.val < 123 then g32p_supplierForest_node_058272 else g32p_supplierForest_node_058306)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_058307 else g32p_supplierForest_node_058308) else (if i.val < 127 then g32p_supplierForest_node_058376 else g32p_supplierForest_node_058391))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_058397 else g32p_supplierForest_node_058399) else (if i.val < 131 then g32p_supplierForest_node_058458 else g32p_supplierForest_node_058469)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_058491 else g32p_supplierForest_node_058537) else (if i.val < 135 then g32p_supplierForest_node_058548 else g32p_supplierForest_node_058567))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_058665 else g32p_supplierForest_node_058677) else (if i.val < 139 then g32p_supplierForest_node_058687 else g32p_supplierForest_node_058711)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_058718 else g32p_supplierForest_node_058738) else (if i.val < 143 then g32p_supplierForest_node_058849 else g32p_supplierForest_node_058851)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_058866 else g32p_supplierForest_node_058868) else (if i.val < 147 then g32p_supplierForest_node_058878 else g32p_supplierForest_node_058897)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_058916 else g32p_supplierForest_node_058928) else (if i.val < 151 then g32p_supplierForest_node_058939 else g32p_supplierForest_node_058951))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_058969 else g32p_supplierForest_node_058977) else (if i.val < 155 then g32p_supplierForest_node_058985 else g32p_supplierForest_node_059019)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_059028 else g32p_supplierForest_node_059073) else (if i.val < 159 then g32p_supplierForest_node_059150 else g32p_supplierForest_node_059170))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_059206 else g32p_supplierForest_node_059288) else (if i.val < 163 then g32p_supplierForest_node_059294 else g32p_supplierForest_node_059304)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_059313 else g32p_supplierForest_node_059318) else (if i.val < 167 then g32p_supplierForest_node_059340 else g32p_supplierForest_node_059350))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_059371 else g32p_supplierForest_node_059395) else (if i.val < 171 then g32p_supplierForest_node_059408 else g32p_supplierForest_node_059461)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_059472 else g32p_supplierForest_node_059484) else (if i.val < 175 then g32p_supplierForest_node_059495 else g32p_supplierForest_node_059515)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_059536 else g32p_supplierForest_node_059569) else (if i.val < 179 then g32p_supplierForest_node_059590 else g32p_supplierForest_node_059598)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_059613 else g32p_supplierForest_node_059615) else (if i.val < 183 then g32p_supplierForest_node_059646 else g32p_supplierForest_node_059658))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_059661 else g32p_supplierForest_node_059685) else (if i.val < 187 then g32p_supplierForest_node_059700 else g32p_supplierForest_node_059731)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_059755 else g32p_supplierForest_node_059790) else (if i.val < 191 then g32p_supplierForest_node_059816 else g32p_supplierForest_node_059855)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_059876 else g32p_supplierForest_node_059882) else (if i.val < 195 then g32p_supplierForest_node_059888 else g32p_supplierForest_node_059917)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_059927 else g32p_supplierForest_node_059979) else (if i.val < 199 then g32p_supplierForest_node_059982 else g32p_supplierForest_node_059986))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_060029 else g32p_supplierForest_node_060043) else (if i.val < 203 then g32p_supplierForest_node_060058 else g32p_supplierForest_node_060135)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_060142 else g32p_supplierForest_node_060143) else (if i.val < 207 then g32p_supplierForest_node_060179 else g32p_supplierForest_node_060183)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_060186 else g32p_supplierForest_node_060237) else (if i.val < 211 then g32p_supplierForest_node_060255 else g32p_supplierForest_node_060293)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_060302 else g32p_supplierForest_node_060306) else (if i.val < 215 then g32p_supplierForest_node_060334 else g32p_supplierForest_node_060353))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_060374 else g32p_supplierForest_node_060403) else (if i.val < 219 then g32p_supplierForest_node_060404 else g32p_supplierForest_node_060434)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_060437 else g32p_supplierForest_node_060448) else (if i.val < 223 then g32p_supplierForest_node_060516 else g32p_supplierForest_node_060537))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_060538 else g32p_supplierForest_node_060556) else (if i.val < 227 then g32p_supplierForest_node_060570 else g32p_supplierForest_node_060577)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_060601 else g32p_supplierForest_node_060605) else (if i.val < 231 then g32p_supplierForest_node_060615 else g32p_supplierForest_node_060638))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_060670 else g32p_supplierForest_node_060706) else (if i.val < 235 then g32p_supplierForest_node_060750 else g32p_supplierForest_node_060753)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_060757 else g32p_supplierForest_node_060766) else (if i.val < 239 then g32p_supplierForest_node_060772 else g32p_supplierForest_node_060794)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_060803 else g32p_supplierForest_node_060814) else (if i.val < 243 then g32p_supplierForest_node_060832 else g32p_supplierForest_node_060833)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_060836 else g32p_supplierForest_node_060839) else (if i.val < 247 then g32p_supplierForest_node_060856 else g32p_supplierForest_node_060866))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_060883 else g32p_supplierForest_node_060893) else (if i.val < 251 then g32p_supplierForest_node_060912 else g32p_supplierForest_node_060967)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_060992 else g32p_supplierForest_node_061020) else (if i.val < 255 then g32p_supplierForest_node_061033 else g32p_supplierForest_node_061066))))))))

def g32p_supplierForest_classes_094 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 21 else 68) else (if i.val < 3 then 68 else 68)) else (if i.val < 6 then (if i.val < 5 then 21 else 43) else (if i.val < 7 then 40 else 75))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 22 else 74) else (if i.val < 11 then 21 else 21)) else (if i.val < 14 then (if i.val < 13 then 21 else 68) else (if i.val < 15 then 75 else 41)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 7 else 41) else (if i.val < 19 then 38 else 73)) else (if i.val < 22 then (if i.val < 21 then 40 else 40) else (if i.val < 23 then 75 else 38))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 39 else 74) else (if i.val < 27 then 40 else 39)) else (if i.val < 30 then (if i.val < 29 then 38 else 21) else (if i.val < 31 then 75 else 69))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 73 else 73) else (if i.val < 35 then 68 else 38)) else (if i.val < 38 then (if i.val < 37 then 22 else 38) else (if i.val < 39 then 38 else 38))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 22 else 73) else (if i.val < 43 then 38 else 38)) else (if i.val < 46 then (if i.val < 45 then 20 else 38) else (if i.val < 47 then 38 else 38)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 19 else 21) else (if i.val < 51 then 6 else 40)) else (if i.val < 54 then (if i.val < 53 then 41 else 21) else (if i.val < 55 then 38 else 41))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 43) else (if i.val < 59 then 43 else 70)) else (if i.val < 62 then (if i.val < 61 then 68 else 74) else (if i.val < 63 then 75 else 21)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 75 else 7) else (if i.val < 67 then 75 else 38)) else (if i.val < 70 then (if i.val < 69 then 74 else 21) else (if i.val < 71 then 20 else 38))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 41 else 38) else (if i.val < 75 then 74 else 74)) else (if i.val < 78 then (if i.val < 77 then 74 else 21) else (if i.val < 79 then 72 else 41)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 70 else 70) else (if i.val < 83 then 22 else 22)) else (if i.val < 86 then (if i.val < 85 then 68 else 6) else (if i.val < 87 then 7 else 6))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 71 else 22) else (if i.val < 91 then 41 else 41)) else (if i.val < 94 then (if i.val < 93 then 21 else 73) else (if i.val < 95 then 73 else 75))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 75 else 21) else (if i.val < 99 then 21 else 75)) else (if i.val < 102 then (if i.val < 101 then 6 else 6) else (if i.val < 103 then 43 else 43))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 22 else 40) else (if i.val < 107 then 42 else 74)) else (if i.val < 110 then (if i.val < 109 then 40 else 21) else (if i.val < 111 then 21 else 21)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 38 else 6) else (if i.val < 115 then 21 else 43)) else (if i.val < 118 then (if i.val < 117 then 21 else 38) else (if i.val < 119 then 22 else 43))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 38 else 21) else (if i.val < 123 then 40 else 21)) else (if i.val < 126 then (if i.val < 125 then 71 else 21) else (if i.val < 127 then 38 else 21))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 38 else 21) else (if i.val < 131 then 21 else 41)) else (if i.val < 134 then (if i.val < 133 then 20 else 70) else (if i.val < 135 then 21 else 38))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 38 else 73) else (if i.val < 139 then 43 else 41)) else (if i.val < 142 then (if i.val < 141 then 38 else 22) else (if i.val < 143 then 43 else 38)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 41 else 20) else (if i.val < 147 then 41 else 22)) else (if i.val < 150 then (if i.val < 149 then 22 else 21) else (if i.val < 151 then 71 else 22))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 21 else 38) else (if i.val < 155 then 70 else 38)) else (if i.val < 158 then (if i.val < 157 then 21 else 21) else (if i.val < 159 then 38 else 22))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 6 else 6) else (if i.val < 163 then 22 else 41)) else (if i.val < 166 then (if i.val < 165 then 21 else 21) else (if i.val < 167 then 39 else 6))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 38 else 22) else (if i.val < 171 then 38 else 5)) else (if i.val < 174 then (if i.val < 173 then 68 else 38) else (if i.val < 175 then 74 else 21)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 21 else 39) else (if i.val < 179 then 43 else 38)) else (if i.val < 182 then (if i.val < 181 then 21 else 38) else (if i.val < 183 then 20 else 41))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 43 else 75) else (if i.val < 187 then 70 else 21)) else (if i.val < 190 then (if i.val < 189 then 38 else 39) else (if i.val < 191 then 21 else 6)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 39 else 21) else (if i.val < 195 then 74 else 38)) else (if i.val < 198 then (if i.val < 197 then 21 else 39) else (if i.val < 199 then 43 else 21))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 41 else 70) else (if i.val < 203 then 7 else 43)) else (if i.val < 206 then (if i.val < 205 then 38 else 40) else (if i.val < 207 then 70 else 43)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 42 else 21) else (if i.val < 211 then 71 else 72)) else (if i.val < 214 then (if i.val < 213 then 20 else 70) else (if i.val < 215 then 22 else 42))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 21 else 41) else (if i.val < 219 then 38 else 40)) else (if i.val < 222 then (if i.val < 221 then 38 else 21) else (if i.val < 223 then 21 else 38))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 38 else 43) else (if i.val < 227 then 21 else 43)) else (if i.val < 230 then (if i.val < 229 then 38 else 21) else (if i.val < 231 then 21 else 7))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 70 else 38) else (if i.val < 235 then 38 else 22)) else (if i.val < 238 then (if i.val < 237 then 70 else 42) else (if i.val < 239 then 38 else 43)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 74 else 22) else (if i.val < 243 then 38 else 22)) else (if i.val < 246 then (if i.val < 245 then 72 else 21) else (if i.val < 247 then 40 else 21))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 38 else 73) else (if i.val < 251 then 72 else 40)) else (if i.val < 254 then (if i.val < 253 then 21 else 74) else (if i.val < 255 then 73 else 74))))))))

theorem g32p_supplierForest_actual_094 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_094 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_094 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_055404
  · exact g32p_supplierForest_actual_055428
  · exact g32p_supplierForest_actual_055432
  · exact g32p_supplierForest_actual_055436
  · exact g32p_supplierForest_actual_055439
  · exact g32p_supplierForest_actual_055456
  · exact g32p_supplierForest_actual_055462
  · exact g32p_supplierForest_actual_055480
  · exact g32p_supplierForest_actual_055514
  · exact g32p_supplierForest_actual_055641
  · exact g32p_supplierForest_actual_055645
  · exact g32p_supplierForest_actual_055647
  · exact g32p_supplierForest_actual_055701
  · exact g32p_supplierForest_actual_055709
  · exact g32p_supplierForest_actual_055722
  · exact g32p_supplierForest_actual_055757
  · exact g32p_supplierForest_actual_055759
  · exact g32p_supplierForest_actual_055766
  · exact g32p_supplierForest_actual_055793
  · exact g32p_supplierForest_actual_055875
  · exact g32p_supplierForest_actual_055877
  · exact g32p_supplierForest_actual_055903
  · exact g32p_supplierForest_actual_055904
  · exact g32p_supplierForest_actual_055909
  · exact g32p_supplierForest_actual_055911
  · exact g32p_supplierForest_actual_055981
  · exact g32p_supplierForest_actual_056000
  · exact g32p_supplierForest_actual_056051
  · exact g32p_supplierForest_actual_056073
  · exact g32p_supplierForest_actual_056080
  · exact g32p_supplierForest_actual_056091
  · exact g32p_supplierForest_actual_056116
  · exact g32p_supplierForest_actual_056129
  · exact g32p_supplierForest_actual_056148
  · exact g32p_supplierForest_actual_056196
  · exact g32p_supplierForest_actual_056204
  · exact g32p_supplierForest_actual_056209
  · exact g32p_supplierForest_actual_056224
  · exact g32p_supplierForest_actual_056249
  · exact g32p_supplierForest_actual_056297
  · exact g32p_supplierForest_actual_056332
  · exact g32p_supplierForest_actual_056362
  · exact g32p_supplierForest_actual_056393
  · exact g32p_supplierForest_actual_056400
  · exact g32p_supplierForest_actual_056419
  · exact g32p_supplierForest_actual_056424
  · exact g32p_supplierForest_actual_056427
  · exact g32p_supplierForest_actual_056430
  · exact g32p_supplierForest_actual_056525
  · exact g32p_supplierForest_actual_056546
  · exact g32p_supplierForest_actual_056551
  · exact g32p_supplierForest_actual_056552
  · exact g32p_supplierForest_actual_056565
  · exact g32p_supplierForest_actual_056580
  · exact g32p_supplierForest_actual_056589
  · exact g32p_supplierForest_actual_056629
  · exact g32p_supplierForest_actual_056630
  · exact g32p_supplierForest_actual_056650
  · exact g32p_supplierForest_actual_056654
  · exact g32p_supplierForest_actual_056661
  · exact g32p_supplierForest_actual_056688
  · exact g32p_supplierForest_actual_056719
  · exact g32p_supplierForest_actual_056728
  · exact g32p_supplierForest_actual_056765
  · exact g32p_supplierForest_actual_056768
  · exact g32p_supplierForest_actual_056771
  · exact g32p_supplierForest_actual_056794
  · exact g32p_supplierForest_actual_056797
  · exact g32p_supplierForest_actual_056843
  · exact g32p_supplierForest_actual_056887
  · exact g32p_supplierForest_actual_056903
  · exact g32p_supplierForest_actual_056909
  · exact g32p_supplierForest_actual_056931
  · exact g32p_supplierForest_actual_056969
  · exact g32p_supplierForest_actual_057004
  · exact g32p_supplierForest_actual_057018
  · exact g32p_supplierForest_actual_057062
  · exact g32p_supplierForest_actual_057087
  · exact g32p_supplierForest_actual_057088
  · exact g32p_supplierForest_actual_057107
  · exact g32p_supplierForest_actual_057125
  · exact g32p_supplierForest_actual_057135
  · exact g32p_supplierForest_actual_057157
  · exact g32p_supplierForest_actual_057171
  · exact g32p_supplierForest_actual_057222
  · exact g32p_supplierForest_actual_057257
  · exact g32p_supplierForest_actual_057271
  · exact g32p_supplierForest_actual_057277
  · exact g32p_supplierForest_actual_057305
  · exact g32p_supplierForest_actual_057314
  · exact g32p_supplierForest_actual_057347
  · exact g32p_supplierForest_actual_057382
  · exact g32p_supplierForest_actual_057386
  · exact g32p_supplierForest_actual_057410
  · exact g32p_supplierForest_actual_057466
  · exact g32p_supplierForest_actual_057558
  · exact g32p_supplierForest_actual_057577
  · exact g32p_supplierForest_actual_057582
  · exact g32p_supplierForest_actual_057592
  · exact g32p_supplierForest_actual_057606
  · exact g32p_supplierForest_actual_057611
  · exact g32p_supplierForest_actual_057680
  · exact g32p_supplierForest_actual_057682
  · exact g32p_supplierForest_actual_057719
  · exact g32p_supplierForest_actual_057794
  · exact g32p_supplierForest_actual_057954
  · exact g32p_supplierForest_actual_057957
  · exact g32p_supplierForest_actual_057974
  · exact g32p_supplierForest_actual_057979
  · exact g32p_supplierForest_actual_057984
  · exact g32p_supplierForest_actual_058018
  · exact g32p_supplierForest_actual_058025
  · exact g32p_supplierForest_actual_058064
  · exact g32p_supplierForest_actual_058068
  · exact g32p_supplierForest_actual_058069
  · exact g32p_supplierForest_actual_058074
  · exact g32p_supplierForest_actual_058085
  · exact g32p_supplierForest_actual_058115
  · exact g32p_supplierForest_actual_058186
  · exact g32p_supplierForest_actual_058189
  · exact g32p_supplierForest_actual_058218
  · exact g32p_supplierForest_actual_058236
  · exact g32p_supplierForest_actual_058272
  · exact g32p_supplierForest_actual_058306
  · exact g32p_supplierForest_actual_058307
  · exact g32p_supplierForest_actual_058308
  · exact g32p_supplierForest_actual_058376
  · exact g32p_supplierForest_actual_058391
  · exact g32p_supplierForest_actual_058397
  · exact g32p_supplierForest_actual_058399
  · exact g32p_supplierForest_actual_058458
  · exact g32p_supplierForest_actual_058469
  · exact g32p_supplierForest_actual_058491
  · exact g32p_supplierForest_actual_058537
  · exact g32p_supplierForest_actual_058548
  · exact g32p_supplierForest_actual_058567
  · exact g32p_supplierForest_actual_058665
  · exact g32p_supplierForest_actual_058677
  · exact g32p_supplierForest_actual_058687
  · exact g32p_supplierForest_actual_058711
  · exact g32p_supplierForest_actual_058718
  · exact g32p_supplierForest_actual_058738
  · exact g32p_supplierForest_actual_058849
  · exact g32p_supplierForest_actual_058851
  · exact g32p_supplierForest_actual_058866
  · exact g32p_supplierForest_actual_058868
  · exact g32p_supplierForest_actual_058878
  · exact g32p_supplierForest_actual_058897
  · exact g32p_supplierForest_actual_058916
  · exact g32p_supplierForest_actual_058928
  · exact g32p_supplierForest_actual_058939
  · exact g32p_supplierForest_actual_058951
  · exact g32p_supplierForest_actual_058969
  · exact g32p_supplierForest_actual_058977
  · exact g32p_supplierForest_actual_058985
  · exact g32p_supplierForest_actual_059019
  · exact g32p_supplierForest_actual_059028
  · exact g32p_supplierForest_actual_059073
  · exact g32p_supplierForest_actual_059150
  · exact g32p_supplierForest_actual_059170
  · exact g32p_supplierForest_actual_059206
  · exact g32p_supplierForest_actual_059288
  · exact g32p_supplierForest_actual_059294
  · exact g32p_supplierForest_actual_059304
  · exact g32p_supplierForest_actual_059313
  · exact g32p_supplierForest_actual_059318
  · exact g32p_supplierForest_actual_059340
  · exact g32p_supplierForest_actual_059350
  · exact g32p_supplierForest_actual_059371
  · exact g32p_supplierForest_actual_059395
  · exact g32p_supplierForest_actual_059408
  · exact g32p_supplierForest_actual_059461
  · exact g32p_supplierForest_actual_059472
  · exact g32p_supplierForest_actual_059484
  · exact g32p_supplierForest_actual_059495
  · exact g32p_supplierForest_actual_059515
  · exact g32p_supplierForest_actual_059536
  · exact g32p_supplierForest_actual_059569
  · exact g32p_supplierForest_actual_059590
  · exact g32p_supplierForest_actual_059598
  · exact g32p_supplierForest_actual_059613
  · exact g32p_supplierForest_actual_059615
  · exact g32p_supplierForest_actual_059646
  · exact g32p_supplierForest_actual_059658
  · exact g32p_supplierForest_actual_059661
  · exact g32p_supplierForest_actual_059685
  · exact g32p_supplierForest_actual_059700
  · exact g32p_supplierForest_actual_059731
  · exact g32p_supplierForest_actual_059755
  · exact g32p_supplierForest_actual_059790
  · exact g32p_supplierForest_actual_059816
  · exact g32p_supplierForest_actual_059855
  · exact g32p_supplierForest_actual_059876
  · exact g32p_supplierForest_actual_059882
  · exact g32p_supplierForest_actual_059888
  · exact g32p_supplierForest_actual_059917
  · exact g32p_supplierForest_actual_059927
  · exact g32p_supplierForest_actual_059979
  · exact g32p_supplierForest_actual_059982
  · exact g32p_supplierForest_actual_059986
  · exact g32p_supplierForest_actual_060029
  · exact g32p_supplierForest_actual_060043
  · exact g32p_supplierForest_actual_060058
  · exact g32p_supplierForest_actual_060135
  · exact g32p_supplierForest_actual_060142
  · exact g32p_supplierForest_actual_060143
  · exact g32p_supplierForest_actual_060179
  · exact g32p_supplierForest_actual_060183
  · exact g32p_supplierForest_actual_060186
  · exact g32p_supplierForest_actual_060237
  · exact g32p_supplierForest_actual_060255
  · exact g32p_supplierForest_actual_060293
  · exact g32p_supplierForest_actual_060302
  · exact g32p_supplierForest_actual_060306
  · exact g32p_supplierForest_actual_060334
  · exact g32p_supplierForest_actual_060353
  · exact g32p_supplierForest_actual_060374
  · exact g32p_supplierForest_actual_060403
  · exact g32p_supplierForest_actual_060404
  · exact g32p_supplierForest_actual_060434
  · exact g32p_supplierForest_actual_060437
  · exact g32p_supplierForest_actual_060448
  · exact g32p_supplierForest_actual_060516
  · exact g32p_supplierForest_actual_060537
  · exact g32p_supplierForest_actual_060538
  · exact g32p_supplierForest_actual_060556
  · exact g32p_supplierForest_actual_060570
  · exact g32p_supplierForest_actual_060577
  · exact g32p_supplierForest_actual_060601
  · exact g32p_supplierForest_actual_060605
  · exact g32p_supplierForest_actual_060615
  · exact g32p_supplierForest_actual_060638
  · exact g32p_supplierForest_actual_060670
  · exact g32p_supplierForest_actual_060706
  · exact g32p_supplierForest_actual_060750
  · exact g32p_supplierForest_actual_060753
  · exact g32p_supplierForest_actual_060757
  · exact g32p_supplierForest_actual_060766
  · exact g32p_supplierForest_actual_060772
  · exact g32p_supplierForest_actual_060794
  · exact g32p_supplierForest_actual_060803
  · exact g32p_supplierForest_actual_060814
  · exact g32p_supplierForest_actual_060832
  · exact g32p_supplierForest_actual_060833
  · exact g32p_supplierForest_actual_060836
  · exact g32p_supplierForest_actual_060839
  · exact g32p_supplierForest_actual_060856
  · exact g32p_supplierForest_actual_060866
  · exact g32p_supplierForest_actual_060883
  · exact g32p_supplierForest_actual_060893
  · exact g32p_supplierForest_actual_060912
  · exact g32p_supplierForest_actual_060967
  · exact g32p_supplierForest_actual_060992
  · exact g32p_supplierForest_actual_061020
  · exact g32p_supplierForest_actual_061033
  · exact g32p_supplierForest_actual_061066

def g32p_supplierForest_nodes_095 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_061069 else g32p_supplierForest_node_061076) else (if i.val < 3 then g32p_supplierForest_node_061084 else g32p_supplierForest_node_061113)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_061115 else g32p_supplierForest_node_061118) else (if i.val < 7 then g32p_supplierForest_node_061153 else g32p_supplierForest_node_061192))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_061212 else g32p_supplierForest_node_061217) else (if i.val < 11 then g32p_supplierForest_node_061234 else g32p_supplierForest_node_061242)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_061253 else g32p_supplierForest_node_061254) else (if i.val < 15 then g32p_supplierForest_node_061267 else g32p_supplierForest_node_061269)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_061270 else g32p_supplierForest_node_061385) else (if i.val < 19 then g32p_supplierForest_node_061392 else g32p_supplierForest_node_061410)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_061458 else g32p_supplierForest_node_061522) else (if i.val < 23 then g32p_supplierForest_node_061565 else g32p_supplierForest_node_061569))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_061621 else g32p_supplierForest_node_061715) else (if i.val < 27 then g32p_supplierForest_node_061752 else g32p_supplierForest_node_061761)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_061765 else g32p_supplierForest_node_061766) else (if i.val < 31 then g32p_supplierForest_node_061775 else g32p_supplierForest_node_061794))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_061858 else g32p_supplierForest_node_061889) else (if i.val < 35 then g32p_supplierForest_node_061898 else g32p_supplierForest_node_061943)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_061955 else g32p_supplierForest_node_061988) else (if i.val < 39 then g32p_supplierForest_node_062044 else g32p_supplierForest_node_062045))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_062111 else g32p_supplierForest_node_062122) else (if i.val < 43 then g32p_supplierForest_node_062123 else g32p_supplierForest_node_062132)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_062135 else g32p_supplierForest_node_062142) else (if i.val < 47 then g32p_supplierForest_node_062176 else g32p_supplierForest_node_062189)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_062202 else g32p_supplierForest_node_062273) else (if i.val < 51 then g32p_supplierForest_node_062291 else g32p_supplierForest_node_062293)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_062299 else g32p_supplierForest_node_062352) else (if i.val < 55 then g32p_supplierForest_node_062360 else g32p_supplierForest_node_062362))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_062365 else g32p_supplierForest_node_062380) else (if i.val < 59 then g32p_supplierForest_node_062384 else g32p_supplierForest_node_062391)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_062408 else g32p_supplierForest_node_062441) else (if i.val < 63 then g32p_supplierForest_node_062492 else g32p_supplierForest_node_062508)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_062527 else g32p_supplierForest_node_062532) else (if i.val < 67 then g32p_supplierForest_node_062553 else g32p_supplierForest_node_062615)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_062622 else g32p_supplierForest_node_062633) else (if i.val < 71 then g32p_supplierForest_node_062638 else g32p_supplierForest_node_062671))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_062679 else g32p_supplierForest_node_062700) else (if i.val < 75 then g32p_supplierForest_node_062716 else g32p_supplierForest_node_062749)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_062808 else g32p_supplierForest_node_062818) else (if i.val < 79 then g32p_supplierForest_node_062821 else g32p_supplierForest_node_062824)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_062837 else g32p_supplierForest_node_062847) else (if i.val < 83 then g32p_supplierForest_node_062858 else g32p_supplierForest_node_062885)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_062946 else g32p_supplierForest_node_062962) else (if i.val < 87 then g32p_supplierForest_node_062979 else g32p_supplierForest_node_062993))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_062999 else g32p_supplierForest_node_063054) else (if i.val < 91 then g32p_supplierForest_node_063055 else g32p_supplierForest_node_063060)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_063062 else g32p_supplierForest_node_063082) else (if i.val < 95 then g32p_supplierForest_node_063105 else g32p_supplierForest_node_063129))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_063188 else g32p_supplierForest_node_063200) else (if i.val < 99 then g32p_supplierForest_node_063203 else g32p_supplierForest_node_063218)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_063254 else g32p_supplierForest_node_063265) else (if i.val < 103 then g32p_supplierForest_node_063275 else g32p_supplierForest_node_063290))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_063341 else g32p_supplierForest_node_063343) else (if i.val < 107 then g32p_supplierForest_node_063435 else g32p_supplierForest_node_063458)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_063462 else g32p_supplierForest_node_063466) else (if i.val < 111 then g32p_supplierForest_node_063532 else g32p_supplierForest_node_063556)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_063562 else g32p_supplierForest_node_063607) else (if i.val < 115 then g32p_supplierForest_node_063628 else g32p_supplierForest_node_063642)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_063673 else g32p_supplierForest_node_063682) else (if i.val < 119 then g32p_supplierForest_node_063683 else g32p_supplierForest_node_063692))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_063697 else g32p_supplierForest_node_063725) else (if i.val < 123 then g32p_supplierForest_node_063738 else g32p_supplierForest_node_063769)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_063784 else g32p_supplierForest_node_063786) else (if i.val < 127 then g32p_supplierForest_node_063798 else g32p_supplierForest_node_063800))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_063818 else g32p_supplierForest_node_063829) else (if i.val < 131 then g32p_supplierForest_node_063848 else g32p_supplierForest_node_063865)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_063885 else g32p_supplierForest_node_063898) else (if i.val < 135 then g32p_supplierForest_node_063910 else g32p_supplierForest_node_063936))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_063946 else g32p_supplierForest_node_063981) else (if i.val < 139 then g32p_supplierForest_node_063983 else g32p_supplierForest_node_064016)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_064032 else g32p_supplierForest_node_064037) else (if i.val < 143 then g32p_supplierForest_node_064059 else g32p_supplierForest_node_064091)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_064127 else g32p_supplierForest_node_064141) else (if i.val < 147 then g32p_supplierForest_node_064160 else g32p_supplierForest_node_064167)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_064184 else g32p_supplierForest_node_064188) else (if i.val < 151 then g32p_supplierForest_node_064195 else g32p_supplierForest_node_064238))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_064254 else g32p_supplierForest_node_064262) else (if i.val < 155 then g32p_supplierForest_node_064322 else g32p_supplierForest_node_064375)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_064394 else g32p_supplierForest_node_064430) else (if i.val < 159 then g32p_supplierForest_node_064435 else g32p_supplierForest_node_064457))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_064497 else g32p_supplierForest_node_064514) else (if i.val < 163 then g32p_supplierForest_node_064581 else g32p_supplierForest_node_064584)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_064596 else g32p_supplierForest_node_064623) else (if i.val < 167 then g32p_supplierForest_node_064653 else g32p_supplierForest_node_064669))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_064684 else g32p_supplierForest_node_064691) else (if i.val < 171 then g32p_supplierForest_node_064736 else g32p_supplierForest_node_064759)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_064772 else g32p_supplierForest_node_064781) else (if i.val < 175 then g32p_supplierForest_node_064784 else g32p_supplierForest_node_064788)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_064827 else g32p_supplierForest_node_064835) else (if i.val < 179 then g32p_supplierForest_node_064846 else g32p_supplierForest_node_064882)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_064906 else g32p_supplierForest_node_064947) else (if i.val < 183 then g32p_supplierForest_node_064962 else g32p_supplierForest_node_065017))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_065105 else g32p_supplierForest_node_065145) else (if i.val < 187 then g32p_supplierForest_node_065166 else g32p_supplierForest_node_065175)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_065176 else g32p_supplierForest_node_065192) else (if i.val < 191 then g32p_supplierForest_node_065243 else g32p_supplierForest_node_065265)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_065283 else g32p_supplierForest_node_065329) else (if i.val < 195 then g32p_supplierForest_node_065337 else g32p_supplierForest_node_065342)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_065348 else g32p_supplierForest_node_065384) else (if i.val < 199 then g32p_supplierForest_node_065404 else g32p_supplierForest_node_065451))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_065459 else g32p_supplierForest_node_065465) else (if i.val < 203 then g32p_supplierForest_node_065487 else g32p_supplierForest_node_065531)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_065539 else g32p_supplierForest_node_065561) else (if i.val < 207 then g32p_supplierForest_node_065573 else g32p_supplierForest_node_065607)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_065611 else g32p_supplierForest_node_065647) else (if i.val < 211 then g32p_supplierForest_node_065666 else g32p_supplierForest_node_065683)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_065693 else g32p_supplierForest_node_065694) else (if i.val < 215 then g32p_supplierForest_node_065714 else g32p_supplierForest_node_065732))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_065743 else g32p_supplierForest_node_065758) else (if i.val < 219 then g32p_supplierForest_node_065759 else g32p_supplierForest_node_065769)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_065782 else g32p_supplierForest_node_065793) else (if i.val < 223 then g32p_supplierForest_node_065794 else g32p_supplierForest_node_065801))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_065830 else g32p_supplierForest_node_065843) else (if i.val < 227 then g32p_supplierForest_node_065849 else g32p_supplierForest_node_065862)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_065875 else g32p_supplierForest_node_065878) else (if i.val < 231 then g32p_supplierForest_node_065931 else g32p_supplierForest_node_065946))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_065969 else g32p_supplierForest_node_065979) else (if i.val < 235 then g32p_supplierForest_node_065993 else g32p_supplierForest_node_066012)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_066018 else g32p_supplierForest_node_066059) else (if i.val < 239 then g32p_supplierForest_node_066070 else g32p_supplierForest_node_066136)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_066142 else g32p_supplierForest_node_066157) else (if i.val < 243 then g32p_supplierForest_node_066171 else g32p_supplierForest_node_066172)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_066182 else g32p_supplierForest_node_066195) else (if i.val < 247 then g32p_supplierForest_node_066248 else g32p_supplierForest_node_066303))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_066312 else g32p_supplierForest_node_066327) else (if i.val < 251 then g32p_supplierForest_node_066351 else g32p_supplierForest_node_066357)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_066366 else g32p_supplierForest_node_066390) else (if i.val < 255 then g32p_supplierForest_node_066415 else g32p_supplierForest_node_066417))))))))

def g32p_supplierForest_classes_095 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 74 else 74) else (if i.val < 3 then 74 else 68)) else (if i.val < 6 then (if i.val < 5 then 21 else 6) else (if i.val < 7 then 75 else 73))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 38) else (if i.val < 11 then 69 else 71)) else (if i.val < 14 then (if i.val < 13 then 21 else 74) else (if i.val < 15 then 6 else 73)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 69 else 69) else (if i.val < 19 then 74 else 43)) else (if i.val < 22 then (if i.val < 21 then 38 else 21) else (if i.val < 23 then 41 else 71))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 6 else 7) else (if i.val < 27 then 73 else 38)) else (if i.val < 30 then (if i.val < 29 then 21 else 21) else (if i.val < 31 then 21 else 73))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 7 else 68) else (if i.val < 35 then 74 else 41)) else (if i.val < 38 then (if i.val < 37 then 69 else 21) else (if i.val < 39 then 40 else 38))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 38 else 39) else (if i.val < 43 then 22 else 21)) else (if i.val < 46 then (if i.val < 45 then 21 else 38) else (if i.val < 47 then 22 else 41)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 21 else 6) else (if i.val < 51 then 38 else 38)) else (if i.val < 54 then (if i.val < 53 then 38 else 73) else (if i.val < 55 then 73 else 21))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 38) else (if i.val < 59 then 38 else 42)) else (if i.val < 62 then (if i.val < 61 then 75 else 38) else (if i.val < 63 then 74 else 6)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 74 else 38) else (if i.val < 67 then 7 else 7)) else (if i.val < 70 then (if i.val < 69 then 38 else 73) else (if i.val < 71 then 21 else 40))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 40 else 75) else (if i.val < 75 then 73 else 40)) else (if i.val < 78 then (if i.val < 77 then 22 else 72) else (if i.val < 79 then 38 else 74)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 21 else 42) else (if i.val < 83 then 23 else 74)) else (if i.val < 86 then (if i.val < 85 then 43 else 43) else (if i.val < 87 then 38 else 74))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 21 else 70) else (if i.val < 91 then 71 else 74)) else (if i.val < 94 then (if i.val < 93 then 74 else 72) else (if i.val < 95 then 38 else 73))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 21 else 22) else (if i.val < 99 then 21 else 21)) else (if i.val < 102 then (if i.val < 101 then 41 else 42) else (if i.val < 103 then 41 else 21))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 74 else 38) else (if i.val < 107 then 38 else 38)) else (if i.val < 110 then (if i.val < 109 then 42 else 21) else (if i.val < 111 then 74 else 22)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 68 else 43) else (if i.val < 115 then 38 else 22)) else (if i.val < 118 then (if i.val < 117 then 22 else 38) else (if i.val < 119 then 38 else 22))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 21 else 38) else (if i.val < 123 then 43 else 38)) else (if i.val < 126 then (if i.val < 125 then 38 else 43) else (if i.val < 127 then 68 else 21))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 22 else 38) else (if i.val < 131 then 7 else 68)) else (if i.val < 134 then (if i.val < 133 then 38 else 21) else (if i.val < 135 then 20 else 43))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 21 else 73) else (if i.val < 139 then 21 else 38)) else (if i.val < 142 then (if i.val < 141 then 38 else 43) else (if i.val < 143 then 23 else 23)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 71 else 38) else (if i.val < 147 then 22 else 21)) else (if i.val < 150 then (if i.val < 149 then 38 else 38) else (if i.val < 151 then 38 else 38))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 38 else 38) else (if i.val < 155 then 38 else 71)) else (if i.val < 158 then (if i.val < 157 then 71 else 7) else (if i.val < 159 then 74 else 22))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 38 else 22) else (if i.val < 163 then 41 else 40)) else (if i.val < 166 then (if i.val < 165 then 21 else 74) else (if i.val < 167 then 38 else 40))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 68 else 41) else (if i.val < 171 then 38 else 73)) else (if i.val < 174 then (if i.val < 173 then 21 else 38) else (if i.val < 175 then 38 else 38)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 39 else 74) else (if i.val < 179 then 22 else 71)) else (if i.val < 182 then (if i.val < 181 then 22 else 38) else (if i.val < 183 then 20 else 38))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 73 else 38) else (if i.val < 187 then 38 else 43)) else (if i.val < 190 then (if i.val < 189 then 38 else 71) else (if i.val < 191 then 38 else 38)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 38 else 74) else (if i.val < 195 then 40 else 39)) else (if i.val < 198 then (if i.val < 197 then 40 else 38) else (if i.val < 199 then 73 else 43))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 21 else 21) else (if i.val < 203 then 41 else 38)) else (if i.val < 206 then (if i.val < 205 then 43 else 38) else (if i.val < 207 then 21 else 38)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 43 else 43) else (if i.val < 211 then 20 else 38)) else (if i.val < 214 then (if i.val < 213 then 38 else 22) else (if i.val < 215 then 71 else 21))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 71 else 21) else (if i.val < 219 then 21 else 39)) else (if i.val < 222 then (if i.val < 221 then 72 else 18) else (if i.val < 223 then 38 else 22))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 22 else 20) else (if i.val < 227 then 75 else 38)) else (if i.val < 230 then (if i.val < 229 then 72 else 21) else (if i.val < 231 then 43 else 21))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 74 else 43) else (if i.val < 235 then 21 else 21)) else (if i.val < 238 then (if i.val < 237 then 75 else 38) else (if i.val < 239 then 38 else 40)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 73 else 74) else (if i.val < 243 then 6 else 40)) else (if i.val < 246 then (if i.val < 245 then 41 else 73) else (if i.val < 247 then 43 else 22))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 74 else 43) else (if i.val < 251 then 73 else 38)) else (if i.val < 254 then (if i.val < 253 then 38 else 43) else (if i.val < 255 then 21 else 39))))))))

theorem g32p_supplierForest_actual_095 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_095 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_095 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_061069
  · exact g32p_supplierForest_actual_061076
  · exact g32p_supplierForest_actual_061084
  · exact g32p_supplierForest_actual_061113
  · exact g32p_supplierForest_actual_061115
  · exact g32p_supplierForest_actual_061118
  · exact g32p_supplierForest_actual_061153
  · exact g32p_supplierForest_actual_061192
  · exact g32p_supplierForest_actual_061212
  · exact g32p_supplierForest_actual_061217
  · exact g32p_supplierForest_actual_061234
  · exact g32p_supplierForest_actual_061242
  · exact g32p_supplierForest_actual_061253
  · exact g32p_supplierForest_actual_061254
  · exact g32p_supplierForest_actual_061267
  · exact g32p_supplierForest_actual_061269
  · exact g32p_supplierForest_actual_061270
  · exact g32p_supplierForest_actual_061385
  · exact g32p_supplierForest_actual_061392
  · exact g32p_supplierForest_actual_061410
  · exact g32p_supplierForest_actual_061458
  · exact g32p_supplierForest_actual_061522
  · exact g32p_supplierForest_actual_061565
  · exact g32p_supplierForest_actual_061569
  · exact g32p_supplierForest_actual_061621
  · exact g32p_supplierForest_actual_061715
  · exact g32p_supplierForest_actual_061752
  · exact g32p_supplierForest_actual_061761
  · exact g32p_supplierForest_actual_061765
  · exact g32p_supplierForest_actual_061766
  · exact g32p_supplierForest_actual_061775
  · exact g32p_supplierForest_actual_061794
  · exact g32p_supplierForest_actual_061858
  · exact g32p_supplierForest_actual_061889
  · exact g32p_supplierForest_actual_061898
  · exact g32p_supplierForest_actual_061943
  · exact g32p_supplierForest_actual_061955
  · exact g32p_supplierForest_actual_061988
  · exact g32p_supplierForest_actual_062044
  · exact g32p_supplierForest_actual_062045
  · exact g32p_supplierForest_actual_062111
  · exact g32p_supplierForest_actual_062122
  · exact g32p_supplierForest_actual_062123
  · exact g32p_supplierForest_actual_062132
  · exact g32p_supplierForest_actual_062135
  · exact g32p_supplierForest_actual_062142
  · exact g32p_supplierForest_actual_062176
  · exact g32p_supplierForest_actual_062189
  · exact g32p_supplierForest_actual_062202
  · exact g32p_supplierForest_actual_062273
  · exact g32p_supplierForest_actual_062291
  · exact g32p_supplierForest_actual_062293
  · exact g32p_supplierForest_actual_062299
  · exact g32p_supplierForest_actual_062352
  · exact g32p_supplierForest_actual_062360
  · exact g32p_supplierForest_actual_062362
  · exact g32p_supplierForest_actual_062365
  · exact g32p_supplierForest_actual_062380
  · exact g32p_supplierForest_actual_062384
  · exact g32p_supplierForest_actual_062391
  · exact g32p_supplierForest_actual_062408
  · exact g32p_supplierForest_actual_062441
  · exact g32p_supplierForest_actual_062492
  · exact g32p_supplierForest_actual_062508
  · exact g32p_supplierForest_actual_062527
  · exact g32p_supplierForest_actual_062532
  · exact g32p_supplierForest_actual_062553
  · exact g32p_supplierForest_actual_062615
  · exact g32p_supplierForest_actual_062622
  · exact g32p_supplierForest_actual_062633
  · exact g32p_supplierForest_actual_062638
  · exact g32p_supplierForest_actual_062671
  · exact g32p_supplierForest_actual_062679
  · exact g32p_supplierForest_actual_062700
  · exact g32p_supplierForest_actual_062716
  · exact g32p_supplierForest_actual_062749
  · exact g32p_supplierForest_actual_062808
  · exact g32p_supplierForest_actual_062818
  · exact g32p_supplierForest_actual_062821
  · exact g32p_supplierForest_actual_062824
  · exact g32p_supplierForest_actual_062837
  · exact g32p_supplierForest_actual_062847
  · exact g32p_supplierForest_actual_062858
  · exact g32p_supplierForest_actual_062885
  · exact g32p_supplierForest_actual_062946
  · exact g32p_supplierForest_actual_062962
  · exact g32p_supplierForest_actual_062979
  · exact g32p_supplierForest_actual_062993
  · exact g32p_supplierForest_actual_062999
  · exact g32p_supplierForest_actual_063054
  · exact g32p_supplierForest_actual_063055
  · exact g32p_supplierForest_actual_063060
  · exact g32p_supplierForest_actual_063062
  · exact g32p_supplierForest_actual_063082
  · exact g32p_supplierForest_actual_063105
  · exact g32p_supplierForest_actual_063129
  · exact g32p_supplierForest_actual_063188
  · exact g32p_supplierForest_actual_063200
  · exact g32p_supplierForest_actual_063203
  · exact g32p_supplierForest_actual_063218
  · exact g32p_supplierForest_actual_063254
  · exact g32p_supplierForest_actual_063265
  · exact g32p_supplierForest_actual_063275
  · exact g32p_supplierForest_actual_063290
  · exact g32p_supplierForest_actual_063341
  · exact g32p_supplierForest_actual_063343
  · exact g32p_supplierForest_actual_063435
  · exact g32p_supplierForest_actual_063458
  · exact g32p_supplierForest_actual_063462
  · exact g32p_supplierForest_actual_063466
  · exact g32p_supplierForest_actual_063532
  · exact g32p_supplierForest_actual_063556
  · exact g32p_supplierForest_actual_063562
  · exact g32p_supplierForest_actual_063607
  · exact g32p_supplierForest_actual_063628
  · exact g32p_supplierForest_actual_063642
  · exact g32p_supplierForest_actual_063673
  · exact g32p_supplierForest_actual_063682
  · exact g32p_supplierForest_actual_063683
  · exact g32p_supplierForest_actual_063692
  · exact g32p_supplierForest_actual_063697
  · exact g32p_supplierForest_actual_063725
  · exact g32p_supplierForest_actual_063738
  · exact g32p_supplierForest_actual_063769
  · exact g32p_supplierForest_actual_063784
  · exact g32p_supplierForest_actual_063786
  · exact g32p_supplierForest_actual_063798
  · exact g32p_supplierForest_actual_063800
  · exact g32p_supplierForest_actual_063818
  · exact g32p_supplierForest_actual_063829
  · exact g32p_supplierForest_actual_063848
  · exact g32p_supplierForest_actual_063865
  · exact g32p_supplierForest_actual_063885
  · exact g32p_supplierForest_actual_063898
  · exact g32p_supplierForest_actual_063910
  · exact g32p_supplierForest_actual_063936
  · exact g32p_supplierForest_actual_063946
  · exact g32p_supplierForest_actual_063981
  · exact g32p_supplierForest_actual_063983
  · exact g32p_supplierForest_actual_064016
  · exact g32p_supplierForest_actual_064032
  · exact g32p_supplierForest_actual_064037
  · exact g32p_supplierForest_actual_064059
  · exact g32p_supplierForest_actual_064091
  · exact g32p_supplierForest_actual_064127
  · exact g32p_supplierForest_actual_064141
  · exact g32p_supplierForest_actual_064160
  · exact g32p_supplierForest_actual_064167
  · exact g32p_supplierForest_actual_064184
  · exact g32p_supplierForest_actual_064188
  · exact g32p_supplierForest_actual_064195
  · exact g32p_supplierForest_actual_064238
  · exact g32p_supplierForest_actual_064254
  · exact g32p_supplierForest_actual_064262
  · exact g32p_supplierForest_actual_064322
  · exact g32p_supplierForest_actual_064375
  · exact g32p_supplierForest_actual_064394
  · exact g32p_supplierForest_actual_064430
  · exact g32p_supplierForest_actual_064435
  · exact g32p_supplierForest_actual_064457
  · exact g32p_supplierForest_actual_064497
  · exact g32p_supplierForest_actual_064514
  · exact g32p_supplierForest_actual_064581
  · exact g32p_supplierForest_actual_064584
  · exact g32p_supplierForest_actual_064596
  · exact g32p_supplierForest_actual_064623
  · exact g32p_supplierForest_actual_064653
  · exact g32p_supplierForest_actual_064669
  · exact g32p_supplierForest_actual_064684
  · exact g32p_supplierForest_actual_064691
  · exact g32p_supplierForest_actual_064736
  · exact g32p_supplierForest_actual_064759
  · exact g32p_supplierForest_actual_064772
  · exact g32p_supplierForest_actual_064781
  · exact g32p_supplierForest_actual_064784
  · exact g32p_supplierForest_actual_064788
  · exact g32p_supplierForest_actual_064827
  · exact g32p_supplierForest_actual_064835
  · exact g32p_supplierForest_actual_064846
  · exact g32p_supplierForest_actual_064882
  · exact g32p_supplierForest_actual_064906
  · exact g32p_supplierForest_actual_064947
  · exact g32p_supplierForest_actual_064962
  · exact g32p_supplierForest_actual_065017
  · exact g32p_supplierForest_actual_065105
  · exact g32p_supplierForest_actual_065145
  · exact g32p_supplierForest_actual_065166
  · exact g32p_supplierForest_actual_065175
  · exact g32p_supplierForest_actual_065176
  · exact g32p_supplierForest_actual_065192
  · exact g32p_supplierForest_actual_065243
  · exact g32p_supplierForest_actual_065265
  · exact g32p_supplierForest_actual_065283
  · exact g32p_supplierForest_actual_065329
  · exact g32p_supplierForest_actual_065337
  · exact g32p_supplierForest_actual_065342
  · exact g32p_supplierForest_actual_065348
  · exact g32p_supplierForest_actual_065384
  · exact g32p_supplierForest_actual_065404
  · exact g32p_supplierForest_actual_065451
  · exact g32p_supplierForest_actual_065459
  · exact g32p_supplierForest_actual_065465
  · exact g32p_supplierForest_actual_065487
  · exact g32p_supplierForest_actual_065531
  · exact g32p_supplierForest_actual_065539
  · exact g32p_supplierForest_actual_065561
  · exact g32p_supplierForest_actual_065573
  · exact g32p_supplierForest_actual_065607
  · exact g32p_supplierForest_actual_065611
  · exact g32p_supplierForest_actual_065647
  · exact g32p_supplierForest_actual_065666
  · exact g32p_supplierForest_actual_065683
  · exact g32p_supplierForest_actual_065693
  · exact g32p_supplierForest_actual_065694
  · exact g32p_supplierForest_actual_065714
  · exact g32p_supplierForest_actual_065732
  · exact g32p_supplierForest_actual_065743
  · exact g32p_supplierForest_actual_065758
  · exact g32p_supplierForest_actual_065759
  · exact g32p_supplierForest_actual_065769
  · exact g32p_supplierForest_actual_065782
  · exact g32p_supplierForest_actual_065793
  · exact g32p_supplierForest_actual_065794
  · exact g32p_supplierForest_actual_065801
  · exact g32p_supplierForest_actual_065830
  · exact g32p_supplierForest_actual_065843
  · exact g32p_supplierForest_actual_065849
  · exact g32p_supplierForest_actual_065862
  · exact g32p_supplierForest_actual_065875
  · exact g32p_supplierForest_actual_065878
  · exact g32p_supplierForest_actual_065931
  · exact g32p_supplierForest_actual_065946
  · exact g32p_supplierForest_actual_065969
  · exact g32p_supplierForest_actual_065979
  · exact g32p_supplierForest_actual_065993
  · exact g32p_supplierForest_actual_066012
  · exact g32p_supplierForest_actual_066018
  · exact g32p_supplierForest_actual_066059
  · exact g32p_supplierForest_actual_066070
  · exact g32p_supplierForest_actual_066136
  · exact g32p_supplierForest_actual_066142
  · exact g32p_supplierForest_actual_066157
  · exact g32p_supplierForest_actual_066171
  · exact g32p_supplierForest_actual_066172
  · exact g32p_supplierForest_actual_066182
  · exact g32p_supplierForest_actual_066195
  · exact g32p_supplierForest_actual_066248
  · exact g32p_supplierForest_actual_066303
  · exact g32p_supplierForest_actual_066312
  · exact g32p_supplierForest_actual_066327
  · exact g32p_supplierForest_actual_066351
  · exact g32p_supplierForest_actual_066357
  · exact g32p_supplierForest_actual_066366
  · exact g32p_supplierForest_actual_066390
  · exact g32p_supplierForest_actual_066415
  · exact g32p_supplierForest_actual_066417

end HodgeLean.Foundations.Program

end
end
