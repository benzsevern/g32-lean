import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0210
import HodgeLean.Foundations.Program.G32PropFourSixPacked0211

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_066558 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066558 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066558 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_044700 := by
  decide +kernel

theorem g32p_supplierForest_actual_066558 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066558) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 3 g32p_supplierForest_edge_066558
    g32p_supplierForest_actual_044700

def g32p_supplierForest_node_066595 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066595 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066595 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_061083 := by
  decide +kernel

theorem g32p_supplierForest_actual_066595 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066595) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_066595
    g32p_supplierForest_actual_061083

def g32p_supplierForest_node_066610 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066610 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066610 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067504 := by
  decide +kernel

theorem g32p_supplierForest_actual_066610 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066610) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_066610
    g32p_supplierForest_actual_067504

def g32p_supplierForest_node_066621 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066621 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066621 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_061232 := by
  decide +kernel

theorem g32p_supplierForest_actual_066621 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066621) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 3 g32p_supplierForest_edge_066621
    g32p_supplierForest_actual_061232

def g32p_supplierForest_node_066729 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066729 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066729 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_066486 := by
  decide +kernel

theorem g32p_supplierForest_actual_066729 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066729) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_066729
    g32p_supplierForest_actual_066486

def g32p_supplierForest_node_066816 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066816 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066816 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048662 := by
  decide +kernel

theorem g32p_supplierForest_actual_066816 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066816) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_066816
    g32p_supplierForest_actual_048662

def g32p_supplierForest_node_066828 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066828 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066828 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_048662 := by
  decide +kernel

theorem g32p_supplierForest_actual_066828 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066828) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_066828
    g32p_supplierForest_actual_048662

def g32p_supplierForest_node_066845 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_066845 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066845 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_133875 := by
  decide +kernel

theorem g32p_supplierForest_actual_066845 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066845) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_066845
    g32p_supplierForest_actual_133875

def g32p_supplierForest_node_066904 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066904 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066904 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_047361 := by
  decide +kernel

theorem g32p_supplierForest_actual_066904 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066904) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 3 g32p_supplierForest_edge_066904
    g32p_supplierForest_actual_047361

def g32p_supplierForest_node_066960 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066960 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066960 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_051967 := by
  decide +kernel

theorem g32p_supplierForest_actual_066960 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066960) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 0 g32p_supplierForest_edge_066960
    g32p_supplierForest_actual_051967

def g32p_supplierForest_node_067001 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067001 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067001 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_045771 := by
  decide +kernel

theorem g32p_supplierForest_actual_067001 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067001) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_067001
    g32p_supplierForest_actual_045771

def g32p_supplierForest_node_067125 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_067125 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067125 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_046828 := by
  decide +kernel

theorem g32p_supplierForest_actual_067125 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067125) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 1 g32p_supplierForest_edge_067125
    g32p_supplierForest_actual_046828

def g32p_supplierForest_node_067251 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_067251 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067251 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010341 := by
  decide +kernel

theorem g32p_supplierForest_actual_067251 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067251) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 3 g32p_supplierForest_edge_067251
    g32p_supplierForest_actual_010341

def g32p_supplierForest_node_067262 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_067262 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067262 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_047386 := by
  decide +kernel

theorem g32p_supplierForest_actual_067262 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067262) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 3 g32p_supplierForest_edge_067262
    g32p_supplierForest_actual_047386

def g32p_supplierForest_node_067561 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_067561 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067561 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_063808 := by
  decide +kernel

theorem g32p_supplierForest_actual_067561 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067561) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_067561
    g32p_supplierForest_actual_063808

def g32p_supplierForest_node_067722 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067722 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067722 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062709 := by
  decide +kernel

theorem g32p_supplierForest_actual_067722 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067722) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_067722
    g32p_supplierForest_actual_062709

def g32p_supplierForest_node_067836 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_067836 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067836 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_135506 := by
  decide +kernel

theorem g32p_supplierForest_actual_067836 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067836) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_067836
    g32p_supplierForest_actual_135506

def g32p_supplierForest_node_067860 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_067860 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067860 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_009243 := by
  decide +kernel

theorem g32p_supplierForest_actual_067860 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067860) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 2 g32p_supplierForest_edge_067860
    g32p_supplierForest_actual_009243

def g32p_supplierForest_node_067877 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_067877 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067877 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_009777 := by
  decide +kernel

theorem g32p_supplierForest_actual_067877 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067877) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_067877
    g32p_supplierForest_actual_009777

def g32p_supplierForest_node_067897 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_067897 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067897 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_127929 := by
  decide +kernel

theorem g32p_supplierForest_actual_067897 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067897) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 3 g32p_supplierForest_edge_067897
    g32p_supplierForest_actual_127929

def g32p_supplierForest_node_068016 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_068016 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068016 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_059535 := by
  decide +kernel

theorem g32p_supplierForest_actual_068016 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068016) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_068016
    g32p_supplierForest_actual_059535

def g32p_supplierForest_node_068171 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_068171 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068171 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_067541 := by
  decide +kernel

theorem g32p_supplierForest_actual_068171 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068171) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_068171
    g32p_supplierForest_actual_067541

def g32p_supplierForest_node_068235 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068235 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068235 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064696 := by
  decide +kernel

theorem g32p_supplierForest_actual_068235 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068235) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 2 g32p_supplierForest_edge_068235
    g32p_supplierForest_actual_064696

def g32p_supplierForest_node_068323 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_068323 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068323 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064928 := by
  decide +kernel

theorem g32p_supplierForest_actual_068323 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068323) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_068323
    g32p_supplierForest_actual_064928

def g32p_supplierForest_node_068399 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_068399 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068399 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_066486 := by
  decide +kernel

theorem g32p_supplierForest_actual_068399 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068399) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_068399
    g32p_supplierForest_actual_066486

def g32p_supplierForest_node_068447 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_068447 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068447 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062264 := by
  decide +kernel

theorem g32p_supplierForest_actual_068447 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068447) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_068447
    g32p_supplierForest_actual_062264

def g32p_supplierForest_node_068488 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068488 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068488 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062302 := by
  decide +kernel

theorem g32p_supplierForest_actual_068488 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068488) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_068488
    g32p_supplierForest_actual_062302

def g32p_supplierForest_node_068506 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_068506 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068506 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051879 := by
  decide +kernel

theorem g32p_supplierForest_actual_068506 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068506) ∧
        IsConj g (g32p_literalRepresentative 67) := by
  exact g32p_archive_step_lift _ _ 67 2 g32p_supplierForest_edge_068506
    g32p_supplierForest_actual_051879

def g32p_supplierForest_node_068724 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068724 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068724 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067487 := by
  decide +kernel

theorem g32p_supplierForest_actual_068724 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068724) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 2 g32p_supplierForest_edge_068724
    g32p_supplierForest_actual_067487

def g32p_supplierForest_node_068756 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068756 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068756 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067504 := by
  decide +kernel

theorem g32p_supplierForest_actual_068756 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068756) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_068756
    g32p_supplierForest_actual_067504

def g32p_supplierForest_node_068769 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068769 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068769 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_005965 := by
  decide +kernel

theorem g32p_supplierForest_actual_068769 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068769) ∧
        IsConj g (g32p_literalRepresentative 18) := by
  exact g32p_archive_step_lift _ _ 18 3 g32p_supplierForest_edge_068769
    g32p_supplierForest_actual_005965

def g32p_supplierForest_node_068770 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_068770 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068770 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048023 := by
  decide +kernel

theorem g32p_supplierForest_actual_068770 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068770) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 3 g32p_supplierForest_edge_068770
    g32p_supplierForest_actual_048023

def g32p_supplierForest_node_068820 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068820 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068820 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_130278 := by
  decide +kernel

theorem g32p_supplierForest_actual_068820 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068820) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 1 g32p_supplierForest_edge_068820
    g32p_supplierForest_actual_130278

def g32p_supplierForest_node_068868 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068868 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068868 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_046333 := by
  decide +kernel

theorem g32p_supplierForest_actual_068868 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068868) ∧
        IsConj g (g32p_literalRepresentative 23) := by
  exact g32p_archive_step_lift _ _ 23 1 g32p_supplierForest_edge_068868
    g32p_supplierForest_actual_046333

def g32p_supplierForest_node_068965 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068965 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068965 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_010924 := by
  decide +kernel

theorem g32p_supplierForest_actual_068965 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068965) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_068965
    g32p_supplierForest_actual_010924

def g32p_supplierForest_node_068984 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068984 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068984 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_068457 := by
  decide +kernel

theorem g32p_supplierForest_actual_068984 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068984) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 2 g32p_supplierForest_edge_068984
    g32p_supplierForest_actual_068457

def g32p_supplierForest_node_069018 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_069018 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069018 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_053118 := by
  decide +kernel

theorem g32p_supplierForest_actual_069018 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069018) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_069018
    g32p_supplierForest_actual_053118

def g32p_supplierForest_node_069115 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_069115 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069115 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070611 := by
  decide +kernel

theorem g32p_supplierForest_actual_069115 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069115) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 0 g32p_supplierForest_edge_069115
    g32p_supplierForest_actual_070611

def g32p_supplierForest_node_069485 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_069485 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069485 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_054826 := by
  decide +kernel

theorem g32p_supplierForest_actual_069485 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069485) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_069485
    g32p_supplierForest_actual_054826

def g32p_supplierForest_node_069486 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_069486 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069486 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010924 := by
  decide +kernel

theorem g32p_supplierForest_actual_069486 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069486) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_069486
    g32p_supplierForest_actual_010924

def g32p_supplierForest_node_069506 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069506 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069506 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_011762 := by
  decide +kernel

theorem g32p_supplierForest_actual_069506 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069506) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_069506
    g32p_supplierForest_actual_011762

def g32p_supplierForest_node_069602 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069602 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069602 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_130563 := by
  decide +kernel

theorem g32p_supplierForest_actual_069602 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069602) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_069602
    g32p_supplierForest_actual_130563

def g32p_supplierForest_node_069607 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_069607 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069607 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_133179 := by
  decide +kernel

theorem g32p_supplierForest_actual_069607 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069607) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 1 g32p_supplierForest_edge_069607
    g32p_supplierForest_actual_133179

def g32p_supplierForest_node_069781 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_069781 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069781 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_070908 := by
  decide +kernel

theorem g32p_supplierForest_actual_069781 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069781) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 2 g32p_supplierForest_edge_069781
    g32p_supplierForest_actual_070908

def g32p_supplierForest_node_069852 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_069852 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069852 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071099 := by
  decide +kernel

theorem g32p_supplierForest_actual_069852 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069852) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 2 g32p_supplierForest_edge_069852
    g32p_supplierForest_actual_071099

def g32p_supplierForest_node_070194 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070194 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070194 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_006362 := by
  decide +kernel

theorem g32p_supplierForest_actual_070194 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070194) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_070194
    g32p_supplierForest_actual_006362

def g32p_supplierForest_node_070252 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_070252 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070252 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_046054 := by
  decide +kernel

theorem g32p_supplierForest_actual_070252 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070252) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 3 g32p_supplierForest_edge_070252
    g32p_supplierForest_actual_046054

def g32p_supplierForest_node_070298 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_070298 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070298 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_065718 := by
  decide +kernel

theorem g32p_supplierForest_actual_070298 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070298) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_070298
    g32p_supplierForest_actual_065718

def g32p_supplierForest_node_070334 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_070334 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070334 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_047886 := by
  decide +kernel

theorem g32p_supplierForest_actual_070334 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070334) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 3 g32p_supplierForest_edge_070334
    g32p_supplierForest_actual_047886

def g32p_supplierForest_node_070407 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_070407 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070407 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048178 := by
  decide +kernel

theorem g32p_supplierForest_actual_070407 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070407) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_070407
    g32p_supplierForest_actual_048178

def g32p_supplierForest_node_070440 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_070440 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070440 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048834 := by
  decide +kernel

theorem g32p_supplierForest_actual_070440 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070440) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_070440
    g32p_supplierForest_actual_048834

def g32p_supplierForest_node_070483 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_070483 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070483 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_143660 := by
  decide +kernel

theorem g32p_supplierForest_actual_070483 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070483) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 1 g32p_supplierForest_edge_070483
    g32p_supplierForest_actual_143660

def g32p_supplierForest_node_070584 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_070584 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070584 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_053027 := by
  decide +kernel

theorem g32p_supplierForest_actual_070584 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070584) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 3 g32p_supplierForest_edge_070584
    g32p_supplierForest_actual_053027

def g32p_supplierForest_node_070608 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_070608 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070608 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_053115 := by
  decide +kernel

theorem g32p_supplierForest_actual_070608 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070608) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_070608
    g32p_supplierForest_actual_053115

def g32p_supplierForest_node_070670 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_070670 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070670 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_007447 := by
  decide +kernel

theorem g32p_supplierForest_actual_070670 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070670) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 3 g32p_supplierForest_edge_070670
    g32p_supplierForest_actual_007447

def g32p_supplierForest_node_070739 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_070739 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070739 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_054434 := by
  decide +kernel

theorem g32p_supplierForest_actual_070739 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070739) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_070739
    g32p_supplierForest_actual_054434

def g32p_supplierForest_node_070790 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_070790 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070790 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051434 := by
  decide +kernel

theorem g32p_supplierForest_actual_070790 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070790) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_070790
    g32p_supplierForest_actual_051434

def g32p_supplierForest_node_070806 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_070806 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070806 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_131920 := by
  decide +kernel

theorem g32p_supplierForest_actual_070806 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070806) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_070806
    g32p_supplierForest_actual_131920

def g32p_supplierForest_node_070884 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070884 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070884 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_138457 := by
  decide +kernel

theorem g32p_supplierForest_actual_070884 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070884) ∧
        IsConj g (g32p_literalRepresentative 79) := by
  exact g32p_archive_step_lift _ _ 79 1 g32p_supplierForest_edge_070884
    g32p_supplierForest_actual_138457

def g32p_supplierForest_node_070974 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070974 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070974 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_057571 := by
  decide +kernel

theorem g32p_supplierForest_actual_070974 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070974) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 3 g32p_supplierForest_edge_070974
    g32p_supplierForest_actual_057571

def g32p_supplierForest_node_071103 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071103 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071103 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048321 := by
  decide +kernel

theorem g32p_supplierForest_actual_071103 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071103) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_071103
    g32p_supplierForest_actual_048321

def g32p_supplierForest_node_071108 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_071108 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071108 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_138879 := by
  decide +kernel

theorem g32p_supplierForest_actual_071108 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071108) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_071108
    g32p_supplierForest_actual_138879

def g32p_supplierForest_node_071111 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_071111 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071111 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_067488 := by
  decide +kernel

theorem g32p_supplierForest_actual_071111 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071111) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 3 g32p_supplierForest_edge_071111
    g32p_supplierForest_actual_067488

def g32p_supplierForest_node_071213 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_071213 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071213 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_067496 := by
  decide +kernel

theorem g32p_supplierForest_actual_071213 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071213) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 3 g32p_supplierForest_edge_071213
    g32p_supplierForest_actual_067496

def g32p_supplierForest_node_071271 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_071271 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071271 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067534 := by
  decide +kernel

theorem g32p_supplierForest_actual_071271 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071271) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_071271
    g32p_supplierForest_actual_067534

def g32p_supplierForest_node_071440 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_071440 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071440 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_011761 := by
  decide +kernel

theorem g32p_supplierForest_actual_071440 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071440) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_071440
    g32p_supplierForest_actual_011761

def g32p_supplierForest_node_071491 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071491 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071491 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_011827 := by
  decide +kernel

theorem g32p_supplierForest_actual_071491 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071491) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_071491
    g32p_supplierForest_actual_011827

def g32p_supplierForest_node_071620 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071620 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071620 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_050851 := by
  decide +kernel

theorem g32p_supplierForest_actual_071620 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071620) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 0 g32p_supplierForest_edge_071620
    g32p_supplierForest_actual_050851

def g32p_supplierForest_node_071638 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071638 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071638 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_044619 := by
  decide +kernel

theorem g32p_supplierForest_actual_071638 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071638) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 3 g32p_supplierForest_edge_071638
    g32p_supplierForest_actual_044619

def g32p_supplierForest_node_071746 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_071746 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071746 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_020002 := by
  decide +kernel

theorem g32p_supplierForest_actual_071746 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071746) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_071746
    g32p_supplierForest_actual_020002

def g32p_supplierForest_node_071765 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_071765 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071765 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_016182 := by
  decide +kernel

theorem g32p_supplierForest_actual_071765 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071765) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_071765
    g32p_supplierForest_actual_016182

def g32p_supplierForest_node_071780 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_071780 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071780 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_014655 := by
  decide +kernel

theorem g32p_supplierForest_actual_071780 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071780) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 0 g32p_supplierForest_edge_071780
    g32p_supplierForest_actual_014655

def g32p_supplierForest_node_071941 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_071941 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071941 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_072446 := by
  decide +kernel

theorem g32p_supplierForest_actual_071941 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071941) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_071941
    g32p_supplierForest_actual_072446

def g32p_supplierForest_node_072028 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_072028 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072028 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_022990 := by
  decide +kernel

theorem g32p_supplierForest_actual_072028 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072028) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_072028
    g32p_supplierForest_actual_022990

def g32p_supplierForest_node_072107 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_072107 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072107 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_015495 := by
  decide +kernel

theorem g32p_supplierForest_actual_072107 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072107) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 0 g32p_supplierForest_edge_072107
    g32p_supplierForest_actual_015495

def g32p_supplierForest_node_072178 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_072178 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072178 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_018075 := by
  decide +kernel

theorem g32p_supplierForest_actual_072178 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072178) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_072178
    g32p_supplierForest_actual_018075

def g32p_supplierForest_node_072224 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_072224 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072224 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082089 := by
  decide +kernel

theorem g32p_supplierForest_actual_072224 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072224) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_072224
    g32p_supplierForest_actual_082089

def g32p_supplierForest_node_072576 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_072576 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072576 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_024184 := by
  decide +kernel

theorem g32p_supplierForest_actual_072576 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072576) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_072576
    g32p_supplierForest_actual_024184

def g32p_supplierForest_node_072604 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072604 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072604 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_016584 := by
  decide +kernel

theorem g32p_supplierForest_actual_072604 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072604) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_072604
    g32p_supplierForest_actual_016584

def g32p_supplierForest_node_072657 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_072657 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072657 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015163 := by
  decide +kernel

theorem g32p_supplierForest_actual_072657 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072657) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 2 g32p_supplierForest_edge_072657
    g32p_supplierForest_actual_015163

def g32p_supplierForest_node_072693 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_072693 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072693 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_077642 := by
  decide +kernel

theorem g32p_supplierForest_actual_072693 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072693) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_072693
    g32p_supplierForest_actual_077642

def g32p_supplierForest_node_072722 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_072722 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072722 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014655 := by
  decide +kernel

theorem g32p_supplierForest_actual_072722 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072722) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 3 g32p_supplierForest_edge_072722
    g32p_supplierForest_actual_014655

def g32p_supplierForest_node_072808 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_072808 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072808 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_014935 := by
  decide +kernel

theorem g32p_supplierForest_actual_072808 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072808) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_072808
    g32p_supplierForest_actual_014935

def g32p_supplierForest_node_072985 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_072985 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072985 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097467 := by
  decide +kernel

theorem g32p_supplierForest_actual_072985 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072985) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 2 g32p_supplierForest_edge_072985
    g32p_supplierForest_actual_097467

def g32p_supplierForest_node_073043 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073043 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073043 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101691 := by
  decide +kernel

theorem g32p_supplierForest_actual_073043 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073043) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 2 g32p_supplierForest_edge_073043
    g32p_supplierForest_actual_101691

def g32p_supplierForest_node_073114 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073114 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073114 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_014931 := by
  decide +kernel

theorem g32p_supplierForest_actual_073114 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073114) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_073114
    g32p_supplierForest_actual_014931

def g32p_supplierForest_node_073341 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073341 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073341 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083511 := by
  decide +kernel

theorem g32p_supplierForest_actual_073341 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073341) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_073341
    g32p_supplierForest_actual_083511

def g32p_supplierForest_node_073346 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073346 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073346 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083476 := by
  decide +kernel

theorem g32p_supplierForest_actual_073346 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073346) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_073346
    g32p_supplierForest_actual_083476

def g32p_supplierForest_node_073381 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073381 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073381 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_016049 := by
  decide +kernel

theorem g32p_supplierForest_actual_073381 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073381) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_073381
    g32p_supplierForest_actual_016049

def g32p_supplierForest_node_073419 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073419 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073419 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021057 := by
  decide +kernel

theorem g32p_supplierForest_actual_073419 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073419) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_073419
    g32p_supplierForest_actual_021057

def g32p_supplierForest_node_073595 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073595 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073595 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_014854 := by
  decide +kernel

theorem g32p_supplierForest_actual_073595 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073595) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_073595
    g32p_supplierForest_actual_014854

def g32p_supplierForest_node_073629 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073629 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073629 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023683 := by
  decide +kernel

theorem g32p_supplierForest_actual_073629 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073629) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_073629
    g32p_supplierForest_actual_023683

def g32p_supplierForest_node_073655 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073655 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073655 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073917 := by
  decide +kernel

theorem g32p_supplierForest_actual_073655 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073655) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_073655
    g32p_supplierForest_actual_073917

def g32p_supplierForest_node_073669 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073669 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073669 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022886 := by
  decide +kernel

theorem g32p_supplierForest_actual_073669 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073669) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_073669
    g32p_supplierForest_actual_022886

def g32p_supplierForest_node_073746 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073746 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073746 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023535 := by
  decide +kernel

theorem g32p_supplierForest_actual_073746 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073746) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_073746
    g32p_supplierForest_actual_023535

def g32p_supplierForest_node_073755 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073755 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073755 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012653 := by
  decide +kernel

theorem g32p_supplierForest_actual_073755 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073755) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_073755
    g32p_supplierForest_actual_012653

def g32p_supplierForest_node_073837 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073837 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073837 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_074337 := by
  decide +kernel

theorem g32p_supplierForest_actual_073837 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073837) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_073837
    g32p_supplierForest_actual_074337

def g32p_supplierForest_node_073875 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073875 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073875 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_074414 := by
  decide +kernel

theorem g32p_supplierForest_actual_073875 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073875) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 1 g32p_supplierForest_edge_073875
    g32p_supplierForest_actual_074414

def g32p_supplierForest_node_073887 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073887 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073887 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073640 := by
  decide +kernel

theorem g32p_supplierForest_actual_073887 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073887) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_073887
    g32p_supplierForest_actual_073640

def g32p_supplierForest_node_073906 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073906 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073906 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_012792 := by
  decide +kernel

theorem g32p_supplierForest_actual_073906 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073906) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_073906
    g32p_supplierForest_actual_012792

def g32p_supplierForest_node_074040 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_074040 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074040 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_018075 := by
  decide +kernel

theorem g32p_supplierForest_actual_074040 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074040) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_074040
    g32p_supplierForest_actual_018075

def g32p_supplierForest_node_074169 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074169 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074169 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019510 := by
  decide +kernel

theorem g32p_supplierForest_actual_074169 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074169) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_074169
    g32p_supplierForest_actual_019510

def g32p_supplierForest_node_074172 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_074172 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074172 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_074164 := by
  decide +kernel

theorem g32p_supplierForest_actual_074172 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074172) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_074172
    g32p_supplierForest_actual_074164

def g32p_supplierForest_node_074188 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074188 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074188 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075150 := by
  decide +kernel

theorem g32p_supplierForest_actual_074188 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074188) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 1 g32p_supplierForest_edge_074188
    g32p_supplierForest_actual_075150

def g32p_supplierForest_node_074190 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074190 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074190 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075144 := by
  decide +kernel

theorem g32p_supplierForest_actual_074190 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074190) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_074190
    g32p_supplierForest_actual_075144

def g32p_supplierForest_node_074262 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_074262 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074262 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_015100 := by
  decide +kernel

theorem g32p_supplierForest_actual_074262 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074262) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_074262
    g32p_supplierForest_actual_015100

def g32p_supplierForest_node_074264 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_074264 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074264 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012387 := by
  decide +kernel

theorem g32p_supplierForest_actual_074264 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074264) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_074264
    g32p_supplierForest_actual_012387

def g32p_supplierForest_node_074285 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074285 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074285 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_014272 := by
  decide +kernel

theorem g32p_supplierForest_actual_074285 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074285) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_074285
    g32p_supplierForest_actual_014272

def g32p_supplierForest_node_074377 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074377 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074377 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013058 := by
  decide +kernel

theorem g32p_supplierForest_actual_074377 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074377) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 3 g32p_supplierForest_edge_074377
    g32p_supplierForest_actual_013058

def g32p_supplierForest_node_074446 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_074446 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074446 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071750 := by
  decide +kernel

theorem g32p_supplierForest_actual_074446 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074446) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_074446
    g32p_supplierForest_actual_071750

def g32p_supplierForest_node_074459 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_074459 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074459 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012632 := by
  decide +kernel

theorem g32p_supplierForest_actual_074459 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074459) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_074459
    g32p_supplierForest_actual_012632

def g32p_supplierForest_node_074472 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074472 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074472 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073640 := by
  decide +kernel

theorem g32p_supplierForest_actual_074472 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074472) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_074472
    g32p_supplierForest_actual_073640

def g32p_supplierForest_node_074506 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_074506 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074506 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071825 := by
  decide +kernel

theorem g32p_supplierForest_actual_074506 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074506) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 2 g32p_supplierForest_edge_074506
    g32p_supplierForest_actual_071825

def g32p_supplierForest_node_074529 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074529 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074529 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074596 := by
  decide +kernel

theorem g32p_supplierForest_actual_074529 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074529) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_074529
    g32p_supplierForest_actual_074596

def g32p_supplierForest_node_074610 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_074610 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074610 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_016968 := by
  decide +kernel

theorem g32p_supplierForest_actual_074610 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074610) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 1 g32p_supplierForest_edge_074610
    g32p_supplierForest_actual_016968

def g32p_supplierForest_node_074742 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_074742 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074742 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_077144 := by
  decide +kernel

theorem g32p_supplierForest_actual_074742 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074742) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_074742
    g32p_supplierForest_actual_077144

def g32p_supplierForest_node_074747 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_074747 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074747 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_074414 := by
  decide +kernel

theorem g32p_supplierForest_actual_074747 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074747) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_074747
    g32p_supplierForest_actual_074414

def g32p_supplierForest_node_074810 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_074810 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074810 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083899 := by
  decide +kernel

theorem g32p_supplierForest_actual_074810 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074810) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_074810
    g32p_supplierForest_actual_083899

def g32p_supplierForest_node_074908 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074908 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074908 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_071750 := by
  decide +kernel

theorem g32p_supplierForest_actual_074908 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074908) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_074908
    g32p_supplierForest_actual_071750

def g32p_supplierForest_node_074919 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_074919 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074919 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_015746 := by
  decide +kernel

theorem g32p_supplierForest_actual_074919 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074919) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_074919
    g32p_supplierForest_actual_015746

def g32p_supplierForest_node_074968 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_074968 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074968 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014249 := by
  decide +kernel

theorem g32p_supplierForest_actual_074968 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074968) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_074968
    g32p_supplierForest_actual_014249

def g32p_supplierForest_node_074979 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_074979 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074979 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085469 := by
  decide +kernel

theorem g32p_supplierForest_actual_074979 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074979) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_074979
    g32p_supplierForest_actual_085469

def g32p_supplierForest_node_075139 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_075139 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075139 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075150 := by
  decide +kernel

theorem g32p_supplierForest_actual_075139 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075139) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 3 g32p_supplierForest_edge_075139
    g32p_supplierForest_actual_075150

def g32p_supplierForest_node_075185 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_075185 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075185 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077144 := by
  decide +kernel

theorem g32p_supplierForest_actual_075185 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075185) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 3 g32p_supplierForest_edge_075185
    g32p_supplierForest_actual_077144

def g32p_supplierForest_node_075187 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_075187 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075187 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013097 := by
  decide +kernel

theorem g32p_supplierForest_actual_075187 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075187) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_075187
    g32p_supplierForest_actual_013097

def g32p_supplierForest_node_075200 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_075200 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075200 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_015439 := by
  decide +kernel

theorem g32p_supplierForest_actual_075200 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075200) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_075200
    g32p_supplierForest_actual_015439

def g32p_supplierForest_node_075206 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075206 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075206 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_023509 := by
  decide +kernel

theorem g32p_supplierForest_actual_075206 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075206) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_075206
    g32p_supplierForest_actual_023509

def g32p_supplierForest_node_075227 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_075227 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075227 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018075 := by
  decide +kernel

theorem g32p_supplierForest_actual_075227 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075227) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_075227
    g32p_supplierForest_actual_018075

def g32p_supplierForest_node_075370 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_075370 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075370 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085956 := by
  decide +kernel

theorem g32p_supplierForest_actual_075370 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075370) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_075370
    g32p_supplierForest_actual_085956

def g32p_supplierForest_node_075377 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_075377 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075377 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_084638 := by
  decide +kernel

theorem g32p_supplierForest_actual_075377 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075377) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_075377
    g32p_supplierForest_actual_084638

def g32p_supplierForest_node_075433 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_075433 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075433 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_015526 := by
  decide +kernel

theorem g32p_supplierForest_actual_075433 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075433) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_075433
    g32p_supplierForest_actual_015526

def g32p_supplierForest_node_075457 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075457 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075457 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075401 := by
  decide +kernel

theorem g32p_supplierForest_actual_075457 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075457) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_075457
    g32p_supplierForest_actual_075401

def g32p_supplierForest_node_075458 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075458 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075458 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012954 := by
  decide +kernel

theorem g32p_supplierForest_actual_075458 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075458) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_075458
    g32p_supplierForest_actual_012954

def g32p_supplierForest_node_075492 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_075492 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075492 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083869 := by
  decide +kernel

theorem g32p_supplierForest_actual_075492 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075492) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 1 g32p_supplierForest_edge_075492
    g32p_supplierForest_actual_083869

def g32p_supplierForest_node_075711 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075711 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075711 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014935 := by
  decide +kernel

theorem g32p_supplierForest_actual_075711 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075711) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 3 g32p_supplierForest_edge_075711
    g32p_supplierForest_actual_014935

def g32p_supplierForest_node_075904 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_075904 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075904 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_146495 := by
  decide +kernel

theorem g32p_supplierForest_actual_075904 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075904) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_075904
    g32p_supplierForest_actual_146495

def g32p_supplierForest_node_075947 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_075947 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075947 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_150830 := by
  decide +kernel

theorem g32p_supplierForest_actual_075947 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075947) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 1 g32p_supplierForest_edge_075947
    g32p_supplierForest_actual_150830

def g32p_supplierForest_node_076192 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_076192 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076192 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_089665 := by
  decide +kernel

theorem g32p_supplierForest_actual_076192 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076192) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 3 g32p_supplierForest_edge_076192
    g32p_supplierForest_actual_089665

def g32p_supplierForest_node_076320 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_076320 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076320 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_078338 := by
  decide +kernel

theorem g32p_supplierForest_actual_076320 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076320) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 2 g32p_supplierForest_edge_076320
    g32p_supplierForest_actual_078338

def g32p_supplierForest_node_076330 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_076330 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076330 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_015879 := by
  decide +kernel

theorem g32p_supplierForest_actual_076330 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076330) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 0 g32p_supplierForest_edge_076330
    g32p_supplierForest_actual_015879

def g32p_supplierForest_node_076415 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_076415 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076415 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_013159 := by
  decide +kernel

theorem g32p_supplierForest_actual_076415 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076415) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_076415
    g32p_supplierForest_actual_013159

def g32p_supplierForest_node_076437 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076437 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076437 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014373 := by
  decide +kernel

theorem g32p_supplierForest_actual_076437 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076437) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 3 g32p_supplierForest_edge_076437
    g32p_supplierForest_actual_014373

def g32p_supplierForest_node_076511 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_076511 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076511 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013179 := by
  decide +kernel

theorem g32p_supplierForest_actual_076511 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076511) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_076511
    g32p_supplierForest_actual_013179

def g32p_supplierForest_node_076527 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_076527 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076527 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_072736 := by
  decide +kernel

theorem g32p_supplierForest_actual_076527 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076527) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_076527
    g32p_supplierForest_actual_072736

def g32p_supplierForest_node_076546 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_076546 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076546 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_020162 := by
  decide +kernel

theorem g32p_supplierForest_actual_076546 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076546) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_076546
    g32p_supplierForest_actual_020162

def g32p_supplierForest_node_076729 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_076729 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076729 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_087532 := by
  decide +kernel

theorem g32p_supplierForest_actual_076729 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076729) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_076729
    g32p_supplierForest_actual_087532

def g32p_supplierForest_node_076745 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_076745 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076745 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015439 := by
  decide +kernel

theorem g32p_supplierForest_actual_076745 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076745) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 3 g32p_supplierForest_edge_076745
    g32p_supplierForest_actual_015439

def g32p_supplierForest_node_076775 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_076775 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076775 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_016046 := by
  decide +kernel

theorem g32p_supplierForest_actual_076775 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076775) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 0 g32p_supplierForest_edge_076775
    g32p_supplierForest_actual_016046

def g32p_supplierForest_node_076813 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_076813 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076813 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_016598 := by
  decide +kernel

theorem g32p_supplierForest_actual_076813 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076813) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 0 g32p_supplierForest_edge_076813
    g32p_supplierForest_actual_016598

def g32p_supplierForest_node_076834 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_076834 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076834 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083393 := by
  decide +kernel

theorem g32p_supplierForest_actual_076834 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076834) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_076834
    g32p_supplierForest_actual_083393

def g32p_supplierForest_node_076882 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_076882 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076882 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013580 := by
  decide +kernel

theorem g32p_supplierForest_actual_076882 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076882) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 3 g32p_supplierForest_edge_076882
    g32p_supplierForest_actual_013580

def g32p_supplierForest_node_076918 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_076918 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076918 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_086545 := by
  decide +kernel

theorem g32p_supplierForest_actual_076918 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076918) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 1 g32p_supplierForest_edge_076918
    g32p_supplierForest_actual_086545

def g32p_supplierForest_node_076944 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_076944 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076944 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_072749 := by
  decide +kernel

theorem g32p_supplierForest_actual_076944 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076944) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_076944
    g32p_supplierForest_actual_072749

def g32p_supplierForest_node_076945 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_076945 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076945 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_087798 := by
  decide +kernel

theorem g32p_supplierForest_actual_076945 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076945) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_076945
    g32p_supplierForest_actual_087798

def g32p_supplierForest_node_076972 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_076972 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076972 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_017901 := by
  decide +kernel

theorem g32p_supplierForest_actual_076972 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076972) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_076972
    g32p_supplierForest_actual_017901

def g32p_supplierForest_node_077076 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_077076 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077076 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076328 := by
  decide +kernel

theorem g32p_supplierForest_actual_077076 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077076) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 1 g32p_supplierForest_edge_077076
    g32p_supplierForest_actual_076328

def g32p_supplierForest_node_077083 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_077083 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077083 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_076328 := by
  decide +kernel

theorem g32p_supplierForest_actual_077083 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077083) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 2 g32p_supplierForest_edge_077083
    g32p_supplierForest_actual_076328

def g32p_supplierForest_node_077210 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_077210 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077210 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015163 := by
  decide +kernel

theorem g32p_supplierForest_actual_077210 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077210) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 3 g32p_supplierForest_edge_077210
    g32p_supplierForest_actual_015163

def g32p_supplierForest_node_077231 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_077231 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077231 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091820 := by
  decide +kernel

theorem g32p_supplierForest_actual_077231 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077231) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_077231
    g32p_supplierForest_actual_091820

def g32p_supplierForest_node_077354 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_077354 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077354 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_096778 := by
  decide +kernel

theorem g32p_supplierForest_actual_077354 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077354) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_077354
    g32p_supplierForest_actual_096778

def g32p_supplierForest_node_077391 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_077391 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077391 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071902 := by
  decide +kernel

theorem g32p_supplierForest_actual_077391 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077391) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_077391
    g32p_supplierForest_actual_071902

def g32p_supplierForest_node_077816 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_077816 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077816 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_074337 := by
  decide +kernel

theorem g32p_supplierForest_actual_077816 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077816) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_077816
    g32p_supplierForest_actual_074337

def g32p_supplierForest_node_077885 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_077885 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077885 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074652 := by
  decide +kernel

theorem g32p_supplierForest_actual_077885 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077885) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 2 g32p_supplierForest_edge_077885
    g32p_supplierForest_actual_074652

def g32p_supplierForest_node_078047 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_078047 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078047 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_074337 := by
  decide +kernel

theorem g32p_supplierForest_actual_078047 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078047) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 0 g32p_supplierForest_edge_078047
    g32p_supplierForest_actual_074337

def g32p_supplierForest_node_078096 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_078096 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078096 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_075144 := by
  decide +kernel

theorem g32p_supplierForest_actual_078096 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078096) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_078096
    g32p_supplierForest_actual_075144

def g32p_supplierForest_node_078105 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_078105 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078105 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094995 := by
  decide +kernel

theorem g32p_supplierForest_actual_078105 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078105) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 1 g32p_supplierForest_edge_078105
    g32p_supplierForest_actual_094995

def g32p_supplierForest_node_078190 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_078190 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078190 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_149729 := by
  decide +kernel

theorem g32p_supplierForest_actual_078190 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078190) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 1 g32p_supplierForest_edge_078190
    g32p_supplierForest_actual_149729

def g32p_supplierForest_node_078302 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_078302 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078302 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015879 := by
  decide +kernel

theorem g32p_supplierForest_actual_078302 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078302) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 3 g32p_supplierForest_edge_078302
    g32p_supplierForest_actual_015879

def g32p_supplierForest_node_078503 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_078503 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078503 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_072446 := by
  decide +kernel

theorem g32p_supplierForest_actual_078503 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078503) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_078503
    g32p_supplierForest_actual_072446

def g32p_supplierForest_node_078853 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_078853 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078853 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_085792 := by
  decide +kernel

theorem g32p_supplierForest_actual_078853 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078853) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_078853
    g32p_supplierForest_actual_085792

def g32p_supplierForest_node_079094 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_079094 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079094 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_084638 := by
  decide +kernel

theorem g32p_supplierForest_actual_079094 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079094) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_079094
    g32p_supplierForest_actual_084638

def g32p_supplierForest_node_079686 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_079686 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079686 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_024232 := by
  decide +kernel

theorem g32p_supplierForest_actual_079686 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079686) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_079686
    g32p_supplierForest_actual_024232

def g32p_supplierForest_node_079690 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_079690 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079690 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_074596 := by
  decide +kernel

theorem g32p_supplierForest_actual_079690 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079690) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_079690
    g32p_supplierForest_actual_074596

def g32p_supplierForest_node_079771 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_079771 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079771 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_079427 := by
  decide +kernel

theorem g32p_supplierForest_actual_079771 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079771) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_079771
    g32p_supplierForest_actual_079427

def g32p_supplierForest_node_079773 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_079773 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079773 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_086804 := by
  decide +kernel

theorem g32p_supplierForest_actual_079773 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079773) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 1 g32p_supplierForest_edge_079773
    g32p_supplierForest_actual_086804

def g32p_supplierForest_node_079957 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_079957 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079957 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012996 := by
  decide +kernel

theorem g32p_supplierForest_actual_079957 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079957) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_079957
    g32p_supplierForest_actual_012996

def g32p_supplierForest_node_079979 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_079979 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079979 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091063 := by
  decide +kernel

theorem g32p_supplierForest_actual_079979 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079979) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_079979
    g32p_supplierForest_actual_091063

def g32p_supplierForest_node_080073 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_080073 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080073 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_018843 := by
  decide +kernel

theorem g32p_supplierForest_actual_080073 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080073) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 0 g32p_supplierForest_edge_080073
    g32p_supplierForest_actual_018843

def g32p_supplierForest_node_080136 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_080136 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080136 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_081992 := by
  decide +kernel

theorem g32p_supplierForest_actual_080136 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080136) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 1 g32p_supplierForest_edge_080136
    g32p_supplierForest_actual_081992

def g32p_supplierForest_node_080207 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_080207 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080207 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023509 := by
  decide +kernel

theorem g32p_supplierForest_actual_080207 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080207) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_080207
    g32p_supplierForest_actual_023509

def g32p_supplierForest_node_080546 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_080546 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080546 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_016046 := by
  decide +kernel

theorem g32p_supplierForest_actual_080546 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080546) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 1 g32p_supplierForest_edge_080546
    g32p_supplierForest_actual_016046

def g32p_supplierForest_node_081105 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_081105 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081105 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019734 := by
  decide +kernel

theorem g32p_supplierForest_actual_081105 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081105) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_081105
    g32p_supplierForest_actual_019734

def g32p_supplierForest_node_081174 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_081174 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081174 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_014333 := by
  decide +kernel

theorem g32p_supplierForest_actual_081174 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081174) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_081174
    g32p_supplierForest_actual_014333

def g32p_supplierForest_node_081175 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_081175 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081175 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_092641 := by
  decide +kernel

theorem g32p_supplierForest_actual_081175 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081175) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_081175
    g32p_supplierForest_actual_092641

def g32p_supplierForest_node_081247 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_081247 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081247 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019978 := by
  decide +kernel

theorem g32p_supplierForest_actual_081247 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081247) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_081247
    g32p_supplierForest_actual_019978

def g32p_supplierForest_node_081249 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_081249 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081249 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_020158 := by
  decide +kernel

theorem g32p_supplierForest_actual_081249 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081249) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 2 g32p_supplierForest_edge_081249
    g32p_supplierForest_actual_020158

def g32p_supplierForest_node_081294 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_081294 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081294 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_014854 := by
  decide +kernel

theorem g32p_supplierForest_actual_081294 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081294) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_081294
    g32p_supplierForest_actual_014854

def g32p_supplierForest_node_081441 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_081441 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081441 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_012459 := by
  decide +kernel

theorem g32p_supplierForest_actual_081441 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081441) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_081441
    g32p_supplierForest_actual_012459

def g32p_supplierForest_node_081477 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_081477 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081477 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_012470 := by
  decide +kernel

theorem g32p_supplierForest_actual_081477 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081477) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_081477
    g32p_supplierForest_actual_012470

def g32p_supplierForest_node_081496 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_081496 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081496 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_072749 := by
  decide +kernel

theorem g32p_supplierForest_actual_081496 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081496) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 1 g32p_supplierForest_edge_081496
    g32p_supplierForest_actual_072749

def g32p_supplierForest_node_081542 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_081542 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081542 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014272 := by
  decide +kernel

theorem g32p_supplierForest_actual_081542 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081542) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_081542
    g32p_supplierForest_actual_014272

def g32p_supplierForest_node_081702 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_081702 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081702 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091878 := by
  decide +kernel

theorem g32p_supplierForest_actual_081702 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081702) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 2 g32p_supplierForest_edge_081702
    g32p_supplierForest_actual_091878

def g32p_supplierForest_node_081994 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_081994 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081994 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_020162 := by
  decide +kernel

theorem g32p_supplierForest_actual_081994 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081994) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_081994
    g32p_supplierForest_actual_020162

def g32p_supplierForest_node_082013 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_082013 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082013 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073551 := by
  decide +kernel

theorem g32p_supplierForest_actual_082013 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082013) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_082013
    g32p_supplierForest_actual_073551

def g32p_supplierForest_node_082035 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_082035 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082035 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_092570 := by
  decide +kernel

theorem g32p_supplierForest_actual_082035 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082035) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_082035
    g32p_supplierForest_actual_092570

def g32p_supplierForest_node_082063 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_082063 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082063 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_077047 := by
  decide +kernel

theorem g32p_supplierForest_actual_082063 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082063) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_082063
    g32p_supplierForest_actual_077047

def g32p_supplierForest_node_082110 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_082110 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082110 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082838 := by
  decide +kernel

theorem g32p_supplierForest_actual_082110 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082110) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 1 g32p_supplierForest_edge_082110
    g32p_supplierForest_actual_082838

def g32p_supplierForest_node_082230 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_082230 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082230 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_014664 := by
  decide +kernel

theorem g32p_supplierForest_actual_082230 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082230) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 1 g32p_supplierForest_edge_082230
    g32p_supplierForest_actual_014664

def g32p_supplierForest_node_082316 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_082316 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082316 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_082311 := by
  decide +kernel

theorem g32p_supplierForest_actual_082316 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082316) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_082316
    g32p_supplierForest_actual_082311

def g32p_supplierForest_node_082334 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_082334 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082334 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021132 := by
  decide +kernel

theorem g32p_supplierForest_actual_082334 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082334) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_082334
    g32p_supplierForest_actual_021132

def g32p_supplierForest_node_082395 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_082395 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082395 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077642 := by
  decide +kernel

theorem g32p_supplierForest_actual_082395 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082395) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_082395
    g32p_supplierForest_actual_077642

def g32p_supplierForest_node_082590 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_082590 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082590 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_022318 := by
  decide +kernel

theorem g32p_supplierForest_actual_082590 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082590) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_082590
    g32p_supplierForest_actual_022318

def g32p_supplierForest_node_082662 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_082662 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082662 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100852 := by
  decide +kernel

theorem g32p_supplierForest_actual_082662 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082662) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_082662
    g32p_supplierForest_actual_100852

def g32p_supplierForest_node_082666 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_082666 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082666 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_023535 := by
  decide +kernel

theorem g32p_supplierForest_actual_082666 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082666) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_082666
    g32p_supplierForest_actual_023535

def g32p_supplierForest_node_082688 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_082688 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082688 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_020275 := by
  decide +kernel

theorem g32p_supplierForest_actual_082688 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082688) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 2 g32p_supplierForest_edge_082688
    g32p_supplierForest_actual_020275

def g32p_supplierForest_node_082862 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_082862 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082862 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_015731 := by
  decide +kernel

theorem g32p_supplierForest_actual_082862 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082862) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_082862
    g32p_supplierForest_actual_015731

def g32p_supplierForest_node_082969 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_082969 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082969 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092641 := by
  decide +kernel

theorem g32p_supplierForest_actual_082969 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082969) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_082969
    g32p_supplierForest_actual_092641

def g32p_supplierForest_node_083206 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_083206 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083206 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083628 := by
  decide +kernel

theorem g32p_supplierForest_actual_083206 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083206) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 2 g32p_supplierForest_edge_083206
    g32p_supplierForest_actual_083628

def g32p_supplierForest_node_083212 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_083212 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083212 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_080913 := by
  decide +kernel

theorem g32p_supplierForest_actual_083212 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083212) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 1 g32p_supplierForest_edge_083212
    g32p_supplierForest_actual_080913

def g32p_supplierForest_node_083215 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_083215 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083215 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_080919 := by
  decide +kernel

theorem g32p_supplierForest_actual_083215 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083215) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 1 g32p_supplierForest_edge_083215
    g32p_supplierForest_actual_080919

def g32p_supplierForest_node_083267 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_083267 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083267 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_015972 := by
  decide +kernel

theorem g32p_supplierForest_actual_083267 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083267) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_083267
    g32p_supplierForest_actual_015972

def g32p_supplierForest_node_083274 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_083274 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083274 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020275 := by
  decide +kernel

theorem g32p_supplierForest_actual_083274 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083274) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 3 g32p_supplierForest_edge_083274
    g32p_supplierForest_actual_020275

def g32p_supplierForest_node_083280 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_083280 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083280 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_071902 := by
  decide +kernel

theorem g32p_supplierForest_actual_083280 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083280) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_083280
    g32p_supplierForest_actual_071902

def g32p_supplierForest_node_083512 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_083512 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083512 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_092641 := by
  decide +kernel

theorem g32p_supplierForest_actual_083512 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083512) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_083512
    g32p_supplierForest_actual_092641

def g32p_supplierForest_node_083593 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_083593 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083593 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_086545 := by
  decide +kernel

theorem g32p_supplierForest_actual_083593 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083593) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_083593
    g32p_supplierForest_actual_086545

def g32p_supplierForest_node_083673 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_083673 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083673 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075150 := by
  decide +kernel

theorem g32p_supplierForest_actual_083673 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083673) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_083673
    g32p_supplierForest_actual_075150

def g32p_supplierForest_node_083861 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_083861 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083861 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_082081 := by
  decide +kernel

theorem g32p_supplierForest_actual_083861 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083861) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_083861
    g32p_supplierForest_actual_082081

def g32p_supplierForest_node_083881 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_083881 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083881 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_082052 := by
  decide +kernel

theorem g32p_supplierForest_actual_083881 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083881) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 2 g32p_supplierForest_edge_083881
    g32p_supplierForest_actual_082052

def g32p_supplierForest_node_083894 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_083894 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083894 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083926 := by
  decide +kernel

theorem g32p_supplierForest_actual_083894 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083894) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_083894
    g32p_supplierForest_actual_083926

def g32p_supplierForest_node_083907 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_083907 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083907 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083900 := by
  decide +kernel

theorem g32p_supplierForest_actual_083907 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083907) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 2 g32p_supplierForest_edge_083907
    g32p_supplierForest_actual_083900

def g32p_supplierForest_node_083944 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_083944 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083944 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082052 := by
  decide +kernel

theorem g32p_supplierForest_actual_083944 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083944) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 1 g32p_supplierForest_edge_083944
    g32p_supplierForest_actual_082052

def g32p_supplierForest_node_084061 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_084061 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084061 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_072749 := by
  decide +kernel

theorem g32p_supplierForest_actual_084061 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084061) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_084061
    g32p_supplierForest_actual_072749

def g32p_supplierForest_node_084091 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_084091 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084091 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_084691 := by
  decide +kernel

theorem g32p_supplierForest_actual_084091 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084091) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 3 g32p_supplierForest_edge_084091
    g32p_supplierForest_actual_084691

def g32p_supplierForest_node_084173 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_084173 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084173 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083899 := by
  decide +kernel

theorem g32p_supplierForest_actual_084173 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084173) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_084173
    g32p_supplierForest_actual_083899

def g32p_supplierForest_node_084355 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_084355 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084355 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015879 := by
  decide +kernel

theorem g32p_supplierForest_actual_084355 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084355) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 2 g32p_supplierForest_edge_084355
    g32p_supplierForest_actual_015879

def g32p_supplierForest_node_084393 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_084393 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084393 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091545 := by
  decide +kernel

theorem g32p_supplierForest_actual_084393 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084393) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_084393
    g32p_supplierForest_actual_091545

def g32p_supplierForest_node_084438 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_084438 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084438 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_084196 := by
  decide +kernel

theorem g32p_supplierForest_actual_084438 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084438) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_084438
    g32p_supplierForest_actual_084196

def g32p_supplierForest_node_084530 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084530 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084530 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_089665 := by
  decide +kernel

theorem g32p_supplierForest_actual_084530 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084530) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_084530
    g32p_supplierForest_actual_089665

def g32p_supplierForest_node_084590 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_084590 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084590 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076787 := by
  decide +kernel

theorem g32p_supplierForest_actual_084590 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084590) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 1 g32p_supplierForest_edge_084590
    g32p_supplierForest_actual_076787

def g32p_supplierForest_node_084597 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084597 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084597 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_094332 := by
  decide +kernel

theorem g32p_supplierForest_actual_084597 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084597) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 0 g32p_supplierForest_edge_084597
    g32p_supplierForest_actual_094332

def g32p_supplierForest_node_084667 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084667 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084667 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_014931 := by
  decide +kernel

theorem g32p_supplierForest_actual_084667 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084667) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_084667
    g32p_supplierForest_actual_014931

def g32p_supplierForest_node_084725 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_084725 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084725 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_095725 := by
  decide +kernel

theorem g32p_supplierForest_actual_084725 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084725) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 0 g32p_supplierForest_edge_084725
    g32p_supplierForest_actual_095725

def g32p_supplierForest_node_084754 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084754 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084754 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015495 := by
  decide +kernel

theorem g32p_supplierForest_actual_084754 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084754) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 2 g32p_supplierForest_edge_084754
    g32p_supplierForest_actual_015495

def g32p_supplierForest_node_084806 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084806 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084806 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083476 := by
  decide +kernel

theorem g32p_supplierForest_actual_084806 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084806) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_084806
    g32p_supplierForest_actual_083476

def g32p_supplierForest_node_084922 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084922 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084922 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_081531 := by
  decide +kernel

theorem g32p_supplierForest_actual_084922 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084922) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 1 g32p_supplierForest_edge_084922
    g32p_supplierForest_actual_081531

def g32p_supplierForest_node_085018 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085018 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085018 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083707 := by
  decide +kernel

theorem g32p_supplierForest_actual_085018 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085018) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 0 g32p_supplierForest_edge_085018
    g32p_supplierForest_actual_083707

def g32p_supplierForest_node_085283 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085283 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085283 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_081660 := by
  decide +kernel

theorem g32p_supplierForest_actual_085283 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085283) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 1 g32p_supplierForest_edge_085283
    g32p_supplierForest_actual_081660

def g32p_supplierForest_node_085290 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085290 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085290 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_085248 := by
  decide +kernel

theorem g32p_supplierForest_actual_085290 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085290) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_085290
    g32p_supplierForest_actual_085248

def g32p_supplierForest_node_085294 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085294 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085294 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083926 := by
  decide +kernel

theorem g32p_supplierForest_actual_085294 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085294) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_085294
    g32p_supplierForest_actual_083926

def g32p_supplierForest_node_085308 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_085308 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085308 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_150830 := by
  decide +kernel

theorem g32p_supplierForest_actual_085308 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085308) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_085308
    g32p_supplierForest_actual_150830

def g32p_supplierForest_node_085385 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085385 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085385 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020003 := by
  decide +kernel

theorem g32p_supplierForest_actual_085385 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085385) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_085385
    g32p_supplierForest_actual_020003

def g32p_supplierForest_node_085473 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_085473 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085473 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022216 := by
  decide +kernel

theorem g32p_supplierForest_actual_085473 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085473) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 1 g32p_supplierForest_edge_085473
    g32p_supplierForest_actual_022216

def g32p_supplierForest_node_085542 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_085542 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085542 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_098247 := by
  decide +kernel

theorem g32p_supplierForest_actual_085542 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085542) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_085542
    g32p_supplierForest_actual_098247

def g32p_supplierForest_node_085589 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_085589 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085589 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_100852 := by
  decide +kernel

theorem g32p_supplierForest_actual_085589 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085589) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_085589
    g32p_supplierForest_actual_100852

def g32p_supplierForest_node_085640 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_085640 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085640 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_099965 := by
  decide +kernel

theorem g32p_supplierForest_actual_085640 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085640) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_085640
    g32p_supplierForest_actual_099965

def g32p_supplierForest_node_085652 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085652 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085652 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_023565 := by
  decide +kernel

theorem g32p_supplierForest_actual_085652 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085652) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_085652
    g32p_supplierForest_actual_023565

def g32p_supplierForest_node_085694 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_085694 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085694 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083900 := by
  decide +kernel

theorem g32p_supplierForest_actual_085694 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085694) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_085694
    g32p_supplierForest_actual_083900

def g32p_supplierForest_node_085696 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085696 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085696 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083926 := by
  decide +kernel

theorem g32p_supplierForest_actual_085696 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085696) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_085696
    g32p_supplierForest_actual_083926

def g32p_supplierForest_node_085755 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085755 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085755 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015439 := by
  decide +kernel

theorem g32p_supplierForest_actual_085755 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085755) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_085755
    g32p_supplierForest_actual_015439

def g32p_supplierForest_node_085850 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_085850 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085850 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_081959 := by
  decide +kernel

theorem g32p_supplierForest_actual_085850 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085850) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 2 g32p_supplierForest_edge_085850
    g32p_supplierForest_actual_081959

def g32p_supplierForest_node_085867 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_085867 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085867 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_081992 := by
  decide +kernel

theorem g32p_supplierForest_actual_085867 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085867) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 2 g32p_supplierForest_edge_085867
    g32p_supplierForest_actual_081992

def g32p_supplierForest_node_085962 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_085962 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085962 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083146 := by
  decide +kernel

theorem g32p_supplierForest_actual_085962 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085962) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 2 g32p_supplierForest_edge_085962
    g32p_supplierForest_actual_083146

def g32p_supplierForest_node_086002 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_086002 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086002 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015100 := by
  decide +kernel

theorem g32p_supplierForest_actual_086002 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086002) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_086002
    g32p_supplierForest_actual_015100

def g32p_supplierForest_node_086038 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_086038 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086038 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_084638 := by
  decide +kernel

theorem g32p_supplierForest_actual_086038 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086038) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_086038
    g32p_supplierForest_actual_084638

def g32p_supplierForest_node_086189 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_086189 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086189 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085792 := by
  decide +kernel

theorem g32p_supplierForest_actual_086189 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086189) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_086189
    g32p_supplierForest_actual_085792

def g32p_supplierForest_node_086227 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_086227 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086227 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_081959 := by
  decide +kernel

theorem g32p_supplierForest_actual_086227 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086227) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 1 g32p_supplierForest_edge_086227
    g32p_supplierForest_actual_081959

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_086237 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_086237 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086237 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_082267 := by
  decide +kernel

theorem g32p_supplierForest_actual_086237 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086237) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 2 g32p_supplierForest_edge_086237
    g32p_supplierForest_actual_082267

def g32p_supplierForest_node_086327 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_086327 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086327 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087111 := by
  decide +kernel

theorem g32p_supplierForest_actual_086327 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086327) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 2 g32p_supplierForest_edge_086327
    g32p_supplierForest_actual_087111

def g32p_supplierForest_node_086435 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_086435 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086435 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019328 := by
  decide +kernel

theorem g32p_supplierForest_actual_086435 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086435) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_086435
    g32p_supplierForest_actual_019328

def g32p_supplierForest_node_086506 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_086506 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086506 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082081 := by
  decide +kernel

theorem g32p_supplierForest_actual_086506 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086506) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_086506
    g32p_supplierForest_actual_082081

def g32p_supplierForest_node_086621 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_086621 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086621 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_085792 := by
  decide +kernel

theorem g32p_supplierForest_actual_086621 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086621) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_086621
    g32p_supplierForest_actual_085792

def g32p_supplierForest_node_086708 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_086708 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086708 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_097467 := by
  decide +kernel

theorem g32p_supplierForest_actual_086708 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086708) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 0 g32p_supplierForest_edge_086708
    g32p_supplierForest_actual_097467

def g32p_supplierForest_node_087069 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_087069 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087069 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082311 := by
  decide +kernel

theorem g32p_supplierForest_actual_087069 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087069) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_087069
    g32p_supplierForest_actual_082311

def g32p_supplierForest_node_087358 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_087358 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087358 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081660 := by
  decide +kernel

theorem g32p_supplierForest_actual_087358 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087358) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 0 g32p_supplierForest_edge_087358
    g32p_supplierForest_actual_081660

def g32p_supplierForest_node_087489 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087489 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087489 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091660 := by
  decide +kernel

theorem g32p_supplierForest_actual_087489 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087489) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 0 g32p_supplierForest_edge_087489
    g32p_supplierForest_actual_091660

def g32p_supplierForest_node_087574 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_087574 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087574 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016049 := by
  decide +kernel

theorem g32p_supplierForest_actual_087574 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087574) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_087574
    g32p_supplierForest_actual_016049

def g32p_supplierForest_node_087653 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_087653 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087653 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082813 := by
  decide +kernel

theorem g32p_supplierForest_actual_087653 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087653) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 0 g32p_supplierForest_edge_087653
    g32p_supplierForest_actual_082813

def g32p_supplierForest_node_087745 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_087745 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087745 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_023095 := by
  decide +kernel

theorem g32p_supplierForest_actual_087745 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087745) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 1 g32p_supplierForest_edge_087745
    g32p_supplierForest_actual_023095

def g32p_supplierForest_node_087760 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_087760 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087760 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_022216 := by
  decide +kernel

theorem g32p_supplierForest_actual_087760 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087760) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 2 g32p_supplierForest_edge_087760
    g32p_supplierForest_actual_022216

def g32p_supplierForest_node_087979 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087979 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087979 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_072236 := by
  decide +kernel

theorem g32p_supplierForest_actual_087979 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087979) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_087979
    g32p_supplierForest_actual_072236

def g32p_supplierForest_node_087982 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_087982 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087982 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_087111 := by
  decide +kernel

theorem g32p_supplierForest_actual_087982 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087982) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_087982
    g32p_supplierForest_actual_087111

def g32p_supplierForest_node_088033 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088033 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088033 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_147664 := by
  decide +kernel

theorem g32p_supplierForest_actual_088033 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088033) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 2 g32p_supplierForest_edge_088033
    g32p_supplierForest_actual_147664

def g32p_supplierForest_node_088037 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_088037 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088037 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015731 := by
  decide +kernel

theorem g32p_supplierForest_actual_088037 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088037) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 3 g32p_supplierForest_edge_088037
    g32p_supplierForest_actual_015731

def g32p_supplierForest_node_088102 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088102 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088102 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075839 := by
  decide +kernel

theorem g32p_supplierForest_actual_088102 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088102) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_088102
    g32p_supplierForest_actual_075839

def g32p_supplierForest_node_088185 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088185 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088185 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_085469 := by
  decide +kernel

theorem g32p_supplierForest_actual_088185 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088185) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 1 g32p_supplierForest_edge_088185
    g32p_supplierForest_actual_085469

def g32p_supplierForest_node_088327 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088327 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088327 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083273 := by
  decide +kernel

theorem g32p_supplierForest_actual_088327 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088327) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 1 g32p_supplierForest_edge_088327
    g32p_supplierForest_actual_083273

def g32p_supplierForest_node_088434 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_088434 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088434 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_098000 := by
  decide +kernel

theorem g32p_supplierForest_actual_088434 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088434) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_088434
    g32p_supplierForest_actual_098000

def g32p_supplierForest_node_088461 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088461 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088461 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083358 := by
  decide +kernel

theorem g32p_supplierForest_actual_088461 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088461) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 2 g32p_supplierForest_edge_088461
    g32p_supplierForest_actual_083358

def g32p_supplierForest_node_088499 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_088499 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088499 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094582 := by
  decide +kernel

theorem g32p_supplierForest_actual_088499 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088499) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_088499
    g32p_supplierForest_actual_094582

def g32p_supplierForest_node_088609 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_088609 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088609 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094536 := by
  decide +kernel

theorem g32p_supplierForest_actual_088609 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088609) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 1 g32p_supplierForest_edge_088609
    g32p_supplierForest_actual_094536

def g32p_supplierForest_node_088645 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_088645 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088645 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083869 := by
  decide +kernel

theorem g32p_supplierForest_actual_088645 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088645) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 2 g32p_supplierForest_edge_088645
    g32p_supplierForest_actual_083869

def g32p_supplierForest_node_088901 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088901 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088901 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_077144 := by
  decide +kernel

theorem g32p_supplierForest_actual_088901 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088901) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 2 g32p_supplierForest_edge_088901
    g32p_supplierForest_actual_077144

def g32p_supplierForest_node_088929 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_088929 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088929 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085248 := by
  decide +kernel

theorem g32p_supplierForest_actual_088929 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088929) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_088929
    g32p_supplierForest_actual_085248

def g32p_supplierForest_node_088949 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨2, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_088949 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088949 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015395 := by
  decide +kernel

theorem g32p_supplierForest_actual_088949 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088949) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 2 g32p_supplierForest_edge_088949
    g32p_supplierForest_actual_015395

def g32p_supplierForest_node_088971 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088971 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088971 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085342 := by
  decide +kernel

theorem g32p_supplierForest_actual_088971 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088971) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_088971
    g32p_supplierForest_actual_085342

def g32p_supplierForest_node_089027 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_089027 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089027 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_088378 := by
  decide +kernel

theorem g32p_supplierForest_actual_089027 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089027) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 1 g32p_supplierForest_edge_089027
    g32p_supplierForest_actual_088378

def g32p_supplierForest_node_089058 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_089058 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089058 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_098879 := by
  decide +kernel

theorem g32p_supplierForest_actual_089058 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089058) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 0 g32p_supplierForest_edge_089058
    g32p_supplierForest_actual_098879

def g32p_supplierForest_node_089110 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089110 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089110 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083911 := by
  decide +kernel

theorem g32p_supplierForest_actual_089110 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089110) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_089110
    g32p_supplierForest_actual_083911

def g32p_supplierForest_node_089361 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_089361 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089361 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_098000 := by
  decide +kernel

theorem g32p_supplierForest_actual_089361 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089361) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 3 g32p_supplierForest_edge_089361
    g32p_supplierForest_actual_098000

def g32p_supplierForest_node_089453 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089453 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089453 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_087532 := by
  decide +kernel

theorem g32p_supplierForest_actual_089453 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089453) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_089453
    g32p_supplierForest_actual_087532

def g32p_supplierForest_node_089458 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_089458 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089458 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_016598 := by
  decide +kernel

theorem g32p_supplierForest_actual_089458 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089458) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 2 g32p_supplierForest_edge_089458
    g32p_supplierForest_actual_016598

def g32p_supplierForest_node_089473 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089473 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089473 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091656 := by
  decide +kernel

theorem g32p_supplierForest_actual_089473 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089473) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 0 g32p_supplierForest_edge_089473
    g32p_supplierForest_actual_091656

def g32p_supplierForest_node_089829 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_089829 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089829 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_021734 := by
  decide +kernel

theorem g32p_supplierForest_actual_089829 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089829) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 1 g32p_supplierForest_edge_089829
    g32p_supplierForest_actual_021734

def g32p_supplierForest_node_089881 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_089881 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089881 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083064 := by
  decide +kernel

theorem g32p_supplierForest_actual_089881 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089881) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 2 g32p_supplierForest_edge_089881
    g32p_supplierForest_actual_083064

def g32p_supplierForest_node_090008 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_090008 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090008 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023690 := by
  decide +kernel

theorem g32p_supplierForest_actual_090008 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090008) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_090008
    g32p_supplierForest_actual_023690

def g32p_supplierForest_node_090167 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_090167 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090167 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087532 := by
  decide +kernel

theorem g32p_supplierForest_actual_090167 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090167) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_090167
    g32p_supplierForest_actual_087532

def g32p_supplierForest_node_090176 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_090176 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090176 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023565 := by
  decide +kernel

theorem g32p_supplierForest_actual_090176 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090176) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_090176
    g32p_supplierForest_actual_023565

def g32p_supplierForest_node_090318 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090318 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090318 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091228 := by
  decide +kernel

theorem g32p_supplierForest_actual_090318 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090318) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 2 g32p_supplierForest_edge_090318
    g32p_supplierForest_actual_091228

def g32p_supplierForest_node_090340 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090340 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090340 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083358 := by
  decide +kernel

theorem g32p_supplierForest_actual_090340 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090340) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 1 g32p_supplierForest_edge_090340
    g32p_supplierForest_actual_083358

def g32p_supplierForest_node_090371 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_090371 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090371 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083393 := by
  decide +kernel

theorem g32p_supplierForest_actual_090371 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090371) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 2 g32p_supplierForest_edge_090371
    g32p_supplierForest_actual_083393

def g32p_supplierForest_node_090379 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090379 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090379 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088378 := by
  decide +kernel

theorem g32p_supplierForest_actual_090379 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090379) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_090379
    g32p_supplierForest_actual_088378

def g32p_supplierForest_node_090534 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090534 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090534 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_020002 := by
  decide +kernel

theorem g32p_supplierForest_actual_090534 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090534) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_090534
    g32p_supplierForest_actual_020002

def g32p_supplierForest_node_090638 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090638 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090638 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_080919 := by
  decide +kernel

theorem g32p_supplierForest_actual_090638 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090638) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 3 g32p_supplierForest_edge_090638
    g32p_supplierForest_actual_080919

def g32p_supplierForest_node_091121 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091121 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091121 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076787 := by
  decide +kernel

theorem g32p_supplierForest_actual_091121 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091121) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 3 g32p_supplierForest_edge_091121
    g32p_supplierForest_actual_076787

def g32p_supplierForest_node_091162 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-2, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_091162 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091162 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_091656 := by
  decide +kernel

theorem g32p_supplierForest_actual_091162 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091162) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 3 g32p_supplierForest_edge_091162
    g32p_supplierForest_actual_091656

def g32p_supplierForest_node_091558 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091558 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091558 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091733 := by
  decide +kernel

theorem g32p_supplierForest_actual_091558 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091558) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 0 g32p_supplierForest_edge_091558
    g32p_supplierForest_actual_091733

def g32p_supplierForest_node_091631 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_091631 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091631 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_101357 := by
  decide +kernel

theorem g32p_supplierForest_actual_091631 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091631) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 1 g32p_supplierForest_edge_091631
    g32p_supplierForest_actual_101357

def g32p_supplierForest_node_091655 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091655 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091655 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014664 := by
  decide +kernel

theorem g32p_supplierForest_actual_091655 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091655) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 3 g32p_supplierForest_edge_091655
    g32p_supplierForest_actual_014664

def g32p_supplierForest_node_091699 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_091699 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091699 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_101064 := by
  decide +kernel

theorem g32p_supplierForest_actual_091699 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091699) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_091699
    g32p_supplierForest_actual_101064

def g32p_supplierForest_node_091761 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_091761 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091761 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_072236 := by
  decide +kernel

theorem g32p_supplierForest_actual_091761 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091761) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_091761
    g32p_supplierForest_actual_072236

def g32p_supplierForest_node_091821 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_091821 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091821 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_084196 := by
  decide +kernel

theorem g32p_supplierForest_actual_091821 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091821) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_091821
    g32p_supplierForest_actual_084196

def g32p_supplierForest_node_091947 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091947 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091947 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_085956 := by
  decide +kernel

theorem g32p_supplierForest_actual_091947 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091947) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_091947
    g32p_supplierForest_actual_085956

def g32p_supplierForest_node_091998 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_091998 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091998 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083911 := by
  decide +kernel

theorem g32p_supplierForest_actual_091998 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091998) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 2 g32p_supplierForest_edge_091998
    g32p_supplierForest_actual_083911

def g32p_supplierForest_node_092219 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092219 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092219 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_024232 := by
  decide +kernel

theorem g32p_supplierForest_actual_092219 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092219) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_092219
    g32p_supplierForest_actual_024232

def g32p_supplierForest_node_092319 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092319 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092319 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_101156 := by
  decide +kernel

theorem g32p_supplierForest_actual_092319 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092319) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 0 g32p_supplierForest_edge_092319
    g32p_supplierForest_actual_101156

def g32p_supplierForest_node_092543 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092543 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092543 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091442 := by
  decide +kernel

theorem g32p_supplierForest_actual_092543 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092543) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 0 g32p_supplierForest_edge_092543
    g32p_supplierForest_actual_091442

def g32p_supplierForest_node_092549 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_092549 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092549 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075401 := by
  decide +kernel

theorem g32p_supplierForest_actual_092549 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092549) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_092549
    g32p_supplierForest_actual_075401

def g32p_supplierForest_node_092576 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_092576 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092576 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092570 := by
  decide +kernel

theorem g32p_supplierForest_actual_092576 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092576) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_092576
    g32p_supplierForest_actual_092570

def g32p_supplierForest_node_092598 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_092598 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092598 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_092570 := by
  decide +kernel

theorem g32p_supplierForest_actual_092598 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092598) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_092598
    g32p_supplierForest_actual_092570

def g32p_supplierForest_node_092678 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_092678 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092678 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_146136 := by
  decide +kernel

theorem g32p_supplierForest_actual_092678 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092678) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 3 g32p_supplierForest_edge_092678
    g32p_supplierForest_actual_146136

def g32p_supplierForest_node_092683 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_092683 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092683 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_082813 := by
  decide +kernel

theorem g32p_supplierForest_actual_092683 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092683) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_092683
    g32p_supplierForest_actual_082813

def g32p_supplierForest_node_092695 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_092695 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092695 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_074596 := by
  decide +kernel

theorem g32p_supplierForest_actual_092695 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092695) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_092695
    g32p_supplierForest_actual_074596

def g32p_supplierForest_node_092764 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092764 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092764 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022903 := by
  decide +kernel

theorem g32p_supplierForest_actual_092764 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092764) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_092764
    g32p_supplierForest_actual_022903

def g32p_supplierForest_node_092777 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092777 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092777 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_082052 := by
  decide +kernel

theorem g32p_supplierForest_actual_092777 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092777) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 3 g32p_supplierForest_edge_092777
    g32p_supplierForest_actual_082052

def g32p_supplierForest_node_092808 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092808 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092808 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098247 := by
  decide +kernel

theorem g32p_supplierForest_actual_092808 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092808) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_092808
    g32p_supplierForest_actual_098247

def g32p_supplierForest_node_092928 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_092928 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092928 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_089665 := by
  decide +kernel

theorem g32p_supplierForest_actual_092928 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092928) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_092928
    g32p_supplierForest_actual_089665

def g32p_supplierForest_node_092938 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092938 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092938 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014333 := by
  decide +kernel

theorem g32p_supplierForest_actual_092938 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092938) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_092938
    g32p_supplierForest_actual_014333

def g32p_supplierForest_node_093237 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093237 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093237 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073909 := by
  decide +kernel

theorem g32p_supplierForest_actual_093237 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093237) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_093237
    g32p_supplierForest_actual_073909

def g32p_supplierForest_node_093263 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_093263 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093263 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_075150 := by
  decide +kernel

theorem g32p_supplierForest_actual_093263 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093263) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 2 g32p_supplierForest_edge_093263
    g32p_supplierForest_actual_075150

def g32p_supplierForest_node_093309 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093309 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093309 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_072236 := by
  decide +kernel

theorem g32p_supplierForest_actual_093309 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093309) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 0 g32p_supplierForest_edge_093309
    g32p_supplierForest_actual_072236

def g32p_supplierForest_node_093315 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093315 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093315 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_079427 := by
  decide +kernel

theorem g32p_supplierForest_actual_093315 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093315) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_093315
    g32p_supplierForest_actual_079427

def g32p_supplierForest_node_093485 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093485 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093485 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_013869 := by
  decide +kernel

theorem g32p_supplierForest_actual_093485 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093485) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 1 g32p_supplierForest_edge_093485
    g32p_supplierForest_actual_013869

def g32p_supplierForest_node_093559 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093559 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093559 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_094332 := by
  decide +kernel

theorem g32p_supplierForest_actual_093559 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093559) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_093559
    g32p_supplierForest_actual_094332

def g32p_supplierForest_node_093751 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093751 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093751 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_100984 := by
  decide +kernel

theorem g32p_supplierForest_actual_093751 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093751) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_093751
    g32p_supplierForest_actual_100984

def g32p_supplierForest_node_093830 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_093830 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093830 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_096620 := by
  decide +kernel

theorem g32p_supplierForest_actual_093830 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093830) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_093830
    g32p_supplierForest_actual_096620

def g32p_supplierForest_node_093852 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093852 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093852 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083273 := by
  decide +kernel

theorem g32p_supplierForest_actual_093852 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093852) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 2 g32p_supplierForest_edge_093852
    g32p_supplierForest_actual_083273

def g32p_supplierForest_node_093891 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093891 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093891 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_078463 := by
  decide +kernel

theorem g32p_supplierForest_actual_093891 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093891) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_093891
    g32p_supplierForest_actual_078463

def g32p_supplierForest_node_094271 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094271 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094271 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_097729 := by
  decide +kernel

theorem g32p_supplierForest_actual_094271 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094271) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 0 g32p_supplierForest_edge_094271
    g32p_supplierForest_actual_097729

def g32p_supplierForest_node_094541 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094541 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094541 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_018903 := by
  decide +kernel

theorem g32p_supplierForest_actual_094541 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094541) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_094541
    g32p_supplierForest_actual_018903

def g32p_supplierForest_node_094594 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094594 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094594 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_094582 := by
  decide +kernel

theorem g32p_supplierForest_actual_094594 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094594) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_094594
    g32p_supplierForest_actual_094582

def g32p_supplierForest_node_094645 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_094645 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094645 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_091878 := by
  decide +kernel

theorem g32p_supplierForest_actual_094645 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094645) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 1 g32p_supplierForest_edge_094645
    g32p_supplierForest_actual_091878

def g32p_supplierForest_node_094656 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_094656 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094656 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083628 := by
  decide +kernel

theorem g32p_supplierForest_actual_094656 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094656) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 0 g32p_supplierForest_edge_094656
    g32p_supplierForest_actual_083628

def g32p_supplierForest_node_094672 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_094672 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094672 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021154 := by
  decide +kernel

theorem g32p_supplierForest_actual_094672 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094672) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_094672
    g32p_supplierForest_actual_021154

def g32p_supplierForest_node_094708 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094708 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094708 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146136 := by
  decide +kernel

theorem g32p_supplierForest_actual_094708 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094708) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_094708
    g32p_supplierForest_actual_146136

def g32p_supplierForest_node_094922 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_094922 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094922 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_082813 := by
  decide +kernel

theorem g32p_supplierForest_actual_094922 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094922) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_094922
    g32p_supplierForest_actual_082813

def g32p_supplierForest_node_095173 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095173 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095173 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083967 := by
  decide +kernel

theorem g32p_supplierForest_actual_095173 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095173) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 0 g32p_supplierForest_edge_095173
    g32p_supplierForest_actual_083967

def g32p_supplierForest_node_095269 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095269 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095269 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073917 := by
  decide +kernel

theorem g32p_supplierForest_actual_095269 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095269) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_095269
    g32p_supplierForest_actual_073917

def g32p_supplierForest_node_095270 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095270 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095270 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146495 := by
  decide +kernel

theorem g32p_supplierForest_actual_095270 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095270) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 0 g32p_supplierForest_edge_095270
    g32p_supplierForest_actual_146495

def g32p_supplierForest_node_095851 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_095851 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095851 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012630 := by
  decide +kernel

theorem g32p_supplierForest_actual_095851 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095851) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 3 g32p_supplierForest_edge_095851
    g32p_supplierForest_actual_012630

def g32p_supplierForest_node_095901 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095901 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095901 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073640 := by
  decide +kernel

theorem g32p_supplierForest_actual_095901 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095901) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_095901
    g32p_supplierForest_actual_073640

def g32p_supplierForest_node_095914 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095914 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095914 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100317 := by
  decide +kernel

theorem g32p_supplierForest_actual_095914 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095914) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_095914
    g32p_supplierForest_actual_100317

def g32p_supplierForest_node_096027 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_096027 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096027 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_097933 := by
  decide +kernel

theorem g32p_supplierForest_actual_096027 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096027) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_096027
    g32p_supplierForest_actual_097933

def g32p_supplierForest_node_096068 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096068 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096068 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085956 := by
  decide +kernel

theorem g32p_supplierForest_actual_096068 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096068) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_096068
    g32p_supplierForest_actual_085956

def g32p_supplierForest_node_096088 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096088 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096088 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_095894 := by
  decide +kernel

theorem g32p_supplierForest_actual_096088 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096088) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 3 g32p_supplierForest_edge_096088
    g32p_supplierForest_actual_095894

def g32p_supplierForest_node_096169 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_096169 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096169 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083911 := by
  decide +kernel

theorem g32p_supplierForest_actual_096169 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096169) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 3 g32p_supplierForest_edge_096169
    g32p_supplierForest_actual_083911

def g32p_supplierForest_node_096191 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096191 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096191 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019112 := by
  decide +kernel

theorem g32p_supplierForest_actual_096191 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096191) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_096191
    g32p_supplierForest_actual_019112

def g32p_supplierForest_node_096209 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096209 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096209 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095894 := by
  decide +kernel

theorem g32p_supplierForest_actual_096209 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096209) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 2 g32p_supplierForest_edge_096209
    g32p_supplierForest_actual_095894

def g32p_supplierForest_node_096362 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096362 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096362 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_098248 := by
  decide +kernel

theorem g32p_supplierForest_actual_096362 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096362) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_096362
    g32p_supplierForest_actual_098248

def g32p_supplierForest_node_096525 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096525 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096525 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100984 := by
  decide +kernel

theorem g32p_supplierForest_actual_096525 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096525) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_096525
    g32p_supplierForest_actual_100984

def g32p_supplierForest_node_096624 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096624 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096624 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096778 := by
  decide +kernel

theorem g32p_supplierForest_actual_096624 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096624) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_096624
    g32p_supplierForest_actual_096778

def g32p_supplierForest_node_096752 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_096752 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096752 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_098874 := by
  decide +kernel

theorem g32p_supplierForest_actual_096752 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096752) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_096752
    g32p_supplierForest_actual_098874

def g32p_supplierForest_node_097053 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097053 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097053 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_098846 := by
  decide +kernel

theorem g32p_supplierForest_actual_097053 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097053) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 3 g32p_supplierForest_edge_097053
    g32p_supplierForest_actual_098846

def g32p_supplierForest_node_097056 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097056 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097056 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022177 := by
  decide +kernel

theorem g32p_supplierForest_actual_097056 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097056) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_097056
    g32p_supplierForest_actual_022177

def g32p_supplierForest_node_097180 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097180 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097180 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_087111 := by
  decide +kernel

theorem g32p_supplierForest_actual_097180 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097180) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 3 g32p_supplierForest_edge_097180
    g32p_supplierForest_actual_087111

def g32p_supplierForest_node_097223 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097223 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097223 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083967 := by
  decide +kernel

theorem g32p_supplierForest_actual_097223 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097223) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_097223
    g32p_supplierForest_actual_083967

def g32p_supplierForest_node_097265 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_097265 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097265 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073909 := by
  decide +kernel

theorem g32p_supplierForest_actual_097265 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097265) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_097265
    g32p_supplierForest_actual_073909

def g32p_supplierForest_node_097411 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097411 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097411 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_071825 := by
  decide +kernel

theorem g32p_supplierForest_actual_097411 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097411) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 3 g32p_supplierForest_edge_097411
    g32p_supplierForest_actual_071825

def g32p_supplierForest_node_097425 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097425 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097425 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097076 := by
  decide +kernel

theorem g32p_supplierForest_actual_097425 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097425) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 1 g32p_supplierForest_edge_097425
    g32p_supplierForest_actual_097076

def g32p_supplierForest_node_097542 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_097542 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097542 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076128 := by
  decide +kernel

theorem g32p_supplierForest_actual_097542 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097542) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 0 g32p_supplierForest_edge_097542
    g32p_supplierForest_actual_076128

def g32p_supplierForest_node_097878 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_097878 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097878 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012665 := by
  decide +kernel

theorem g32p_supplierForest_actual_097878 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097878) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_097878
    g32p_supplierForest_actual_012665

def g32p_supplierForest_node_097898 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097898 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097898 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_017977 := by
  decide +kernel

theorem g32p_supplierForest_actual_097898 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097898) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_097898
    g32p_supplierForest_actual_017977

def g32p_supplierForest_node_097901 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097901 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097901 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_100852 := by
  decide +kernel

theorem g32p_supplierForest_actual_097901 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097901) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_097901
    g32p_supplierForest_actual_100852

def g32p_supplierForest_node_097968 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097968 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097968 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_082089 := by
  decide +kernel

theorem g32p_supplierForest_actual_097968 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097968) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_097968
    g32p_supplierForest_actual_082089

def g32p_supplierForest_node_098016 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098016 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098016 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073917 := by
  decide +kernel

theorem g32p_supplierForest_actual_098016 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098016) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_098016
    g32p_supplierForest_actual_073917

def g32p_supplierForest_node_098085 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098085 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098085 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_101064 := by
  decide +kernel

theorem g32p_supplierForest_actual_098085 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098085) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_098085
    g32p_supplierForest_actual_101064

def g32p_supplierForest_node_098171 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098171 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098171 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_101156 := by
  decide +kernel

theorem g32p_supplierForest_actual_098171 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098171) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_098171
    g32p_supplierForest_actual_101156

def g32p_supplierForest_node_098208 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098208 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098208 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076787 := by
  decide +kernel

theorem g32p_supplierForest_actual_098208 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098208) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 0 g32p_supplierForest_edge_098208
    g32p_supplierForest_actual_076787

def g32p_supplierForest_node_098235 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_098235 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098235 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073551 := by
  decide +kernel

theorem g32p_supplierForest_actual_098235 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098235) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_098235
    g32p_supplierForest_actual_073551

def g32p_supplierForest_node_098241 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_098241 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098241 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_080913 := by
  decide +kernel

theorem g32p_supplierForest_actual_098241 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098241) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_098241
    g32p_supplierForest_actual_080913

def g32p_supplierForest_node_098563 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098563 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098563 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077780 := by
  decide +kernel

theorem g32p_supplierForest_actual_098563 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098563) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 3 g32p_supplierForest_edge_098563
    g32p_supplierForest_actual_077780

def g32p_supplierForest_node_098655 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_098655 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098655 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077047 := by
  decide +kernel

theorem g32p_supplierForest_actual_098655 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098655) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 3 g32p_supplierForest_edge_098655
    g32p_supplierForest_actual_077047

def g32p_supplierForest_node_098754 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_098754 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098754 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085733 := by
  decide +kernel

theorem g32p_supplierForest_actual_098754 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098754) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 0 g32p_supplierForest_edge_098754
    g32p_supplierForest_actual_085733

def g32p_supplierForest_node_098762 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098762 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098762 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_082089 := by
  decide +kernel

theorem g32p_supplierForest_actual_098762 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098762) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 3 g32p_supplierForest_edge_098762
    g32p_supplierForest_actual_082089

def g32p_supplierForest_node_099027 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_099027 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099027 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091656 := by
  decide +kernel

theorem g32p_supplierForest_actual_099027 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099027) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 2 g32p_supplierForest_edge_099027
    g32p_supplierForest_actual_091656

def g32p_supplierForest_node_099251 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_099251 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099251 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_091733 := by
  decide +kernel

theorem g32p_supplierForest_actual_099251 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099251) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 3 g32p_supplierForest_edge_099251
    g32p_supplierForest_actual_091733

def g32p_supplierForest_node_099336 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_099336 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099336 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076128 := by
  decide +kernel

theorem g32p_supplierForest_actual_099336 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099336) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 3 g32p_supplierForest_edge_099336
    g32p_supplierForest_actual_076128

def g32p_supplierForest_node_099539 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_099539 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099539 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_152262 := by
  decide +kernel

theorem g32p_supplierForest_actual_099539 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099539) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_099539
    g32p_supplierForest_actual_152262

def g32p_supplierForest_node_099666 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_099666 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099666 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098248 := by
  decide +kernel

theorem g32p_supplierForest_actual_099666 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099666) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_099666
    g32p_supplierForest_actual_098248

def g32p_supplierForest_node_099680 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_099680 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099680 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091660 := by
  decide +kernel

theorem g32p_supplierForest_actual_099680 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099680) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 2 g32p_supplierForest_edge_099680
    g32p_supplierForest_actual_091660

def g32p_supplierForest_node_099821 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_099821 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099821 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098879 := by
  decide +kernel

theorem g32p_supplierForest_actual_099821 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099821) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_099821
    g32p_supplierForest_actual_098879

def g32p_supplierForest_node_099916 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_099916 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099916 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_099369 := by
  decide +kernel

theorem g32p_supplierForest_actual_099916 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099916) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_099916
    g32p_supplierForest_actual_099369

def g32p_supplierForest_node_100349 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_100349 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_100349 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101011 := by
  decide +kernel

theorem g32p_supplierForest_actual_100349 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_100349) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_100349
    g32p_supplierForest_actual_101011

def g32p_supplierForest_node_100401 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_100401 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_100401 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_023683 := by
  decide +kernel

theorem g32p_supplierForest_actual_100401 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_100401) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_100401
    g32p_supplierForest_actual_023683

def g32p_supplierForest_node_100407 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_100407 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_100407 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_023690 := by
  decide +kernel

theorem g32p_supplierForest_actual_100407 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_100407) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_100407
    g32p_supplierForest_actual_023690

def g32p_supplierForest_node_100548 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_100548 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_100548 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101281 := by
  decide +kernel

theorem g32p_supplierForest_actual_100548 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_100548) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_100548
    g32p_supplierForest_actual_101281

def g32p_supplierForest_node_100562 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_100562 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_100562 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101064 := by
  decide +kernel

theorem g32p_supplierForest_actual_100562 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_100562) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_100562
    g32p_supplierForest_actual_101064

def g32p_supplierForest_node_100598 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_100598 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_100598 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_023095 := by
  decide +kernel

theorem g32p_supplierForest_actual_100598 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_100598) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 3 g32p_supplierForest_edge_100598
    g32p_supplierForest_actual_023095

def g32p_supplierForest_node_100631 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_100631 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_100631 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_022177 := by
  decide +kernel

theorem g32p_supplierForest_actual_100631 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_100631) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_100631
    g32p_supplierForest_actual_022177

def g32p_supplierForest_node_100963 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_100963 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_100963 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013337 := by
  decide +kernel

theorem g32p_supplierForest_actual_100963 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_100963) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_100963
    g32p_supplierForest_actual_013337

def g32p_supplierForest_node_101034 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_101034 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101034 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013556 := by
  decide +kernel

theorem g32p_supplierForest_actual_101034 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101034) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_101034
    g32p_supplierForest_actual_013556

def g32p_supplierForest_node_101035 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_101035 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101035 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078463 := by
  decide +kernel

theorem g32p_supplierForest_actual_101035 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101035) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_101035
    g32p_supplierForest_actual_078463

def g32p_supplierForest_node_101389 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_101389 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101389 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086545 := by
  decide +kernel

theorem g32p_supplierForest_actual_101389 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101389) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_101389
    g32p_supplierForest_actual_086545

def g32p_supplierForest_node_101592 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_101592 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101592 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_147768 := by
  decide +kernel

theorem g32p_supplierForest_actual_101592 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101592) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_101592
    g32p_supplierForest_actual_147768

def g32p_supplierForest_node_101704 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_101704 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101704 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_100984 := by
  decide +kernel

theorem g32p_supplierForest_actual_101704 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101704) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 3 g32p_supplierForest_edge_101704
    g32p_supplierForest_actual_100984

def g32p_supplierForest_node_101793 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_101793 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101793 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_098879 := by
  decide +kernel

theorem g32p_supplierForest_actual_101793 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101793) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_101793
    g32p_supplierForest_actual_098879

def g32p_supplierForest_node_101889 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_101889 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101889 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098874 := by
  decide +kernel

theorem g32p_supplierForest_actual_101889 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101889) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_101889
    g32p_supplierForest_actual_098874

def g32p_supplierForest_node_101893 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_101893 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101893 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_040144 := by
  decide +kernel

theorem g32p_supplierForest_actual_101893 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101893) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_101893
    g32p_supplierForest_actual_040144

def g32p_supplierForest_node_101947 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_101947 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101947 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_113085 := by
  decide +kernel

theorem g32p_supplierForest_actual_101947 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101947) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_101947
    g32p_supplierForest_actual_113085

def g32p_supplierForest_node_101956 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_101956 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101956 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_024604 := by
  decide +kernel

theorem g32p_supplierForest_actual_101956 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101956) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_101956
    g32p_supplierForest_actual_024604

def g32p_supplierForest_node_101975 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_101975 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101975 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_037937 := by
  decide +kernel

theorem g32p_supplierForest_actual_101975 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101975) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_101975
    g32p_supplierForest_actual_037937

def g32p_supplierForest_node_102006 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_102006 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_102006 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_035033 := by
  decide +kernel

theorem g32p_supplierForest_actual_102006 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_102006) ∧
        IsConj g (g32p_literalRepresentative 64) := by
  exact g32p_archive_step_lift _ _ 64 1 g32p_supplierForest_edge_102006
    g32p_supplierForest_actual_035033

def g32p_supplierForest_node_102240 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_102240 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_102240 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_113406 := by
  decide +kernel

theorem g32p_supplierForest_actual_102240 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_102240) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_102240
    g32p_supplierForest_actual_113406

def g32p_supplierForest_node_102247 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_102247 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_102247 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_102976 := by
  decide +kernel

theorem g32p_supplierForest_actual_102247 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_102247) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_102247
    g32p_supplierForest_actual_102976

def g32p_supplierForest_node_102283 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_102283 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_102283 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_103146 := by
  decide +kernel

theorem g32p_supplierForest_actual_102283 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_102283) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_102283
    g32p_supplierForest_actual_103146

def g32p_supplierForest_node_102285 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_102285 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_102285 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_035682 := by
  decide +kernel

theorem g32p_supplierForest_actual_102285 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_102285) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_102285
    g32p_supplierForest_actual_035682

def g32p_supplierForest_node_102293 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_102293 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_102293 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_026234 := by
  decide +kernel

theorem g32p_supplierForest_actual_102293 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_102293) ∧
        IsConj g (g32p_literalRepresentative 64) := by
  exact g32p_archive_step_lift _ _ 64 1 g32p_supplierForest_edge_102293
    g32p_supplierForest_actual_026234

def g32p_supplierForest_node_102456 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_102456 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_102456 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_029106 := by
  decide +kernel

theorem g32p_supplierForest_actual_102456 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_102456) ∧
        IsConj g (g32p_literalRepresentative 64) := by
  exact g32p_archive_step_lift _ _ 64 1 g32p_supplierForest_edge_102456
    g32p_supplierForest_actual_029106

def g32p_supplierForest_node_102483 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_102483 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_102483 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_107453 := by
  decide +kernel

theorem g32p_supplierForest_actual_102483 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_102483) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_102483
    g32p_supplierForest_actual_107453

def g32p_supplierForest_node_103069 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_103069 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_103069 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_032571 := by
  decide +kernel

theorem g32p_supplierForest_actual_103069 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_103069) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_103069
    g32p_supplierForest_actual_032571

def g32p_supplierForest_node_103139 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_103139 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_103139 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_029947 := by
  decide +kernel

theorem g32p_supplierForest_actual_103139 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_103139) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_103139
    g32p_supplierForest_actual_029947

def g32p_supplierForest_node_103179 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_103179 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_103179 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043100 := by
  decide +kernel

theorem g32p_supplierForest_actual_103179 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_103179) ∧
        IsConj g (g32p_literalRepresentative 65) := by
  exact g32p_archive_step_lift _ _ 65 2 g32p_supplierForest_edge_103179
    g32p_supplierForest_actual_043100

def g32p_supplierForest_node_103359 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_103359 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_103359 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_029521 := by
  decide +kernel

theorem g32p_supplierForest_actual_103359 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_103359) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 0 g32p_supplierForest_edge_103359
    g32p_supplierForest_actual_029521

def g32p_supplierForest_node_103505 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_103505 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_103505 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113085 := by
  decide +kernel

theorem g32p_supplierForest_actual_103505 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_103505) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_103505
    g32p_supplierForest_actual_113085

def g32p_supplierForest_node_103618 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_103618 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_103618 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_040200 := by
  decide +kernel

theorem g32p_supplierForest_actual_103618 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_103618) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_103618
    g32p_supplierForest_actual_040200

def g32p_supplierForest_node_103759 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_103759 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_103759 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_029234 := by
  decide +kernel

theorem g32p_supplierForest_actual_103759 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_103759) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 0 g32p_supplierForest_edge_103759
    g32p_supplierForest_actual_029234

def g32p_supplierForest_node_103785 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_103785 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_103785 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_026234 := by
  decide +kernel

theorem g32p_supplierForest_actual_103785 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_103785) ∧
        IsConj g (g32p_literalRepresentative 64) := by
  exact g32p_archive_step_lift _ _ 64 3 g32p_supplierForest_edge_103785
    g32p_supplierForest_actual_026234

def g32p_supplierForest_node_103954 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_103954 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_103954 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_115083 := by
  decide +kernel

theorem g32p_supplierForest_actual_103954 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_103954) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 0 g32p_supplierForest_edge_103954
    g32p_supplierForest_actual_115083

def g32p_supplierForest_node_103991 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_103991 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_103991 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_113120 := by
  decide +kernel

theorem g32p_supplierForest_actual_103991 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_103991) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_103991
    g32p_supplierForest_actual_113120

def g32p_supplierForest_node_104025 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_104025 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104025 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108610 := by
  decide +kernel

theorem g32p_supplierForest_actual_104025 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104025) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_104025
    g32p_supplierForest_actual_108610

def g32p_supplierForest_node_104144 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_104144 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104144 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_029512 := by
  decide +kernel

theorem g32p_supplierForest_actual_104144 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104144) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_104144
    g32p_supplierForest_actual_029512

def g32p_supplierForest_node_104235 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_104235 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104235 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101980 := by
  decide +kernel

theorem g32p_supplierForest_actual_104235 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104235) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_104235
    g32p_supplierForest_actual_101980

def g32p_supplierForest_node_104252 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_104252 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104252 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_031404 := by
  decide +kernel

theorem g32p_supplierForest_actual_104252 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104252) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_104252
    g32p_supplierForest_actual_031404

def g32p_supplierForest_node_104376 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_104376 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104376 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_029403 := by
  decide +kernel

theorem g32p_supplierForest_actual_104376 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104376) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_104376
    g32p_supplierForest_actual_029403

def g32p_supplierForest_node_104387 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_104387 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104387 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_043309 := by
  decide +kernel

theorem g32p_supplierForest_actual_104387 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104387) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_104387
    g32p_supplierForest_actual_043309

def g32p_supplierForest_node_104393 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_104393 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104393 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_042890 := by
  decide +kernel

theorem g32p_supplierForest_actual_104393 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104393) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_104393
    g32p_supplierForest_actual_042890

def g32p_supplierForest_node_104423 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_104423 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104423 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_104779 := by
  decide +kernel

theorem g32p_supplierForest_actual_104423 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104423) ∧
        IsConj g (g32p_literalRepresentative 88) := by
  exact g32p_archive_step_lift _ _ 88 1 g32p_supplierForest_edge_104423
    g32p_supplierForest_actual_104779

def g32p_supplierForest_node_104484 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_104484 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104484 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_043075 := by
  decide +kernel

theorem g32p_supplierForest_actual_104484 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104484) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_104484
    g32p_supplierForest_actual_043075

def g32p_supplierForest_node_104504 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_104504 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104504 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104991 := by
  decide +kernel

theorem g32p_supplierForest_actual_104504 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104504) ∧
        IsConj g (g32p_literalRepresentative 88) := by
  exact g32p_archive_step_lift _ _ 88 2 g32p_supplierForest_edge_104504
    g32p_supplierForest_actual_104991

def g32p_supplierForest_node_104506 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_104506 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104506 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_104991 := by
  decide +kernel

theorem g32p_supplierForest_actual_104506 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104506) ∧
        IsConj g (g32p_literalRepresentative 88) := by
  exact g32p_archive_step_lift _ _ 88 1 g32p_supplierForest_edge_104506
    g32p_supplierForest_actual_104991

def g32p_supplierForest_node_104674 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_104674 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104674 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_025448 := by
  decide +kernel

theorem g32p_supplierForest_actual_104674 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104674) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_104674
    g32p_supplierForest_actual_025448

def g32p_supplierForest_node_104675 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_104675 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104675 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_105368 := by
  decide +kernel

theorem g32p_supplierForest_actual_104675 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104675) ∧
        IsConj g (g32p_literalRepresentative 88) := by
  exact g32p_archive_step_lift _ _ 88 1 g32p_supplierForest_edge_104675
    g32p_supplierForest_actual_105368

def g32p_supplierForest_node_104679 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_104679 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104679 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_029590 := by
  decide +kernel

theorem g32p_supplierForest_actual_104679 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104679) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_104679
    g32p_supplierForest_actual_029590

def g32p_supplierForest_node_104787 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_104787 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104787 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_042169 := by
  decide +kernel

theorem g32p_supplierForest_actual_104787 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104787) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_104787
    g32p_supplierForest_actual_042169

def g32p_supplierForest_node_104809 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_104809 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104809 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_025202 := by
  decide +kernel

theorem g32p_supplierForest_actual_104809 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104809) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_104809
    g32p_supplierForest_actual_025202

def g32p_supplierForest_node_104970 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_104970 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104970 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_104381 := by
  decide +kernel

theorem g32p_supplierForest_actual_104970 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104970) ∧
        IsConj g (g32p_literalRepresentative 88) := by
  exact g32p_archive_step_lift _ _ 88 1 g32p_supplierForest_edge_104970
    g32p_supplierForest_actual_104381

def g32p_supplierForest_node_104988 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_104988 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_104988 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_104991 := by
  decide +kernel

theorem g32p_supplierForest_actual_104988 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_104988) ∧
        IsConj g (g32p_literalRepresentative 88) := by
  exact g32p_archive_step_lift _ _ 88 3 g32p_supplierForest_edge_104988
    g32p_supplierForest_actual_104991

def g32p_supplierForest_node_105045 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_105045 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_105045 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_028659 := by
  decide +kernel

theorem g32p_supplierForest_actual_105045 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_105045) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 3 g32p_supplierForest_edge_105045
    g32p_supplierForest_actual_028659

def g32p_supplierForest_node_105326 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_105326 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_105326 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_025127 := by
  decide +kernel

theorem g32p_supplierForest_actual_105326 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_105326) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_105326
    g32p_supplierForest_actual_025127

def g32p_supplierForest_node_105332 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_105332 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_105332 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_032195 := by
  decide +kernel

theorem g32p_supplierForest_actual_105332 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_105332) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 0 g32p_supplierForest_edge_105332
    g32p_supplierForest_actual_032195

def g32p_supplierForest_node_105389 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_105389 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_105389 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_105466 := by
  decide +kernel

theorem g32p_supplierForest_actual_105389 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_105389) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_105389
    g32p_supplierForest_actual_105466

def g32p_supplierForest_node_105407 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_105407 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_105407 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102017 := by
  decide +kernel

theorem g32p_supplierForest_actual_105407 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_105407) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_105407
    g32p_supplierForest_actual_102017

def g32p_supplierForest_node_105596 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_105596 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_105596 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_025222 := by
  decide +kernel

theorem g32p_supplierForest_actual_105596 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_105596) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_105596
    g32p_supplierForest_actual_025222

def g32p_supplierForest_node_105717 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_105717 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_105717 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_030184 := by
  decide +kernel

theorem g32p_supplierForest_actual_105717 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_105717) ∧
        IsConj g (g32p_literalRepresentative 65) := by
  exact g32p_archive_step_lift _ _ 65 0 g32p_supplierForest_edge_105717
    g32p_supplierForest_actual_030184

def g32p_supplierForest_node_105727 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_105727 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_105727 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_025109 := by
  decide +kernel

theorem g32p_supplierForest_actual_105727 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_105727) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_105727
    g32p_supplierForest_actual_025109

def g32p_supplierForest_node_105870 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_105870 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_105870 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_101980 := by
  decide +kernel

theorem g32p_supplierForest_actual_105870 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_105870) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_105870
    g32p_supplierForest_actual_101980

def g32p_supplierForest_node_105889 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_105889 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_105889 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_103487 := by
  decide +kernel

theorem g32p_supplierForest_actual_105889 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_105889) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 1 g32p_supplierForest_edge_105889
    g32p_supplierForest_actual_103487

def g32p_supplierForest_node_106246 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_106246 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106246 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_039681 := by
  decide +kernel

theorem g32p_supplierForest_actual_106246 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106246) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_106246
    g32p_supplierForest_actual_039681

def g32p_supplierForest_node_106263 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_106263 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106263 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029234 := by
  decide +kernel

theorem g32p_supplierForest_actual_106263 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106263) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 3 g32p_supplierForest_edge_106263
    g32p_supplierForest_actual_029234

def g32p_supplierForest_node_106272 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_106272 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106272 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043309 := by
  decide +kernel

theorem g32p_supplierForest_actual_106272 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106272) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_106272
    g32p_supplierForest_actual_043309

def g32p_supplierForest_node_106338 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_106338 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106338 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_024779 := by
  decide +kernel

theorem g32p_supplierForest_actual_106338 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106338) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_106338
    g32p_supplierForest_actual_024779

def g32p_supplierForest_node_106410 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_106410 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106410 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_025202 := by
  decide +kernel

theorem g32p_supplierForest_actual_106410 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106410) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_106410
    g32p_supplierForest_actual_025202

def g32p_supplierForest_node_106436 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_106436 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106436 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_043073 := by
  decide +kernel

theorem g32p_supplierForest_actual_106436 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106436) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_106436
    g32p_supplierForest_actual_043073

def g32p_supplierForest_node_106504 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_106504 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106504 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_108610 := by
  decide +kernel

theorem g32p_supplierForest_actual_106504 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106504) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_106504
    g32p_supplierForest_actual_108610

def g32p_supplierForest_node_106709 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_106709 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106709 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_024604 := by
  decide +kernel

theorem g32p_supplierForest_actual_106709 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106709) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_106709
    g32p_supplierForest_actual_024604

def g32p_supplierForest_node_106809 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_106809 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106809 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029521 := by
  decide +kernel

theorem g32p_supplierForest_actual_106809 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106809) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 3 g32p_supplierForest_edge_106809
    g32p_supplierForest_actual_029521

def g32p_supplierForest_node_106924 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_106924 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106924 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_029590 := by
  decide +kernel

theorem g32p_supplierForest_actual_106924 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106924) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_106924
    g32p_supplierForest_actual_029590

def g32p_supplierForest_node_106985 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_106985 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106985 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_105368 := by
  decide +kernel

theorem g32p_supplierForest_actual_106985 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106985) ∧
        IsConj g (g32p_literalRepresentative 88) := by
  exact g32p_archive_step_lift _ _ 88 3 g32p_supplierForest_edge_106985
    g32p_supplierForest_actual_105368

def g32p_supplierForest_node_107299 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_107299 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_107299 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_108912 := by
  decide +kernel

theorem g32p_supplierForest_actual_107299 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_107299) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_107299
    g32p_supplierForest_actual_108912

def g32p_supplierForest_node_107393 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_107393 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_107393 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_114215 := by
  decide +kernel

theorem g32p_supplierForest_actual_107393 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_107393) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_107393
    g32p_supplierForest_actual_114215

def g32p_supplierForest_node_107426 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_107426 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_107426 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_117826 := by
  decide +kernel

theorem g32p_supplierForest_actual_107426 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_107426) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 2 g32p_supplierForest_edge_107426
    g32p_supplierForest_actual_117826

def g32p_supplierForest_node_107529 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_107529 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_107529 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_109158 := by
  decide +kernel

theorem g32p_supplierForest_actual_107529 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_107529) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_107529
    g32p_supplierForest_actual_109158

def g32p_supplierForest_node_107537 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_107537 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_107537 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_115836 := by
  decide +kernel

theorem g32p_supplierForest_actual_107537 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_107537) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 1 g32p_supplierForest_edge_107537
    g32p_supplierForest_actual_115836

def g32p_supplierForest_node_107747 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_107747 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_107747 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_117292 := by
  decide +kernel

theorem g32p_supplierForest_actual_107747 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_107747) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_107747
    g32p_supplierForest_actual_117292

def g32p_supplierForest_node_107767 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_107767 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_107767 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_038182 := by
  decide +kernel

theorem g32p_supplierForest_actual_107767 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_107767) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_107767
    g32p_supplierForest_actual_038182

def g32p_supplierForest_node_108015 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_108015 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108015 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_038616 := by
  decide +kernel

theorem g32p_supplierForest_actual_108015 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108015) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_108015
    g32p_supplierForest_actual_038616

def g32p_supplierForest_node_108024 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_108024 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108024 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_118650 := by
  decide +kernel

theorem g32p_supplierForest_actual_108024 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108024) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_108024
    g32p_supplierForest_actual_118650

def g32p_supplierForest_node_108053 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_108053 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108053 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_031789 := by
  decide +kernel

theorem g32p_supplierForest_actual_108053 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108053) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_108053
    g32p_supplierForest_actual_031789

def g32p_supplierForest_node_108059 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108059 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108059 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_118673 := by
  decide +kernel

theorem g32p_supplierForest_actual_108059 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108059) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_108059
    g32p_supplierForest_actual_118673

def g32p_supplierForest_node_108081 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_108081 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108081 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117269 := by
  decide +kernel

theorem g32p_supplierForest_actual_108081 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108081) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 1 g32p_supplierForest_edge_108081
    g32p_supplierForest_actual_117269

def g32p_supplierForest_node_108180 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_108180 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108180 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_116797 := by
  decide +kernel

theorem g32p_supplierForest_actual_108180 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108180) ∧
        IsConj g (g32p_literalRepresentative 87) := by
  exact g32p_archive_step_lift _ _ 87 0 g32p_supplierForest_edge_108180
    g32p_supplierForest_actual_116797

def g32p_supplierForest_node_108334 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_108334 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108334 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108854 := by
  decide +kernel

theorem g32p_supplierForest_actual_108334 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108334) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_108334
    g32p_supplierForest_actual_108854

def g32p_supplierForest_node_108338 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108338 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108338 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_026852 := by
  decide +kernel

theorem g32p_supplierForest_actual_108338 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108338) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_108338
    g32p_supplierForest_actual_026852

def g32p_supplierForest_node_108423 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_108423 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108423 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_109636 := by
  decide +kernel

theorem g32p_supplierForest_actual_108423 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108423) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 2 g32p_supplierForest_edge_108423
    g32p_supplierForest_actual_109636

def g32p_supplierForest_node_108439 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_108439 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108439 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_039681 := by
  decide +kernel

theorem g32p_supplierForest_actual_108439 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108439) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_108439
    g32p_supplierForest_actual_039681

def g32p_supplierForest_node_108496 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_108496 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108496 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_117783 := by
  decide +kernel

theorem g32p_supplierForest_actual_108496 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108496) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_108496
    g32p_supplierForest_actual_117783

def g32p_supplierForest_node_108562 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108562 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108562 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_110385 := by
  decide +kernel

theorem g32p_supplierForest_actual_108562 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108562) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 2 g32p_supplierForest_edge_108562
    g32p_supplierForest_actual_110385

def g32p_supplierForest_node_108591 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108591 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108591 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_107453 := by
  decide +kernel

theorem g32p_supplierForest_actual_108591 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108591) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_108591
    g32p_supplierForest_actual_107453

def g32p_supplierForest_node_108701 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_108701 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108701 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_112847 := by
  decide +kernel

theorem g32p_supplierForest_actual_108701 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108701) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_108701
    g32p_supplierForest_actual_112847

def g32p_supplierForest_node_108809 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_108809 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108809 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_042946 := by
  decide +kernel

theorem g32p_supplierForest_actual_108809 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108809) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 0 g32p_supplierForest_edge_108809
    g32p_supplierForest_actual_042946

def g32p_supplierForest_node_108887 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108887 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108887 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_040406 := by
  decide +kernel

theorem g32p_supplierForest_actual_108887 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108887) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 1 g32p_supplierForest_edge_108887
    g32p_supplierForest_actual_040406

def g32p_supplierForest_node_109186 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_109186 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109186 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_035114 := by
  decide +kernel

theorem g32p_supplierForest_actual_109186 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109186) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_109186
    g32p_supplierForest_actual_035114

def g32p_supplierForest_node_109301 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_109301 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109301 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_029367 := by
  decide +kernel

theorem g32p_supplierForest_actual_109301 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109301) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_109301
    g32p_supplierForest_actual_029367

def g32p_supplierForest_node_109336 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109336 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109336 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_043113 := by
  decide +kernel

theorem g32p_supplierForest_actual_109336 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109336) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_109336
    g32p_supplierForest_actual_043113

def g32p_supplierForest_node_109341 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109341 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109341 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_042203 := by
  decide +kernel

theorem g32p_supplierForest_actual_109341 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109341) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 1 g32p_supplierForest_edge_109341
    g32p_supplierForest_actual_042203

def g32p_supplierForest_node_109436 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109436 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109436 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_105790 := by
  decide +kernel

theorem g32p_supplierForest_actual_109436 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109436) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_109436
    g32p_supplierForest_actual_105790

def g32p_supplierForest_node_109646 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109646 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109646 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_120018 := by
  decide +kernel

theorem g32p_supplierForest_actual_109646 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109646) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_109646
    g32p_supplierForest_actual_120018

def g32p_supplierForest_node_109896 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109896 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109896 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037926 := by
  decide +kernel

theorem g32p_supplierForest_actual_109896 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109896) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_109896
    g32p_supplierForest_actual_037926

def g32p_supplierForest_node_109915 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_109915 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109915 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108550 := by
  decide +kernel

theorem g32p_supplierForest_actual_109915 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109915) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_109915
    g32p_supplierForest_actual_108550

def g32p_supplierForest_node_110308 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110308 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110308 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_120512 := by
  decide +kernel

theorem g32p_supplierForest_actual_110308 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110308) ∧
        IsConj g (g32p_literalRepresentative 87) := by
  exact g32p_archive_step_lift _ _ 87 0 g32p_supplierForest_edge_110308
    g32p_supplierForest_actual_120512

def g32p_supplierForest_node_110328 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110328 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110328 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_120533 := by
  decide +kernel

theorem g32p_supplierForest_actual_110328 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110328) ∧
        IsConj g (g32p_literalRepresentative 87) := by
  exact g32p_archive_step_lift _ _ 87 0 g32p_supplierForest_edge_110328
    g32p_supplierForest_actual_120533

def g32p_supplierForest_node_110351 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_110351 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110351 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_036536 := by
  decide +kernel

theorem g32p_supplierForest_actual_110351 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110351) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_110351
    g32p_supplierForest_actual_036536

def g32p_supplierForest_node_110364 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_110364 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110364 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_124083 := by
  decide +kernel

theorem g32p_supplierForest_actual_110364 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110364) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 1 g32p_supplierForest_edge_110364
    g32p_supplierForest_actual_124083

def g32p_supplierForest_node_110446 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110446 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110446 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_110451 := by
  decide +kernel

theorem g32p_supplierForest_actual_110446 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110446) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_110446
    g32p_supplierForest_actual_110451

def g32p_supplierForest_node_110517 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_110517 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110517 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_042890 := by
  decide +kernel

theorem g32p_supplierForest_actual_110517 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110517) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 0 g32p_supplierForest_edge_110517
    g32p_supplierForest_actual_042890

def g32p_supplierForest_node_110653 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_110653 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110653 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_037537 := by
  decide +kernel

theorem g32p_supplierForest_actual_110653 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110653) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_110653
    g32p_supplierForest_actual_037537

def g32p_supplierForest_node_110902 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_110902 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110902 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038616 := by
  decide +kernel

theorem g32p_supplierForest_actual_110902 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110902) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_110902
    g32p_supplierForest_actual_038616

def g32p_supplierForest_node_111025 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111025 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111025 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_026949 := by
  decide +kernel

theorem g32p_supplierForest_actual_111025 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111025) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_111025
    g32p_supplierForest_actual_026949

def g32p_supplierForest_node_111330 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_111330 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111330 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108610 := by
  decide +kernel

theorem g32p_supplierForest_actual_111330 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111330) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_111330
    g32p_supplierForest_actual_108610

def g32p_supplierForest_node_111338 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111338 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111338 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_110970 := by
  decide +kernel

theorem g32p_supplierForest_actual_111338 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111338) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_111338
    g32p_supplierForest_actual_110970

def g32p_supplierForest_node_111412 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111412 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111412 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_035133 := by
  decide +kernel

theorem g32p_supplierForest_actual_111412 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111412) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_111412
    g32p_supplierForest_actual_035133

def g32p_supplierForest_node_111426 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111426 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111426 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_040406 := by
  decide +kernel

theorem g32p_supplierForest_actual_111426 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111426) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_111426
    g32p_supplierForest_actual_040406

def g32p_supplierForest_node_111450 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_111450 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111450 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122546 := by
  decide +kernel

theorem g32p_supplierForest_actual_111450 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111450) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 1 g32p_supplierForest_edge_111450
    g32p_supplierForest_actual_122546

end HodgeLean.Foundations.Program

end
end
