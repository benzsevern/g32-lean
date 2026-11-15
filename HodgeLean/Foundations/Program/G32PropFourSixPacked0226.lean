import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0215
import HodgeLean.Foundations.Program.G32PropFourSixPacked0216
import HodgeLean.Foundations.Program.G32PropFourSixPacked0217
import HodgeLean.Foundations.Program.G32PropFourSixPacked0218
import HodgeLean.Foundations.Program.G32PropFourSixPacked0219
import HodgeLean.Foundations.Program.G32PropFourSixPacked0222
import HodgeLean.Foundations.Program.G32PropFourSixPacked0223
import HodgeLean.Foundations.Program.G32PropFourSixPacked0224
import HodgeLean.Foundations.Program.G32PropFourSixPacked0225

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_147775 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_147775 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_147775 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_146518 := by
  decide +kernel

theorem g32p_supplierForest_actual_147775 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_147775) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_147775
    g32p_supplierForest_actual_146518

def g32p_supplierForest_node_147782 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_147782 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_147782 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075947 := by
  decide +kernel

theorem g32p_supplierForest_actual_147782 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_147782) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_147782
    g32p_supplierForest_actual_075947

def g32p_supplierForest_node_147922 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_147922 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_147922 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100349 := by
  decide +kernel

theorem g32p_supplierForest_actual_147922 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_147922) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_147922
    g32p_supplierForest_actual_100349

def g32p_supplierForest_node_147924 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_147924 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_147924 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_099916 := by
  decide +kernel

theorem g32p_supplierForest_actual_147924 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_147924) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_147924
    g32p_supplierForest_actual_099916

def g32p_supplierForest_node_147977 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_147977 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_147977 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088033 := by
  decide +kernel

theorem g32p_supplierForest_actual_147977 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_147977) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 2 g32p_supplierForest_edge_147977
    g32p_supplierForest_actual_088033

def g32p_supplierForest_node_148026 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_148026 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148026 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_146173 := by
  decide +kernel

theorem g32p_supplierForest_actual_148026 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148026) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_148026
    g32p_supplierForest_actual_146173

def g32p_supplierForest_node_148027 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_148027 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148027 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_146434 := by
  decide +kernel

theorem g32p_supplierForest_actual_148027 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148027) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_148027
    g32p_supplierForest_actual_146434

def g32p_supplierForest_node_148165 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_148165 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148165 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_151529 := by
  decide +kernel

theorem g32p_supplierForest_actual_148165 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148165) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 0 g32p_supplierForest_edge_148165
    g32p_supplierForest_actual_151529

def g32p_supplierForest_node_148246 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_148246 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148246 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_151054 := by
  decide +kernel

theorem g32p_supplierForest_actual_148246 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148246) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_148246
    g32p_supplierForest_actual_151054

def g32p_supplierForest_node_148397 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_148397 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148397 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_150607 := by
  decide +kernel

theorem g32p_supplierForest_actual_148397 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148397) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_148397
    g32p_supplierForest_actual_150607

def g32p_supplierForest_node_148408 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_148408 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148408 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_085867 := by
  decide +kernel

theorem g32p_supplierForest_actual_148408 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148408) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 1 g32p_supplierForest_edge_148408
    g32p_supplierForest_actual_085867

def g32p_supplierForest_node_148473 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_148473 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148473 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_098563 := by
  decide +kernel

theorem g32p_supplierForest_actual_148473 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148473) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_148473
    g32p_supplierForest_actual_098563

def g32p_supplierForest_node_148488 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_148488 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148488 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_087982 := by
  decide +kernel

theorem g32p_supplierForest_actual_148488 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148488) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_148488
    g32p_supplierForest_actual_087982

def g32p_supplierForest_node_148509 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_148509 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148509 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085962 := by
  decide +kernel

theorem g32p_supplierForest_actual_148509 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148509) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 2 g32p_supplierForest_edge_148509
    g32p_supplierForest_actual_085962

def g32p_supplierForest_node_148531 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_148531 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148531 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_151657 := by
  decide +kernel

theorem g32p_supplierForest_actual_148531 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148531) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_148531
    g32p_supplierForest_actual_151657

def g32p_supplierForest_node_148608 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_148608 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148608 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_144822 := by
  decide +kernel

theorem g32p_supplierForest_actual_148608 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148608) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_148608
    g32p_supplierForest_actual_144822

def g32p_supplierForest_node_148619 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_148619 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148619 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087489 := by
  decide +kernel

theorem g32p_supplierForest_actual_148619 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148619) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 2 g32p_supplierForest_edge_148619
    g32p_supplierForest_actual_087489

def g32p_supplierForest_node_148631 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_148631 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148631 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_151053 := by
  decide +kernel

theorem g32p_supplierForest_actual_148631 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148631) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_148631
    g32p_supplierForest_actual_151053

def g32p_supplierForest_node_148665 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_148665 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148665 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_145901 := by
  decide +kernel

theorem g32p_supplierForest_actual_148665 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148665) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_148665
    g32p_supplierForest_actual_145901

def g32p_supplierForest_node_148703 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_148703 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148703 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_145951 := by
  decide +kernel

theorem g32p_supplierForest_actual_148703 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148703) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_148703
    g32p_supplierForest_actual_145951

def g32p_supplierForest_node_148780 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_148780 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148780 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_146544 := by
  decide +kernel

theorem g32p_supplierForest_actual_148780 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148780) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_148780
    g32p_supplierForest_actual_146544

def g32p_supplierForest_node_148798 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_148798 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148798 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_145916 := by
  decide +kernel

theorem g32p_supplierForest_actual_148798 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148798) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_148798
    g32p_supplierForest_actual_145916

def g32p_supplierForest_node_148853 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_148853 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148853 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074810 := by
  decide +kernel

theorem g32p_supplierForest_actual_148853 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148853) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_148853
    g32p_supplierForest_actual_074810

def g32p_supplierForest_node_148906 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_148906 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148906 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_145409 := by
  decide +kernel

theorem g32p_supplierForest_actual_148906 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148906) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_148906
    g32p_supplierForest_actual_145409

def g32p_supplierForest_node_148933 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_148933 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148933 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097542 := by
  decide +kernel

theorem g32p_supplierForest_actual_148933 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148933) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 2 g32p_supplierForest_edge_148933
    g32p_supplierForest_actual_097542

def g32p_supplierForest_node_149015 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_149015 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149015 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_149912 := by
  decide +kernel

theorem g32p_supplierForest_actual_149015 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149015) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 3 g32p_supplierForest_edge_149015
    g32p_supplierForest_actual_149912

def g32p_supplierForest_node_149017 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_149017 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149017 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_147662 := by
  decide +kernel

theorem g32p_supplierForest_actual_149017 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149017) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 2 g32p_supplierForest_edge_149017
    g32p_supplierForest_actual_147662

def g32p_supplierForest_node_149049 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_149049 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149049 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_148437 := by
  decide +kernel

theorem g32p_supplierForest_actual_149049 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149049) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_149049
    g32p_supplierForest_actual_148437

def g32p_supplierForest_node_149095 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_149095 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149095 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_077354 := by
  decide +kernel

theorem g32p_supplierForest_actual_149095 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149095) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_149095
    g32p_supplierForest_actual_077354

def g32p_supplierForest_node_149213 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_149213 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149213 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_147490 := by
  decide +kernel

theorem g32p_supplierForest_actual_149213 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149213) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 2 g32p_supplierForest_edge_149213
    g32p_supplierForest_actual_147490

def g32p_supplierForest_node_149228 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_149228 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149228 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_089829 := by
  decide +kernel

theorem g32p_supplierForest_actual_149228 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149228) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 0 g32p_supplierForest_edge_149228
    g32p_supplierForest_actual_089829

def g32p_supplierForest_node_149264 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_149264 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149264 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_146487 := by
  decide +kernel

theorem g32p_supplierForest_actual_149264 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149264) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_149264
    g32p_supplierForest_actual_146487

def g32p_supplierForest_node_149388 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_149388 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149388 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100963 := by
  decide +kernel

theorem g32p_supplierForest_actual_149388 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149388) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_149388
    g32p_supplierForest_actual_100963

def g32p_supplierForest_node_149406 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_149406 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149406 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_151924 := by
  decide +kernel

theorem g32p_supplierForest_actual_149406 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149406) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 0 g32p_supplierForest_edge_149406
    g32p_supplierForest_actual_151924

def g32p_supplierForest_node_149526 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_149526 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149526 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_092938 := by
  decide +kernel

theorem g32p_supplierForest_actual_149526 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149526) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_149526
    g32p_supplierForest_actual_092938

def g32p_supplierForest_node_149691 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_149691 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149691 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091699 := by
  decide +kernel

theorem g32p_supplierForest_actual_149691 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149691) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_149691
    g32p_supplierForest_actual_091699

def g32p_supplierForest_node_149694 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_149694 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149694 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086227 := by
  decide +kernel

theorem g32p_supplierForest_actual_149694 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149694) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 3 g32p_supplierForest_edge_149694
    g32p_supplierForest_actual_086227

def g32p_supplierForest_node_149792 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_149792 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149792 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_092777 := by
  decide +kernel

theorem g32p_supplierForest_actual_149792 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149792) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 2 g32p_supplierForest_edge_149792
    g32p_supplierForest_actual_092777

def g32p_supplierForest_node_149807 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_149807 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149807 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_098085 := by
  decide +kernel

theorem g32p_supplierForest_actual_149807 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149807) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_149807
    g32p_supplierForest_actual_098085

def g32p_supplierForest_node_149841 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_149841 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149841 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_097425 := by
  decide +kernel

theorem g32p_supplierForest_actual_149841 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149841) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 3 g32p_supplierForest_edge_149841
    g32p_supplierForest_actual_097425

def g32p_supplierForest_node_149919 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_149919 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149919 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_096752 := by
  decide +kernel

theorem g32p_supplierForest_actual_149919 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149919) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_149919
    g32p_supplierForest_actual_096752

def g32p_supplierForest_node_149997 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_149997 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149997 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_149334 := by
  decide +kernel

theorem g32p_supplierForest_actual_149997 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149997) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_149997
    g32p_supplierForest_actual_149334

def g32p_supplierForest_node_150003 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150003 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150003 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083280 := by
  decide +kernel

theorem g32p_supplierForest_actual_150003 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150003) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_150003
    g32p_supplierForest_actual_083280

def g32p_supplierForest_node_150017 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150017 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150017 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_150176 := by
  decide +kernel

theorem g32p_supplierForest_actual_150017 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150017) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_150017
    g32p_supplierForest_actual_150176

def g32p_supplierForest_node_150040 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150040 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150040 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076918 := by
  decide +kernel

theorem g32p_supplierForest_actual_150040 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150040) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_150040
    g32p_supplierForest_actual_076918

def g32p_supplierForest_node_150084 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150084 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150084 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_148437 := by
  decide +kernel

theorem g32p_supplierForest_actual_150084 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150084) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_150084
    g32p_supplierForest_actual_148437

def g32p_supplierForest_node_150089 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_150089 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150089 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_151054 := by
  decide +kernel

theorem g32p_supplierForest_actual_150089 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150089) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_150089
    g32p_supplierForest_actual_151054

def g32p_supplierForest_node_150166 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_150166 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150166 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_145951 := by
  decide +kernel

theorem g32p_supplierForest_actual_150166 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150166) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_150166
    g32p_supplierForest_actual_145951

def g32p_supplierForest_node_150169 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_150169 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150169 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_099916 := by
  decide +kernel

theorem g32p_supplierForest_actual_150169 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150169) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_150169
    g32p_supplierForest_actual_099916

def g32p_supplierForest_node_150197 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_150197 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150197 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_152210 := by
  decide +kernel

theorem g32p_supplierForest_actual_150197 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150197) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_150197
    g32p_supplierForest_actual_152210

def g32p_supplierForest_node_150312 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_150312 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150312 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_095851 := by
  decide +kernel

theorem g32p_supplierForest_actual_150312 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150312) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 0 g32p_supplierForest_edge_150312
    g32p_supplierForest_actual_095851

def g32p_supplierForest_node_150362 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_150362 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150362 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_148065 := by
  decide +kernel

theorem g32p_supplierForest_actual_150362 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150362) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_150362
    g32p_supplierForest_actual_148065

def g32p_supplierForest_node_150395 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_150395 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150395 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152210 := by
  decide +kernel

theorem g32p_supplierForest_actual_150395 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150395) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_150395
    g32p_supplierForest_actual_152210

def g32p_supplierForest_node_150420 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_150420 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150420 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_150872 := by
  decide +kernel

theorem g32p_supplierForest_actual_150420 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150420) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_150420
    g32p_supplierForest_actual_150872

def g32p_supplierForest_node_150421 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150421 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150421 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_093485 := by
  decide +kernel

theorem g32p_supplierForest_actual_150421 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150421) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 0 g32p_supplierForest_edge_150421
    g32p_supplierForest_actual_093485

def g32p_supplierForest_node_150422 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_150422 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150422 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152175 := by
  decide +kernel

theorem g32p_supplierForest_actual_150422 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150422) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_150422
    g32p_supplierForest_actual_152175

def g32p_supplierForest_node_150667 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_150667 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150667 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_151531 := by
  decide +kernel

theorem g32p_supplierForest_actual_150667 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150667) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_150667
    g32p_supplierForest_actual_151531

def g32p_supplierForest_node_150831 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_150831 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150831 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_146684 := by
  decide +kernel

theorem g32p_supplierForest_actual_150831 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150831) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_150831
    g32p_supplierForest_actual_146684

def g32p_supplierForest_node_150844 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150844 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150844 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152225 := by
  decide +kernel

theorem g32p_supplierForest_actual_150844 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150844) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_150844
    g32p_supplierForest_actual_152225

def g32p_supplierForest_node_150893 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_150893 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150893 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_150925 := by
  decide +kernel

theorem g32p_supplierForest_actual_150893 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150893) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_150893
    g32p_supplierForest_actual_150925

def g32p_supplierForest_node_150918 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150918 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150918 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_151340 := by
  decide +kernel

theorem g32p_supplierForest_actual_150918 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150918) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 3 g32p_supplierForest_edge_150918
    g32p_supplierForest_actual_151340

def g32p_supplierForest_node_150959 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150959 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150959 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_151780 := by
  decide +kernel

theorem g32p_supplierForest_actual_150959 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150959) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_150959
    g32p_supplierForest_actual_151780

def g32p_supplierForest_node_151040 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_151040 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151040 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_151053 := by
  decide +kernel

theorem g32p_supplierForest_actual_151040 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151040) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_151040
    g32p_supplierForest_actual_151053

def g32p_supplierForest_node_151043 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_151043 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151043 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_148028 := by
  decide +kernel

theorem g32p_supplierForest_actual_151043 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151043) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 0 g32p_supplierForest_edge_151043
    g32p_supplierForest_actual_148028

def g32p_supplierForest_node_151058 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151058 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151058 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_147333 := by
  decide +kernel

theorem g32p_supplierForest_actual_151058 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151058) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 0 g32p_supplierForest_edge_151058
    g32p_supplierForest_actual_147333

def g32p_supplierForest_node_151071 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_151071 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151071 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_150399 := by
  decide +kernel

theorem g32p_supplierForest_actual_151071 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151071) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 3 g32p_supplierForest_edge_151071
    g32p_supplierForest_actual_150399

def g32p_supplierForest_node_151117 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151117 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151117 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_151531 := by
  decide +kernel

theorem g32p_supplierForest_actual_151117 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151117) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_151117
    g32p_supplierForest_actual_151531

def g32p_supplierForest_node_151238 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151238 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151238 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_148049 := by
  decide +kernel

theorem g32p_supplierForest_actual_151238 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151238) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_151238
    g32p_supplierForest_actual_148049

def g32p_supplierForest_node_151297 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151297 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151297 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086435 := by
  decide +kernel

theorem g32p_supplierForest_actual_151297 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151297) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_151297
    g32p_supplierForest_actual_086435

def g32p_supplierForest_node_151304 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_151304 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151304 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092683 := by
  decide +kernel

theorem g32p_supplierForest_actual_151304 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151304) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_151304
    g32p_supplierForest_actual_092683

def g32p_supplierForest_node_151379 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_151379 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151379 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_151492 := by
  decide +kernel

theorem g32p_supplierForest_actual_151379 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151379) ∧
        IsConj g (g32p_literalRepresentative 98) := by
  exact g32p_archive_step_lift _ _ 98 1 g32p_supplierForest_edge_151379
    g32p_supplierForest_actual_151492

def g32p_supplierForest_node_151445 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_151445 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151445 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_151454 := by
  decide +kernel

theorem g32p_supplierForest_actual_151445 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151445) ∧
        IsConj g (g32p_literalRepresentative 98) := by
  exact g32p_archive_step_lift _ _ 98 1 g32p_supplierForest_edge_151445
    g32p_supplierForest_actual_151454

def g32p_supplierForest_node_151452 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_151452 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151452 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_152475 := by
  decide +kernel

theorem g32p_supplierForest_actual_151452 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151452) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_151452
    g32p_supplierForest_actual_152475

def g32p_supplierForest_node_151536 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151536 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151536 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146173 := by
  decide +kernel

theorem g32p_supplierForest_actual_151536 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151536) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_151536
    g32p_supplierForest_actual_146173

def g32p_supplierForest_node_151538 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_151538 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151538 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152475 := by
  decide +kernel

theorem g32p_supplierForest_actual_151538 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151538) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_151538
    g32p_supplierForest_actual_152475

def g32p_supplierForest_node_151681 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_151681 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151681 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_150607 := by
  decide +kernel

theorem g32p_supplierForest_actual_151681 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151681) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_151681
    g32p_supplierForest_actual_150607

def g32p_supplierForest_node_151812 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_151812 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151812 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_149348 := by
  decide +kernel

theorem g32p_supplierForest_actual_151812 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151812) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_151812
    g32p_supplierForest_actual_149348

def g32p_supplierForest_node_151882 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_151882 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151882 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_099666 := by
  decide +kernel

theorem g32p_supplierForest_actual_151882 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151882) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_151882
    g32p_supplierForest_actual_099666

def g32p_supplierForest_node_151927 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151927 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151927 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_150925 := by
  decide +kernel

theorem g32p_supplierForest_actual_151927 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151927) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_151927
    g32p_supplierForest_actual_150925

def g32p_supplierForest_node_151934 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151934 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151934 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_145951 := by
  decide +kernel

theorem g32p_supplierForest_actual_151934 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151934) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_151934
    g32p_supplierForest_actual_145951

def g32p_supplierForest_node_151972 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151972 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151972 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_149914 := by
  decide +kernel

theorem g32p_supplierForest_actual_151972 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151972) ∧
        IsConj g (g32p_literalRepresentative 98) := by
  exact g32p_archive_step_lift _ _ 98 2 g32p_supplierForest_edge_151972
    g32p_supplierForest_actual_149914

def g32p_supplierForest_node_152002 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152002 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152002 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_148965 := by
  decide +kernel

theorem g32p_supplierForest_actual_152002 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152002) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_152002
    g32p_supplierForest_actual_148965

def g32p_supplierForest_node_152039 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152039 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152039 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152105 := by
  decide +kernel

theorem g32p_supplierForest_actual_152039 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152039) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_152039
    g32p_supplierForest_actual_152105

def g32p_supplierForest_node_152041 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152041 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152041 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_149509 := by
  decide +kernel

theorem g32p_supplierForest_actual_152041 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152041) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_152041
    g32p_supplierForest_actual_149509

def g32p_supplierForest_node_152064 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152064 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152064 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152306 := by
  decide +kernel

theorem g32p_supplierForest_actual_152064 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152064) ∧
        IsConj g (g32p_literalRepresentative 98) := by
  exact g32p_archive_step_lift _ _ 98 0 g32p_supplierForest_edge_152064
    g32p_supplierForest_actual_152306

def g32p_supplierForest_node_152079 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152079 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152079 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_152067 := by
  decide +kernel

theorem g32p_supplierForest_actual_152079 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152079) ∧
        IsConj g (g32p_literalRepresentative 98) := by
  exact g32p_archive_step_lift _ _ 98 3 g32p_supplierForest_edge_152079
    g32p_supplierForest_actual_152067

def g32p_supplierForest_node_152091 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152091 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152091 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146781 := by
  decide +kernel

theorem g32p_supplierForest_actual_152091 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152091) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_152091
    g32p_supplierForest_actual_146781

def g32p_supplierForest_node_152143 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_152143 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152143 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_146961 := by
  decide +kernel

theorem g32p_supplierForest_actual_152143 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152143) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 1 g32p_supplierForest_edge_152143
    g32p_supplierForest_actual_146961

def g32p_supplierForest_node_152162 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_152162 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152162 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_152225 := by
  decide +kernel

theorem g32p_supplierForest_actual_152162 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152162) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_152162
    g32p_supplierForest_actual_152225

def g32p_supplierForest_node_152229 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152229 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152229 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_148862 := by
  decide +kernel

theorem g32p_supplierForest_actual_152229 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152229) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_152229
    g32p_supplierForest_actual_148862

def g32p_supplierForest_node_152255 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_152255 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152255 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_151924 := by
  decide +kernel

theorem g32p_supplierForest_actual_152255 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152255) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_152255
    g32p_supplierForest_actual_151924

def g32p_supplierForest_node_152344 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_152344 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152344 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_150228 := by
  decide +kernel

theorem g32p_supplierForest_actual_152344 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152344) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_152344
    g32p_supplierForest_actual_150228

def g32p_supplierForest_node_152374 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_152374 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152374 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152225 := by
  decide +kernel

theorem g32p_supplierForest_actual_152374 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152374) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_152374
    g32p_supplierForest_actual_152225

def g32p_supplierForest_node_152394 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_152394 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152394 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152175 := by
  decide +kernel

theorem g32p_supplierForest_actual_152394 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152394) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_152394
    g32p_supplierForest_actual_152175

def g32p_supplierForest_node_152524 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_152524 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152524 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_105717 := by
  decide +kernel

theorem g32p_supplierForest_actual_152524 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152524) ∧
        IsConj g (g32p_literalRepresentative 65) := by
  exact g32p_archive_step_lift _ _ 65 3 g32p_supplierForest_edge_152524
    g32p_supplierForest_actual_105717

def g32p_supplierForest_node_152533 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_152533 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152533 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_152755 := by
  decide +kernel

theorem g32p_supplierForest_actual_152533 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152533) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 1 g32p_supplierForest_edge_152533
    g32p_supplierForest_actual_152755

def g32p_supplierForest_node_152582 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152582 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152582 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_125800 := by
  decide +kernel

theorem g32p_supplierForest_actual_152582 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152582) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_152582
    g32p_supplierForest_actual_125800

def g32p_supplierForest_node_152595 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_152595 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152595 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153808 := by
  decide +kernel

theorem g32p_supplierForest_actual_152595 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152595) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 2 g32p_supplierForest_edge_152595
    g32p_supplierForest_actual_153808

def g32p_supplierForest_node_152628 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_152628 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152628 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122119 := by
  decide +kernel

theorem g32p_supplierForest_actual_152628 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152628) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_152628
    g32p_supplierForest_actual_122119

def g32p_supplierForest_node_152656 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_152656 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152656 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_154379 := by
  decide +kernel

theorem g32p_supplierForest_actual_152656 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152656) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_152656
    g32p_supplierForest_actual_154379

def g32p_supplierForest_node_152659 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_152659 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152659 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108334 := by
  decide +kernel

theorem g32p_supplierForest_actual_152659 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152659) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_152659
    g32p_supplierForest_actual_108334

def g32p_supplierForest_node_152779 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_152779 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152779 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153727 := by
  decide +kernel

theorem g32p_supplierForest_actual_152779 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152779) ∧
        IsConj g (g32p_literalRepresentative 93) := by
  exact g32p_archive_step_lift _ _ 93 0 g32p_supplierForest_edge_152779
    g32p_supplierForest_actual_153727

def g32p_supplierForest_node_152793 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_152793 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152793 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118167 := by
  decide +kernel

theorem g32p_supplierForest_actual_152793 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152793) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 2 g32p_supplierForest_edge_152793
    g32p_supplierForest_actual_118167

def g32p_supplierForest_node_152796 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152796 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152796 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_119786 := by
  decide +kernel

theorem g32p_supplierForest_actual_152796 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152796) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 1 g32p_supplierForest_edge_152796
    g32p_supplierForest_actual_119786

def g32p_supplierForest_node_152842 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_152842 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152842 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126372 := by
  decide +kernel

theorem g32p_supplierForest_actual_152842 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152842) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_152842
    g32p_supplierForest_actual_126372

def g32p_supplierForest_node_152859 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152859 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152859 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153458 := by
  decide +kernel

theorem g32p_supplierForest_actual_152859 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152859) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 2 g32p_supplierForest_edge_152859
    g32p_supplierForest_actual_153458

def g32p_supplierForest_node_152870 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152870 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152870 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154933 := by
  decide +kernel

theorem g32p_supplierForest_actual_152870 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152870) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 3 g32p_supplierForest_edge_152870
    g32p_supplierForest_actual_154933

def g32p_supplierForest_node_153011 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_153011 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153011 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122963 := by
  decide +kernel

theorem g32p_supplierForest_actual_153011 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153011) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 2 g32p_supplierForest_edge_153011
    g32p_supplierForest_actual_122963

def g32p_supplierForest_node_153113 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153113 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153113 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_107299 := by
  decide +kernel

theorem g32p_supplierForest_actual_153113 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153113) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_153113
    g32p_supplierForest_actual_107299

def g32p_supplierForest_node_153117 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_153117 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153117 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_121910 := by
  decide +kernel

theorem g32p_supplierForest_actual_153117 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153117) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_153117
    g32p_supplierForest_actual_121910

def g32p_supplierForest_node_153127 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_153127 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153127 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108496 := by
  decide +kernel

theorem g32p_supplierForest_actual_153127 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153127) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 2 g32p_supplierForest_edge_153127
    g32p_supplierForest_actual_108496

def g32p_supplierForest_node_153171 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_153171 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153171 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126975 := by
  decide +kernel

theorem g32p_supplierForest_actual_153171 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153171) ∧
        IsConj g (g32p_literalRepresentative 87) := by
  exact g32p_archive_step_lift _ _ 87 1 g32p_supplierForest_edge_153171
    g32p_supplierForest_actual_126975

def g32p_supplierForest_node_153184 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153184 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153184 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_107747 := by
  decide +kernel

theorem g32p_supplierForest_actual_153184 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153184) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 3 g32p_supplierForest_edge_153184
    g32p_supplierForest_actual_107747

def g32p_supplierForest_node_153201 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153201 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153201 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154311 := by
  decide +kernel

theorem g32p_supplierForest_actual_153201 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153201) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 2 g32p_supplierForest_edge_153201
    g32p_supplierForest_actual_154311

def g32p_supplierForest_node_153238 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153238 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153238 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153130 := by
  decide +kernel

theorem g32p_supplierForest_actual_153238 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153238) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 2 g32p_supplierForest_edge_153238
    g32p_supplierForest_actual_153130

def g32p_supplierForest_node_153245 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153245 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153245 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153094 := by
  decide +kernel

theorem g32p_supplierForest_actual_153245 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153245) ∧
        IsConj g (g32p_literalRepresentative 93) := by
  exact g32p_archive_step_lift _ _ 93 2 g32p_supplierForest_edge_153245
    g32p_supplierForest_actual_153094

def g32p_supplierForest_node_153288 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153288 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153288 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_127331 := by
  decide +kernel

theorem g32p_supplierForest_actual_153288 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153288) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_153288
    g32p_supplierForest_actual_127331

def g32p_supplierForest_node_153297 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_153297 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153297 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_127713 := by
  decide +kernel

theorem g32p_supplierForest_actual_153297 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153297) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_153297
    g32p_supplierForest_actual_127713

def g32p_supplierForest_node_153298 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153298 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153298 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_115851 := by
  decide +kernel

theorem g32p_supplierForest_actual_153298 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153298) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_153298
    g32p_supplierForest_actual_115851

def g32p_supplierForest_node_153326 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_153326 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153326 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153130 := by
  decide +kernel

theorem g32p_supplierForest_actual_153326 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153326) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 1 g32p_supplierForest_edge_153326
    g32p_supplierForest_actual_153130

def g32p_supplierForest_node_153407 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_153407 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153407 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127735 := by
  decide +kernel

theorem g32p_supplierForest_actual_153407 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153407) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_153407
    g32p_supplierForest_actual_127735

def g32p_supplierForest_node_153463 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153463 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153463 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_119962 := by
  decide +kernel

theorem g32p_supplierForest_actual_153463 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153463) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 1 g32p_supplierForest_edge_153463
    g32p_supplierForest_actual_119962

def g32p_supplierForest_node_153487 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153487 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153487 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_154311 := by
  decide +kernel

theorem g32p_supplierForest_actual_153487 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153487) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_153487
    g32p_supplierForest_actual_154311

def g32p_supplierForest_node_153496 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153496 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153496 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_154939 := by
  decide +kernel

theorem g32p_supplierForest_actual_153496 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153496) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 1 g32p_supplierForest_edge_153496
    g32p_supplierForest_actual_154939

def g32p_supplierForest_node_153542 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153542 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153542 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_124062 := by
  decide +kernel

theorem g32p_supplierForest_actual_153542 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153542) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 2 g32p_supplierForest_edge_153542
    g32p_supplierForest_actual_124062

def g32p_supplierForest_node_153578 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153578 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153578 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_125936 := by
  decide +kernel

theorem g32p_supplierForest_actual_153578 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153578) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 2 g32p_supplierForest_edge_153578
    g32p_supplierForest_actual_125936

def g32p_supplierForest_node_153587 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153587 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153587 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152591 := by
  decide +kernel

theorem g32p_supplierForest_actual_153587 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153587) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 2 g32p_supplierForest_edge_153587
    g32p_supplierForest_actual_152591

def g32p_supplierForest_node_153606 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153606 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153606 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_114333 := by
  decide +kernel

theorem g32p_supplierForest_actual_153606 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153606) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_153606
    g32p_supplierForest_actual_114333

def g32p_supplierForest_node_153678 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153678 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153678 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_105870 := by
  decide +kernel

theorem g32p_supplierForest_actual_153678 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153678) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_153678
    g32p_supplierForest_actual_105870

def g32p_supplierForest_node_153691 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153691 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153691 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122921 := by
  decide +kernel

theorem g32p_supplierForest_actual_153691 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153691) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_153691
    g32p_supplierForest_actual_122921

def g32p_supplierForest_node_153717 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153717 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153717 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_154019 := by
  decide +kernel

theorem g32p_supplierForest_actual_153717 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153717) ∧
        IsConj g (g32p_literalRepresentative 87) := by
  exact g32p_archive_step_lift _ _ 87 1 g32p_supplierForest_edge_153717
    g32p_supplierForest_actual_154019

def g32p_supplierForest_node_153737 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153737 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153737 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113732 := by
  decide +kernel

theorem g32p_supplierForest_actual_153737 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153737) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 3 g32p_supplierForest_edge_153737
    g32p_supplierForest_actual_113732

def g32p_supplierForest_node_153784 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153784 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153784 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_154335 := by
  decide +kernel

theorem g32p_supplierForest_actual_153784 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153784) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 0 g32p_supplierForest_edge_153784
    g32p_supplierForest_actual_154335

def g32p_supplierForest_node_153859 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153859 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153859 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153130 := by
  decide +kernel

theorem g32p_supplierForest_actual_153859 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153859) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 3 g32p_supplierForest_edge_153859
    g32p_supplierForest_actual_153130

def g32p_supplierForest_node_153877 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153877 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153877 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_154248 := by
  decide +kernel

theorem g32p_supplierForest_actual_153877 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153877) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_153877
    g32p_supplierForest_actual_154248

def g32p_supplierForest_node_153885 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153885 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153885 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_127735 := by
  decide +kernel

theorem g32p_supplierForest_actual_153885 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153885) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_153885
    g32p_supplierForest_actual_127735

def g32p_supplierForest_node_153887 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153887 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153887 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124067 := by
  decide +kernel

theorem g32p_supplierForest_actual_153887 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153887) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_153887
    g32p_supplierForest_actual_124067

def g32p_supplierForest_node_153901 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153901 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153901 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_115704 := by
  decide +kernel

theorem g32p_supplierForest_actual_153901 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153901) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 3 g32p_supplierForest_edge_153901
    g32p_supplierForest_actual_115704

def g32p_supplierForest_node_153953 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153953 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153953 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_126527 := by
  decide +kernel

theorem g32p_supplierForest_actual_153953 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153953) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 2 g32p_supplierForest_edge_153953
    g32p_supplierForest_actual_126527

def g32p_supplierForest_node_153964 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153964 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153964 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127541 := by
  decide +kernel

theorem g32p_supplierForest_actual_153964 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153964) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 0 g32p_supplierForest_edge_153964
    g32p_supplierForest_actual_127541

def g32p_supplierForest_node_153994 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153994 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153994 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153808 := by
  decide +kernel

theorem g32p_supplierForest_actual_153994 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153994) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 3 g32p_supplierForest_edge_153994
    g32p_supplierForest_actual_153808

def g32p_supplierForest_node_153998 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153998 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153998 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_125800 := by
  decide +kernel

theorem g32p_supplierForest_actual_153998 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153998) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_153998
    g32p_supplierForest_actual_125800

def g32p_supplierForest_node_154021 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154021 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154021 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_126984 := by
  decide +kernel

theorem g32p_supplierForest_actual_154021 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154021) ∧
        IsConj g (g32p_literalRepresentative 87) := by
  exact g32p_archive_step_lift _ _ 87 3 g32p_supplierForest_edge_154021
    g32p_supplierForest_actual_126984

def g32p_supplierForest_node_154046 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154046 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154046 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153103 := by
  decide +kernel

theorem g32p_supplierForest_actual_154046 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154046) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_154046
    g32p_supplierForest_actual_153103

def g32p_supplierForest_node_154069 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_154069 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154069 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154343 := by
  decide +kernel

theorem g32p_supplierForest_actual_154069 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154069) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 3 g32p_supplierForest_edge_154069
    g32p_supplierForest_actual_154343

def g32p_supplierForest_node_154108 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154108 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154108 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154335 := by
  decide +kernel

theorem g32p_supplierForest_actual_154108 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154108) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 3 g32p_supplierForest_edge_154108
    g32p_supplierForest_actual_154335

def g32p_supplierForest_node_154115 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154115 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154115 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153560 := by
  decide +kernel

theorem g32p_supplierForest_actual_154115 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154115) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_154115
    g32p_supplierForest_actual_153560

def g32p_supplierForest_node_154202 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154202 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154202 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_106410 := by
  decide +kernel

theorem g32p_supplierForest_actual_154202 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154202) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_154202
    g32p_supplierForest_actual_106410

def g32p_supplierForest_node_154218 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_154218 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154218 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_109646 := by
  decide +kernel

theorem g32p_supplierForest_actual_154218 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154218) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_154218
    g32p_supplierForest_actual_109646

def g32p_supplierForest_node_154231 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_154231 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154231 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122805 := by
  decide +kernel

theorem g32p_supplierForest_actual_154231 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154231) ∧
        IsConj g (g32p_literalRepresentative 93) := by
  exact g32p_archive_step_lift _ _ 93 1 g32p_supplierForest_edge_154231
    g32p_supplierForest_actual_122805

def g32p_supplierForest_node_154245 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154245 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154245 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_115676 := by
  decide +kernel

theorem g32p_supplierForest_actual_154245 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154245) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 3 g32p_supplierForest_edge_154245
    g32p_supplierForest_actual_115676

def g32p_supplierForest_node_154263 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154263 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154263 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_117162 := by
  decide +kernel

theorem g32p_supplierForest_actual_154263 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154263) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 3 g32p_supplierForest_edge_154263
    g32p_supplierForest_actual_117162

def g32p_supplierForest_node_154296 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154296 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154296 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_127386 := by
  decide +kernel

theorem g32p_supplierForest_actual_154296 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154296) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 3 g32p_supplierForest_edge_154296
    g32p_supplierForest_actual_127386

def g32p_supplierForest_node_154319 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154319 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154319 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154248 := by
  decide +kernel

theorem g32p_supplierForest_actual_154319 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154319) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_154319
    g32p_supplierForest_actual_154248

def g32p_supplierForest_node_154395 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_154395 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154395 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_124637 := by
  decide +kernel

theorem g32p_supplierForest_actual_154395 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154395) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 3 g32p_supplierForest_edge_154395
    g32p_supplierForest_actual_124637

def g32p_supplierForest_node_154461 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_154461 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154461 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118560 := by
  decide +kernel

theorem g32p_supplierForest_actual_154461 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154461) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_154461
    g32p_supplierForest_actual_118560

def g32p_supplierForest_node_154474 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_154474 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154474 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154343 := by
  decide +kernel

theorem g32p_supplierForest_actual_154474 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154474) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 2 g32p_supplierForest_edge_154474
    g32p_supplierForest_actual_154343

def g32p_supplierForest_node_154513 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154513 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154513 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_124303 := by
  decide +kernel

theorem g32p_supplierForest_actual_154513 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154513) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 3 g32p_supplierForest_edge_154513
    g32p_supplierForest_actual_124303

def g32p_supplierForest_node_154514 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_154514 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154514 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153915 := by
  decide +kernel

theorem g32p_supplierForest_actual_154514 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154514) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 3 g32p_supplierForest_edge_154514
    g32p_supplierForest_actual_153915

def g32p_supplierForest_node_154567 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_154567 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154567 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153085 := by
  decide +kernel

theorem g32p_supplierForest_actual_154567 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154567) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_154567
    g32p_supplierForest_actual_153085

def g32p_supplierForest_node_154574 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_154574 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154574 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154939 := by
  decide +kernel

theorem g32p_supplierForest_actual_154574 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154574) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 3 g32p_supplierForest_edge_154574
    g32p_supplierForest_actual_154939

def g32p_supplierForest_node_154626 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_154626 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154626 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154542 := by
  decide +kernel

theorem g32p_supplierForest_actual_154626 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154626) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_154626
    g32p_supplierForest_actual_154542

def g32p_supplierForest_node_154643 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_154643 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154643 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122963 := by
  decide +kernel

theorem g32p_supplierForest_actual_154643 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154643) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_154643
    g32p_supplierForest_actual_122963

def g32p_supplierForest_node_154664 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154664 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154664 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_154933 := by
  decide +kernel

theorem g32p_supplierForest_actual_154664 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154664) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_154664
    g32p_supplierForest_actual_154933

def g32p_supplierForest_node_154705 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_154705 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154705 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154854 := by
  decide +kernel

theorem g32p_supplierForest_actual_154705 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154705) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_154705
    g32p_supplierForest_actual_154854

def g32p_supplierForest_node_154706 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154706 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154706 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153085 := by
  decide +kernel

theorem g32p_supplierForest_actual_154706 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154706) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_154706
    g32p_supplierForest_actual_153085

def g32p_supplierForest_node_154724 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_154724 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154724 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_125936 := by
  decide +kernel

theorem g32p_supplierForest_actual_154724 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154724) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_154724
    g32p_supplierForest_actual_125936

def g32p_supplierForest_node_154757 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_154757 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154757 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122676 := by
  decide +kernel

theorem g32p_supplierForest_actual_154757 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154757) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_154757
    g32p_supplierForest_actual_122676

def g32p_supplierForest_node_154798 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_154798 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154798 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_124845 := by
  decide +kernel

theorem g32p_supplierForest_actual_154798 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154798) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_154798
    g32p_supplierForest_actual_124845

def g32p_supplierForest_node_154803 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_154803 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154803 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127338 := by
  decide +kernel

theorem g32p_supplierForest_actual_154803 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154803) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_154803
    g32p_supplierForest_actual_127338

def g32p_supplierForest_node_154856 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154856 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154856 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127446 := by
  decide +kernel

theorem g32p_supplierForest_actual_154856 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154856) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_154856
    g32p_supplierForest_actual_127446

def g32p_supplierForest_node_154874 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154874 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154874 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154565 := by
  decide +kernel

theorem g32p_supplierForest_actual_154874 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154874) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 2 g32p_supplierForest_edge_154874
    g32p_supplierForest_actual_154565

def g32p_supplierForest_node_154885 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_154885 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154885 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153727 := by
  decide +kernel

theorem g32p_supplierForest_actual_154885 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154885) ∧
        IsConj g (g32p_literalRepresentative 93) := by
  exact g32p_archive_step_lift _ _ 93 3 g32p_supplierForest_edge_154885
    g32p_supplierForest_actual_153727

def g32p_supplierForest_node_154914 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_154914 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154914 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154782 := by
  decide +kernel

theorem g32p_supplierForest_actual_154914 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154914) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_154914
    g32p_supplierForest_actual_154782

def g32p_supplierForest_node_154954 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_154954 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154954 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153458 := by
  decide +kernel

theorem g32p_supplierForest_actual_154954 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154954) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_154954
    g32p_supplierForest_actual_153458

def g32p_supplierForest_node_155063 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155063 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155063 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_137104 := by
  decide +kernel

theorem g32p_supplierForest_actual_155063 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155063) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 3 g32p_supplierForest_edge_155063
    g32p_supplierForest_actual_137104

def g32p_supplierForest_node_155071 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_155071 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155071 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_137065 := by
  decide +kernel

theorem g32p_supplierForest_actual_155071 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155071) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 3 g32p_supplierForest_edge_155071
    g32p_supplierForest_actual_137065

def g32p_supplierForest_node_155091 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_155091 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155091 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_139225 := by
  decide +kernel

theorem g32p_supplierForest_actual_155091 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155091) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 0 g32p_supplierForest_edge_155091
    g32p_supplierForest_actual_139225

def g32p_supplierForest_node_155110 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155110 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155110 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_143407 := by
  decide +kernel

theorem g32p_supplierForest_actual_155110 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155110) ∧
        IsConj g (g32p_literalRepresentative 94) := by
  exact g32p_archive_step_lift _ _ 94 2 g32p_supplierForest_edge_155110
    g32p_supplierForest_actual_143407

def g32p_supplierForest_node_155124 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155124 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155124 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_130493 := by
  decide +kernel

theorem g32p_supplierForest_actual_155124 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155124) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 1 g32p_supplierForest_edge_155124
    g32p_supplierForest_actual_130493

def g32p_supplierForest_node_155147 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_155147 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155147 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_139713 := by
  decide +kernel

theorem g32p_supplierForest_actual_155147 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155147) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 3 g32p_supplierForest_edge_155147
    g32p_supplierForest_actual_139713

def g32p_supplierForest_node_155154 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155154 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155154 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_155250 := by
  decide +kernel

theorem g32p_supplierForest_actual_155154 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155154) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 2 g32p_supplierForest_edge_155154
    g32p_supplierForest_actual_155250

def g32p_supplierForest_node_155158 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155158 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155158 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_155195 := by
  decide +kernel

theorem g32p_supplierForest_actual_155158 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155158) ∧
        IsConj g (g32p_literalRepresentative 76) := by
  exact g32p_archive_step_lift _ _ 76 1 g32p_supplierForest_edge_155158
    g32p_supplierForest_actual_155195

def g32p_supplierForest_node_155184 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155184 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155184 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_155169 := by
  decide +kernel

theorem g32p_supplierForest_actual_155184 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155184) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 2 g32p_supplierForest_edge_155184
    g32p_supplierForest_actual_155169

def g32p_supplierForest_node_155189 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155189 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155189 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_155195 := by
  decide +kernel

theorem g32p_supplierForest_actual_155189 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155189) ∧
        IsConj g (g32p_literalRepresentative 76) := by
  exact g32p_archive_step_lift _ _ 76 2 g32p_supplierForest_edge_155189
    g32p_supplierForest_actual_155195

def g32p_supplierForest_node_155192 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_155192 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155192 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_155325 := by
  decide +kernel

theorem g32p_supplierForest_actual_155192 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155192) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 2 g32p_supplierForest_edge_155192
    g32p_supplierForest_actual_155325

def g32p_supplierForest_node_155214 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155214 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155214 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_155082 := by
  decide +kernel

theorem g32p_supplierForest_actual_155214 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155214) ∧
        IsConj g (g32p_literalRepresentative 76) := by
  exact g32p_archive_step_lift _ _ 76 0 g32p_supplierForest_edge_155214
    g32p_supplierForest_actual_155082

def g32p_supplierForest_node_155227 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155227 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155227 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_155245 := by
  decide +kernel

theorem g32p_supplierForest_actual_155227 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155227) ∧
        IsConj g (g32p_literalRepresentative 76) := by
  exact g32p_archive_step_lift _ _ 76 1 g32p_supplierForest_edge_155227
    g32p_supplierForest_actual_155245

def g32p_supplierForest_node_155243 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155243 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155243 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_138940 := by
  decide +kernel

theorem g32p_supplierForest_actual_155243 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155243) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 2 g32p_supplierForest_edge_155243
    g32p_supplierForest_actual_138940

def g32p_supplierForest_node_155247 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155247 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155247 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_155294 := by
  decide +kernel

theorem g32p_supplierForest_actual_155247 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155247) ∧
        IsConj g (g32p_literalRepresentative 76) := by
  exact g32p_archive_step_lift _ _ 76 1 g32p_supplierForest_edge_155247
    g32p_supplierForest_actual_155294

def g32p_supplierForest_node_155254 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155254 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155254 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_155082 := by
  decide +kernel

theorem g32p_supplierForest_actual_155254 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155254) ∧
        IsConj g (g32p_literalRepresentative 76) := by
  exact g32p_archive_step_lift _ _ 76 1 g32p_supplierForest_edge_155254
    g32p_supplierForest_actual_155082

def g32p_supplierForest_node_155285 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155285 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155285 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_155136 := by
  decide +kernel

theorem g32p_supplierForest_actual_155285 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155285) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 2 g32p_supplierForest_edge_155285
    g32p_supplierForest_actual_155136

def g32p_supplierForest_node_155311 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155311 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155311 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_134821 := by
  decide +kernel

theorem g32p_supplierForest_actual_155311 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155311) ∧
        IsConj g (g32p_literalRepresentative 94) := by
  exact g32p_archive_step_lift _ _ 94 2 g32p_supplierForest_edge_155311
    g32p_supplierForest_actual_134821

def g32p_supplierForest_node_155315 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155315 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155315 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_144317 := by
  decide +kernel

theorem g32p_supplierForest_actual_155315 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155315) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 2 g32p_supplierForest_edge_155315
    g32p_supplierForest_actual_144317

def g32p_supplierForest_node_155326 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155326 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155326 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_132797 := by
  decide +kernel

theorem g32p_supplierForest_actual_155326 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155326) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 2 g32p_supplierForest_edge_155326
    g32p_supplierForest_actual_132797

def g32p_supplierForest_node_155407 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_155407 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155407 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_144359 := by
  decide +kernel

theorem g32p_supplierForest_actual_155407 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155407) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 2 g32p_supplierForest_edge_155407
    g32p_supplierForest_actual_144359

def g32p_supplierForest_node_155428 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155428 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155428 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_155317 := by
  decide +kernel

theorem g32p_supplierForest_actual_155428 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155428) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 3 g32p_supplierForest_edge_155428
    g32p_supplierForest_actual_155317

def g32p_supplierForest_node_155435 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_155435 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155435 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_143506 := by
  decide +kernel

theorem g32p_supplierForest_actual_155435 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155435) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 3 g32p_supplierForest_edge_155435
    g32p_supplierForest_actual_143506

def g32p_supplierForest_node_155463 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155463 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155463 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_144197 := by
  decide +kernel

theorem g32p_supplierForest_actual_155463 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155463) ∧
        IsConj g (g32p_literalRepresentative 94) := by
  exact g32p_archive_step_lift _ _ 94 2 g32p_supplierForest_edge_155463
    g32p_supplierForest_actual_144197

def g32p_supplierForest_node_155468 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155468 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155468 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_155245 := by
  decide +kernel

theorem g32p_supplierForest_actual_155468 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155468) ∧
        IsConj g (g32p_literalRepresentative 76) := by
  exact g32p_archive_step_lift _ _ 76 3 g32p_supplierForest_edge_155468
    g32p_supplierForest_actual_155245

def g32p_supplierForest_node_155477 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155477 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155477 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_155471 := by
  decide +kernel

theorem g32p_supplierForest_actual_155477 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155477) ∧
        IsConj g (g32p_literalRepresentative 100) := by
  exact g32p_archive_step_lift _ _ 100 2 g32p_supplierForest_edge_155477
    g32p_supplierForest_actual_155471

def g32p_supplierForest_node_155481 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155481 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155481 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_155486 := by
  decide +kernel

theorem g32p_supplierForest_actual_155481 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155481) ∧
        IsConj g (g32p_literalRepresentative 100) := by
  exact g32p_archive_step_lift _ _ 100 0 g32p_supplierForest_edge_155481
    g32p_supplierForest_actual_155486

def g32p_supplierForest_node_155487 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155487 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155487 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_155496 := by
  decide +kernel

theorem g32p_supplierForest_actual_155487 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155487) ∧
        IsConj g (g32p_literalRepresentative 100) := by
  exact g32p_archive_step_lift _ _ 100 1 g32p_supplierForest_edge_155487
    g32p_supplierForest_actual_155496

def g32p_supplierForest_node_155499 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_155499 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155499 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_155472 := by
  decide +kernel

theorem g32p_supplierForest_actual_155499 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155499) ∧
        IsConj g (g32p_literalRepresentative 100) := by
  exact g32p_archive_step_lift _ _ 100 1 g32p_supplierForest_edge_155499
    g32p_supplierForest_actual_155472

def g32p_supplierForest_node_155501 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155501 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155501 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_155474 := by
  decide +kernel

theorem g32p_supplierForest_actual_155501 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155501) ∧
        IsConj g (g32p_literalRepresentative 100) := by
  exact g32p_archive_step_lift _ _ 100 3 g32p_supplierForest_edge_155501
    g32p_supplierForest_actual_155474

def g32p_supplierForest_node_155508 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155508 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155508 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_155496 := by
  decide +kernel

theorem g32p_supplierForest_actual_155508 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155508) ∧
        IsConj g (g32p_literalRepresentative 100) := by
  exact g32p_archive_step_lift _ _ 100 2 g32p_supplierForest_edge_155508
    g32p_supplierForest_actual_155496

def g32p_supplierForest_node_155514 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155514 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155514 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_155507 := by
  decide +kernel

theorem g32p_supplierForest_actual_155514 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155514) ∧
        IsConj g (g32p_literalRepresentative 100) := by
  exact g32p_archive_step_lift _ _ 100 2 g32p_supplierForest_edge_155514
    g32p_supplierForest_actual_155507

def g32p_supplierForest_node_000029 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_000029 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000029 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_000750 := by
  decide +kernel

theorem g32p_supplierForest_actual_000029 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000029) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 1 g32p_supplierForest_edge_000029
    g32p_supplierForest_actual_000750

def g32p_supplierForest_node_000038 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000038 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000038 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000453 := by
  decide +kernel

theorem g32p_supplierForest_actual_000038 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000038) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 0 g32p_supplierForest_edge_000038
    g32p_supplierForest_actual_000453

def g32p_supplierForest_node_000227 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000227 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000227 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000013 := by
  decide +kernel

theorem g32p_supplierForest_actual_000227 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000227) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 0 g32p_supplierForest_edge_000227
    g32p_supplierForest_actual_000013

def g32p_supplierForest_node_000329 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_000329 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000329 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000323 := by
  decide +kernel

theorem g32p_supplierForest_actual_000329 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000329) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 3 g32p_supplierForest_edge_000329
    g32p_supplierForest_actual_000323

def g32p_supplierForest_node_000469 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000469 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000469 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000592 := by
  decide +kernel

theorem g32p_supplierForest_actual_000469 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000469) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 0 g32p_supplierForest_edge_000469
    g32p_supplierForest_actual_000592

def g32p_supplierForest_node_000476 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000476 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000476 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_000764 := by
  decide +kernel

theorem g32p_supplierForest_actual_000476 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000476) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 1 g32p_supplierForest_edge_000476
    g32p_supplierForest_actual_000764

def g32p_supplierForest_node_000479 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000479 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000479 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000991 := by
  decide +kernel

theorem g32p_supplierForest_actual_000479 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000479) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 3 g32p_supplierForest_edge_000479
    g32p_supplierForest_actual_000991

def g32p_supplierForest_node_000487 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000487 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000487 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000635 := by
  decide +kernel

theorem g32p_supplierForest_actual_000487 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000487) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 0 g32p_supplierForest_edge_000487
    g32p_supplierForest_actual_000635

def g32p_supplierForest_node_000492 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_000492 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000492 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000023 := by
  decide +kernel

theorem g32p_supplierForest_actual_000492 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000492) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 3 g32p_supplierForest_edge_000492
    g32p_supplierForest_actual_000023

def g32p_supplierForest_node_000552 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_000552 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000552 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_007705 := by
  decide +kernel

theorem g32p_supplierForest_actual_000552 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000552) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 3 g32p_supplierForest_edge_000552
    g32p_supplierForest_actual_007705

def g32p_supplierForest_node_000553 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000553 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000553 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012216 := by
  decide +kernel

theorem g32p_supplierForest_actual_000553 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000553) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 3 g32p_supplierForest_edge_000553
    g32p_supplierForest_actual_012216

def g32p_supplierForest_node_000567 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000567 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000567 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000807 := by
  decide +kernel

theorem g32p_supplierForest_actual_000567 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000567) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 0 g32p_supplierForest_edge_000567
    g32p_supplierForest_actual_000807

def g32p_supplierForest_node_000595 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000595 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000595 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000045 := by
  decide +kernel

theorem g32p_supplierForest_actual_000595 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000595) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 0 g32p_supplierForest_edge_000595
    g32p_supplierForest_actual_000045

def g32p_supplierForest_node_000601 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_000601 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000601 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000907 := by
  decide +kernel

theorem g32p_supplierForest_actual_000601 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000601) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 0 g32p_supplierForest_edge_000601
    g32p_supplierForest_actual_000907

def g32p_supplierForest_node_000639 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000639 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000639 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000031 := by
  decide +kernel

theorem g32p_supplierForest_actual_000639 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000639) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 2 g32p_supplierForest_edge_000639
    g32p_supplierForest_actual_000031

def g32p_supplierForest_node_000702 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_000702 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000702 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_000603 := by
  decide +kernel

theorem g32p_supplierForest_actual_000702 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000702) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 1 g32p_supplierForest_edge_000702
    g32p_supplierForest_actual_000603

def g32p_supplierForest_node_000706 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000706 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000706 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_000027 := by
  decide +kernel

theorem g32p_supplierForest_actual_000706 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000706) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 1 g32p_supplierForest_edge_000706
    g32p_supplierForest_actual_000027

def g32p_supplierForest_node_000713 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_000713 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000713 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_008288 := by
  decide +kernel

theorem g32p_supplierForest_actual_000713 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000713) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 2 g32p_supplierForest_edge_000713
    g32p_supplierForest_actual_008288

def g32p_supplierForest_node_000719 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000719 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000719 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_000643 := by
  decide +kernel

theorem g32p_supplierForest_actual_000719 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000719) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 1 g32p_supplierForest_edge_000719
    g32p_supplierForest_actual_000643

def g32p_supplierForest_node_000722 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_000722 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000722 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_000649 := by
  decide +kernel

theorem g32p_supplierForest_actual_000722 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000722) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 1 g32p_supplierForest_edge_000722
    g32p_supplierForest_actual_000649

def g32p_supplierForest_node_000761 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000761 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000761 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_000807 := by
  decide +kernel

theorem g32p_supplierForest_actual_000761 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000761) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 1 g32p_supplierForest_edge_000761
    g32p_supplierForest_actual_000807

def g32p_supplierForest_node_000765 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_000765 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000765 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_005980 := by
  decide +kernel

theorem g32p_supplierForest_actual_000765 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000765) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 0 g32p_supplierForest_edge_000765
    g32p_supplierForest_actual_005980

def g32p_supplierForest_node_000784 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000784 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000784 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_011101 := by
  decide +kernel

theorem g32p_supplierForest_actual_000784 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000784) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 2 g32p_supplierForest_edge_000784
    g32p_supplierForest_actual_011101

def g32p_supplierForest_node_000785 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000785 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000785 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_000856 := by
  decide +kernel

theorem g32p_supplierForest_actual_000785 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000785) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 1 g32p_supplierForest_edge_000785
    g32p_supplierForest_actual_000856

def g32p_supplierForest_node_000815 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_000815 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000815 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000764 := by
  decide +kernel

theorem g32p_supplierForest_actual_000815 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000815) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 2 g32p_supplierForest_edge_000815
    g32p_supplierForest_actual_000764

def g32p_supplierForest_node_000828 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_000828 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000828 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_000963 := by
  decide +kernel

theorem g32p_supplierForest_actual_000828 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000828) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_000828
    g32p_supplierForest_actual_000963

def g32p_supplierForest_node_000853 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_000853 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000853 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_006181 := by
  decide +kernel

theorem g32p_supplierForest_actual_000853 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000853) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 0 g32p_supplierForest_edge_000853
    g32p_supplierForest_actual_006181

def g32p_supplierForest_node_000974 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_000974 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000974 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_006451 := by
  decide +kernel

theorem g32p_supplierForest_actual_000974 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000974) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 0 g32p_supplierForest_edge_000974
    g32p_supplierForest_actual_006451

def g32p_supplierForest_node_001029 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001029 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001029 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000592 := by
  decide +kernel

theorem g32p_supplierForest_actual_001029 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001029) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 3 g32p_supplierForest_edge_001029
    g32p_supplierForest_actual_000592

def g32p_supplierForest_node_001091 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001091 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001091 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018813 := by
  decide +kernel

theorem g32p_supplierForest_actual_001091 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001091) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_001091
    g32p_supplierForest_actual_018813

def g32p_supplierForest_node_001092 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_001092 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001092 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_001334 := by
  decide +kernel

theorem g32p_supplierForest_actual_001092 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001092) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_001092
    g32p_supplierForest_actual_001334

def g32p_supplierForest_node_001165 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001165 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001165 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001461 := by
  decide +kernel

theorem g32p_supplierForest_actual_001165 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001165) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001165
    g32p_supplierForest_actual_001461

def g32p_supplierForest_node_001197 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_001197 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001197 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001538 := by
  decide +kernel

theorem g32p_supplierForest_actual_001197 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001197) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001197
    g32p_supplierForest_actual_001538

def g32p_supplierForest_node_001208 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_001208 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001208 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001558 := by
  decide +kernel

theorem g32p_supplierForest_actual_001208 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001208) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 0 g32p_supplierForest_edge_001208
    g32p_supplierForest_actual_001558

def g32p_supplierForest_node_001220 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001220 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001220 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001588 := by
  decide +kernel

theorem g32p_supplierForest_actual_001220 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001220) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001220
    g32p_supplierForest_actual_001588

def g32p_supplierForest_node_001271 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_001271 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001271 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001707 := by
  decide +kernel

theorem g32p_supplierForest_actual_001271 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001271) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_001271
    g32p_supplierForest_actual_001707

def g32p_supplierForest_node_001295 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_001295 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001295 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014731 := by
  decide +kernel

theorem g32p_supplierForest_actual_001295 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001295) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_001295
    g32p_supplierForest_actual_014731

def g32p_supplierForest_node_001302 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001302 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001302 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_001443 := by
  decide +kernel

theorem g32p_supplierForest_actual_001302 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001302) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001302
    g32p_supplierForest_actual_001443

def g32p_supplierForest_node_001308 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001308 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001308 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001789 := by
  decide +kernel

theorem g32p_supplierForest_actual_001308 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001308) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001308
    g32p_supplierForest_actual_001789

def g32p_supplierForest_node_001322 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001322 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001322 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015945 := by
  decide +kernel

theorem g32p_supplierForest_actual_001322 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001322) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_001322
    g32p_supplierForest_actual_015945

def g32p_supplierForest_node_001332 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_001332 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001332 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_014256 := by
  decide +kernel

theorem g32p_supplierForest_actual_001332 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001332) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_001332
    g32p_supplierForest_actual_014256

def g32p_supplierForest_node_001342 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_001342 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001342 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001850 := by
  decide +kernel

theorem g32p_supplierForest_actual_001342 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001342) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_001342
    g32p_supplierForest_actual_001850

def g32p_supplierForest_node_001384 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_001384 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001384 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021953 := by
  decide +kernel

theorem g32p_supplierForest_actual_001384 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001384) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 3 g32p_supplierForest_edge_001384
    g32p_supplierForest_actual_021953

def g32p_supplierForest_node_001425 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001425 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001425 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_014449 := by
  decide +kernel

theorem g32p_supplierForest_actual_001425 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001425) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001425
    g32p_supplierForest_actual_014449

def g32p_supplierForest_node_001444 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001444 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001444 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_014481 := by
  decide +kernel

theorem g32p_supplierForest_actual_001444 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001444) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001444
    g32p_supplierForest_actual_014481

def g32p_supplierForest_node_001447 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001447 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001447 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_002018 := by
  decide +kernel

theorem g32p_supplierForest_actual_001447 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001447) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 0 g32p_supplierForest_edge_001447
    g32p_supplierForest_actual_002018

def g32p_supplierForest_node_001463 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_001463 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001463 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016406 := by
  decide +kernel

theorem g32p_supplierForest_actual_001463 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001463) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 3 g32p_supplierForest_edge_001463
    g32p_supplierForest_actual_016406

def g32p_supplierForest_node_001502 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001502 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001502 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000138 := by
  decide +kernel

theorem g32p_supplierForest_actual_001502 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001502) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 0 g32p_supplierForest_edge_001502
    g32p_supplierForest_actual_000138

def g32p_supplierForest_node_001508 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001508 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001508 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_014731 := by
  decide +kernel

theorem g32p_supplierForest_actual_001508 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001508) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001508
    g32p_supplierForest_actual_014731

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_024 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_073186 else g32p_supplierForest_node_073239) else (if i.val < 3 then g32p_supplierForest_node_073286 else g32p_supplierForest_node_073289)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_073325 else g32p_supplierForest_node_073373) else (if i.val < 7 then g32p_supplierForest_node_073383 else g32p_supplierForest_node_073394))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_073450 else g32p_supplierForest_node_073452) else (if i.val < 11 then g32p_supplierForest_node_073460 else g32p_supplierForest_node_073461)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_073495 else g32p_supplierForest_node_073497) else (if i.val < 15 then g32p_supplierForest_node_073504 else g32p_supplierForest_node_073585)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_073606 else g32p_supplierForest_node_073633) else (if i.val < 19 then g32p_supplierForest_node_073649 else g32p_supplierForest_node_073654)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_073679 else g32p_supplierForest_node_073685) else (if i.val < 23 then g32p_supplierForest_node_073711 else g32p_supplierForest_node_073727))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_073758 else g32p_supplierForest_node_073776) else (if i.val < 27 then g32p_supplierForest_node_073805 else g32p_supplierForest_node_073891)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_073921 else g32p_supplierForest_node_073963) else (if i.val < 31 then g32p_supplierForest_node_074000 else g32p_supplierForest_node_074005))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_074009 else g32p_supplierForest_node_074030) else (if i.val < 35 then g32p_supplierForest_node_074074 else g32p_supplierForest_node_074131)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_074184 else g32p_supplierForest_node_074200) else (if i.val < 39 then g32p_supplierForest_node_074205 else g32p_supplierForest_node_074284))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_074291 else g32p_supplierForest_node_074342) else (if i.val < 43 then g32p_supplierForest_node_074374 else g32p_supplierForest_node_074445)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_074456 else g32p_supplierForest_node_074465) else (if i.val < 47 then g32p_supplierForest_node_074475 else g32p_supplierForest_node_074504)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_074602 else g32p_supplierForest_node_074614) else (if i.val < 51 then g32p_supplierForest_node_074695 else g32p_supplierForest_node_074787)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_074789 else g32p_supplierForest_node_074854) else (if i.val < 55 then g32p_supplierForest_node_074901 else g32p_supplierForest_node_074916))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_075036 else g32p_supplierForest_node_075159) else (if i.val < 59 then g32p_supplierForest_node_075176 else g32p_supplierForest_node_075182)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_075214 else g32p_supplierForest_node_075217) else (if i.val < 63 then g32p_supplierForest_node_075264 else g32p_supplierForest_node_075284)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_075386 else g32p_supplierForest_node_075405) else (if i.val < 67 then g32p_supplierForest_node_075447 else g32p_supplierForest_node_075459)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_075463 else g32p_supplierForest_node_075465) else (if i.val < 71 then g32p_supplierForest_node_075469 else g32p_supplierForest_node_075531))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_075534 else g32p_supplierForest_node_075582) else (if i.val < 75 then g32p_supplierForest_node_075655 else g32p_supplierForest_node_075667)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_075774 else g32p_supplierForest_node_075779) else (if i.val < 79 then g32p_supplierForest_node_075785 else g32p_supplierForest_node_075786)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_075792 else g32p_supplierForest_node_075801) else (if i.val < 83 then g32p_supplierForest_node_075821 else g32p_supplierForest_node_075855)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_075906 else g32p_supplierForest_node_075968) else (if i.val < 87 then g32p_supplierForest_node_076174 else g32p_supplierForest_node_076208))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_076223 else g32p_supplierForest_node_076258) else (if i.val < 91 then g32p_supplierForest_node_076319 else g32p_supplierForest_node_076326)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_076373 else g32p_supplierForest_node_076390) else (if i.val < 95 then g32p_supplierForest_node_076401 else g32p_supplierForest_node_076406))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_076451 else g32p_supplierForest_node_076477) else (if i.val < 99 then g32p_supplierForest_node_076516 else g32p_supplierForest_node_076662)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_076665 else g32p_supplierForest_node_076767) else (if i.val < 103 then g32p_supplierForest_node_076780 else g32p_supplierForest_node_076898))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_076943 else g32p_supplierForest_node_076948) else (if i.val < 107 then g32p_supplierForest_node_077044 else g32p_supplierForest_node_077081)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_077110 else g32p_supplierForest_node_077188) else (if i.val < 111 then g32p_supplierForest_node_077194 else g32p_supplierForest_node_077197)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_077211 else g32p_supplierForest_node_077250) else (if i.val < 115 then g32p_supplierForest_node_077271 else g32p_supplierForest_node_077290)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_077296 else g32p_supplierForest_node_077321) else (if i.val < 119 then g32p_supplierForest_node_077370 else g32p_supplierForest_node_077394))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_077405 else g32p_supplierForest_node_077456) else (if i.val < 123 then g32p_supplierForest_node_077463 else g32p_supplierForest_node_077474)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_077491 else g32p_supplierForest_node_077537) else (if i.val < 127 then g32p_supplierForest_node_077547 else g32p_supplierForest_node_077564))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_077576 else g32p_supplierForest_node_077783) else (if i.val < 131 then g32p_supplierForest_node_077822 else g32p_supplierForest_node_077841)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_077845 else g32p_supplierForest_node_077921) else (if i.val < 135 then g32p_supplierForest_node_077923 else g32p_supplierForest_node_078020))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_078051 else g32p_supplierForest_node_078052) else (if i.val < 139 then g32p_supplierForest_node_078079 else g32p_supplierForest_node_078097)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_078109 else g32p_supplierForest_node_078155) else (if i.val < 143 then g32p_supplierForest_node_078255 else g32p_supplierForest_node_078304)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_078385 else g32p_supplierForest_node_078399) else (if i.val < 147 then g32p_supplierForest_node_078404 else g32p_supplierForest_node_078409)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_078426 else g32p_supplierForest_node_078499) else (if i.val < 151 then g32p_supplierForest_node_078540 else g32p_supplierForest_node_078543))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_078545 else g32p_supplierForest_node_078569) else (if i.val < 155 then g32p_supplierForest_node_078700 else g32p_supplierForest_node_078808)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_078842 else g32p_supplierForest_node_078912) else (if i.val < 159 then g32p_supplierForest_node_078974 else g32p_supplierForest_node_079006))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_079019 else g32p_supplierForest_node_079028) else (if i.val < 163 then g32p_supplierForest_node_079056 else g32p_supplierForest_node_079165)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_079189 else g32p_supplierForest_node_079196) else (if i.val < 167 then g32p_supplierForest_node_079198 else g32p_supplierForest_node_079249))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_079284 else g32p_supplierForest_node_079310) else (if i.val < 171 then g32p_supplierForest_node_079324 else g32p_supplierForest_node_079397)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_079445 else g32p_supplierForest_node_079461) else (if i.val < 175 then g32p_supplierForest_node_079569 else g32p_supplierForest_node_079590)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_079598 else g32p_supplierForest_node_079700) else (if i.val < 179 then g32p_supplierForest_node_079796 else g32p_supplierForest_node_079890)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_079900 else g32p_supplierForest_node_079905) else (if i.val < 183 then g32p_supplierForest_node_079939 else g32p_supplierForest_node_079970))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_079993 else g32p_supplierForest_node_080011) else (if i.val < 187 then g32p_supplierForest_node_080012 else g32p_supplierForest_node_080025)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_080067 else g32p_supplierForest_node_080090) else (if i.val < 191 then g32p_supplierForest_node_080105 else g32p_supplierForest_node_080108)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_080129 else g32p_supplierForest_node_080179) else (if i.val < 195 then g32p_supplierForest_node_080229 else g32p_supplierForest_node_080291)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_080395 else g32p_supplierForest_node_080462) else (if i.val < 199 then g32p_supplierForest_node_080473 else g32p_supplierForest_node_080525))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_080543 else g32p_supplierForest_node_080590) else (if i.val < 203 then g32p_supplierForest_node_080797 else g32p_supplierForest_node_080842)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_080983 else g32p_supplierForest_node_081005) else (if i.val < 207 then g32p_supplierForest_node_081044 else g32p_supplierForest_node_081069)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_081071 else g32p_supplierForest_node_081147) else (if i.val < 211 then g32p_supplierForest_node_081149 else g32p_supplierForest_node_081209)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_081232 else g32p_supplierForest_node_081347) else (if i.val < 215 then g32p_supplierForest_node_081480 else g32p_supplierForest_node_081490))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_081506 else g32p_supplierForest_node_081548) else (if i.val < 219 then g32p_supplierForest_node_081595 else g32p_supplierForest_node_081640)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_081699 else g32p_supplierForest_node_081718) else (if i.val < 223 then g32p_supplierForest_node_081728 else g32p_supplierForest_node_081772))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_081803 else g32p_supplierForest_node_081809) else (if i.val < 227 then g32p_supplierForest_node_081850 else g32p_supplierForest_node_081895)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_081896 else g32p_supplierForest_node_081972) else (if i.val < 231 then g32p_supplierForest_node_081973 else g32p_supplierForest_node_082101))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_082108 else g32p_supplierForest_node_082128) else (if i.val < 235 then g32p_supplierForest_node_082250 else g32p_supplierForest_node_082282)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_082332 else g32p_supplierForest_node_082352) else (if i.val < 239 then g32p_supplierForest_node_082362 else g32p_supplierForest_node_082390)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_082561 else g32p_supplierForest_node_082569) else (if i.val < 243 then g32p_supplierForest_node_082596 else g32p_supplierForest_node_082601)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_082631 else g32p_supplierForest_node_082665) else (if i.val < 247 then g32p_supplierForest_node_082715 else g32p_supplierForest_node_082747))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_082799 else g32p_supplierForest_node_082814) else (if i.val < 251 then g32p_supplierForest_node_082837 else g32p_supplierForest_node_082853)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_082894 else g32p_supplierForest_node_082952) else (if i.val < 255 then g32p_supplierForest_node_083025 else g32p_supplierForest_node_083060))))))))

def g32p_supplierForest_classes_024 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 26 else 13) else (if i.val < 3 then 47 else 47)) else (if i.val < 6 then (if i.val < 5 then 84 else 27) else (if i.val < 7 then 56 else 26))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 10 else 50) else (if i.val < 11 then 83 else 46)) else (if i.val < 14 then (if i.val < 13 then 46 else 25) else (if i.val < 15 then 46 else 47)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 46 else 9) else (if i.val < 19 then 26 else 46)) else (if i.val < 22 then (if i.val < 21 then 10 else 27) else (if i.val < 23 then 13 else 12))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 27 else 10) else (if i.val < 27 then 46 else 26)) else (if i.val < 30 then (if i.val < 29 then 84 else 10) else (if i.val < 31 then 46 else 83))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 83 else 13) else (if i.val < 35 then 49 else 27)) else (if i.val < 38 then (if i.val < 37 then 83 else 49) else (if i.val < 39 then 83 else 46))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 11 else 13) else (if i.val < 43 then 50 else 46)) else (if i.val < 46 then (if i.val < 45 then 50 else 26) else (if i.val < 47 then 49 else 27)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 26 else 54) else (if i.val < 51 then 84 else 46)) else (if i.val < 54 then (if i.val < 53 then 12 else 80) else (if i.val < 55 then 27 else 46))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 84 else 84) else (if i.val < 59 then 25 else 9)) else (if i.val < 62 then (if i.val < 61 then 46 else 46) else (if i.val < 63 then 25 else 12)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 84 else 46) else (if i.val < 67 then 46 else 25)) else (if i.val < 70 then (if i.val < 69 then 46 else 45) else (if i.val < 71 then 54 else 9))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 49 else 83) else (if i.val < 75 then 50 else 45)) else (if i.val < 78 then (if i.val < 77 then 11 else 53) else (if i.val < 79 then 48 else 46)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 46 else 26) else (if i.val < 83 then 46 else 83)) else (if i.val < 86 then (if i.val < 85 then 84 else 84) else (if i.val < 87 then 27 else 49))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 12 else 49) else (if i.val < 91 then 85 else 84)) else (if i.val < 94 then (if i.val < 93 then 10 else 54) else (if i.val < 95 then 83 else 50))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 26 else 47) else (if i.val < 99 then 50 else 11)) else (if i.val < 102 then (if i.val < 101 then 56 else 49) else (if i.val < 103 then 50 else 52))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 46 else 45) else (if i.val < 107 then 46 else 80)) else (if i.val < 110 then (if i.val < 109 then 80 else 49) else (if i.val < 111 then 83 else 13)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 54 else 46) else (if i.val < 115 then 53 else 53)) else (if i.val < 118 then (if i.val < 117 then 49 else 49) else (if i.val < 119 then 51 else 47))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 47 else 25) else (if i.val < 123 then 55 else 45)) else (if i.val < 126 then (if i.val < 125 then 48 else 46) else (if i.val < 127 then 47 else 46))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 47 else 26) else (if i.val < 131 then 46 else 84)) else (if i.val < 134 then (if i.val < 133 then 11 else 83) else (if i.val < 135 then 83 else 45))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 80 else 80) else (if i.val < 139 then 84 else 84)) else (if i.val < 142 then (if i.val < 141 then 48 else 83) else (if i.val < 143 then 48 else 48)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 50 else 49) else (if i.val < 147 then 50 else 84)) else (if i.val < 150 then (if i.val < 149 then 50 else 47) else (if i.val < 151 then 52 else 49))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 13 else 53) else (if i.val < 155 then 47 else 86)) else (if i.val < 158 then (if i.val < 157 then 13 else 11) else (if i.val < 159 then 13 else 10))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 52 else 50) else (if i.val < 163 then 13 else 48)) else (if i.val < 166 then (if i.val < 165 then 25 else 45) else (if i.val < 167 then 49 else 82))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 52 else 48) else (if i.val < 171 then 46 else 10)) else (if i.val < 174 then (if i.val < 173 then 49 else 52) else (if i.val < 175 then 49 else 47)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 47 else 27) else (if i.val < 179 then 83 else 13)) else (if i.val < 182 then (if i.val < 181 then 9 else 8) else (if i.val < 183 then 47 else 81))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 13 else 49) else (if i.val < 187 then 47 else 49)) else (if i.val < 190 then (if i.val < 189 then 25 else 49) else (if i.val < 191 then 48 else 26)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 52 else 84) else (if i.val < 195 then 56 else 25)) else (if i.val < 198 then (if i.val < 197 then 48 else 47) else (if i.val < 199 then 11 else 56))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 52 else 84) else (if i.val < 203 then 50 else 53)) else (if i.val < 206 then (if i.val < 205 then 11 else 49) else (if i.val < 207 then 85 else 46)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 26 else 49) else (if i.val < 211 then 84 else 9)) else (if i.val < 214 then (if i.val < 213 then 10 else 84) else (if i.val < 215 then 47 else 49))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 26 else 49) else (if i.val < 219 then 9 else 47)) else (if i.val < 222 then (if i.val < 221 then 27 else 83) else (if i.val < 223 then 26 else 49))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 49 else 25) else (if i.val < 227 then 47 else 45)) else (if i.val < 230 then (if i.val < 229 then 25 else 46) else (if i.val < 231 then 48 else 47))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 46 else 49) else (if i.val < 235 then 83 else 50)) else (if i.val < 238 then (if i.val < 237 then 55 else 56) else (if i.val < 239 then 47 else 56)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 50 else 9) else (if i.val < 243 then 49 else 46)) else (if i.val < 246 then (if i.val < 245 then 25 else 84) else (if i.val < 247 then 45 else 82))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 9 else 84) else (if i.val < 251 then 50 else 13)) else (if i.val < 254 then (if i.val < 253 then 49 else 49) else (if i.val < 255 then 56 else 56))))))))

theorem g32p_supplierForest_actual_024 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_024 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_024 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_073186
  · exact g32p_supplierForest_actual_073239
  · exact g32p_supplierForest_actual_073286
  · exact g32p_supplierForest_actual_073289
  · exact g32p_supplierForest_actual_073325
  · exact g32p_supplierForest_actual_073373
  · exact g32p_supplierForest_actual_073383
  · exact g32p_supplierForest_actual_073394
  · exact g32p_supplierForest_actual_073450
  · exact g32p_supplierForest_actual_073452
  · exact g32p_supplierForest_actual_073460
  · exact g32p_supplierForest_actual_073461
  · exact g32p_supplierForest_actual_073495
  · exact g32p_supplierForest_actual_073497
  · exact g32p_supplierForest_actual_073504
  · exact g32p_supplierForest_actual_073585
  · exact g32p_supplierForest_actual_073606
  · exact g32p_supplierForest_actual_073633
  · exact g32p_supplierForest_actual_073649
  · exact g32p_supplierForest_actual_073654
  · exact g32p_supplierForest_actual_073679
  · exact g32p_supplierForest_actual_073685
  · exact g32p_supplierForest_actual_073711
  · exact g32p_supplierForest_actual_073727
  · exact g32p_supplierForest_actual_073758
  · exact g32p_supplierForest_actual_073776
  · exact g32p_supplierForest_actual_073805
  · exact g32p_supplierForest_actual_073891
  · exact g32p_supplierForest_actual_073921
  · exact g32p_supplierForest_actual_073963
  · exact g32p_supplierForest_actual_074000
  · exact g32p_supplierForest_actual_074005
  · exact g32p_supplierForest_actual_074009
  · exact g32p_supplierForest_actual_074030
  · exact g32p_supplierForest_actual_074074
  · exact g32p_supplierForest_actual_074131
  · exact g32p_supplierForest_actual_074184
  · exact g32p_supplierForest_actual_074200
  · exact g32p_supplierForest_actual_074205
  · exact g32p_supplierForest_actual_074284
  · exact g32p_supplierForest_actual_074291
  · exact g32p_supplierForest_actual_074342
  · exact g32p_supplierForest_actual_074374
  · exact g32p_supplierForest_actual_074445
  · exact g32p_supplierForest_actual_074456
  · exact g32p_supplierForest_actual_074465
  · exact g32p_supplierForest_actual_074475
  · exact g32p_supplierForest_actual_074504
  · exact g32p_supplierForest_actual_074602
  · exact g32p_supplierForest_actual_074614
  · exact g32p_supplierForest_actual_074695
  · exact g32p_supplierForest_actual_074787
  · exact g32p_supplierForest_actual_074789
  · exact g32p_supplierForest_actual_074854
  · exact g32p_supplierForest_actual_074901
  · exact g32p_supplierForest_actual_074916
  · exact g32p_supplierForest_actual_075036
  · exact g32p_supplierForest_actual_075159
  · exact g32p_supplierForest_actual_075176
  · exact g32p_supplierForest_actual_075182
  · exact g32p_supplierForest_actual_075214
  · exact g32p_supplierForest_actual_075217
  · exact g32p_supplierForest_actual_075264
  · exact g32p_supplierForest_actual_075284
  · exact g32p_supplierForest_actual_075386
  · exact g32p_supplierForest_actual_075405
  · exact g32p_supplierForest_actual_075447
  · exact g32p_supplierForest_actual_075459
  · exact g32p_supplierForest_actual_075463
  · exact g32p_supplierForest_actual_075465
  · exact g32p_supplierForest_actual_075469
  · exact g32p_supplierForest_actual_075531
  · exact g32p_supplierForest_actual_075534
  · exact g32p_supplierForest_actual_075582
  · exact g32p_supplierForest_actual_075655
  · exact g32p_supplierForest_actual_075667
  · exact g32p_supplierForest_actual_075774
  · exact g32p_supplierForest_actual_075779
  · exact g32p_supplierForest_actual_075785
  · exact g32p_supplierForest_actual_075786
  · exact g32p_supplierForest_actual_075792
  · exact g32p_supplierForest_actual_075801
  · exact g32p_supplierForest_actual_075821
  · exact g32p_supplierForest_actual_075855
  · exact g32p_supplierForest_actual_075906
  · exact g32p_supplierForest_actual_075968
  · exact g32p_supplierForest_actual_076174
  · exact g32p_supplierForest_actual_076208
  · exact g32p_supplierForest_actual_076223
  · exact g32p_supplierForest_actual_076258
  · exact g32p_supplierForest_actual_076319
  · exact g32p_supplierForest_actual_076326
  · exact g32p_supplierForest_actual_076373
  · exact g32p_supplierForest_actual_076390
  · exact g32p_supplierForest_actual_076401
  · exact g32p_supplierForest_actual_076406
  · exact g32p_supplierForest_actual_076451
  · exact g32p_supplierForest_actual_076477
  · exact g32p_supplierForest_actual_076516
  · exact g32p_supplierForest_actual_076662
  · exact g32p_supplierForest_actual_076665
  · exact g32p_supplierForest_actual_076767
  · exact g32p_supplierForest_actual_076780
  · exact g32p_supplierForest_actual_076898
  · exact g32p_supplierForest_actual_076943
  · exact g32p_supplierForest_actual_076948
  · exact g32p_supplierForest_actual_077044
  · exact g32p_supplierForest_actual_077081
  · exact g32p_supplierForest_actual_077110
  · exact g32p_supplierForest_actual_077188
  · exact g32p_supplierForest_actual_077194
  · exact g32p_supplierForest_actual_077197
  · exact g32p_supplierForest_actual_077211
  · exact g32p_supplierForest_actual_077250
  · exact g32p_supplierForest_actual_077271
  · exact g32p_supplierForest_actual_077290
  · exact g32p_supplierForest_actual_077296
  · exact g32p_supplierForest_actual_077321
  · exact g32p_supplierForest_actual_077370
  · exact g32p_supplierForest_actual_077394
  · exact g32p_supplierForest_actual_077405
  · exact g32p_supplierForest_actual_077456
  · exact g32p_supplierForest_actual_077463
  · exact g32p_supplierForest_actual_077474
  · exact g32p_supplierForest_actual_077491
  · exact g32p_supplierForest_actual_077537
  · exact g32p_supplierForest_actual_077547
  · exact g32p_supplierForest_actual_077564
  · exact g32p_supplierForest_actual_077576
  · exact g32p_supplierForest_actual_077783
  · exact g32p_supplierForest_actual_077822
  · exact g32p_supplierForest_actual_077841
  · exact g32p_supplierForest_actual_077845
  · exact g32p_supplierForest_actual_077921
  · exact g32p_supplierForest_actual_077923
  · exact g32p_supplierForest_actual_078020
  · exact g32p_supplierForest_actual_078051
  · exact g32p_supplierForest_actual_078052
  · exact g32p_supplierForest_actual_078079
  · exact g32p_supplierForest_actual_078097
  · exact g32p_supplierForest_actual_078109
  · exact g32p_supplierForest_actual_078155
  · exact g32p_supplierForest_actual_078255
  · exact g32p_supplierForest_actual_078304
  · exact g32p_supplierForest_actual_078385
  · exact g32p_supplierForest_actual_078399
  · exact g32p_supplierForest_actual_078404
  · exact g32p_supplierForest_actual_078409
  · exact g32p_supplierForest_actual_078426
  · exact g32p_supplierForest_actual_078499
  · exact g32p_supplierForest_actual_078540
  · exact g32p_supplierForest_actual_078543
  · exact g32p_supplierForest_actual_078545
  · exact g32p_supplierForest_actual_078569
  · exact g32p_supplierForest_actual_078700
  · exact g32p_supplierForest_actual_078808
  · exact g32p_supplierForest_actual_078842
  · exact g32p_supplierForest_actual_078912
  · exact g32p_supplierForest_actual_078974
  · exact g32p_supplierForest_actual_079006
  · exact g32p_supplierForest_actual_079019
  · exact g32p_supplierForest_actual_079028
  · exact g32p_supplierForest_actual_079056
  · exact g32p_supplierForest_actual_079165
  · exact g32p_supplierForest_actual_079189
  · exact g32p_supplierForest_actual_079196
  · exact g32p_supplierForest_actual_079198
  · exact g32p_supplierForest_actual_079249
  · exact g32p_supplierForest_actual_079284
  · exact g32p_supplierForest_actual_079310
  · exact g32p_supplierForest_actual_079324
  · exact g32p_supplierForest_actual_079397
  · exact g32p_supplierForest_actual_079445
  · exact g32p_supplierForest_actual_079461
  · exact g32p_supplierForest_actual_079569
  · exact g32p_supplierForest_actual_079590
  · exact g32p_supplierForest_actual_079598
  · exact g32p_supplierForest_actual_079700
  · exact g32p_supplierForest_actual_079796
  · exact g32p_supplierForest_actual_079890
  · exact g32p_supplierForest_actual_079900
  · exact g32p_supplierForest_actual_079905
  · exact g32p_supplierForest_actual_079939
  · exact g32p_supplierForest_actual_079970
  · exact g32p_supplierForest_actual_079993
  · exact g32p_supplierForest_actual_080011
  · exact g32p_supplierForest_actual_080012
  · exact g32p_supplierForest_actual_080025
  · exact g32p_supplierForest_actual_080067
  · exact g32p_supplierForest_actual_080090
  · exact g32p_supplierForest_actual_080105
  · exact g32p_supplierForest_actual_080108
  · exact g32p_supplierForest_actual_080129
  · exact g32p_supplierForest_actual_080179
  · exact g32p_supplierForest_actual_080229
  · exact g32p_supplierForest_actual_080291
  · exact g32p_supplierForest_actual_080395
  · exact g32p_supplierForest_actual_080462
  · exact g32p_supplierForest_actual_080473
  · exact g32p_supplierForest_actual_080525
  · exact g32p_supplierForest_actual_080543
  · exact g32p_supplierForest_actual_080590
  · exact g32p_supplierForest_actual_080797
  · exact g32p_supplierForest_actual_080842
  · exact g32p_supplierForest_actual_080983
  · exact g32p_supplierForest_actual_081005
  · exact g32p_supplierForest_actual_081044
  · exact g32p_supplierForest_actual_081069
  · exact g32p_supplierForest_actual_081071
  · exact g32p_supplierForest_actual_081147
  · exact g32p_supplierForest_actual_081149
  · exact g32p_supplierForest_actual_081209
  · exact g32p_supplierForest_actual_081232
  · exact g32p_supplierForest_actual_081347
  · exact g32p_supplierForest_actual_081480
  · exact g32p_supplierForest_actual_081490
  · exact g32p_supplierForest_actual_081506
  · exact g32p_supplierForest_actual_081548
  · exact g32p_supplierForest_actual_081595
  · exact g32p_supplierForest_actual_081640
  · exact g32p_supplierForest_actual_081699
  · exact g32p_supplierForest_actual_081718
  · exact g32p_supplierForest_actual_081728
  · exact g32p_supplierForest_actual_081772
  · exact g32p_supplierForest_actual_081803
  · exact g32p_supplierForest_actual_081809
  · exact g32p_supplierForest_actual_081850
  · exact g32p_supplierForest_actual_081895
  · exact g32p_supplierForest_actual_081896
  · exact g32p_supplierForest_actual_081972
  · exact g32p_supplierForest_actual_081973
  · exact g32p_supplierForest_actual_082101
  · exact g32p_supplierForest_actual_082108
  · exact g32p_supplierForest_actual_082128
  · exact g32p_supplierForest_actual_082250
  · exact g32p_supplierForest_actual_082282
  · exact g32p_supplierForest_actual_082332
  · exact g32p_supplierForest_actual_082352
  · exact g32p_supplierForest_actual_082362
  · exact g32p_supplierForest_actual_082390
  · exact g32p_supplierForest_actual_082561
  · exact g32p_supplierForest_actual_082569
  · exact g32p_supplierForest_actual_082596
  · exact g32p_supplierForest_actual_082601
  · exact g32p_supplierForest_actual_082631
  · exact g32p_supplierForest_actual_082665
  · exact g32p_supplierForest_actual_082715
  · exact g32p_supplierForest_actual_082747
  · exact g32p_supplierForest_actual_082799
  · exact g32p_supplierForest_actual_082814
  · exact g32p_supplierForest_actual_082837
  · exact g32p_supplierForest_actual_082853
  · exact g32p_supplierForest_actual_082894
  · exact g32p_supplierForest_actual_082952
  · exact g32p_supplierForest_actual_083025
  · exact g32p_supplierForest_actual_083060

def g32p_supplierForest_nodes_025 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_083100 else g32p_supplierForest_node_083205) else (if i.val < 3 then g32p_supplierForest_node_083229 else g32p_supplierForest_node_083235)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_083415 else g32p_supplierForest_node_083444) else (if i.val < 7 then g32p_supplierForest_node_083470 else g32p_supplierForest_node_083473))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_083498 else g32p_supplierForest_node_083523) else (if i.val < 11 then g32p_supplierForest_node_083550 else g32p_supplierForest_node_083629)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_083656 else g32p_supplierForest_node_083674) else (if i.val < 15 then g32p_supplierForest_node_083702 else g32p_supplierForest_node_083718)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_083834 else g32p_supplierForest_node_083843) else (if i.val < 19 then g32p_supplierForest_node_083847 else g32p_supplierForest_node_083902)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_083912 else g32p_supplierForest_node_083917) else (if i.val < 23 then g32p_supplierForest_node_083946 else g32p_supplierForest_node_084027))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_084062 else g32p_supplierForest_node_084100) else (if i.val < 27 then g32p_supplierForest_node_084101 else g32p_supplierForest_node_084137)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_084171 else g32p_supplierForest_node_084306) else (if i.val < 31 then g32p_supplierForest_node_084462 else g32p_supplierForest_node_084491))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_084547 else g32p_supplierForest_node_084571) else (if i.val < 35 then g32p_supplierForest_node_084609 else g32p_supplierForest_node_084613)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_084625 else g32p_supplierForest_node_084634) else (if i.val < 39 then g32p_supplierForest_node_084681 else g32p_supplierForest_node_084696))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_084720 else g32p_supplierForest_node_084761) else (if i.val < 43 then g32p_supplierForest_node_084780 else g32p_supplierForest_node_084790)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_084801 else g32p_supplierForest_node_084809) else (if i.val < 47 then g32p_supplierForest_node_084927 else g32p_supplierForest_node_084929)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_084995 else g32p_supplierForest_node_085002) else (if i.val < 51 then g32p_supplierForest_node_085008 else g32p_supplierForest_node_085020)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_085065 else g32p_supplierForest_node_085110) else (if i.val < 55 then g32p_supplierForest_node_085132 else g32p_supplierForest_node_085170))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_085191 else g32p_supplierForest_node_085244) else (if i.val < 59 then g32p_supplierForest_node_085276 else g32p_supplierForest_node_085281)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_085284 else g32p_supplierForest_node_085301) else (if i.val < 63 then g32p_supplierForest_node_085330 else g32p_supplierForest_node_085347)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_085389 else g32p_supplierForest_node_085412) else (if i.val < 67 then g32p_supplierForest_node_085464 else g32p_supplierForest_node_085495)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_085501 else g32p_supplierForest_node_085511) else (if i.val < 71 then g32p_supplierForest_node_085572 else g32p_supplierForest_node_085660))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_085684 else g32p_supplierForest_node_085765) else (if i.val < 75 then g32p_supplierForest_node_085784 else g32p_supplierForest_node_085846)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_085880 else g32p_supplierForest_node_085983) else (if i.val < 79 then g32p_supplierForest_node_085990 else g32p_supplierForest_node_085997)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_086027 else g32p_supplierForest_node_086044) else (if i.val < 83 then g32p_supplierForest_node_086045 else g32p_supplierForest_node_086136)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_086140 else g32p_supplierForest_node_086146) else (if i.val < 87 then g32p_supplierForest_node_086220 else g32p_supplierForest_node_086298))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_086302 else g32p_supplierForest_node_086368) else (if i.val < 91 then g32p_supplierForest_node_086400 else g32p_supplierForest_node_086410)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_086464 else g32p_supplierForest_node_086504) else (if i.val < 95 then g32p_supplierForest_node_086510 else g32p_supplierForest_node_086515))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_086614 else g32p_supplierForest_node_086619) else (if i.val < 99 then g32p_supplierForest_node_086640 else g32p_supplierForest_node_086643)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_086644 else g32p_supplierForest_node_086654) else (if i.val < 103 then g32p_supplierForest_node_086711 else g32p_supplierForest_node_086841))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_086903 else g32p_supplierForest_node_087009) else (if i.val < 107 then g32p_supplierForest_node_087063 else g32p_supplierForest_node_087127)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_087243 else g32p_supplierForest_node_087244) else (if i.val < 111 then g32p_supplierForest_node_087247 else g32p_supplierForest_node_087288)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_087323 else g32p_supplierForest_node_087362) else (if i.val < 115 then g32p_supplierForest_node_087549 else g32p_supplierForest_node_087580)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_087595 else g32p_supplierForest_node_087629) else (if i.val < 119 then g32p_supplierForest_node_087636 else g32p_supplierForest_node_087668))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_087674 else g32p_supplierForest_node_087701) else (if i.val < 123 then g32p_supplierForest_node_087742 else g32p_supplierForest_node_087804)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_087809 else g32p_supplierForest_node_087918) else (if i.val < 127 then g32p_supplierForest_node_087941 else g32p_supplierForest_node_087970))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_087980 else g32p_supplierForest_node_087986) else (if i.val < 131 then g32p_supplierForest_node_088012 else g32p_supplierForest_node_088024)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_088054 else g32p_supplierForest_node_088082) else (if i.val < 135 then g32p_supplierForest_node_088084 else g32p_supplierForest_node_088147))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_088188 else g32p_supplierForest_node_088207) else (if i.val < 139 then g32p_supplierForest_node_088210 else g32p_supplierForest_node_088252)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_088297 else g32p_supplierForest_node_088329) else (if i.val < 143 then g32p_supplierForest_node_088366 else g32p_supplierForest_node_088417)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_088433 else g32p_supplierForest_node_088478) else (if i.val < 147 then g32p_supplierForest_node_088504 else g32p_supplierForest_node_088525)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_088602 else g32p_supplierForest_node_088619) else (if i.val < 151 then g32p_supplierForest_node_088692 else g32p_supplierForest_node_088707))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_088727 else g32p_supplierForest_node_088734) else (if i.val < 155 then g32p_supplierForest_node_088748 else g32p_supplierForest_node_088754)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_088820 else g32p_supplierForest_node_088828) else (if i.val < 159 then g32p_supplierForest_node_088845 else g32p_supplierForest_node_088894))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_088932 else g32p_supplierForest_node_089025) else (if i.val < 163 then g32p_supplierForest_node_089078 else g32p_supplierForest_node_089136)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_089167 else g32p_supplierForest_node_089189) else (if i.val < 167 then g32p_supplierForest_node_089231 else g32p_supplierForest_node_089287))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_089345 else g32p_supplierForest_node_089357) else (if i.val < 171 then g32p_supplierForest_node_089390 else g32p_supplierForest_node_089407)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_089417 else g32p_supplierForest_node_089480) else (if i.val < 175 then g32p_supplierForest_node_089573 else g32p_supplierForest_node_089608)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_089641 else g32p_supplierForest_node_089676) else (if i.val < 179 then g32p_supplierForest_node_089680 else g32p_supplierForest_node_089698)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_089712 else g32p_supplierForest_node_089719) else (if i.val < 183 then g32p_supplierForest_node_089738 else g32p_supplierForest_node_089840))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_089879 else g32p_supplierForest_node_089894) else (if i.val < 187 then g32p_supplierForest_node_089897 else g32p_supplierForest_node_089906)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_090088 else g32p_supplierForest_node_090133) else (if i.val < 191 then g32p_supplierForest_node_090175 else g32p_supplierForest_node_090385)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_090391 else g32p_supplierForest_node_090541) else (if i.val < 195 then g32p_supplierForest_node_090561 else g32p_supplierForest_node_090610)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_090623 else g32p_supplierForest_node_090699) else (if i.val < 199 then g32p_supplierForest_node_090709 else g32p_supplierForest_node_090715))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_090757 else g32p_supplierForest_node_090783) else (if i.val < 203 then g32p_supplierForest_node_090817 else g32p_supplierForest_node_090916)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_090924 else g32p_supplierForest_node_090938) else (if i.val < 207 then g32p_supplierForest_node_090953 else g32p_supplierForest_node_090969)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_091067 else g32p_supplierForest_node_091090) else (if i.val < 211 then g32p_supplierForest_node_091092 else g32p_supplierForest_node_091096)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_091124 else g32p_supplierForest_node_091127) else (if i.val < 215 then g32p_supplierForest_node_091128 else g32p_supplierForest_node_091178))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_091193 else g32p_supplierForest_node_091261) else (if i.val < 219 then g32p_supplierForest_node_091270 else g32p_supplierForest_node_091274)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_091335 else g32p_supplierForest_node_091348) else (if i.val < 223 then g32p_supplierForest_node_091407 else g32p_supplierForest_node_091441))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_091470 else g32p_supplierForest_node_091501) else (if i.val < 227 then g32p_supplierForest_node_091589 else g32p_supplierForest_node_091686)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_091910 else g32p_supplierForest_node_091930) else (if i.val < 231 then g32p_supplierForest_node_091983 else g32p_supplierForest_node_091994))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_092050 else g32p_supplierForest_node_092067) else (if i.val < 235 then g32p_supplierForest_node_092081 else g32p_supplierForest_node_092099)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_092136 else g32p_supplierForest_node_092187) else (if i.val < 239 then g32p_supplierForest_node_092271 else g32p_supplierForest_node_092287)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_092376 else g32p_supplierForest_node_092390) else (if i.val < 243 then g32p_supplierForest_node_092479 else g32p_supplierForest_node_092569)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_092589 else g32p_supplierForest_node_092629) else (if i.val < 247 then g32p_supplierForest_node_092702 else g32p_supplierForest_node_092798))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_092809 else g32p_supplierForest_node_092821) else (if i.val < 251 then g32p_supplierForest_node_092839 else g32p_supplierForest_node_092986)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_093030 else g32p_supplierForest_node_093037) else (if i.val < 255 then g32p_supplierForest_node_093085 else g32p_supplierForest_node_093130))))))))

def g32p_supplierForest_classes_025 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 45 else 54) else (if i.val < 3 then 26 else 47)) else (if i.val < 6 then (if i.val < 5 then 84 else 47) else (if i.val < 7 then 52 else 48))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 84 else 82) else (if i.val < 11 then 49 else 80)) else (if i.val < 14 then (if i.val < 13 then 81 else 46) else (if i.val < 15 then 13 else 53)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 9 else 49) else (if i.val < 19 then 84 else 83)) else (if i.val < 22 then (if i.val < 21 then 54 else 46) else (if i.val < 23 then 83 else 83))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 46 else 50) else (if i.val < 27 then 53 else 56)) else (if i.val < 30 then (if i.val < 29 then 46 else 82) else (if i.val < 31 then 13 else 84))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 13 else 55) else (if i.val < 35 then 45 else 45)) else (if i.val < 38 then (if i.val < 37 then 56 else 49) else (if i.val < 39 then 46 else 84))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 50 else 56) else (if i.val < 43 then 52 else 13)) else (if i.val < 46 then (if i.val < 45 then 48 else 49) else (if i.val < 47 then 50 else 49)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 25 else 49) else (if i.val < 51 then 26 else 26)) else (if i.val < 54 then (if i.val < 53 then 25 else 85) else (if i.val < 55 then 46 else 84))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 84 else 46) else (if i.val < 59 then 56 else 52)) else (if i.val < 62 then (if i.val < 61 then 45 else 54) else (if i.val < 63 then 84 else 11)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 51) else (if i.val < 67 then 45 else 56)) else (if i.val < 70 then (if i.val < 69 then 53 else 55) else (if i.val < 71 then 82 else 13))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 46 else 49) else (if i.val < 75 then 47 else 9)) else (if i.val < 78 then (if i.val < 77 then 49 else 53) else (if i.val < 79 then 80 else 84)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 25 else 53) else (if i.val < 83 then 26 else 53)) else (if i.val < 86 then (if i.val < 85 then 52 else 46) else (if i.val < 87 then 54 else 56))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 47 else 13) else (if i.val < 91 then 53 else 55)) else (if i.val < 94 then (if i.val < 93 then 46 else 83) else (if i.val < 95 then 11 else 80))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 84 else 46) else (if i.val < 99 then 48 else 82)) else (if i.val < 102 then (if i.val < 101 then 49 else 85) else (if i.val < 103 then 47 else 56))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 55 else 49) else (if i.val < 107 then 86 else 49)) else (if i.val < 110 then (if i.val < 109 then 27 else 52) else (if i.val < 111 then 45 else 46)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 53 else 46) else (if i.val < 115 then 46 else 52)) else (if i.val < 118 then (if i.val < 117 then 82 else 46) else (if i.val < 119 then 47 else 46))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 53 else 52) else (if i.val < 123 then 46 else 46)) else (if i.val < 126 then (if i.val < 125 then 53 else 13) else (if i.val < 127 then 82 else 11))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 54 else 85) else (if i.val < 131 then 82 else 85)) else (if i.val < 134 then (if i.val < 133 then 47 else 11) else (if i.val < 135 then 83 else 82))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 53 else 55) else (if i.val < 139 then 53 else 12)) else (if i.val < 142 then (if i.val < 141 then 81 else 56) else (if i.val < 143 then 49 else 45)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 52 else 46) else (if i.val < 147 then 54 else 46)) else (if i.val < 150 then (if i.val < 149 then 46 else 55) else (if i.val < 151 then 13 else 56))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 46 else 80) else (if i.val < 155 then 83 else 83)) else (if i.val < 158 then (if i.val < 157 then 53 else 53) else (if i.val < 159 then 82 else 54))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 46 else 55) else (if i.val < 163 then 45 else 50)) else (if i.val < 166 then (if i.val < 165 then 86 else 52) else (if i.val < 167 then 55 else 25))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 46 else 48) else (if i.val < 171 then 80 else 48)) else (if i.val < 174 then (if i.val < 173 then 25 else 56) else (if i.val < 175 then 47 else 46)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 47 else 86) else (if i.val < 179 then 84 else 52)) else (if i.val < 182 then (if i.val < 181 then 80 else 45) else (if i.val < 183 then 83 else 53))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 54 else 54) else (if i.val < 187 then 50 else 80)) else (if i.val < 190 then (if i.val < 189 then 82 else 49) else (if i.val < 191 then 26 else 55)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 84 else 81) else (if i.val < 195 then 47 else 80)) else (if i.val < 198 then (if i.val < 197 then 56 else 54) else (if i.val < 199 then 80 else 80))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 56 else 84) else (if i.val < 203 then 55 else 55)) else (if i.val < 206 then (if i.val < 205 then 13 else 84) else (if i.val < 207 then 83 else 82)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 80 else 50) else (if i.val < 211 then 49 else 46)) else (if i.val < 214 then (if i.val < 213 then 47 else 81) else (if i.val < 215 then 48 else 47))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 26 else 55) else (if i.val < 219 then 26 else 84)) else (if i.val < 222 then (if i.val < 221 then 52 else 80) else (if i.val < 223 then 46 else 13))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 12 else 49) else (if i.val < 227 then 54 else 80)) else (if i.val < 230 then (if i.val < 229 then 8 else 52) else (if i.val < 231 then 55 else 26))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 26 else 82) else (if i.val < 235 then 80 else 50)) else (if i.val < 238 then (if i.val < 237 then 82 else 53) else (if i.val < 239 then 27 else 25)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 82 else 80) else (if i.val < 243 then 81 else 84)) else (if i.val < 246 then (if i.val < 245 then 25 else 49) else (if i.val < 247 then 25 else 47))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 25 else 52) else (if i.val < 251 then 46 else 45)) else (if i.val < 254 then (if i.val < 253 then 45 else 84) else (if i.val < 255 then 45 else 53))))))))

theorem g32p_supplierForest_actual_025 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_025 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_025 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_083100
  · exact g32p_supplierForest_actual_083205
  · exact g32p_supplierForest_actual_083229
  · exact g32p_supplierForest_actual_083235
  · exact g32p_supplierForest_actual_083415
  · exact g32p_supplierForest_actual_083444
  · exact g32p_supplierForest_actual_083470
  · exact g32p_supplierForest_actual_083473
  · exact g32p_supplierForest_actual_083498
  · exact g32p_supplierForest_actual_083523
  · exact g32p_supplierForest_actual_083550
  · exact g32p_supplierForest_actual_083629
  · exact g32p_supplierForest_actual_083656
  · exact g32p_supplierForest_actual_083674
  · exact g32p_supplierForest_actual_083702
  · exact g32p_supplierForest_actual_083718
  · exact g32p_supplierForest_actual_083834
  · exact g32p_supplierForest_actual_083843
  · exact g32p_supplierForest_actual_083847
  · exact g32p_supplierForest_actual_083902
  · exact g32p_supplierForest_actual_083912
  · exact g32p_supplierForest_actual_083917
  · exact g32p_supplierForest_actual_083946
  · exact g32p_supplierForest_actual_084027
  · exact g32p_supplierForest_actual_084062
  · exact g32p_supplierForest_actual_084100
  · exact g32p_supplierForest_actual_084101
  · exact g32p_supplierForest_actual_084137
  · exact g32p_supplierForest_actual_084171
  · exact g32p_supplierForest_actual_084306
  · exact g32p_supplierForest_actual_084462
  · exact g32p_supplierForest_actual_084491
  · exact g32p_supplierForest_actual_084547
  · exact g32p_supplierForest_actual_084571
  · exact g32p_supplierForest_actual_084609
  · exact g32p_supplierForest_actual_084613
  · exact g32p_supplierForest_actual_084625
  · exact g32p_supplierForest_actual_084634
  · exact g32p_supplierForest_actual_084681
  · exact g32p_supplierForest_actual_084696
  · exact g32p_supplierForest_actual_084720
  · exact g32p_supplierForest_actual_084761
  · exact g32p_supplierForest_actual_084780
  · exact g32p_supplierForest_actual_084790
  · exact g32p_supplierForest_actual_084801
  · exact g32p_supplierForest_actual_084809
  · exact g32p_supplierForest_actual_084927
  · exact g32p_supplierForest_actual_084929
  · exact g32p_supplierForest_actual_084995
  · exact g32p_supplierForest_actual_085002
  · exact g32p_supplierForest_actual_085008
  · exact g32p_supplierForest_actual_085020
  · exact g32p_supplierForest_actual_085065
  · exact g32p_supplierForest_actual_085110
  · exact g32p_supplierForest_actual_085132
  · exact g32p_supplierForest_actual_085170
  · exact g32p_supplierForest_actual_085191
  · exact g32p_supplierForest_actual_085244
  · exact g32p_supplierForest_actual_085276
  · exact g32p_supplierForest_actual_085281
  · exact g32p_supplierForest_actual_085284
  · exact g32p_supplierForest_actual_085301
  · exact g32p_supplierForest_actual_085330
  · exact g32p_supplierForest_actual_085347
  · exact g32p_supplierForest_actual_085389
  · exact g32p_supplierForest_actual_085412
  · exact g32p_supplierForest_actual_085464
  · exact g32p_supplierForest_actual_085495
  · exact g32p_supplierForest_actual_085501
  · exact g32p_supplierForest_actual_085511
  · exact g32p_supplierForest_actual_085572
  · exact g32p_supplierForest_actual_085660
  · exact g32p_supplierForest_actual_085684
  · exact g32p_supplierForest_actual_085765
  · exact g32p_supplierForest_actual_085784
  · exact g32p_supplierForest_actual_085846
  · exact g32p_supplierForest_actual_085880
  · exact g32p_supplierForest_actual_085983
  · exact g32p_supplierForest_actual_085990
  · exact g32p_supplierForest_actual_085997
  · exact g32p_supplierForest_actual_086027
  · exact g32p_supplierForest_actual_086044
  · exact g32p_supplierForest_actual_086045
  · exact g32p_supplierForest_actual_086136
  · exact g32p_supplierForest_actual_086140
  · exact g32p_supplierForest_actual_086146
  · exact g32p_supplierForest_actual_086220
  · exact g32p_supplierForest_actual_086298
  · exact g32p_supplierForest_actual_086302
  · exact g32p_supplierForest_actual_086368
  · exact g32p_supplierForest_actual_086400
  · exact g32p_supplierForest_actual_086410
  · exact g32p_supplierForest_actual_086464
  · exact g32p_supplierForest_actual_086504
  · exact g32p_supplierForest_actual_086510
  · exact g32p_supplierForest_actual_086515
  · exact g32p_supplierForest_actual_086614
  · exact g32p_supplierForest_actual_086619
  · exact g32p_supplierForest_actual_086640
  · exact g32p_supplierForest_actual_086643
  · exact g32p_supplierForest_actual_086644
  · exact g32p_supplierForest_actual_086654
  · exact g32p_supplierForest_actual_086711
  · exact g32p_supplierForest_actual_086841
  · exact g32p_supplierForest_actual_086903
  · exact g32p_supplierForest_actual_087009
  · exact g32p_supplierForest_actual_087063
  · exact g32p_supplierForest_actual_087127
  · exact g32p_supplierForest_actual_087243
  · exact g32p_supplierForest_actual_087244
  · exact g32p_supplierForest_actual_087247
  · exact g32p_supplierForest_actual_087288
  · exact g32p_supplierForest_actual_087323
  · exact g32p_supplierForest_actual_087362
  · exact g32p_supplierForest_actual_087549
  · exact g32p_supplierForest_actual_087580
  · exact g32p_supplierForest_actual_087595
  · exact g32p_supplierForest_actual_087629
  · exact g32p_supplierForest_actual_087636
  · exact g32p_supplierForest_actual_087668
  · exact g32p_supplierForest_actual_087674
  · exact g32p_supplierForest_actual_087701
  · exact g32p_supplierForest_actual_087742
  · exact g32p_supplierForest_actual_087804
  · exact g32p_supplierForest_actual_087809
  · exact g32p_supplierForest_actual_087918
  · exact g32p_supplierForest_actual_087941
  · exact g32p_supplierForest_actual_087970
  · exact g32p_supplierForest_actual_087980
  · exact g32p_supplierForest_actual_087986
  · exact g32p_supplierForest_actual_088012
  · exact g32p_supplierForest_actual_088024
  · exact g32p_supplierForest_actual_088054
  · exact g32p_supplierForest_actual_088082
  · exact g32p_supplierForest_actual_088084
  · exact g32p_supplierForest_actual_088147
  · exact g32p_supplierForest_actual_088188
  · exact g32p_supplierForest_actual_088207
  · exact g32p_supplierForest_actual_088210
  · exact g32p_supplierForest_actual_088252
  · exact g32p_supplierForest_actual_088297
  · exact g32p_supplierForest_actual_088329
  · exact g32p_supplierForest_actual_088366
  · exact g32p_supplierForest_actual_088417
  · exact g32p_supplierForest_actual_088433
  · exact g32p_supplierForest_actual_088478
  · exact g32p_supplierForest_actual_088504
  · exact g32p_supplierForest_actual_088525
  · exact g32p_supplierForest_actual_088602
  · exact g32p_supplierForest_actual_088619
  · exact g32p_supplierForest_actual_088692
  · exact g32p_supplierForest_actual_088707
  · exact g32p_supplierForest_actual_088727
  · exact g32p_supplierForest_actual_088734
  · exact g32p_supplierForest_actual_088748
  · exact g32p_supplierForest_actual_088754
  · exact g32p_supplierForest_actual_088820
  · exact g32p_supplierForest_actual_088828
  · exact g32p_supplierForest_actual_088845
  · exact g32p_supplierForest_actual_088894
  · exact g32p_supplierForest_actual_088932
  · exact g32p_supplierForest_actual_089025
  · exact g32p_supplierForest_actual_089078
  · exact g32p_supplierForest_actual_089136
  · exact g32p_supplierForest_actual_089167
  · exact g32p_supplierForest_actual_089189
  · exact g32p_supplierForest_actual_089231
  · exact g32p_supplierForest_actual_089287
  · exact g32p_supplierForest_actual_089345
  · exact g32p_supplierForest_actual_089357
  · exact g32p_supplierForest_actual_089390
  · exact g32p_supplierForest_actual_089407
  · exact g32p_supplierForest_actual_089417
  · exact g32p_supplierForest_actual_089480
  · exact g32p_supplierForest_actual_089573
  · exact g32p_supplierForest_actual_089608
  · exact g32p_supplierForest_actual_089641
  · exact g32p_supplierForest_actual_089676
  · exact g32p_supplierForest_actual_089680
  · exact g32p_supplierForest_actual_089698
  · exact g32p_supplierForest_actual_089712
  · exact g32p_supplierForest_actual_089719
  · exact g32p_supplierForest_actual_089738
  · exact g32p_supplierForest_actual_089840
  · exact g32p_supplierForest_actual_089879
  · exact g32p_supplierForest_actual_089894
  · exact g32p_supplierForest_actual_089897
  · exact g32p_supplierForest_actual_089906
  · exact g32p_supplierForest_actual_090088
  · exact g32p_supplierForest_actual_090133
  · exact g32p_supplierForest_actual_090175
  · exact g32p_supplierForest_actual_090385
  · exact g32p_supplierForest_actual_090391
  · exact g32p_supplierForest_actual_090541
  · exact g32p_supplierForest_actual_090561
  · exact g32p_supplierForest_actual_090610
  · exact g32p_supplierForest_actual_090623
  · exact g32p_supplierForest_actual_090699
  · exact g32p_supplierForest_actual_090709
  · exact g32p_supplierForest_actual_090715
  · exact g32p_supplierForest_actual_090757
  · exact g32p_supplierForest_actual_090783
  · exact g32p_supplierForest_actual_090817
  · exact g32p_supplierForest_actual_090916
  · exact g32p_supplierForest_actual_090924
  · exact g32p_supplierForest_actual_090938
  · exact g32p_supplierForest_actual_090953
  · exact g32p_supplierForest_actual_090969
  · exact g32p_supplierForest_actual_091067
  · exact g32p_supplierForest_actual_091090
  · exact g32p_supplierForest_actual_091092
  · exact g32p_supplierForest_actual_091096
  · exact g32p_supplierForest_actual_091124
  · exact g32p_supplierForest_actual_091127
  · exact g32p_supplierForest_actual_091128
  · exact g32p_supplierForest_actual_091178
  · exact g32p_supplierForest_actual_091193
  · exact g32p_supplierForest_actual_091261
  · exact g32p_supplierForest_actual_091270
  · exact g32p_supplierForest_actual_091274
  · exact g32p_supplierForest_actual_091335
  · exact g32p_supplierForest_actual_091348
  · exact g32p_supplierForest_actual_091407
  · exact g32p_supplierForest_actual_091441
  · exact g32p_supplierForest_actual_091470
  · exact g32p_supplierForest_actual_091501
  · exact g32p_supplierForest_actual_091589
  · exact g32p_supplierForest_actual_091686
  · exact g32p_supplierForest_actual_091910
  · exact g32p_supplierForest_actual_091930
  · exact g32p_supplierForest_actual_091983
  · exact g32p_supplierForest_actual_091994
  · exact g32p_supplierForest_actual_092050
  · exact g32p_supplierForest_actual_092067
  · exact g32p_supplierForest_actual_092081
  · exact g32p_supplierForest_actual_092099
  · exact g32p_supplierForest_actual_092136
  · exact g32p_supplierForest_actual_092187
  · exact g32p_supplierForest_actual_092271
  · exact g32p_supplierForest_actual_092287
  · exact g32p_supplierForest_actual_092376
  · exact g32p_supplierForest_actual_092390
  · exact g32p_supplierForest_actual_092479
  · exact g32p_supplierForest_actual_092569
  · exact g32p_supplierForest_actual_092589
  · exact g32p_supplierForest_actual_092629
  · exact g32p_supplierForest_actual_092702
  · exact g32p_supplierForest_actual_092798
  · exact g32p_supplierForest_actual_092809
  · exact g32p_supplierForest_actual_092821
  · exact g32p_supplierForest_actual_092839
  · exact g32p_supplierForest_actual_092986
  · exact g32p_supplierForest_actual_093030
  · exact g32p_supplierForest_actual_093037
  · exact g32p_supplierForest_actual_093085
  · exact g32p_supplierForest_actual_093130

def g32p_supplierForest_nodes_026 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_093156 else g32p_supplierForest_node_093214) else (if i.val < 3 then g32p_supplierForest_node_093229 else g32p_supplierForest_node_093234)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_093261 else g32p_supplierForest_node_093317) else (if i.val < 7 then g32p_supplierForest_node_093323 else g32p_supplierForest_node_093521))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_093526 else g32p_supplierForest_node_093533) else (if i.val < 11 then g32p_supplierForest_node_093543 else g32p_supplierForest_node_093566)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_093838 else g32p_supplierForest_node_093861) else (if i.val < 15 then g32p_supplierForest_node_093911 else g32p_supplierForest_node_093988)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_094033 else g32p_supplierForest_node_094086) else (if i.val < 19 then g32p_supplierForest_node_094122 else g32p_supplierForest_node_094156)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_094213 else g32p_supplierForest_node_094247) else (if i.val < 23 then g32p_supplierForest_node_094251 else g32p_supplierForest_node_094253))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_094260 else g32p_supplierForest_node_094270) else (if i.val < 27 then g32p_supplierForest_node_094384 else g32p_supplierForest_node_094385)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_094393 else g32p_supplierForest_node_094401) else (if i.val < 31 then g32p_supplierForest_node_094431 else g32p_supplierForest_node_094532))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_094572 else g32p_supplierForest_node_094610) else (if i.val < 35 then g32p_supplierForest_node_094651 else g32p_supplierForest_node_094674)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_094690 else g32p_supplierForest_node_094693) else (if i.val < 39 then g32p_supplierForest_node_094751 else g32p_supplierForest_node_094806))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_094841 else g32p_supplierForest_node_094843) else (if i.val < 43 then g32p_supplierForest_node_094848 else g32p_supplierForest_node_094910)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_094919 else g32p_supplierForest_node_094933) else (if i.val < 47 then g32p_supplierForest_node_094977 else g32p_supplierForest_node_095023)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_095024 else g32p_supplierForest_node_095046) else (if i.val < 51 then g32p_supplierForest_node_095047 else g32p_supplierForest_node_095058)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_095066 else g32p_supplierForest_node_095310) else (if i.val < 55 then g32p_supplierForest_node_095439 else g32p_supplierForest_node_095467))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_095476 else g32p_supplierForest_node_095580) else (if i.val < 59 then g32p_supplierForest_node_095630 else g32p_supplierForest_node_095673)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_095700 else g32p_supplierForest_node_095722) else (if i.val < 63 then g32p_supplierForest_node_095727 else g32p_supplierForest_node_095788)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_095794 else g32p_supplierForest_node_095803) else (if i.val < 67 then g32p_supplierForest_node_095887 else g32p_supplierForest_node_095976)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_096042 else g32p_supplierForest_node_096142) else (if i.val < 71 then g32p_supplierForest_node_096159 else g32p_supplierForest_node_096160))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_096210 else g32p_supplierForest_node_096234) else (if i.val < 75 then g32p_supplierForest_node_096301 else g32p_supplierForest_node_096351)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_096355 else g32p_supplierForest_node_096397) else (if i.val < 79 then g32p_supplierForest_node_096483 else g32p_supplierForest_node_096508)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_096537 else g32p_supplierForest_node_096540) else (if i.val < 83 then g32p_supplierForest_node_096556 else g32p_supplierForest_node_096577)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_096598 else g32p_supplierForest_node_096640) else (if i.val < 87 then g32p_supplierForest_node_096685 else g32p_supplierForest_node_096741))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_096786 else g32p_supplierForest_node_096795) else (if i.val < 91 then g32p_supplierForest_node_096831 else g32p_supplierForest_node_096871)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_096879 else g32p_supplierForest_node_096981) else (if i.val < 95 then g32p_supplierForest_node_096995 else g32p_supplierForest_node_097035))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_097074 else g32p_supplierForest_node_097111) else (if i.val < 99 then g32p_supplierForest_node_097197 else g32p_supplierForest_node_097210)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_097308 else g32p_supplierForest_node_097317) else (if i.val < 103 then g32p_supplierForest_node_097336 else g32p_supplierForest_node_097434))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_097444 else g32p_supplierForest_node_097459) else (if i.val < 107 then g32p_supplierForest_node_097495 else g32p_supplierForest_node_097619)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_097638 else g32p_supplierForest_node_097725) else (if i.val < 111 then g32p_supplierForest_node_097726 else g32p_supplierForest_node_097806)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_097914 else g32p_supplierForest_node_097923) else (if i.val < 115 then g32p_supplierForest_node_097928 else g32p_supplierForest_node_097942)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_097948 else g32p_supplierForest_node_098058) else (if i.val < 119 then g32p_supplierForest_node_098069 else g32p_supplierForest_node_098142))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_098192 else g32p_supplierForest_node_098206) else (if i.val < 123 then g32p_supplierForest_node_098260 else g32p_supplierForest_node_098417)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_098433 else g32p_supplierForest_node_098491) else (if i.val < 127 then g32p_supplierForest_node_098606 else g32p_supplierForest_node_098617))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_098704 else g32p_supplierForest_node_098730) else (if i.val < 131 then g32p_supplierForest_node_098818 else g32p_supplierForest_node_098829)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_098897 else g32p_supplierForest_node_098951) else (if i.val < 135 then g32p_supplierForest_node_098992 else g32p_supplierForest_node_099159))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_099161 else g32p_supplierForest_node_099170) else (if i.val < 139 then g32p_supplierForest_node_099196 else g32p_supplierForest_node_099200)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_099227 else g32p_supplierForest_node_099283) else (if i.val < 143 then g32p_supplierForest_node_099327 else g32p_supplierForest_node_099332)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_099362 else g32p_supplierForest_node_099378) else (if i.val < 147 then g32p_supplierForest_node_099408 else g32p_supplierForest_node_099412)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_099425 else g32p_supplierForest_node_099438) else (if i.val < 151 then g32p_supplierForest_node_099473 else g32p_supplierForest_node_099583))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_099608 else g32p_supplierForest_node_099609) else (if i.val < 155 then g32p_supplierForest_node_099659 else g32p_supplierForest_node_099700)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_099714 else g32p_supplierForest_node_099742) else (if i.val < 159 then g32p_supplierForest_node_099755 else g32p_supplierForest_node_099920))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_100002 else g32p_supplierForest_node_100124) else (if i.val < 163 then g32p_supplierForest_node_100155 else g32p_supplierForest_node_100183)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_100331 else g32p_supplierForest_node_100392) else (if i.val < 167 then g32p_supplierForest_node_100400 else g32p_supplierForest_node_100660))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_100698 else g32p_supplierForest_node_100702) else (if i.val < 171 then g32p_supplierForest_node_100708 else g32p_supplierForest_node_100951)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_100952 else g32p_supplierForest_node_100977) else (if i.val < 175 then g32p_supplierForest_node_100989 else g32p_supplierForest_node_100991)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_101085 else g32p_supplierForest_node_101182) else (if i.val < 179 then g32p_supplierForest_node_101183 else g32p_supplierForest_node_101234)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_101285 else g32p_supplierForest_node_101333) else (if i.val < 183 then g32p_supplierForest_node_101336 else g32p_supplierForest_node_101383))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_101404 else g32p_supplierForest_node_101434) else (if i.val < 187 then g32p_supplierForest_node_101488 else g32p_supplierForest_node_101489)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_101537 else g32p_supplierForest_node_101551) else (if i.val < 191 then g32p_supplierForest_node_101601 else g32p_supplierForest_node_101614)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_101680 else g32p_supplierForest_node_101687) else (if i.val < 195 then g32p_supplierForest_node_101702 else g32p_supplierForest_node_101718)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_101721 else g32p_supplierForest_node_101722) else (if i.val < 199 then g32p_supplierForest_node_101817 else g32p_supplierForest_node_101925))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_101938 else g32p_supplierForest_node_101940) else (if i.val < 203 then g32p_supplierForest_node_101944 else g32p_supplierForest_node_101969)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_102052 else g32p_supplierForest_node_102170) else (if i.val < 207 then g32p_supplierForest_node_102218 else g32p_supplierForest_node_102226)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_102298 else g32p_supplierForest_node_102299) else (if i.val < 211 then g32p_supplierForest_node_102306 else g32p_supplierForest_node_102309)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_102312 else g32p_supplierForest_node_102334) else (if i.val < 215 then g32p_supplierForest_node_102390 else g32p_supplierForest_node_102425))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_102454 else g32p_supplierForest_node_102457) else (if i.val < 219 then g32p_supplierForest_node_102469 else g32p_supplierForest_node_102524)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_102557 else g32p_supplierForest_node_102569) else (if i.val < 223 then g32p_supplierForest_node_102580 else g32p_supplierForest_node_102756))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_102866 else g32p_supplierForest_node_102891) else (if i.val < 227 then g32p_supplierForest_node_102988 else g32p_supplierForest_node_103057)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_103089 else g32p_supplierForest_node_103158) else (if i.val < 231 then g32p_supplierForest_node_103167 else g32p_supplierForest_node_103174))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_103191 else g32p_supplierForest_node_103205) else (if i.val < 235 then g32p_supplierForest_node_103249 else g32p_supplierForest_node_103322)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_103344 else g32p_supplierForest_node_103354) else (if i.val < 239 then g32p_supplierForest_node_103464 else g32p_supplierForest_node_103476)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_103489 else g32p_supplierForest_node_103550) else (if i.val < 243 then g32p_supplierForest_node_103570 else g32p_supplierForest_node_103590)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_103631 else g32p_supplierForest_node_103761) else (if i.val < 247 then g32p_supplierForest_node_103813 else g32p_supplierForest_node_103862))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_103942 else g32p_supplierForest_node_103995) else (if i.val < 251 then g32p_supplierForest_node_104016 else g32p_supplierForest_node_104026)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_104028 else g32p_supplierForest_node_104037) else (if i.val < 255 then g32p_supplierForest_node_104179 else g32p_supplierForest_node_104197))))))))

def g32p_supplierForest_classes_026 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 53 else 47) else (if i.val < 3 then 25 else 53)) else (if i.val < 6 then (if i.val < 5 then 54 else 49) else (if i.val < 7 then 84 else 47))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 53 else 81) else (if i.val < 11 then 52 else 56)) else (if i.val < 14 then (if i.val < 13 then 52 else 46) else (if i.val < 15 then 50 else 52)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 85 else 49) else (if i.val < 19 then 45 else 48)) else (if i.val < 22 then (if i.val < 21 then 82 else 52) else (if i.val < 23 then 46 else 49))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 54 else 85) else (if i.val < 27 then 13 else 49)) else (if i.val < 30 then (if i.val < 29 then 82 else 52) else (if i.val < 31 then 48 else 84))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 86 else 47) else (if i.val < 35 then 13 else 47)) else (if i.val < 38 then (if i.val < 37 then 26 else 26) else (if i.val < 39 then 26 else 26))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 81 else 55) else (if i.val < 43 then 82 else 53)) else (if i.val < 46 then (if i.val < 45 then 46 else 26) else (if i.val < 47 then 46 else 25)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 46 else 55) else (if i.val < 51 then 25 else 25)) else (if i.val < 54 then (if i.val < 53 then 49 else 11) else (if i.val < 55 then 13 else 46))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 27 else 80) else (if i.val < 59 then 55 else 11)) else (if i.val < 62 then (if i.val < 61 then 46 else 9) else (if i.val < 63 then 9 else 48)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 46) else (if i.val < 67 then 26 else 26)) else (if i.val < 70 then (if i.val < 69 then 81 else 45) else (if i.val < 71 then 46 else 84))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 26 else 26) else (if i.val < 75 then 56 else 46)) else (if i.val < 78 then (if i.val < 77 then 45 else 81) else (if i.val < 79 then 82 else 45)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 45 else 56) else (if i.val < 83 then 83 else 26)) else (if i.val < 86 then (if i.val < 85 then 45 else 26) else (if i.val < 87 then 53 else 50))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 56 else 49) else (if i.val < 91 then 46 else 83)) else (if i.val < 94 then (if i.val < 93 then 47 else 45) else (if i.val < 95 then 13 else 25))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 80 else 45) else (if i.val < 99 then 54 else 80)) else (if i.val < 102 then (if i.val < 101 then 80 else 54) else (if i.val < 103 then 54 else 56))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 11 else 54) else (if i.val < 107 then 49 else 85)) else (if i.val < 110 then (if i.val < 109 then 47 else 46) else (if i.val < 111 then 86 else 54)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 53 else 25) else (if i.val < 115 then 83 else 53)) else (if i.val < 118 then (if i.val < 117 then 49 else 46) else (if i.val < 119 then 46 else 82))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 80 else 50) else (if i.val < 123 then 84 else 80)) else (if i.val < 126 then (if i.val < 125 then 46 else 11) else (if i.val < 127 then 26 else 25))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 52 else 56) else (if i.val < 131 then 54 else 55)) else (if i.val < 134 then (if i.val < 133 then 26 else 47) else (if i.val < 135 then 45 else 46))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 50 else 54) else (if i.val < 139 then 26 else 46)) else (if i.val < 142 then (if i.val < 141 then 46 else 54) else (if i.val < 143 then 46 else 84)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 54 else 11) else (if i.val < 147 then 45 else 84)) else (if i.val < 150 then (if i.val < 149 then 56 else 55) else (if i.val < 151 then 27 else 81))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 11 else 85) else (if i.val < 155 then 52 else 52)) else (if i.val < 158 then (if i.val < 157 then 86 else 11) else (if i.val < 159 then 46 else 26))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 56 else 55) else (if i.val < 163 then 46 else 85)) else (if i.val < 166 then (if i.val < 165 then 55 else 53) else (if i.val < 167 then 54 else 80))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 26 else 55) else (if i.val < 171 then 54 else 54)) else (if i.val < 174 then (if i.val < 173 then 80 else 84) else (if i.val < 175 then 46 else 26)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 86 else 47) else (if i.val < 179 then 45 else 84)) else (if i.val < 182 then (if i.val < 181 then 80 else 52) else (if i.val < 183 then 52 else 80))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 80 else 47) else (if i.val < 187 then 25 else 80)) else (if i.val < 190 then (if i.val < 189 then 53 else 53) else (if i.val < 191 then 85 else 54)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 25 else 25) else (if i.val < 195 then 55 else 49)) else (if i.val < 198 then (if i.val < 197 then 25 else 46) else (if i.val < 199 then 47 else 63))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 63 else 16) else (if i.val < 203 then 63 else 59)) else (if i.val < 206 then (if i.val < 205 then 66 else 66) else (if i.val < 207 then 60 else 57)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 57 else 63) else (if i.val < 211 then 59 else 57)) else (if i.val < 214 then (if i.val < 213 then 59 else 61) else (if i.val < 215 then 66 else 34))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 64 else 64) else (if i.val < 219 then 30 else 60)) else (if i.val < 222 then (if i.val < 221 then 33 else 62) else (if i.val < 223 then 57 else 36))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 64 else 57) else (if i.val < 227 then 34 else 59)) else (if i.val < 230 then (if i.val < 229 then 57 else 36) else (if i.val < 231 then 63 else 66))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 61 else 57) else (if i.val < 235 then 29 else 64)) else (if i.val < 238 then (if i.val < 237 then 60 else 33) else (if i.val < 239 then 30 else 29)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 63 else 60) else (if i.val < 243 then 33 else 29)) else (if i.val < 246 then (if i.val < 245 then 59 else 61) else (if i.val < 247 then 62 else 64))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 61 else 33) else (if i.val < 251 then 29 else 16)) else (if i.val < 254 then (if i.val < 253 then 58 else 34) else (if i.val < 255 then 59 else 29))))))))

theorem g32p_supplierForest_actual_026 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_026 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_026 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_093156
  · exact g32p_supplierForest_actual_093214
  · exact g32p_supplierForest_actual_093229
  · exact g32p_supplierForest_actual_093234
  · exact g32p_supplierForest_actual_093261
  · exact g32p_supplierForest_actual_093317
  · exact g32p_supplierForest_actual_093323
  · exact g32p_supplierForest_actual_093521
  · exact g32p_supplierForest_actual_093526
  · exact g32p_supplierForest_actual_093533
  · exact g32p_supplierForest_actual_093543
  · exact g32p_supplierForest_actual_093566
  · exact g32p_supplierForest_actual_093838
  · exact g32p_supplierForest_actual_093861
  · exact g32p_supplierForest_actual_093911
  · exact g32p_supplierForest_actual_093988
  · exact g32p_supplierForest_actual_094033
  · exact g32p_supplierForest_actual_094086
  · exact g32p_supplierForest_actual_094122
  · exact g32p_supplierForest_actual_094156
  · exact g32p_supplierForest_actual_094213
  · exact g32p_supplierForest_actual_094247
  · exact g32p_supplierForest_actual_094251
  · exact g32p_supplierForest_actual_094253
  · exact g32p_supplierForest_actual_094260
  · exact g32p_supplierForest_actual_094270
  · exact g32p_supplierForest_actual_094384
  · exact g32p_supplierForest_actual_094385
  · exact g32p_supplierForest_actual_094393
  · exact g32p_supplierForest_actual_094401
  · exact g32p_supplierForest_actual_094431
  · exact g32p_supplierForest_actual_094532
  · exact g32p_supplierForest_actual_094572
  · exact g32p_supplierForest_actual_094610
  · exact g32p_supplierForest_actual_094651
  · exact g32p_supplierForest_actual_094674
  · exact g32p_supplierForest_actual_094690
  · exact g32p_supplierForest_actual_094693
  · exact g32p_supplierForest_actual_094751
  · exact g32p_supplierForest_actual_094806
  · exact g32p_supplierForest_actual_094841
  · exact g32p_supplierForest_actual_094843
  · exact g32p_supplierForest_actual_094848
  · exact g32p_supplierForest_actual_094910
  · exact g32p_supplierForest_actual_094919
  · exact g32p_supplierForest_actual_094933
  · exact g32p_supplierForest_actual_094977
  · exact g32p_supplierForest_actual_095023
  · exact g32p_supplierForest_actual_095024
  · exact g32p_supplierForest_actual_095046
  · exact g32p_supplierForest_actual_095047
  · exact g32p_supplierForest_actual_095058
  · exact g32p_supplierForest_actual_095066
  · exact g32p_supplierForest_actual_095310
  · exact g32p_supplierForest_actual_095439
  · exact g32p_supplierForest_actual_095467
  · exact g32p_supplierForest_actual_095476
  · exact g32p_supplierForest_actual_095580
  · exact g32p_supplierForest_actual_095630
  · exact g32p_supplierForest_actual_095673
  · exact g32p_supplierForest_actual_095700
  · exact g32p_supplierForest_actual_095722
  · exact g32p_supplierForest_actual_095727
  · exact g32p_supplierForest_actual_095788
  · exact g32p_supplierForest_actual_095794
  · exact g32p_supplierForest_actual_095803
  · exact g32p_supplierForest_actual_095887
  · exact g32p_supplierForest_actual_095976
  · exact g32p_supplierForest_actual_096042
  · exact g32p_supplierForest_actual_096142
  · exact g32p_supplierForest_actual_096159
  · exact g32p_supplierForest_actual_096160
  · exact g32p_supplierForest_actual_096210
  · exact g32p_supplierForest_actual_096234
  · exact g32p_supplierForest_actual_096301
  · exact g32p_supplierForest_actual_096351
  · exact g32p_supplierForest_actual_096355
  · exact g32p_supplierForest_actual_096397
  · exact g32p_supplierForest_actual_096483
  · exact g32p_supplierForest_actual_096508
  · exact g32p_supplierForest_actual_096537
  · exact g32p_supplierForest_actual_096540
  · exact g32p_supplierForest_actual_096556
  · exact g32p_supplierForest_actual_096577
  · exact g32p_supplierForest_actual_096598
  · exact g32p_supplierForest_actual_096640
  · exact g32p_supplierForest_actual_096685
  · exact g32p_supplierForest_actual_096741
  · exact g32p_supplierForest_actual_096786
  · exact g32p_supplierForest_actual_096795
  · exact g32p_supplierForest_actual_096831
  · exact g32p_supplierForest_actual_096871
  · exact g32p_supplierForest_actual_096879
  · exact g32p_supplierForest_actual_096981
  · exact g32p_supplierForest_actual_096995
  · exact g32p_supplierForest_actual_097035
  · exact g32p_supplierForest_actual_097074
  · exact g32p_supplierForest_actual_097111
  · exact g32p_supplierForest_actual_097197
  · exact g32p_supplierForest_actual_097210
  · exact g32p_supplierForest_actual_097308
  · exact g32p_supplierForest_actual_097317
  · exact g32p_supplierForest_actual_097336
  · exact g32p_supplierForest_actual_097434
  · exact g32p_supplierForest_actual_097444
  · exact g32p_supplierForest_actual_097459
  · exact g32p_supplierForest_actual_097495
  · exact g32p_supplierForest_actual_097619
  · exact g32p_supplierForest_actual_097638
  · exact g32p_supplierForest_actual_097725
  · exact g32p_supplierForest_actual_097726
  · exact g32p_supplierForest_actual_097806
  · exact g32p_supplierForest_actual_097914
  · exact g32p_supplierForest_actual_097923
  · exact g32p_supplierForest_actual_097928
  · exact g32p_supplierForest_actual_097942
  · exact g32p_supplierForest_actual_097948
  · exact g32p_supplierForest_actual_098058
  · exact g32p_supplierForest_actual_098069
  · exact g32p_supplierForest_actual_098142
  · exact g32p_supplierForest_actual_098192
  · exact g32p_supplierForest_actual_098206
  · exact g32p_supplierForest_actual_098260
  · exact g32p_supplierForest_actual_098417
  · exact g32p_supplierForest_actual_098433
  · exact g32p_supplierForest_actual_098491
  · exact g32p_supplierForest_actual_098606
  · exact g32p_supplierForest_actual_098617
  · exact g32p_supplierForest_actual_098704
  · exact g32p_supplierForest_actual_098730
  · exact g32p_supplierForest_actual_098818
  · exact g32p_supplierForest_actual_098829
  · exact g32p_supplierForest_actual_098897
  · exact g32p_supplierForest_actual_098951
  · exact g32p_supplierForest_actual_098992
  · exact g32p_supplierForest_actual_099159
  · exact g32p_supplierForest_actual_099161
  · exact g32p_supplierForest_actual_099170
  · exact g32p_supplierForest_actual_099196
  · exact g32p_supplierForest_actual_099200
  · exact g32p_supplierForest_actual_099227
  · exact g32p_supplierForest_actual_099283
  · exact g32p_supplierForest_actual_099327
  · exact g32p_supplierForest_actual_099332
  · exact g32p_supplierForest_actual_099362
  · exact g32p_supplierForest_actual_099378
  · exact g32p_supplierForest_actual_099408
  · exact g32p_supplierForest_actual_099412
  · exact g32p_supplierForest_actual_099425
  · exact g32p_supplierForest_actual_099438
  · exact g32p_supplierForest_actual_099473
  · exact g32p_supplierForest_actual_099583
  · exact g32p_supplierForest_actual_099608
  · exact g32p_supplierForest_actual_099609
  · exact g32p_supplierForest_actual_099659
  · exact g32p_supplierForest_actual_099700
  · exact g32p_supplierForest_actual_099714
  · exact g32p_supplierForest_actual_099742
  · exact g32p_supplierForest_actual_099755
  · exact g32p_supplierForest_actual_099920
  · exact g32p_supplierForest_actual_100002
  · exact g32p_supplierForest_actual_100124
  · exact g32p_supplierForest_actual_100155
  · exact g32p_supplierForest_actual_100183
  · exact g32p_supplierForest_actual_100331
  · exact g32p_supplierForest_actual_100392
  · exact g32p_supplierForest_actual_100400
  · exact g32p_supplierForest_actual_100660
  · exact g32p_supplierForest_actual_100698
  · exact g32p_supplierForest_actual_100702
  · exact g32p_supplierForest_actual_100708
  · exact g32p_supplierForest_actual_100951
  · exact g32p_supplierForest_actual_100952
  · exact g32p_supplierForest_actual_100977
  · exact g32p_supplierForest_actual_100989
  · exact g32p_supplierForest_actual_100991
  · exact g32p_supplierForest_actual_101085
  · exact g32p_supplierForest_actual_101182
  · exact g32p_supplierForest_actual_101183
  · exact g32p_supplierForest_actual_101234
  · exact g32p_supplierForest_actual_101285
  · exact g32p_supplierForest_actual_101333
  · exact g32p_supplierForest_actual_101336
  · exact g32p_supplierForest_actual_101383
  · exact g32p_supplierForest_actual_101404
  · exact g32p_supplierForest_actual_101434
  · exact g32p_supplierForest_actual_101488
  · exact g32p_supplierForest_actual_101489
  · exact g32p_supplierForest_actual_101537
  · exact g32p_supplierForest_actual_101551
  · exact g32p_supplierForest_actual_101601
  · exact g32p_supplierForest_actual_101614
  · exact g32p_supplierForest_actual_101680
  · exact g32p_supplierForest_actual_101687
  · exact g32p_supplierForest_actual_101702
  · exact g32p_supplierForest_actual_101718
  · exact g32p_supplierForest_actual_101721
  · exact g32p_supplierForest_actual_101722
  · exact g32p_supplierForest_actual_101817
  · exact g32p_supplierForest_actual_101925
  · exact g32p_supplierForest_actual_101938
  · exact g32p_supplierForest_actual_101940
  · exact g32p_supplierForest_actual_101944
  · exact g32p_supplierForest_actual_101969
  · exact g32p_supplierForest_actual_102052
  · exact g32p_supplierForest_actual_102170
  · exact g32p_supplierForest_actual_102218
  · exact g32p_supplierForest_actual_102226
  · exact g32p_supplierForest_actual_102298
  · exact g32p_supplierForest_actual_102299
  · exact g32p_supplierForest_actual_102306
  · exact g32p_supplierForest_actual_102309
  · exact g32p_supplierForest_actual_102312
  · exact g32p_supplierForest_actual_102334
  · exact g32p_supplierForest_actual_102390
  · exact g32p_supplierForest_actual_102425
  · exact g32p_supplierForest_actual_102454
  · exact g32p_supplierForest_actual_102457
  · exact g32p_supplierForest_actual_102469
  · exact g32p_supplierForest_actual_102524
  · exact g32p_supplierForest_actual_102557
  · exact g32p_supplierForest_actual_102569
  · exact g32p_supplierForest_actual_102580
  · exact g32p_supplierForest_actual_102756
  · exact g32p_supplierForest_actual_102866
  · exact g32p_supplierForest_actual_102891
  · exact g32p_supplierForest_actual_102988
  · exact g32p_supplierForest_actual_103057
  · exact g32p_supplierForest_actual_103089
  · exact g32p_supplierForest_actual_103158
  · exact g32p_supplierForest_actual_103167
  · exact g32p_supplierForest_actual_103174
  · exact g32p_supplierForest_actual_103191
  · exact g32p_supplierForest_actual_103205
  · exact g32p_supplierForest_actual_103249
  · exact g32p_supplierForest_actual_103322
  · exact g32p_supplierForest_actual_103344
  · exact g32p_supplierForest_actual_103354
  · exact g32p_supplierForest_actual_103464
  · exact g32p_supplierForest_actual_103476
  · exact g32p_supplierForest_actual_103489
  · exact g32p_supplierForest_actual_103550
  · exact g32p_supplierForest_actual_103570
  · exact g32p_supplierForest_actual_103590
  · exact g32p_supplierForest_actual_103631
  · exact g32p_supplierForest_actual_103761
  · exact g32p_supplierForest_actual_103813
  · exact g32p_supplierForest_actual_103862
  · exact g32p_supplierForest_actual_103942
  · exact g32p_supplierForest_actual_103995
  · exact g32p_supplierForest_actual_104016
  · exact g32p_supplierForest_actual_104026
  · exact g32p_supplierForest_actual_104028
  · exact g32p_supplierForest_actual_104037
  · exact g32p_supplierForest_actual_104179
  · exact g32p_supplierForest_actual_104197

def g32p_supplierForest_nodes_027 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_104234 else g32p_supplierForest_node_104289) else (if i.val < 3 then g32p_supplierForest_node_104312 else g32p_supplierForest_node_104351)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_104437 else g32p_supplierForest_node_104492) else (if i.val < 7 then g32p_supplierForest_node_104493 else g32p_supplierForest_node_104509))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_104716 else g32p_supplierForest_node_104729) else (if i.val < 11 then g32p_supplierForest_node_104763 else g32p_supplierForest_node_104856)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_104916 else g32p_supplierForest_node_104956) else (if i.val < 15 then g32p_supplierForest_node_104990 else g32p_supplierForest_node_104998)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_105005 else g32p_supplierForest_node_105033) else (if i.val < 19 then g32p_supplierForest_node_105115 else g32p_supplierForest_node_105169)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_105239 else g32p_supplierForest_node_105292) else (if i.val < 23 then g32p_supplierForest_node_105339 else g32p_supplierForest_node_105341))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_105406 else g32p_supplierForest_node_105541) else (if i.val < 27 then g32p_supplierForest_node_105546 else g32p_supplierForest_node_105563)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_105572 else g32p_supplierForest_node_105573) else (if i.val < 31 then g32p_supplierForest_node_105649 else g32p_supplierForest_node_105694))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_105699 else g32p_supplierForest_node_105705) else (if i.val < 35 then g32p_supplierForest_node_105722 else g32p_supplierForest_node_105865)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_105984 else g32p_supplierForest_node_106008) else (if i.val < 39 then g32p_supplierForest_node_106065 else g32p_supplierForest_node_106178))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_106189 else g32p_supplierForest_node_106209) else (if i.val < 43 then g32p_supplierForest_node_106244 else g32p_supplierForest_node_106268)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_106336 else g32p_supplierForest_node_106341) else (if i.val < 47 then g32p_supplierForest_node_106345 else g32p_supplierForest_node_106359)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_106422 else g32p_supplierForest_node_106484) else (if i.val < 51 then g32p_supplierForest_node_106514 else g32p_supplierForest_node_106523)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_106528 else g32p_supplierForest_node_106606) else (if i.val < 55 then g32p_supplierForest_node_106645 else g32p_supplierForest_node_106748))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_106753 else g32p_supplierForest_node_106934) else (if i.val < 59 then g32p_supplierForest_node_106938 else g32p_supplierForest_node_107063)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_107064 else g32p_supplierForest_node_107123) else (if i.val < 63 then g32p_supplierForest_node_107190 else g32p_supplierForest_node_107254)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_107284 else g32p_supplierForest_node_107394) else (if i.val < 67 then g32p_supplierForest_node_107405 else g32p_supplierForest_node_107406)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_107431 else g32p_supplierForest_node_107446) else (if i.val < 71 then g32p_supplierForest_node_107451 else g32p_supplierForest_node_107528))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_107542 else g32p_supplierForest_node_107603) else (if i.val < 75 then g32p_supplierForest_node_107606 else g32p_supplierForest_node_107652)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_107660 else g32p_supplierForest_node_107702) else (if i.val < 79 then g32p_supplierForest_node_107828 else g32p_supplierForest_node_107851)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_107882 else g32p_supplierForest_node_107894) else (if i.val < 83 then g32p_supplierForest_node_107933 else g32p_supplierForest_node_108061)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_108120 else g32p_supplierForest_node_108123) else (if i.val < 87 then g32p_supplierForest_node_108233 else g32p_supplierForest_node_108263))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_108319 else g32p_supplierForest_node_108432) else (if i.val < 91 then g32p_supplierForest_node_108465 else g32p_supplierForest_node_108490)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_108537 else g32p_supplierForest_node_108548) else (if i.val < 95 then g32p_supplierForest_node_108554 else g32p_supplierForest_node_108564))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_108571 else g32p_supplierForest_node_108626) else (if i.val < 99 then g32p_supplierForest_node_108645 else g32p_supplierForest_node_108698)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_108725 else g32p_supplierForest_node_108757) else (if i.val < 103 then g32p_supplierForest_node_108778 else g32p_supplierForest_node_108807))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_108845 else g32p_supplierForest_node_108848) else (if i.val < 107 then g32p_supplierForest_node_108852 else g32p_supplierForest_node_108863)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_108906 else g32p_supplierForest_node_109003) else (if i.val < 111 then g32p_supplierForest_node_109004 else g32p_supplierForest_node_109062)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_109080 else g32p_supplierForest_node_109088) else (if i.val < 115 then g32p_supplierForest_node_109094 else g32p_supplierForest_node_109101)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_109117 else g32p_supplierForest_node_109243) else (if i.val < 119 then g32p_supplierForest_node_109271 else g32p_supplierForest_node_109302))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_109404 else g32p_supplierForest_node_109408) else (if i.val < 123 then g32p_supplierForest_node_109426 else g32p_supplierForest_node_109558)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_109598 else g32p_supplierForest_node_109622) else (if i.val < 127 then g32p_supplierForest_node_109672 else g32p_supplierForest_node_109724))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_109809 else g32p_supplierForest_node_109868) else (if i.val < 131 then g32p_supplierForest_node_109920 else g32p_supplierForest_node_110066)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_110093 else g32p_supplierForest_node_110108) else (if i.val < 135 then g32p_supplierForest_node_110209 else g32p_supplierForest_node_110215))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_110333 else g32p_supplierForest_node_110376) else (if i.val < 139 then g32p_supplierForest_node_110388 else g32p_supplierForest_node_110405)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_110562 else g32p_supplierForest_node_110570) else (if i.val < 143 then g32p_supplierForest_node_110752 else g32p_supplierForest_node_110765)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_110789 else g32p_supplierForest_node_110790) else (if i.val < 147 then g32p_supplierForest_node_110866 else g32p_supplierForest_node_110913)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_111211 else g32p_supplierForest_node_111353) else (if i.val < 151 then g32p_supplierForest_node_111505 else g32p_supplierForest_node_111533))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_111571 else g32p_supplierForest_node_111584) else (if i.val < 155 then g32p_supplierForest_node_111631 else g32p_supplierForest_node_111634)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_111641 else g32p_supplierForest_node_111644) else (if i.val < 159 then g32p_supplierForest_node_111653 else g32p_supplierForest_node_111660))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_111663 else g32p_supplierForest_node_111668) else (if i.val < 163 then g32p_supplierForest_node_111836 else g32p_supplierForest_node_111870)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_111887 else g32p_supplierForest_node_111894) else (if i.val < 167 then g32p_supplierForest_node_111940 else g32p_supplierForest_node_111951))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_112107 else g32p_supplierForest_node_112402) else (if i.val < 171 then g32p_supplierForest_node_112417 else g32p_supplierForest_node_112473)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_112492 else g32p_supplierForest_node_112619) else (if i.val < 175 then g32p_supplierForest_node_112631 else g32p_supplierForest_node_112673)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_112751 else g32p_supplierForest_node_112760) else (if i.val < 179 then g32p_supplierForest_node_112815 else g32p_supplierForest_node_112853)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_112987 else g32p_supplierForest_node_113025) else (if i.val < 183 then g32p_supplierForest_node_113045 else g32p_supplierForest_node_113078))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_113174 else g32p_supplierForest_node_113184) else (if i.val < 187 then g32p_supplierForest_node_113203 else g32p_supplierForest_node_113206)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_113225 else g32p_supplierForest_node_113237) else (if i.val < 191 then g32p_supplierForest_node_113276 else g32p_supplierForest_node_113309)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_113417 else g32p_supplierForest_node_113426) else (if i.val < 195 then g32p_supplierForest_node_113444 else g32p_supplierForest_node_113452)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_113502 else g32p_supplierForest_node_113538) else (if i.val < 199 then g32p_supplierForest_node_113543 else g32p_supplierForest_node_113555))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_113568 else g32p_supplierForest_node_113574) else (if i.val < 203 then g32p_supplierForest_node_113606 else g32p_supplierForest_node_113624)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_113644 else g32p_supplierForest_node_113656) else (if i.val < 207 then g32p_supplierForest_node_113667 else g32p_supplierForest_node_113687)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_113698 else g32p_supplierForest_node_113699) else (if i.val < 211 then g32p_supplierForest_node_113716 else g32p_supplierForest_node_113721)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_113739 else g32p_supplierForest_node_113783) else (if i.val < 215 then g32p_supplierForest_node_113796 else g32p_supplierForest_node_113801))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_113823 else g32p_supplierForest_node_113853) else (if i.val < 219 then g32p_supplierForest_node_113868 else g32p_supplierForest_node_113870)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_113885 else g32p_supplierForest_node_113896) else (if i.val < 223 then g32p_supplierForest_node_113949 else g32p_supplierForest_node_113979))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_114072 else g32p_supplierForest_node_114170) else (if i.val < 227 then g32p_supplierForest_node_114214 else g32p_supplierForest_node_114226)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_114238 else g32p_supplierForest_node_114246) else (if i.val < 231 then g32p_supplierForest_node_114280 else g32p_supplierForest_node_114311))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_114446 else g32p_supplierForest_node_114469) else (if i.val < 235 then g32p_supplierForest_node_114516 else g32p_supplierForest_node_114546)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_114570 else g32p_supplierForest_node_114590) else (if i.val < 239 then g32p_supplierForest_node_114613 else g32p_supplierForest_node_114758)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_114779 else g32p_supplierForest_node_114860) else (if i.val < 243 then g32p_supplierForest_node_114887 else g32p_supplierForest_node_114994)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_115042 else g32p_supplierForest_node_115049) else (if i.val < 247 then g32p_supplierForest_node_115089 else g32p_supplierForest_node_115235))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_115273 else g32p_supplierForest_node_115310) else (if i.val < 251 then g32p_supplierForest_node_115317 else g32p_supplierForest_node_115355)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_115393 else g32p_supplierForest_node_115398) else (if i.val < 255 then g32p_supplierForest_node_115443 else g32p_supplierForest_node_115485))))))))

def g32p_supplierForest_classes_027 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 35) else (if i.val < 3 then 57 else 30)) else (if i.val < 6 then (if i.val < 5 then 30 else 29) else (if i.val < 7 then 88 else 88))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 29 else 4) else (if i.val < 11 then 29 else 60)) else (if i.val < 14 then (if i.val < 13 then 33 else 60) else (if i.val < 15 then 88 else 88)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 58 else 60) else (if i.val < 19 then 59 else 60)) else (if i.val < 22 then (if i.val < 21 then 30 else 17) else (if i.val < 23 then 60 else 33))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 57 else 35) else (if i.val < 27 then 30 else 61)) else (if i.val < 30 then (if i.val < 29 then 57 else 58) else (if i.val < 31 then 88 else 57))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 15 else 30) else (if i.val < 35 then 29 else 63)) else (if i.val < 38 then (if i.val < 37 then 30 else 36) else (if i.val < 39 then 61 else 29))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 57 else 30) else (if i.val < 43 then 60 else 30)) else (if i.val < 46 then (if i.val < 45 then 66 else 64) else (if i.val < 47 then 59 else 14)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 61 else 30) else (if i.val < 51 then 34 else 29)) else (if i.val < 54 then (if i.val < 53 then 29 else 16) else (if i.val < 55 then 59 else 4))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 60 else 58) else (if i.val < 59 then 60 else 36)) else (if i.val < 62 then (if i.val < 61 then 89 else 59) else (if i.val < 63 then 57 else 30)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 91 else 59) else (if i.val < 67 then 57 else 30)) else (if i.val < 70 then (if i.val < 69 then 89 else 89) else (if i.val < 71 then 57 else 59))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 90 else 88) else (if i.val < 75 then 59 else 35)) else (if i.val < 78 then (if i.val < 77 then 59 else 14) else (if i.val < 79 then 92 else 61)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 93 else 66) else (if i.val < 83 then 62 else 36)) else (if i.val < 86 then (if i.val < 85 then 57 else 59) else (if i.val < 87 then 64 else 57))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 57 else 62) else (if i.val < 91 then 91 else 90)) else (if i.val < 94 then (if i.val < 93 then 57 else 63) else (if i.val < 95 then 58 else 91))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 57 else 59) else (if i.val < 99 then 57 else 30)) else (if i.val < 102 then (if i.val < 101 then 58 else 60) else (if i.val < 103 then 63 else 66))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 57 else 60) else (if i.val < 107 then 57 else 34)) else (if i.val < 110 then (if i.val < 109 then 62 else 34) else (if i.val < 111 then 29 else 58)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 36 else 29) else (if i.val < 115 then 57 else 66)) else (if i.val < 118 then (if i.val < 117 then 57 else 61) else (if i.val < 119 then 60 else 33))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 65 else 29) else (if i.val < 123 then 64 else 63)) else (if i.val < 126 then (if i.val < 125 then 91 else 90) else (if i.val < 127 then 61 else 92))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 87 else 59) else (if i.val < 131 then 92 else 35)) else (if i.val < 134 then (if i.val < 133 then 60 else 33) else (if i.val < 135 then 33 else 33))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 57 else 57) else (if i.val < 139 then 57 else 61)) else (if i.val < 142 then (if i.val < 141 then 34 else 36) else (if i.val < 143 then 66 else 30)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 66 else 62) else (if i.val < 147 then 66 else 57)) else (if i.val < 150 then (if i.val < 149 then 59 else 33) else (if i.val < 151 then 63 else 62))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 58 else 59) else (if i.val < 155 then 29 else 30)) else (if i.val < 158 then (if i.val < 157 then 66 else 62) else (if i.val < 159 then 57 else 58))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 65 else 34) else (if i.val < 163 then 36 else 35)) else (if i.val < 166 then (if i.val < 165 then 29 else 62) else (if i.val < 167 then 59 else 36))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 34 else 59) else (if i.val < 171 then 57 else 33)) else (if i.val < 174 then (if i.val < 173 then 35 else 90) else (if i.val < 175 then 58 else 90)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 88 else 60) else (if i.val < 179 then 16 else 33)) else (if i.val < 182 then (if i.val < 181 then 60 else 57) else (if i.val < 183 then 32 else 36))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 59 else 60) else (if i.val < 187 then 66 else 63)) else (if i.val < 190 then (if i.val < 189 then 59 else 60) else (if i.val < 191 then 62 else 62)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 57 else 60) else (if i.val < 195 then 59 else 30)) else (if i.val < 198 then (if i.val < 197 then 34 else 29) else (if i.val < 199 then 66 else 66))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 66 else 62) else (if i.val < 203 then 61 else 66)) else (if i.val < 206 then (if i.val < 205 then 63 else 59) else (if i.val < 207 then 58 else 30)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 4 else 60) else (if i.val < 211 then 29 else 33)) else (if i.val < 214 then (if i.val < 213 then 14 else 29) else (if i.val < 215 then 59 else 60))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 57 else 66) else (if i.val < 219 then 59 else 36)) else (if i.val < 222 then (if i.val < 221 then 30 else 4) else (if i.val < 223 then 63 else 59))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 66 else 60) else (if i.val < 227 then 60 else 59)) else (if i.val < 230 then (if i.val < 229 then 17 else 59) else (if i.val < 231 then 60 else 65))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 30 else 60) else (if i.val < 235 then 58 else 59)) else (if i.val < 238 then (if i.val < 237 then 60 else 59) else (if i.val < 239 then 66 else 60)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 60 else 29) else (if i.val < 243 then 30 else 64)) else (if i.val < 246 then (if i.val < 245 then 61 else 57) else (if i.val < 247 then 57 else 60))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 60 else 60) else (if i.val < 251 then 60 else 66)) else (if i.val < 254 then (if i.val < 253 then 30 else 29) else (if i.val < 255 then 60 else 30))))))))

theorem g32p_supplierForest_actual_027 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_027 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_027 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_104234
  · exact g32p_supplierForest_actual_104289
  · exact g32p_supplierForest_actual_104312
  · exact g32p_supplierForest_actual_104351
  · exact g32p_supplierForest_actual_104437
  · exact g32p_supplierForest_actual_104492
  · exact g32p_supplierForest_actual_104493
  · exact g32p_supplierForest_actual_104509
  · exact g32p_supplierForest_actual_104716
  · exact g32p_supplierForest_actual_104729
  · exact g32p_supplierForest_actual_104763
  · exact g32p_supplierForest_actual_104856
  · exact g32p_supplierForest_actual_104916
  · exact g32p_supplierForest_actual_104956
  · exact g32p_supplierForest_actual_104990
  · exact g32p_supplierForest_actual_104998
  · exact g32p_supplierForest_actual_105005
  · exact g32p_supplierForest_actual_105033
  · exact g32p_supplierForest_actual_105115
  · exact g32p_supplierForest_actual_105169
  · exact g32p_supplierForest_actual_105239
  · exact g32p_supplierForest_actual_105292
  · exact g32p_supplierForest_actual_105339
  · exact g32p_supplierForest_actual_105341
  · exact g32p_supplierForest_actual_105406
  · exact g32p_supplierForest_actual_105541
  · exact g32p_supplierForest_actual_105546
  · exact g32p_supplierForest_actual_105563
  · exact g32p_supplierForest_actual_105572
  · exact g32p_supplierForest_actual_105573
  · exact g32p_supplierForest_actual_105649
  · exact g32p_supplierForest_actual_105694
  · exact g32p_supplierForest_actual_105699
  · exact g32p_supplierForest_actual_105705
  · exact g32p_supplierForest_actual_105722
  · exact g32p_supplierForest_actual_105865
  · exact g32p_supplierForest_actual_105984
  · exact g32p_supplierForest_actual_106008
  · exact g32p_supplierForest_actual_106065
  · exact g32p_supplierForest_actual_106178
  · exact g32p_supplierForest_actual_106189
  · exact g32p_supplierForest_actual_106209
  · exact g32p_supplierForest_actual_106244
  · exact g32p_supplierForest_actual_106268
  · exact g32p_supplierForest_actual_106336
  · exact g32p_supplierForest_actual_106341
  · exact g32p_supplierForest_actual_106345
  · exact g32p_supplierForest_actual_106359
  · exact g32p_supplierForest_actual_106422
  · exact g32p_supplierForest_actual_106484
  · exact g32p_supplierForest_actual_106514
  · exact g32p_supplierForest_actual_106523
  · exact g32p_supplierForest_actual_106528
  · exact g32p_supplierForest_actual_106606
  · exact g32p_supplierForest_actual_106645
  · exact g32p_supplierForest_actual_106748
  · exact g32p_supplierForest_actual_106753
  · exact g32p_supplierForest_actual_106934
  · exact g32p_supplierForest_actual_106938
  · exact g32p_supplierForest_actual_107063
  · exact g32p_supplierForest_actual_107064
  · exact g32p_supplierForest_actual_107123
  · exact g32p_supplierForest_actual_107190
  · exact g32p_supplierForest_actual_107254
  · exact g32p_supplierForest_actual_107284
  · exact g32p_supplierForest_actual_107394
  · exact g32p_supplierForest_actual_107405
  · exact g32p_supplierForest_actual_107406
  · exact g32p_supplierForest_actual_107431
  · exact g32p_supplierForest_actual_107446
  · exact g32p_supplierForest_actual_107451
  · exact g32p_supplierForest_actual_107528
  · exact g32p_supplierForest_actual_107542
  · exact g32p_supplierForest_actual_107603
  · exact g32p_supplierForest_actual_107606
  · exact g32p_supplierForest_actual_107652
  · exact g32p_supplierForest_actual_107660
  · exact g32p_supplierForest_actual_107702
  · exact g32p_supplierForest_actual_107828
  · exact g32p_supplierForest_actual_107851
  · exact g32p_supplierForest_actual_107882
  · exact g32p_supplierForest_actual_107894
  · exact g32p_supplierForest_actual_107933
  · exact g32p_supplierForest_actual_108061
  · exact g32p_supplierForest_actual_108120
  · exact g32p_supplierForest_actual_108123
  · exact g32p_supplierForest_actual_108233
  · exact g32p_supplierForest_actual_108263
  · exact g32p_supplierForest_actual_108319
  · exact g32p_supplierForest_actual_108432
  · exact g32p_supplierForest_actual_108465
  · exact g32p_supplierForest_actual_108490
  · exact g32p_supplierForest_actual_108537
  · exact g32p_supplierForest_actual_108548
  · exact g32p_supplierForest_actual_108554
  · exact g32p_supplierForest_actual_108564
  · exact g32p_supplierForest_actual_108571
  · exact g32p_supplierForest_actual_108626
  · exact g32p_supplierForest_actual_108645
  · exact g32p_supplierForest_actual_108698
  · exact g32p_supplierForest_actual_108725
  · exact g32p_supplierForest_actual_108757
  · exact g32p_supplierForest_actual_108778
  · exact g32p_supplierForest_actual_108807
  · exact g32p_supplierForest_actual_108845
  · exact g32p_supplierForest_actual_108848
  · exact g32p_supplierForest_actual_108852
  · exact g32p_supplierForest_actual_108863
  · exact g32p_supplierForest_actual_108906
  · exact g32p_supplierForest_actual_109003
  · exact g32p_supplierForest_actual_109004
  · exact g32p_supplierForest_actual_109062
  · exact g32p_supplierForest_actual_109080
  · exact g32p_supplierForest_actual_109088
  · exact g32p_supplierForest_actual_109094
  · exact g32p_supplierForest_actual_109101
  · exact g32p_supplierForest_actual_109117
  · exact g32p_supplierForest_actual_109243
  · exact g32p_supplierForest_actual_109271
  · exact g32p_supplierForest_actual_109302
  · exact g32p_supplierForest_actual_109404
  · exact g32p_supplierForest_actual_109408
  · exact g32p_supplierForest_actual_109426
  · exact g32p_supplierForest_actual_109558
  · exact g32p_supplierForest_actual_109598
  · exact g32p_supplierForest_actual_109622
  · exact g32p_supplierForest_actual_109672
  · exact g32p_supplierForest_actual_109724
  · exact g32p_supplierForest_actual_109809
  · exact g32p_supplierForest_actual_109868
  · exact g32p_supplierForest_actual_109920
  · exact g32p_supplierForest_actual_110066
  · exact g32p_supplierForest_actual_110093
  · exact g32p_supplierForest_actual_110108
  · exact g32p_supplierForest_actual_110209
  · exact g32p_supplierForest_actual_110215
  · exact g32p_supplierForest_actual_110333
  · exact g32p_supplierForest_actual_110376
  · exact g32p_supplierForest_actual_110388
  · exact g32p_supplierForest_actual_110405
  · exact g32p_supplierForest_actual_110562
  · exact g32p_supplierForest_actual_110570
  · exact g32p_supplierForest_actual_110752
  · exact g32p_supplierForest_actual_110765
  · exact g32p_supplierForest_actual_110789
  · exact g32p_supplierForest_actual_110790
  · exact g32p_supplierForest_actual_110866
  · exact g32p_supplierForest_actual_110913
  · exact g32p_supplierForest_actual_111211
  · exact g32p_supplierForest_actual_111353
  · exact g32p_supplierForest_actual_111505
  · exact g32p_supplierForest_actual_111533
  · exact g32p_supplierForest_actual_111571
  · exact g32p_supplierForest_actual_111584
  · exact g32p_supplierForest_actual_111631
  · exact g32p_supplierForest_actual_111634
  · exact g32p_supplierForest_actual_111641
  · exact g32p_supplierForest_actual_111644
  · exact g32p_supplierForest_actual_111653
  · exact g32p_supplierForest_actual_111660
  · exact g32p_supplierForest_actual_111663
  · exact g32p_supplierForest_actual_111668
  · exact g32p_supplierForest_actual_111836
  · exact g32p_supplierForest_actual_111870
  · exact g32p_supplierForest_actual_111887
  · exact g32p_supplierForest_actual_111894
  · exact g32p_supplierForest_actual_111940
  · exact g32p_supplierForest_actual_111951
  · exact g32p_supplierForest_actual_112107
  · exact g32p_supplierForest_actual_112402
  · exact g32p_supplierForest_actual_112417
  · exact g32p_supplierForest_actual_112473
  · exact g32p_supplierForest_actual_112492
  · exact g32p_supplierForest_actual_112619
  · exact g32p_supplierForest_actual_112631
  · exact g32p_supplierForest_actual_112673
  · exact g32p_supplierForest_actual_112751
  · exact g32p_supplierForest_actual_112760
  · exact g32p_supplierForest_actual_112815
  · exact g32p_supplierForest_actual_112853
  · exact g32p_supplierForest_actual_112987
  · exact g32p_supplierForest_actual_113025
  · exact g32p_supplierForest_actual_113045
  · exact g32p_supplierForest_actual_113078
  · exact g32p_supplierForest_actual_113174
  · exact g32p_supplierForest_actual_113184
  · exact g32p_supplierForest_actual_113203
  · exact g32p_supplierForest_actual_113206
  · exact g32p_supplierForest_actual_113225
  · exact g32p_supplierForest_actual_113237
  · exact g32p_supplierForest_actual_113276
  · exact g32p_supplierForest_actual_113309
  · exact g32p_supplierForest_actual_113417
  · exact g32p_supplierForest_actual_113426
  · exact g32p_supplierForest_actual_113444
  · exact g32p_supplierForest_actual_113452
  · exact g32p_supplierForest_actual_113502
  · exact g32p_supplierForest_actual_113538
  · exact g32p_supplierForest_actual_113543
  · exact g32p_supplierForest_actual_113555
  · exact g32p_supplierForest_actual_113568
  · exact g32p_supplierForest_actual_113574
  · exact g32p_supplierForest_actual_113606
  · exact g32p_supplierForest_actual_113624
  · exact g32p_supplierForest_actual_113644
  · exact g32p_supplierForest_actual_113656
  · exact g32p_supplierForest_actual_113667
  · exact g32p_supplierForest_actual_113687
  · exact g32p_supplierForest_actual_113698
  · exact g32p_supplierForest_actual_113699
  · exact g32p_supplierForest_actual_113716
  · exact g32p_supplierForest_actual_113721
  · exact g32p_supplierForest_actual_113739
  · exact g32p_supplierForest_actual_113783
  · exact g32p_supplierForest_actual_113796
  · exact g32p_supplierForest_actual_113801
  · exact g32p_supplierForest_actual_113823
  · exact g32p_supplierForest_actual_113853
  · exact g32p_supplierForest_actual_113868
  · exact g32p_supplierForest_actual_113870
  · exact g32p_supplierForest_actual_113885
  · exact g32p_supplierForest_actual_113896
  · exact g32p_supplierForest_actual_113949
  · exact g32p_supplierForest_actual_113979
  · exact g32p_supplierForest_actual_114072
  · exact g32p_supplierForest_actual_114170
  · exact g32p_supplierForest_actual_114214
  · exact g32p_supplierForest_actual_114226
  · exact g32p_supplierForest_actual_114238
  · exact g32p_supplierForest_actual_114246
  · exact g32p_supplierForest_actual_114280
  · exact g32p_supplierForest_actual_114311
  · exact g32p_supplierForest_actual_114446
  · exact g32p_supplierForest_actual_114469
  · exact g32p_supplierForest_actual_114516
  · exact g32p_supplierForest_actual_114546
  · exact g32p_supplierForest_actual_114570
  · exact g32p_supplierForest_actual_114590
  · exact g32p_supplierForest_actual_114613
  · exact g32p_supplierForest_actual_114758
  · exact g32p_supplierForest_actual_114779
  · exact g32p_supplierForest_actual_114860
  · exact g32p_supplierForest_actual_114887
  · exact g32p_supplierForest_actual_114994
  · exact g32p_supplierForest_actual_115042
  · exact g32p_supplierForest_actual_115049
  · exact g32p_supplierForest_actual_115089
  · exact g32p_supplierForest_actual_115235
  · exact g32p_supplierForest_actual_115273
  · exact g32p_supplierForest_actual_115310
  · exact g32p_supplierForest_actual_115317
  · exact g32p_supplierForest_actual_115355
  · exact g32p_supplierForest_actual_115393
  · exact g32p_supplierForest_actual_115398
  · exact g32p_supplierForest_actual_115443
  · exact g32p_supplierForest_actual_115485

def g32p_supplierForest_nodes_028 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_115545 else g32p_supplierForest_node_115575) else (if i.val < 3 then g32p_supplierForest_node_115711 else g32p_supplierForest_node_115782)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_115818 else g32p_supplierForest_node_115850) else (if i.val < 7 then g32p_supplierForest_node_115866 else g32p_supplierForest_node_115868))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_116044 else g32p_supplierForest_node_116048) else (if i.val < 11 then g32p_supplierForest_node_116088 else g32p_supplierForest_node_116091)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_116108 else g32p_supplierForest_node_116153) else (if i.val < 15 then g32p_supplierForest_node_116158 else g32p_supplierForest_node_116179)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_116192 else g32p_supplierForest_node_116209) else (if i.val < 19 then g32p_supplierForest_node_116237 else g32p_supplierForest_node_116269)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_116320 else g32p_supplierForest_node_116357) else (if i.val < 23 then g32p_supplierForest_node_116398 else g32p_supplierForest_node_116419))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_116423 else g32p_supplierForest_node_116434) else (if i.val < 27 then g32p_supplierForest_node_116469 else g32p_supplierForest_node_116479)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_116540 else g32p_supplierForest_node_116581) else (if i.val < 31 then g32p_supplierForest_node_116622 else g32p_supplierForest_node_116631))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_116638 else g32p_supplierForest_node_116699) else (if i.val < 35 then g32p_supplierForest_node_116723 else g32p_supplierForest_node_116737)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_116785 else g32p_supplierForest_node_116821) else (if i.val < 39 then g32p_supplierForest_node_116871 else g32p_supplierForest_node_116875))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_116881 else g32p_supplierForest_node_116896) else (if i.val < 43 then g32p_supplierForest_node_117070 else g32p_supplierForest_node_117120)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_117164 else g32p_supplierForest_node_117188) else (if i.val < 47 then g32p_supplierForest_node_117199 else g32p_supplierForest_node_117232)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_117245 else g32p_supplierForest_node_117256) else (if i.val < 51 then g32p_supplierForest_node_117357 else g32p_supplierForest_node_117386)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_117439 else g32p_supplierForest_node_117460) else (if i.val < 55 then g32p_supplierForest_node_117551 else g32p_supplierForest_node_117662))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_117693 else g32p_supplierForest_node_117817) else (if i.val < 59 then g32p_supplierForest_node_117988 else g32p_supplierForest_node_118033)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_118193 else g32p_supplierForest_node_118353) else (if i.val < 63 then g32p_supplierForest_node_118357 else g32p_supplierForest_node_118396)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_118402 else g32p_supplierForest_node_118432) else (if i.val < 67 then g32p_supplierForest_node_118460 else g32p_supplierForest_node_118638)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_118683 else g32p_supplierForest_node_118714) else (if i.val < 71 then g32p_supplierForest_node_118772 else g32p_supplierForest_node_118793))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_118960 else g32p_supplierForest_node_118985) else (if i.val < 75 then g32p_supplierForest_node_119071 else g32p_supplierForest_node_119082)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_119162 else g32p_supplierForest_node_119257) else (if i.val < 79 then g32p_supplierForest_node_119312 else g32p_supplierForest_node_119338)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_119381 else g32p_supplierForest_node_119407) else (if i.val < 83 then g32p_supplierForest_node_119518 else g32p_supplierForest_node_119520)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_119549 else g32p_supplierForest_node_119610) else (if i.val < 87 then g32p_supplierForest_node_119638 else g32p_supplierForest_node_119640))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_119656 else g32p_supplierForest_node_119665) else (if i.val < 91 then g32p_supplierForest_node_119702 else g32p_supplierForest_node_119726)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_119754 else g32p_supplierForest_node_119845) else (if i.val < 95 then g32p_supplierForest_node_119868 else g32p_supplierForest_node_119903))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_119952 else g32p_supplierForest_node_119979) else (if i.val < 99 then g32p_supplierForest_node_120013 else g32p_supplierForest_node_120016)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_120058 else g32p_supplierForest_node_120067) else (if i.val < 103 then g32p_supplierForest_node_120099 else g32p_supplierForest_node_120149))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_120286 else g32p_supplierForest_node_120347) else (if i.val < 107 then g32p_supplierForest_node_120355 else g32p_supplierForest_node_120372)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_120378 else g32p_supplierForest_node_120396) else (if i.val < 111 then g32p_supplierForest_node_120440 else g32p_supplierForest_node_120477)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_120620 else g32p_supplierForest_node_120636) else (if i.val < 115 then g32p_supplierForest_node_120660 else g32p_supplierForest_node_120798)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_120808 else g32p_supplierForest_node_120900) else (if i.val < 119 then g32p_supplierForest_node_120966 else g32p_supplierForest_node_121049))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_121059 else g32p_supplierForest_node_121062) else (if i.val < 123 then g32p_supplierForest_node_121064 else g32p_supplierForest_node_121211)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_121215 else g32p_supplierForest_node_121309) else (if i.val < 127 then g32p_supplierForest_node_121334 else g32p_supplierForest_node_121340))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_121399 else g32p_supplierForest_node_121506) else (if i.val < 131 then g32p_supplierForest_node_121531 else g32p_supplierForest_node_121839)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_121972 else g32p_supplierForest_node_122058) else (if i.val < 135 then g32p_supplierForest_node_122175 else g32p_supplierForest_node_122198))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_122212 else g32p_supplierForest_node_122351) else (if i.val < 139 then g32p_supplierForest_node_122363 else g32p_supplierForest_node_122375)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_122376 else g32p_supplierForest_node_122378) else (if i.val < 143 then g32p_supplierForest_node_122510 else g32p_supplierForest_node_122513)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_122566 else g32p_supplierForest_node_122623) else (if i.val < 147 then g32p_supplierForest_node_122633 else g32p_supplierForest_node_122684)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_122794 else g32p_supplierForest_node_122878) else (if i.val < 151 then g32p_supplierForest_node_122886 else g32p_supplierForest_node_122940))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_122943 else g32p_supplierForest_node_122957) else (if i.val < 155 then g32p_supplierForest_node_122959 else g32p_supplierForest_node_122971)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_123008 else g32p_supplierForest_node_123034) else (if i.val < 159 then g32p_supplierForest_node_123065 else g32p_supplierForest_node_123069))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_123230 else g32p_supplierForest_node_123278) else (if i.val < 163 then g32p_supplierForest_node_123294 else g32p_supplierForest_node_123342)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_123365 else g32p_supplierForest_node_123394) else (if i.val < 167 then g32p_supplierForest_node_123415 else g32p_supplierForest_node_123439))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_123476 else g32p_supplierForest_node_123545) else (if i.val < 171 then g32p_supplierForest_node_123628 else g32p_supplierForest_node_123633)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_123666 else g32p_supplierForest_node_123710) else (if i.val < 175 then g32p_supplierForest_node_123796 else g32p_supplierForest_node_123871)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_123965 else g32p_supplierForest_node_123978) else (if i.val < 179 then g32p_supplierForest_node_124022 else g32p_supplierForest_node_124078)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_124085 else g32p_supplierForest_node_124098) else (if i.val < 183 then g32p_supplierForest_node_124109 else g32p_supplierForest_node_124214))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_124233 else g32p_supplierForest_node_124427) else (if i.val < 187 then g32p_supplierForest_node_124429 else g32p_supplierForest_node_124530)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_124561 else g32p_supplierForest_node_124569) else (if i.val < 191 then g32p_supplierForest_node_124611 else g32p_supplierForest_node_124708)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_124777 else g32p_supplierForest_node_124804) else (if i.val < 195 then g32p_supplierForest_node_124850 else g32p_supplierForest_node_124879)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_124907 else g32p_supplierForest_node_124936) else (if i.val < 199 then g32p_supplierForest_node_124957 else g32p_supplierForest_node_125053))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_125054 else g32p_supplierForest_node_125189) else (if i.val < 203 then g32p_supplierForest_node_125212 else g32p_supplierForest_node_125327)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_125341 else g32p_supplierForest_node_125407) else (if i.val < 207 then g32p_supplierForest_node_125414 else g32p_supplierForest_node_125505)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_125525 else g32p_supplierForest_node_125539) else (if i.val < 211 then g32p_supplierForest_node_125542 else g32p_supplierForest_node_125586)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_125622 else g32p_supplierForest_node_125696) else (if i.val < 215 then g32p_supplierForest_node_125748 else g32p_supplierForest_node_125789))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_125812 else g32p_supplierForest_node_125819) else (if i.val < 219 then g32p_supplierForest_node_125845 else g32p_supplierForest_node_125908)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_125928 else g32p_supplierForest_node_125929) else (if i.val < 223 then g32p_supplierForest_node_125930 else g32p_supplierForest_node_125943))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_125945 else g32p_supplierForest_node_125959) else (if i.val < 227 then g32p_supplierForest_node_126044 else g32p_supplierForest_node_126073)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_126160 else g32p_supplierForest_node_126180) else (if i.val < 231 then g32p_supplierForest_node_126243 else g32p_supplierForest_node_126348))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_126375 else g32p_supplierForest_node_126378) else (if i.val < 235 then g32p_supplierForest_node_126390 else g32p_supplierForest_node_126415)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_126554 else g32p_supplierForest_node_126600) else (if i.val < 239 then g32p_supplierForest_node_126615 else g32p_supplierForest_node_126636)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_126703 else g32p_supplierForest_node_126754) else (if i.val < 243 then g32p_supplierForest_node_126793 else g32p_supplierForest_node_126832)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_126897 else g32p_supplierForest_node_126916) else (if i.val < 247 then g32p_supplierForest_node_126958 else g32p_supplierForest_node_126964))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_126981 else g32p_supplierForest_node_127014) else (if i.val < 251 then g32p_supplierForest_node_127091 else g32p_supplierForest_node_127139)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_127158 else g32p_supplierForest_node_127195) else (if i.val < 255 then g32p_supplierForest_node_127220 else g32p_supplierForest_node_127261))))))))

def g32p_supplierForest_classes_028 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 62 else 30) else (if i.val < 3 then 33 else 62)) else (if i.val < 6 then (if i.val < 5 then 91 else 91) else (if i.val < 7 then 35 else 35))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 89 else 35) else (if i.val < 11 then 35 else 59)) else (if i.val < 14 then (if i.val < 13 then 29 else 34) else (if i.val < 15 then 60 else 33)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 61 else 59) else (if i.val < 19 then 36 else 58)) else (if i.val < 22 then (if i.val < 21 then 33 else 61) else (if i.val < 23 then 58 else 61))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 62 else 29) else (if i.val < 27 then 34 else 63)) else (if i.val < 30 then (if i.val < 29 then 66 else 35) else (if i.val < 31 then 61 else 30))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 60 else 61) else (if i.val < 35 then 91 else 90)) else (if i.val < 38 then (if i.val < 37 then 60 else 66) else (if i.val < 39 then 63 else 62))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 66 else 60) else (if i.val < 43 then 89 else 35)) else (if i.val < 46 then (if i.val < 45 then 60 else 90) else (if i.val < 47 then 60 else 57)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 59 else 29) else (if i.val < 51 then 61 else 33)) else (if i.val < 54 then (if i.val < 53 then 29 else 29) else (if i.val < 55 then 92 else 61))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 91 else 58) else (if i.val < 59 then 30 else 91)) else (if i.val < 62 then (if i.val < 61 then 92 else 61) else (if i.val < 63 then 30 else 65)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 62 else 62) else (if i.val < 67 then 66 else 65)) else (if i.val < 70 then (if i.val < 69 then 57 else 57) else (if i.val < 71 then 63 else 36))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 61 else 30) else (if i.val < 75 then 61 else 91)) else (if i.val < 78 then (if i.val < 77 then 60 else 34) else (if i.val < 79 then 63 else 66)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 30 else 66) else (if i.val < 83 then 66 else 62)) else (if i.val < 86 then (if i.val < 85 then 66 else 15) else (if i.val < 87 then 29 else 89))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 89 else 91) else (if i.val < 91 then 91 else 35)) else (if i.val < 94 then (if i.val < 93 then 59 else 91) else (if i.val < 95 then 30 else 93))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 34 else 89) else (if i.val < 99 then 92 else 30)) else (if i.val < 102 then (if i.val < 101 then 36 else 60) else (if i.val < 103 then 62 else 29))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 34 else 58) else (if i.val < 107 then 62 else 35)) else (if i.val < 110 then (if i.val < 109 then 35 else 92) else (if i.val < 111 then 35 else 34)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 59 else 35) else (if i.val < 115 then 29 else 29)) else (if i.val < 118 then (if i.val < 117 then 59 else 60) else (if i.val < 119 then 66 else 92))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 91 else 59) else (if i.val < 123 then 91 else 91)) else (if i.val < 126 then (if i.val < 125 then 35 else 90) else (if i.val < 127 then 29 else 30))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 60 else 29) else (if i.val < 131 then 33 else 61)) else (if i.val < 134 then (if i.val < 133 then 14 else 90) else (if i.val < 135 then 62 else 60))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 35 else 35) else (if i.val < 139 then 30 else 16)) else (if i.val < 142 then (if i.val < 141 then 59 else 60) else (if i.val < 143 then 89 else 92)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 33 else 92) else (if i.val < 147 then 92 else 60)) else (if i.val < 150 then (if i.val < 149 then 90 else 35) else (if i.val < 151 then 60 else 60))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 87 else 90) else (if i.val < 155 then 30 else 60)) else (if i.val < 158 then (if i.val < 157 then 62 else 60) else (if i.val < 159 then 60 else 58))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 63 else 62) else (if i.val < 163 then 34 else 61)) else (if i.val < 166 then (if i.val < 165 then 58 else 93) else (if i.val < 167 then 35 else 62))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 92 else 63) else (if i.val < 171 then 93 else 62)) else (if i.val < 174 then (if i.val < 173 then 34 else 58) else (if i.val < 175 then 92 else 63)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 34 else 62) else (if i.val < 179 then 61 else 35)) else (if i.val < 182 then (if i.val < 181 then 60 else 35) else (if i.val < 183 then 90 else 62))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 29 else 91) else (if i.val < 187 then 60 else 36)) else (if i.val < 190 then (if i.val < 189 then 35 else 58) else (if i.val < 191 then 34 else 58)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 29 else 91) else (if i.val < 195 then 58 else 87)) else (if i.val < 198 then (if i.val < 197 then 65 else 93) else (if i.val < 199 then 92 else 59))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 63 else 66) else (if i.val < 203 then 62 else 66)) else (if i.val < 206 then (if i.val < 205 then 66 else 61) else (if i.val < 207 then 60 else 35)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 30 else 89) else (if i.val < 211 then 66 else 66)) else (if i.val < 214 then (if i.val < 213 then 90 else 34) else (if i.val < 215 then 92 else 66))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 60 else 90) else (if i.val < 219 then 30 else 66)) else (if i.val < 222 then (if i.val < 221 then 66 else 35) else (if i.val < 223 then 60 else 33))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 91 else 35) else (if i.val < 227 then 30 else 58)) else (if i.val < 230 then (if i.val < 229 then 66 else 66) else (if i.val < 231 then 57 else 61))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 92 else 92) else (if i.val < 235 then 66 else 66)) else (if i.val < 238 then (if i.val < 237 then 35 else 60) else (if i.val < 239 then 90 else 63)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 90 else 91) else (if i.val < 243 then 61 else 66)) else (if i.val < 246 then (if i.val < 245 then 61 else 35) else (if i.val < 247 then 66 else 60))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 66 else 90) else (if i.val < 251 then 35 else 90)) else (if i.val < 254 then (if i.val < 253 then 36 else 89) else (if i.val < 255 then 91 else 35))))))))

theorem g32p_supplierForest_actual_028 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_028 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_028 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_115545
  · exact g32p_supplierForest_actual_115575
  · exact g32p_supplierForest_actual_115711
  · exact g32p_supplierForest_actual_115782
  · exact g32p_supplierForest_actual_115818
  · exact g32p_supplierForest_actual_115850
  · exact g32p_supplierForest_actual_115866
  · exact g32p_supplierForest_actual_115868
  · exact g32p_supplierForest_actual_116044
  · exact g32p_supplierForest_actual_116048
  · exact g32p_supplierForest_actual_116088
  · exact g32p_supplierForest_actual_116091
  · exact g32p_supplierForest_actual_116108
  · exact g32p_supplierForest_actual_116153
  · exact g32p_supplierForest_actual_116158
  · exact g32p_supplierForest_actual_116179
  · exact g32p_supplierForest_actual_116192
  · exact g32p_supplierForest_actual_116209
  · exact g32p_supplierForest_actual_116237
  · exact g32p_supplierForest_actual_116269
  · exact g32p_supplierForest_actual_116320
  · exact g32p_supplierForest_actual_116357
  · exact g32p_supplierForest_actual_116398
  · exact g32p_supplierForest_actual_116419
  · exact g32p_supplierForest_actual_116423
  · exact g32p_supplierForest_actual_116434
  · exact g32p_supplierForest_actual_116469
  · exact g32p_supplierForest_actual_116479
  · exact g32p_supplierForest_actual_116540
  · exact g32p_supplierForest_actual_116581
  · exact g32p_supplierForest_actual_116622
  · exact g32p_supplierForest_actual_116631
  · exact g32p_supplierForest_actual_116638
  · exact g32p_supplierForest_actual_116699
  · exact g32p_supplierForest_actual_116723
  · exact g32p_supplierForest_actual_116737
  · exact g32p_supplierForest_actual_116785
  · exact g32p_supplierForest_actual_116821
  · exact g32p_supplierForest_actual_116871
  · exact g32p_supplierForest_actual_116875
  · exact g32p_supplierForest_actual_116881
  · exact g32p_supplierForest_actual_116896
  · exact g32p_supplierForest_actual_117070
  · exact g32p_supplierForest_actual_117120
  · exact g32p_supplierForest_actual_117164
  · exact g32p_supplierForest_actual_117188
  · exact g32p_supplierForest_actual_117199
  · exact g32p_supplierForest_actual_117232
  · exact g32p_supplierForest_actual_117245
  · exact g32p_supplierForest_actual_117256
  · exact g32p_supplierForest_actual_117357
  · exact g32p_supplierForest_actual_117386
  · exact g32p_supplierForest_actual_117439
  · exact g32p_supplierForest_actual_117460
  · exact g32p_supplierForest_actual_117551
  · exact g32p_supplierForest_actual_117662
  · exact g32p_supplierForest_actual_117693
  · exact g32p_supplierForest_actual_117817
  · exact g32p_supplierForest_actual_117988
  · exact g32p_supplierForest_actual_118033
  · exact g32p_supplierForest_actual_118193
  · exact g32p_supplierForest_actual_118353
  · exact g32p_supplierForest_actual_118357
  · exact g32p_supplierForest_actual_118396
  · exact g32p_supplierForest_actual_118402
  · exact g32p_supplierForest_actual_118432
  · exact g32p_supplierForest_actual_118460
  · exact g32p_supplierForest_actual_118638
  · exact g32p_supplierForest_actual_118683
  · exact g32p_supplierForest_actual_118714
  · exact g32p_supplierForest_actual_118772
  · exact g32p_supplierForest_actual_118793
  · exact g32p_supplierForest_actual_118960
  · exact g32p_supplierForest_actual_118985
  · exact g32p_supplierForest_actual_119071
  · exact g32p_supplierForest_actual_119082
  · exact g32p_supplierForest_actual_119162
  · exact g32p_supplierForest_actual_119257
  · exact g32p_supplierForest_actual_119312
  · exact g32p_supplierForest_actual_119338
  · exact g32p_supplierForest_actual_119381
  · exact g32p_supplierForest_actual_119407
  · exact g32p_supplierForest_actual_119518
  · exact g32p_supplierForest_actual_119520
  · exact g32p_supplierForest_actual_119549
  · exact g32p_supplierForest_actual_119610
  · exact g32p_supplierForest_actual_119638
  · exact g32p_supplierForest_actual_119640
  · exact g32p_supplierForest_actual_119656
  · exact g32p_supplierForest_actual_119665
  · exact g32p_supplierForest_actual_119702
  · exact g32p_supplierForest_actual_119726
  · exact g32p_supplierForest_actual_119754
  · exact g32p_supplierForest_actual_119845
  · exact g32p_supplierForest_actual_119868
  · exact g32p_supplierForest_actual_119903
  · exact g32p_supplierForest_actual_119952
  · exact g32p_supplierForest_actual_119979
  · exact g32p_supplierForest_actual_120013
  · exact g32p_supplierForest_actual_120016
  · exact g32p_supplierForest_actual_120058
  · exact g32p_supplierForest_actual_120067
  · exact g32p_supplierForest_actual_120099
  · exact g32p_supplierForest_actual_120149
  · exact g32p_supplierForest_actual_120286
  · exact g32p_supplierForest_actual_120347
  · exact g32p_supplierForest_actual_120355
  · exact g32p_supplierForest_actual_120372
  · exact g32p_supplierForest_actual_120378
  · exact g32p_supplierForest_actual_120396
  · exact g32p_supplierForest_actual_120440
  · exact g32p_supplierForest_actual_120477
  · exact g32p_supplierForest_actual_120620
  · exact g32p_supplierForest_actual_120636
  · exact g32p_supplierForest_actual_120660
  · exact g32p_supplierForest_actual_120798
  · exact g32p_supplierForest_actual_120808
  · exact g32p_supplierForest_actual_120900
  · exact g32p_supplierForest_actual_120966
  · exact g32p_supplierForest_actual_121049
  · exact g32p_supplierForest_actual_121059
  · exact g32p_supplierForest_actual_121062
  · exact g32p_supplierForest_actual_121064
  · exact g32p_supplierForest_actual_121211
  · exact g32p_supplierForest_actual_121215
  · exact g32p_supplierForest_actual_121309
  · exact g32p_supplierForest_actual_121334
  · exact g32p_supplierForest_actual_121340
  · exact g32p_supplierForest_actual_121399
  · exact g32p_supplierForest_actual_121506
  · exact g32p_supplierForest_actual_121531
  · exact g32p_supplierForest_actual_121839
  · exact g32p_supplierForest_actual_121972
  · exact g32p_supplierForest_actual_122058
  · exact g32p_supplierForest_actual_122175
  · exact g32p_supplierForest_actual_122198
  · exact g32p_supplierForest_actual_122212
  · exact g32p_supplierForest_actual_122351
  · exact g32p_supplierForest_actual_122363
  · exact g32p_supplierForest_actual_122375
  · exact g32p_supplierForest_actual_122376
  · exact g32p_supplierForest_actual_122378
  · exact g32p_supplierForest_actual_122510
  · exact g32p_supplierForest_actual_122513
  · exact g32p_supplierForest_actual_122566
  · exact g32p_supplierForest_actual_122623
  · exact g32p_supplierForest_actual_122633
  · exact g32p_supplierForest_actual_122684
  · exact g32p_supplierForest_actual_122794
  · exact g32p_supplierForest_actual_122878
  · exact g32p_supplierForest_actual_122886
  · exact g32p_supplierForest_actual_122940
  · exact g32p_supplierForest_actual_122943
  · exact g32p_supplierForest_actual_122957
  · exact g32p_supplierForest_actual_122959
  · exact g32p_supplierForest_actual_122971
  · exact g32p_supplierForest_actual_123008
  · exact g32p_supplierForest_actual_123034
  · exact g32p_supplierForest_actual_123065
  · exact g32p_supplierForest_actual_123069
  · exact g32p_supplierForest_actual_123230
  · exact g32p_supplierForest_actual_123278
  · exact g32p_supplierForest_actual_123294
  · exact g32p_supplierForest_actual_123342
  · exact g32p_supplierForest_actual_123365
  · exact g32p_supplierForest_actual_123394
  · exact g32p_supplierForest_actual_123415
  · exact g32p_supplierForest_actual_123439
  · exact g32p_supplierForest_actual_123476
  · exact g32p_supplierForest_actual_123545
  · exact g32p_supplierForest_actual_123628
  · exact g32p_supplierForest_actual_123633
  · exact g32p_supplierForest_actual_123666
  · exact g32p_supplierForest_actual_123710
  · exact g32p_supplierForest_actual_123796
  · exact g32p_supplierForest_actual_123871
  · exact g32p_supplierForest_actual_123965
  · exact g32p_supplierForest_actual_123978
  · exact g32p_supplierForest_actual_124022
  · exact g32p_supplierForest_actual_124078
  · exact g32p_supplierForest_actual_124085
  · exact g32p_supplierForest_actual_124098
  · exact g32p_supplierForest_actual_124109
  · exact g32p_supplierForest_actual_124214
  · exact g32p_supplierForest_actual_124233
  · exact g32p_supplierForest_actual_124427
  · exact g32p_supplierForest_actual_124429
  · exact g32p_supplierForest_actual_124530
  · exact g32p_supplierForest_actual_124561
  · exact g32p_supplierForest_actual_124569
  · exact g32p_supplierForest_actual_124611
  · exact g32p_supplierForest_actual_124708
  · exact g32p_supplierForest_actual_124777
  · exact g32p_supplierForest_actual_124804
  · exact g32p_supplierForest_actual_124850
  · exact g32p_supplierForest_actual_124879
  · exact g32p_supplierForest_actual_124907
  · exact g32p_supplierForest_actual_124936
  · exact g32p_supplierForest_actual_124957
  · exact g32p_supplierForest_actual_125053
  · exact g32p_supplierForest_actual_125054
  · exact g32p_supplierForest_actual_125189
  · exact g32p_supplierForest_actual_125212
  · exact g32p_supplierForest_actual_125327
  · exact g32p_supplierForest_actual_125341
  · exact g32p_supplierForest_actual_125407
  · exact g32p_supplierForest_actual_125414
  · exact g32p_supplierForest_actual_125505
  · exact g32p_supplierForest_actual_125525
  · exact g32p_supplierForest_actual_125539
  · exact g32p_supplierForest_actual_125542
  · exact g32p_supplierForest_actual_125586
  · exact g32p_supplierForest_actual_125622
  · exact g32p_supplierForest_actual_125696
  · exact g32p_supplierForest_actual_125748
  · exact g32p_supplierForest_actual_125789
  · exact g32p_supplierForest_actual_125812
  · exact g32p_supplierForest_actual_125819
  · exact g32p_supplierForest_actual_125845
  · exact g32p_supplierForest_actual_125908
  · exact g32p_supplierForest_actual_125928
  · exact g32p_supplierForest_actual_125929
  · exact g32p_supplierForest_actual_125930
  · exact g32p_supplierForest_actual_125943
  · exact g32p_supplierForest_actual_125945
  · exact g32p_supplierForest_actual_125959
  · exact g32p_supplierForest_actual_126044
  · exact g32p_supplierForest_actual_126073
  · exact g32p_supplierForest_actual_126160
  · exact g32p_supplierForest_actual_126180
  · exact g32p_supplierForest_actual_126243
  · exact g32p_supplierForest_actual_126348
  · exact g32p_supplierForest_actual_126375
  · exact g32p_supplierForest_actual_126378
  · exact g32p_supplierForest_actual_126390
  · exact g32p_supplierForest_actual_126415
  · exact g32p_supplierForest_actual_126554
  · exact g32p_supplierForest_actual_126600
  · exact g32p_supplierForest_actual_126615
  · exact g32p_supplierForest_actual_126636
  · exact g32p_supplierForest_actual_126703
  · exact g32p_supplierForest_actual_126754
  · exact g32p_supplierForest_actual_126793
  · exact g32p_supplierForest_actual_126832
  · exact g32p_supplierForest_actual_126897
  · exact g32p_supplierForest_actual_126916
  · exact g32p_supplierForest_actual_126958
  · exact g32p_supplierForest_actual_126964
  · exact g32p_supplierForest_actual_126981
  · exact g32p_supplierForest_actual_127014
  · exact g32p_supplierForest_actual_127091
  · exact g32p_supplierForest_actual_127139
  · exact g32p_supplierForest_actual_127158
  · exact g32p_supplierForest_actual_127195
  · exact g32p_supplierForest_actual_127220
  · exact g32p_supplierForest_actual_127261

def g32p_supplierForest_nodes_029 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_127287 else g32p_supplierForest_node_127308) else (if i.val < 3 then g32p_supplierForest_node_127502 else g32p_supplierForest_node_127507)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_127542 else g32p_supplierForest_node_127654) else (if i.val < 7 then g32p_supplierForest_node_127673 else g32p_supplierForest_node_127700))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_127707 else g32p_supplierForest_node_127767) else (if i.val < 11 then g32p_supplierForest_node_127791 else g32p_supplierForest_node_127809)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_127821 else g32p_supplierForest_node_127832) else (if i.val < 15 then g32p_supplierForest_node_127833 else g32p_supplierForest_node_127883)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_127899 else g32p_supplierForest_node_127904) else (if i.val < 19 then g32p_supplierForest_node_127935 else g32p_supplierForest_node_127950)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_128232 else g32p_supplierForest_node_128233) else (if i.val < 23 then g32p_supplierForest_node_128238 else g32p_supplierForest_node_128258))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_128290 else g32p_supplierForest_node_128310) else (if i.val < 27 then g32p_supplierForest_node_128313 else g32p_supplierForest_node_128314)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_128367 else g32p_supplierForest_node_128406) else (if i.val < 31 then g32p_supplierForest_node_128471 else g32p_supplierForest_node_128545))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_128575 else g32p_supplierForest_node_128592) else (if i.val < 35 then g32p_supplierForest_node_128624 else g32p_supplierForest_node_128694)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_128730 else g32p_supplierForest_node_128778) else (if i.val < 39 then g32p_supplierForest_node_128810 else g32p_supplierForest_node_128875))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_128889 else g32p_supplierForest_node_128891) else (if i.val < 43 then g32p_supplierForest_node_129137 else g32p_supplierForest_node_129247)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_129309 else g32p_supplierForest_node_129396) else (if i.val < 47 then g32p_supplierForest_node_129413 else g32p_supplierForest_node_129414)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_129469 else g32p_supplierForest_node_129470) else (if i.val < 51 then g32p_supplierForest_node_129471 else g32p_supplierForest_node_129528)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_129530 else g32p_supplierForest_node_129602) else (if i.val < 55 then g32p_supplierForest_node_129655 else g32p_supplierForest_node_129656))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_129691 else g32p_supplierForest_node_129749) else (if i.val < 59 then g32p_supplierForest_node_129758 else g32p_supplierForest_node_129835)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_129868 else g32p_supplierForest_node_129934) else (if i.val < 63 then g32p_supplierForest_node_129981 else g32p_supplierForest_node_129986)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_129996 else g32p_supplierForest_node_130094) else (if i.val < 67 then g32p_supplierForest_node_130144 else g32p_supplierForest_node_130215)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_130254 else g32p_supplierForest_node_130258) else (if i.val < 71 then g32p_supplierForest_node_130265 else g32p_supplierForest_node_130335))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_130371 else g32p_supplierForest_node_130386) else (if i.val < 75 then g32p_supplierForest_node_130392 else g32p_supplierForest_node_130409)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_130412 else g32p_supplierForest_node_130419) else (if i.val < 79 then g32p_supplierForest_node_130603 else g32p_supplierForest_node_130795)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_130866 else g32p_supplierForest_node_130958) else (if i.val < 83 then g32p_supplierForest_node_130987 else g32p_supplierForest_node_131017)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_131025 else g32p_supplierForest_node_131064) else (if i.val < 87 then g32p_supplierForest_node_131110 else g32p_supplierForest_node_131115))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_131140 else g32p_supplierForest_node_131226) else (if i.val < 91 then g32p_supplierForest_node_131272 else g32p_supplierForest_node_131278)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_131297 else g32p_supplierForest_node_131333) else (if i.val < 95 then g32p_supplierForest_node_131439 else g32p_supplierForest_node_131480))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_131484 else g32p_supplierForest_node_131666) else (if i.val < 99 then g32p_supplierForest_node_131669 else g32p_supplierForest_node_131676)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_131684 else g32p_supplierForest_node_131689) else (if i.val < 103 then g32p_supplierForest_node_131766 else g32p_supplierForest_node_131785))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_131802 else g32p_supplierForest_node_131861) else (if i.val < 107 then g32p_supplierForest_node_131866 else g32p_supplierForest_node_131869)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_131877 else g32p_supplierForest_node_131883) else (if i.val < 111 then g32p_supplierForest_node_131885 else g32p_supplierForest_node_131931)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_132068 else g32p_supplierForest_node_132078) else (if i.val < 115 then g32p_supplierForest_node_132097 else g32p_supplierForest_node_132202)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_132275 else g32p_supplierForest_node_132309) else (if i.val < 119 then g32p_supplierForest_node_132318 else g32p_supplierForest_node_132331))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_132335 else g32p_supplierForest_node_132372) else (if i.val < 123 then g32p_supplierForest_node_132379 else g32p_supplierForest_node_132381)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_132417 else g32p_supplierForest_node_132430) else (if i.val < 127 then g32p_supplierForest_node_132447 else g32p_supplierForest_node_132462))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_132485 else g32p_supplierForest_node_132561) else (if i.val < 131 then g32p_supplierForest_node_132678 else g32p_supplierForest_node_132709)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_132733 else g32p_supplierForest_node_132737) else (if i.val < 135 then g32p_supplierForest_node_132771 else g32p_supplierForest_node_132787))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_132877 else g32p_supplierForest_node_132953) else (if i.val < 139 then g32p_supplierForest_node_133032 else g32p_supplierForest_node_133035)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_133074 else g32p_supplierForest_node_133108) else (if i.val < 143 then g32p_supplierForest_node_133151 else g32p_supplierForest_node_133162)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_133171 else g32p_supplierForest_node_133199) else (if i.val < 147 then g32p_supplierForest_node_133222 else g32p_supplierForest_node_133225)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_133269 else g32p_supplierForest_node_133271) else (if i.val < 151 then g32p_supplierForest_node_133388 else g32p_supplierForest_node_133391))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_133530 else g32p_supplierForest_node_133535) else (if i.val < 155 then g32p_supplierForest_node_133725 else g32p_supplierForest_node_133784)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_133798 else g32p_supplierForest_node_133799) else (if i.val < 159 then g32p_supplierForest_node_133866 else g32p_supplierForest_node_133892))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_133901 else g32p_supplierForest_node_133909) else (if i.val < 163 then g32p_supplierForest_node_133929 else g32p_supplierForest_node_133933)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_133958 else g32p_supplierForest_node_133969) else (if i.val < 167 then g32p_supplierForest_node_134020 else g32p_supplierForest_node_134033))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_134202 else g32p_supplierForest_node_134206) else (if i.val < 171 then g32p_supplierForest_node_134216 else g32p_supplierForest_node_134240)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_134317 else g32p_supplierForest_node_134422) else (if i.val < 175 then g32p_supplierForest_node_134429 else g32p_supplierForest_node_134436)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_134447 else g32p_supplierForest_node_134488) else (if i.val < 179 then g32p_supplierForest_node_134512 else g32p_supplierForest_node_134596)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_134623 else g32p_supplierForest_node_134658) else (if i.val < 183 then g32p_supplierForest_node_134716 else g32p_supplierForest_node_134742))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_134753 else g32p_supplierForest_node_134755) else (if i.val < 187 then g32p_supplierForest_node_134793 else g32p_supplierForest_node_134816)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_134824 else g32p_supplierForest_node_134878) else (if i.val < 191 then g32p_supplierForest_node_134947 else g32p_supplierForest_node_134981)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_134994 else g32p_supplierForest_node_135006) else (if i.val < 195 then g32p_supplierForest_node_135037 else g32p_supplierForest_node_135058)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_135084 else g32p_supplierForest_node_135088) else (if i.val < 199 then g32p_supplierForest_node_135239 else g32p_supplierForest_node_135246))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_135250 else g32p_supplierForest_node_135253) else (if i.val < 203 then g32p_supplierForest_node_135337 else g32p_supplierForest_node_135509)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_135579 else g32p_supplierForest_node_135708) else (if i.val < 207 then g32p_supplierForest_node_135838 else g32p_supplierForest_node_135923)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_135980 else g32p_supplierForest_node_136102) else (if i.val < 211 then g32p_supplierForest_node_136113 else g32p_supplierForest_node_136167)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_136186 else g32p_supplierForest_node_136197) else (if i.val < 215 then g32p_supplierForest_node_136226 else g32p_supplierForest_node_136227))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_136248 else g32p_supplierForest_node_136314) else (if i.val < 219 then g32p_supplierForest_node_136324 else g32p_supplierForest_node_136486)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_136552 else g32p_supplierForest_node_136625) else (if i.val < 223 then g32p_supplierForest_node_136688 else g32p_supplierForest_node_136708))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_136752 else g32p_supplierForest_node_136781) else (if i.val < 227 then g32p_supplierForest_node_136786 else g32p_supplierForest_node_136807)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_136825 else g32p_supplierForest_node_136840) else (if i.val < 231 then g32p_supplierForest_node_136861 else g32p_supplierForest_node_136877))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_136898 else g32p_supplierForest_node_136901) else (if i.val < 235 then g32p_supplierForest_node_136953 else g32p_supplierForest_node_137009)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_137058 else g32p_supplierForest_node_137124) else (if i.val < 239 then g32p_supplierForest_node_137161 else g32p_supplierForest_node_137203)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_137213 else g32p_supplierForest_node_137224) else (if i.val < 243 then g32p_supplierForest_node_137242 else g32p_supplierForest_node_137278)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_137295 else g32p_supplierForest_node_137331) else (if i.val < 247 then g32p_supplierForest_node_137368 else g32p_supplierForest_node_137424))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_137459 else g32p_supplierForest_node_137560) else (if i.val < 251 then g32p_supplierForest_node_137570 else g32p_supplierForest_node_137581)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_137586 else g32p_supplierForest_node_137608) else (if i.val < 255 then g32p_supplierForest_node_137683 else g32p_supplierForest_node_137693))))))))

def g32p_supplierForest_classes_029 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 30 else 92) else (if i.val < 3 then 61 else 61)) else (if i.val < 6 then (if i.val < 5 then 61 else 60) else (if i.val < 7 then 66 else 35))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 60 else 90) else (if i.val < 11 then 89 else 68)) else (if i.val < 14 then (if i.val < 13 then 41 else 75) else (if i.val < 15 then 68 else 71)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 74 else 38) else (if i.val < 19 then 68 else 38)) else (if i.val < 22 then (if i.val < 21 then 73 else 74) else (if i.val < 23 then 68 else 68))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 41 else 73) else (if i.val < 27 then 68 else 21)) else (if i.val < 30 then (if i.val < 29 then 70 else 79) else (if i.val < 31 then 38 else 72))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 75 else 73) else (if i.val < 35 then 43 else 77)) else (if i.val < 38 then (if i.val < 37 then 77 else 20) else (if i.val < 39 then 43 else 79))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 43 else 69) else (if i.val < 43 then 73 else 74)) else (if i.val < 46 then (if i.val < 45 then 68 else 78) else (if i.val < 47 then 77 else 94)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 69 else 71) else (if i.val < 51 then 42 else 69)) else (if i.val < 54 then (if i.val < 53 then 73 else 68) else (if i.val < 55 then 7 else 43))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 69 else 79) else (if i.val < 59 then 79 else 78)) else (if i.val < 62 then (if i.val < 61 then 68 else 69) else (if i.val < 63 then 22 else 69)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 72 else 71) else (if i.val < 67 then 43 else 43)) else (if i.val < 70 then (if i.val < 69 then 69 else 71) else (if i.val < 71 then 73 else 69))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 72 else 70) else (if i.val < 75 then 41 else 40)) else (if i.val < 78 then (if i.val < 77 then 41 else 68) else (if i.val < 79 then 23 else 73)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 72 else 38) else (if i.val < 83 then 69 else 68)) else (if i.val < 86 then (if i.val < 85 then 73 else 73) else (if i.val < 87 then 38 else 71))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 74 else 72) else (if i.val < 91 then 43 else 69)) else (if i.val < 94 then (if i.val < 93 then 42 else 21) else (if i.val < 95 then 18 else 38))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 71 else 78) else (if i.val < 99 then 75 else 77)) else (if i.val < 102 then (if i.val < 101 then 43 else 77) else (if i.val < 103 then 74 else 18))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 68 else 74) else (if i.val < 107 then 71 else 95)) else (if i.val < 110 then (if i.val < 109 then 71 else 74) else (if i.val < 111 then 69 else 38)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 94 else 73) else (if i.val < 115 then 38 else 71)) else (if i.val < 118 then (if i.val < 117 then 73 else 43) else (if i.val < 119 then 73 else 42))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 71 else 18) else (if i.val < 123 then 94 else 94)) else (if i.val < 126 then (if i.val < 125 then 69 else 43) else (if i.val < 127 then 71 else 71))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 71 else 43) else (if i.val < 131 then 79 else 42)) else (if i.val < 134 then (if i.val < 133 then 73 else 72) else (if i.val < 135 then 69 else 77))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 43 else 73) else (if i.val < 139 then 95 else 73)) else (if i.val < 142 then (if i.val < 141 then 70 else 43) else (if i.val < 143 then 20 else 73)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 73 else 75) else (if i.val < 147 then 75 else 75)) else (if i.val < 150 then (if i.val < 149 then 77 else 74) else (if i.val < 151 then 94 else 77))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 41 else 78) else (if i.val < 155 then 43 else 74)) else (if i.val < 158 then (if i.val < 157 then 70 else 95) else (if i.val < 159 then 95 else 71))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 73 else 69) else (if i.val < 163 then 42 else 42)) else (if i.val < 166 then (if i.val < 165 then 73 else 73) else (if i.val < 167 then 77 else 94))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 69 else 43) else (if i.val < 171 then 43 else 69)) else (if i.val < 174 then (if i.val < 173 then 73 else 38) else (if i.val < 175 then 68 else 71)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 38 else 43) else (if i.val < 179 then 71 else 38)) else (if i.val < 182 then (if i.val < 181 then 43 else 18) else (if i.val < 183 then 73 else 71))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 71 else 95) else (if i.val < 187 then 72 else 71)) else (if i.val < 190 then (if i.val < 189 then 77 else 73) else (if i.val < 191 then 73 else 75)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 74 else 95) else (if i.val < 195 then 38 else 68)) else (if i.val < 198 then (if i.val < 197 then 73 else 69) else (if i.val < 199 then 72 else 42))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 43 else 73) else (if i.val < 203 then 71 else 70)) else (if i.val < 206 then (if i.val < 205 then 43 else 41) else (if i.val < 207 then 69 else 42)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 74 else 20) else (if i.val < 211 then 71 else 43)) else (if i.val < 214 then (if i.val < 213 then 68 else 71) else (if i.val < 215 then 72 else 73))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 70 else 72) else (if i.val < 219 then 42 else 39)) else (if i.val < 222 then (if i.val < 221 then 73 else 43) else (if i.val < 223 then 40 else 73))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 75 else 77) else (if i.val < 227 then 69 else 43)) else (if i.val < 230 then (if i.val < 229 then 75 else 73) else (if i.val < 231 then 79 else 73))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 43 else 69) else (if i.val < 235 then 38 else 72)) else (if i.val < 238 then (if i.val < 237 then 73 else 43) else (if i.val < 239 then 68 else 73)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 67 else 74) else (if i.val < 243 then 72 else 71)) else (if i.val < 246 then (if i.val < 245 then 42 else 71) else (if i.val < 247 then 75 else 73))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 73 else 70) else (if i.val < 251 then 94 else 73)) else (if i.val < 254 then (if i.val < 253 then 73 else 94) else (if i.val < 255 then 77 else 71))))))))

theorem g32p_supplierForest_actual_029 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_029 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_029 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_127287
  · exact g32p_supplierForest_actual_127308
  · exact g32p_supplierForest_actual_127502
  · exact g32p_supplierForest_actual_127507
  · exact g32p_supplierForest_actual_127542
  · exact g32p_supplierForest_actual_127654
  · exact g32p_supplierForest_actual_127673
  · exact g32p_supplierForest_actual_127700
  · exact g32p_supplierForest_actual_127707
  · exact g32p_supplierForest_actual_127767
  · exact g32p_supplierForest_actual_127791
  · exact g32p_supplierForest_actual_127809
  · exact g32p_supplierForest_actual_127821
  · exact g32p_supplierForest_actual_127832
  · exact g32p_supplierForest_actual_127833
  · exact g32p_supplierForest_actual_127883
  · exact g32p_supplierForest_actual_127899
  · exact g32p_supplierForest_actual_127904
  · exact g32p_supplierForest_actual_127935
  · exact g32p_supplierForest_actual_127950
  · exact g32p_supplierForest_actual_128232
  · exact g32p_supplierForest_actual_128233
  · exact g32p_supplierForest_actual_128238
  · exact g32p_supplierForest_actual_128258
  · exact g32p_supplierForest_actual_128290
  · exact g32p_supplierForest_actual_128310
  · exact g32p_supplierForest_actual_128313
  · exact g32p_supplierForest_actual_128314
  · exact g32p_supplierForest_actual_128367
  · exact g32p_supplierForest_actual_128406
  · exact g32p_supplierForest_actual_128471
  · exact g32p_supplierForest_actual_128545
  · exact g32p_supplierForest_actual_128575
  · exact g32p_supplierForest_actual_128592
  · exact g32p_supplierForest_actual_128624
  · exact g32p_supplierForest_actual_128694
  · exact g32p_supplierForest_actual_128730
  · exact g32p_supplierForest_actual_128778
  · exact g32p_supplierForest_actual_128810
  · exact g32p_supplierForest_actual_128875
  · exact g32p_supplierForest_actual_128889
  · exact g32p_supplierForest_actual_128891
  · exact g32p_supplierForest_actual_129137
  · exact g32p_supplierForest_actual_129247
  · exact g32p_supplierForest_actual_129309
  · exact g32p_supplierForest_actual_129396
  · exact g32p_supplierForest_actual_129413
  · exact g32p_supplierForest_actual_129414
  · exact g32p_supplierForest_actual_129469
  · exact g32p_supplierForest_actual_129470
  · exact g32p_supplierForest_actual_129471
  · exact g32p_supplierForest_actual_129528
  · exact g32p_supplierForest_actual_129530
  · exact g32p_supplierForest_actual_129602
  · exact g32p_supplierForest_actual_129655
  · exact g32p_supplierForest_actual_129656
  · exact g32p_supplierForest_actual_129691
  · exact g32p_supplierForest_actual_129749
  · exact g32p_supplierForest_actual_129758
  · exact g32p_supplierForest_actual_129835
  · exact g32p_supplierForest_actual_129868
  · exact g32p_supplierForest_actual_129934
  · exact g32p_supplierForest_actual_129981
  · exact g32p_supplierForest_actual_129986
  · exact g32p_supplierForest_actual_129996
  · exact g32p_supplierForest_actual_130094
  · exact g32p_supplierForest_actual_130144
  · exact g32p_supplierForest_actual_130215
  · exact g32p_supplierForest_actual_130254
  · exact g32p_supplierForest_actual_130258
  · exact g32p_supplierForest_actual_130265
  · exact g32p_supplierForest_actual_130335
  · exact g32p_supplierForest_actual_130371
  · exact g32p_supplierForest_actual_130386
  · exact g32p_supplierForest_actual_130392
  · exact g32p_supplierForest_actual_130409
  · exact g32p_supplierForest_actual_130412
  · exact g32p_supplierForest_actual_130419
  · exact g32p_supplierForest_actual_130603
  · exact g32p_supplierForest_actual_130795
  · exact g32p_supplierForest_actual_130866
  · exact g32p_supplierForest_actual_130958
  · exact g32p_supplierForest_actual_130987
  · exact g32p_supplierForest_actual_131017
  · exact g32p_supplierForest_actual_131025
  · exact g32p_supplierForest_actual_131064
  · exact g32p_supplierForest_actual_131110
  · exact g32p_supplierForest_actual_131115
  · exact g32p_supplierForest_actual_131140
  · exact g32p_supplierForest_actual_131226
  · exact g32p_supplierForest_actual_131272
  · exact g32p_supplierForest_actual_131278
  · exact g32p_supplierForest_actual_131297
  · exact g32p_supplierForest_actual_131333
  · exact g32p_supplierForest_actual_131439
  · exact g32p_supplierForest_actual_131480
  · exact g32p_supplierForest_actual_131484
  · exact g32p_supplierForest_actual_131666
  · exact g32p_supplierForest_actual_131669
  · exact g32p_supplierForest_actual_131676
  · exact g32p_supplierForest_actual_131684
  · exact g32p_supplierForest_actual_131689
  · exact g32p_supplierForest_actual_131766
  · exact g32p_supplierForest_actual_131785
  · exact g32p_supplierForest_actual_131802
  · exact g32p_supplierForest_actual_131861
  · exact g32p_supplierForest_actual_131866
  · exact g32p_supplierForest_actual_131869
  · exact g32p_supplierForest_actual_131877
  · exact g32p_supplierForest_actual_131883
  · exact g32p_supplierForest_actual_131885
  · exact g32p_supplierForest_actual_131931
  · exact g32p_supplierForest_actual_132068
  · exact g32p_supplierForest_actual_132078
  · exact g32p_supplierForest_actual_132097
  · exact g32p_supplierForest_actual_132202
  · exact g32p_supplierForest_actual_132275
  · exact g32p_supplierForest_actual_132309
  · exact g32p_supplierForest_actual_132318
  · exact g32p_supplierForest_actual_132331
  · exact g32p_supplierForest_actual_132335
  · exact g32p_supplierForest_actual_132372
  · exact g32p_supplierForest_actual_132379
  · exact g32p_supplierForest_actual_132381
  · exact g32p_supplierForest_actual_132417
  · exact g32p_supplierForest_actual_132430
  · exact g32p_supplierForest_actual_132447
  · exact g32p_supplierForest_actual_132462
  · exact g32p_supplierForest_actual_132485
  · exact g32p_supplierForest_actual_132561
  · exact g32p_supplierForest_actual_132678
  · exact g32p_supplierForest_actual_132709
  · exact g32p_supplierForest_actual_132733
  · exact g32p_supplierForest_actual_132737
  · exact g32p_supplierForest_actual_132771
  · exact g32p_supplierForest_actual_132787
  · exact g32p_supplierForest_actual_132877
  · exact g32p_supplierForest_actual_132953
  · exact g32p_supplierForest_actual_133032
  · exact g32p_supplierForest_actual_133035
  · exact g32p_supplierForest_actual_133074
  · exact g32p_supplierForest_actual_133108
  · exact g32p_supplierForest_actual_133151
  · exact g32p_supplierForest_actual_133162
  · exact g32p_supplierForest_actual_133171
  · exact g32p_supplierForest_actual_133199
  · exact g32p_supplierForest_actual_133222
  · exact g32p_supplierForest_actual_133225
  · exact g32p_supplierForest_actual_133269
  · exact g32p_supplierForest_actual_133271
  · exact g32p_supplierForest_actual_133388
  · exact g32p_supplierForest_actual_133391
  · exact g32p_supplierForest_actual_133530
  · exact g32p_supplierForest_actual_133535
  · exact g32p_supplierForest_actual_133725
  · exact g32p_supplierForest_actual_133784
  · exact g32p_supplierForest_actual_133798
  · exact g32p_supplierForest_actual_133799
  · exact g32p_supplierForest_actual_133866
  · exact g32p_supplierForest_actual_133892
  · exact g32p_supplierForest_actual_133901
  · exact g32p_supplierForest_actual_133909
  · exact g32p_supplierForest_actual_133929
  · exact g32p_supplierForest_actual_133933
  · exact g32p_supplierForest_actual_133958
  · exact g32p_supplierForest_actual_133969
  · exact g32p_supplierForest_actual_134020
  · exact g32p_supplierForest_actual_134033
  · exact g32p_supplierForest_actual_134202
  · exact g32p_supplierForest_actual_134206
  · exact g32p_supplierForest_actual_134216
  · exact g32p_supplierForest_actual_134240
  · exact g32p_supplierForest_actual_134317
  · exact g32p_supplierForest_actual_134422
  · exact g32p_supplierForest_actual_134429
  · exact g32p_supplierForest_actual_134436
  · exact g32p_supplierForest_actual_134447
  · exact g32p_supplierForest_actual_134488
  · exact g32p_supplierForest_actual_134512
  · exact g32p_supplierForest_actual_134596
  · exact g32p_supplierForest_actual_134623
  · exact g32p_supplierForest_actual_134658
  · exact g32p_supplierForest_actual_134716
  · exact g32p_supplierForest_actual_134742
  · exact g32p_supplierForest_actual_134753
  · exact g32p_supplierForest_actual_134755
  · exact g32p_supplierForest_actual_134793
  · exact g32p_supplierForest_actual_134816
  · exact g32p_supplierForest_actual_134824
  · exact g32p_supplierForest_actual_134878
  · exact g32p_supplierForest_actual_134947
  · exact g32p_supplierForest_actual_134981
  · exact g32p_supplierForest_actual_134994
  · exact g32p_supplierForest_actual_135006
  · exact g32p_supplierForest_actual_135037
  · exact g32p_supplierForest_actual_135058
  · exact g32p_supplierForest_actual_135084
  · exact g32p_supplierForest_actual_135088
  · exact g32p_supplierForest_actual_135239
  · exact g32p_supplierForest_actual_135246
  · exact g32p_supplierForest_actual_135250
  · exact g32p_supplierForest_actual_135253
  · exact g32p_supplierForest_actual_135337
  · exact g32p_supplierForest_actual_135509
  · exact g32p_supplierForest_actual_135579
  · exact g32p_supplierForest_actual_135708
  · exact g32p_supplierForest_actual_135838
  · exact g32p_supplierForest_actual_135923
  · exact g32p_supplierForest_actual_135980
  · exact g32p_supplierForest_actual_136102
  · exact g32p_supplierForest_actual_136113
  · exact g32p_supplierForest_actual_136167
  · exact g32p_supplierForest_actual_136186
  · exact g32p_supplierForest_actual_136197
  · exact g32p_supplierForest_actual_136226
  · exact g32p_supplierForest_actual_136227
  · exact g32p_supplierForest_actual_136248
  · exact g32p_supplierForest_actual_136314
  · exact g32p_supplierForest_actual_136324
  · exact g32p_supplierForest_actual_136486
  · exact g32p_supplierForest_actual_136552
  · exact g32p_supplierForest_actual_136625
  · exact g32p_supplierForest_actual_136688
  · exact g32p_supplierForest_actual_136708
  · exact g32p_supplierForest_actual_136752
  · exact g32p_supplierForest_actual_136781
  · exact g32p_supplierForest_actual_136786
  · exact g32p_supplierForest_actual_136807
  · exact g32p_supplierForest_actual_136825
  · exact g32p_supplierForest_actual_136840
  · exact g32p_supplierForest_actual_136861
  · exact g32p_supplierForest_actual_136877
  · exact g32p_supplierForest_actual_136898
  · exact g32p_supplierForest_actual_136901
  · exact g32p_supplierForest_actual_136953
  · exact g32p_supplierForest_actual_137009
  · exact g32p_supplierForest_actual_137058
  · exact g32p_supplierForest_actual_137124
  · exact g32p_supplierForest_actual_137161
  · exact g32p_supplierForest_actual_137203
  · exact g32p_supplierForest_actual_137213
  · exact g32p_supplierForest_actual_137224
  · exact g32p_supplierForest_actual_137242
  · exact g32p_supplierForest_actual_137278
  · exact g32p_supplierForest_actual_137295
  · exact g32p_supplierForest_actual_137331
  · exact g32p_supplierForest_actual_137368
  · exact g32p_supplierForest_actual_137424
  · exact g32p_supplierForest_actual_137459
  · exact g32p_supplierForest_actual_137560
  · exact g32p_supplierForest_actual_137570
  · exact g32p_supplierForest_actual_137581
  · exact g32p_supplierForest_actual_137586
  · exact g32p_supplierForest_actual_137608
  · exact g32p_supplierForest_actual_137683
  · exact g32p_supplierForest_actual_137693

def g32p_supplierForest_nodes_030 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_137712 else g32p_supplierForest_node_137732) else (if i.val < 3 then g32p_supplierForest_node_137821 else g32p_supplierForest_node_137827)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_137847 else g32p_supplierForest_node_137917) else (if i.val < 7 then g32p_supplierForest_node_138013 else g32p_supplierForest_node_138037))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_138084 else g32p_supplierForest_node_138100) else (if i.val < 11 then g32p_supplierForest_node_138149 else g32p_supplierForest_node_138157)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_138192 else g32p_supplierForest_node_138253) else (if i.val < 15 then g32p_supplierForest_node_138283 else g32p_supplierForest_node_138287)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_138297 else g32p_supplierForest_node_138308) else (if i.val < 19 then g32p_supplierForest_node_138376 else g32p_supplierForest_node_138383)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_138389 else g32p_supplierForest_node_138400) else (if i.val < 23 then g32p_supplierForest_node_138411 else g32p_supplierForest_node_138434))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_138476 else g32p_supplierForest_node_138491) else (if i.val < 27 then g32p_supplierForest_node_138535 else g32p_supplierForest_node_138584)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_138666 else g32p_supplierForest_node_138763) else (if i.val < 31 then g32p_supplierForest_node_138819 else g32p_supplierForest_node_138833))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_138838 else g32p_supplierForest_node_138869) else (if i.val < 35 then g32p_supplierForest_node_138966 else g32p_supplierForest_node_139011)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_139067 else g32p_supplierForest_node_139073) else (if i.val < 39 then g32p_supplierForest_node_139111 else g32p_supplierForest_node_139204))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_139211 else g32p_supplierForest_node_139248) else (if i.val < 43 then g32p_supplierForest_node_139272 else g32p_supplierForest_node_139284)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_139334 else g32p_supplierForest_node_139337) else (if i.val < 47 then g32p_supplierForest_node_139410 else g32p_supplierForest_node_139458)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_139493 else g32p_supplierForest_node_139532) else (if i.val < 51 then g32p_supplierForest_node_139543 else g32p_supplierForest_node_139567)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_139625 else g32p_supplierForest_node_139658) else (if i.val < 55 then g32p_supplierForest_node_139718 else g32p_supplierForest_node_139865))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_139866 else g32p_supplierForest_node_139880) else (if i.val < 59 then g32p_supplierForest_node_139901 else g32p_supplierForest_node_139988)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_140055 else g32p_supplierForest_node_140089) else (if i.val < 63 then g32p_supplierForest_node_140112 else g32p_supplierForest_node_140140)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_140173 else g32p_supplierForest_node_140196) else (if i.val < 67 then g32p_supplierForest_node_140201 else g32p_supplierForest_node_140210)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_140223 else g32p_supplierForest_node_140226) else (if i.val < 71 then g32p_supplierForest_node_140243 else g32p_supplierForest_node_140295))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_140359 else g32p_supplierForest_node_140368) else (if i.val < 75 then g32p_supplierForest_node_140390 else g32p_supplierForest_node_140408)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_140466 else g32p_supplierForest_node_140556) else (if i.val < 79 then g32p_supplierForest_node_140558 else g32p_supplierForest_node_140610)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_140799 else g32p_supplierForest_node_140869) else (if i.val < 83 then g32p_supplierForest_node_140953 else g32p_supplierForest_node_140977)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_141042 else g32p_supplierForest_node_141051) else (if i.val < 87 then g32p_supplierForest_node_141092 else g32p_supplierForest_node_141105))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_141114 else g32p_supplierForest_node_141118) else (if i.val < 91 then g32p_supplierForest_node_141234 else g32p_supplierForest_node_141304)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_141311 else g32p_supplierForest_node_141403) else (if i.val < 95 then g32p_supplierForest_node_141429 else g32p_supplierForest_node_141437))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_141457 else g32p_supplierForest_node_141548) else (if i.val < 99 then g32p_supplierForest_node_141556 else g32p_supplierForest_node_141569)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_141641 else g32p_supplierForest_node_141678) else (if i.val < 103 then g32p_supplierForest_node_141729 else g32p_supplierForest_node_141771))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_141826 else g32p_supplierForest_node_141851) else (if i.val < 107 then g32p_supplierForest_node_141856 else g32p_supplierForest_node_141885)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_141915 else g32p_supplierForest_node_141919) else (if i.val < 111 then g32p_supplierForest_node_141949 else g32p_supplierForest_node_142004)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_142068 else g32p_supplierForest_node_142127) else (if i.val < 115 then g32p_supplierForest_node_142133 else g32p_supplierForest_node_142169)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_142172 else g32p_supplierForest_node_142197) else (if i.val < 119 then g32p_supplierForest_node_142343 else g32p_supplierForest_node_142368))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_142396 else g32p_supplierForest_node_142434) else (if i.val < 123 then g32p_supplierForest_node_142524 else g32p_supplierForest_node_142543)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_142554 else g32p_supplierForest_node_142670) else (if i.val < 127 then g32p_supplierForest_node_142843 else g32p_supplierForest_node_142844))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_142851 else g32p_supplierForest_node_142884) else (if i.val < 131 then g32p_supplierForest_node_142978 else g32p_supplierForest_node_142998)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_143034 else g32p_supplierForest_node_143081) else (if i.val < 135 then g32p_supplierForest_node_143145 else g32p_supplierForest_node_143207))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_143255 else g32p_supplierForest_node_143265) else (if i.val < 139 then g32p_supplierForest_node_143316 else g32p_supplierForest_node_143358)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_143375 else g32p_supplierForest_node_143425) else (if i.val < 143 then g32p_supplierForest_node_143510 else g32p_supplierForest_node_143535)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_143543 else g32p_supplierForest_node_143600) else (if i.val < 147 then g32p_supplierForest_node_143619 else g32p_supplierForest_node_143723)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_143773 else g32p_supplierForest_node_143810) else (if i.val < 151 then g32p_supplierForest_node_143819 else g32p_supplierForest_node_143823))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_143850 else g32p_supplierForest_node_143885) else (if i.val < 155 then g32p_supplierForest_node_143896 else g32p_supplierForest_node_143922)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_143923 else g32p_supplierForest_node_143934) else (if i.val < 159 then g32p_supplierForest_node_143939 else g32p_supplierForest_node_143945))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_143962 else g32p_supplierForest_node_143967) else (if i.val < 163 then g32p_supplierForest_node_144021 else g32p_supplierForest_node_144041)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_144103 else g32p_supplierForest_node_144105) else (if i.val < 167 then g32p_supplierForest_node_144114 else g32p_supplierForest_node_144141))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_144144 else g32p_supplierForest_node_144172) else (if i.val < 171 then g32p_supplierForest_node_144180 else g32p_supplierForest_node_144232)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_144236 else g32p_supplierForest_node_144259) else (if i.val < 175 then g32p_supplierForest_node_144278 else g32p_supplierForest_node_144283)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_144285 else g32p_supplierForest_node_144323) else (if i.val < 179 then g32p_supplierForest_node_144382 else g32p_supplierForest_node_144383)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_144396 else g32p_supplierForest_node_144418) else (if i.val < 183 then g32p_supplierForest_node_144461 else g32p_supplierForest_node_144471))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_144472 else g32p_supplierForest_node_144502) else (if i.val < 187 then g32p_supplierForest_node_144525 else g32p_supplierForest_node_144569)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_144594 else g32p_supplierForest_node_144771) else (if i.val < 191 then g32p_supplierForest_node_144785 else g32p_supplierForest_node_144853)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_144951 else g32p_supplierForest_node_144953) else (if i.val < 195 then g32p_supplierForest_node_145133 else g32p_supplierForest_node_145151)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_145270 else g32p_supplierForest_node_145332) else (if i.val < 199 then g32p_supplierForest_node_145338 else g32p_supplierForest_node_145357))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_145360 else g32p_supplierForest_node_145375) else (if i.val < 203 then g32p_supplierForest_node_145412 else g32p_supplierForest_node_145442)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_145508 else g32p_supplierForest_node_145634) else (if i.val < 207 then g32p_supplierForest_node_145656 else g32p_supplierForest_node_145662)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_145690 else g32p_supplierForest_node_145701) else (if i.val < 211 then g32p_supplierForest_node_145722 else g32p_supplierForest_node_145737)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_145800 else g32p_supplierForest_node_145858) else (if i.val < 215 then g32p_supplierForest_node_145881 else g32p_supplierForest_node_145910))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_146005 else g32p_supplierForest_node_146054) else (if i.val < 219 then g32p_supplierForest_node_146071 else g32p_supplierForest_node_146075)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_146172 else g32p_supplierForest_node_146174) else (if i.val < 223 then g32p_supplierForest_node_146209 else g32p_supplierForest_node_146251))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_146281 else g32p_supplierForest_node_146340) else (if i.val < 227 then g32p_supplierForest_node_146409 else g32p_supplierForest_node_146463)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_146471 else g32p_supplierForest_node_146532) else (if i.val < 231 then g32p_supplierForest_node_146543 else g32p_supplierForest_node_146581))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_146612 else g32p_supplierForest_node_146645) else (if i.val < 235 then g32p_supplierForest_node_146649 else g32p_supplierForest_node_146681)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_146916 else g32p_supplierForest_node_146917) else (if i.val < 239 then g32p_supplierForest_node_146936 else g32p_supplierForest_node_146950)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_147013 else g32p_supplierForest_node_147025) else (if i.val < 243 then g32p_supplierForest_node_147122 else g32p_supplierForest_node_147127)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_147140 else g32p_supplierForest_node_147176) else (if i.val < 247 then g32p_supplierForest_node_147213 else g32p_supplierForest_node_147337))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_147358 else g32p_supplierForest_node_147392) else (if i.val < 251 then g32p_supplierForest_node_147406 else g32p_supplierForest_node_147465)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_147517 else g32p_supplierForest_node_147519) else (if i.val < 255 then g32p_supplierForest_node_147638 else g32p_supplierForest_node_147683))))))))

def g32p_supplierForest_classes_030 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 78 else 21) else (if i.val < 3 then 71 else 71)) else (if i.val < 6 then (if i.val < 5 then 74 else 78) else (if i.val < 7 then 42 else 21))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 73 else 73) else (if i.val < 11 then 22 else 72)) else (if i.val < 14 then (if i.val < 13 then 73 else 94) else (if i.val < 15 then 68 else 94)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 79 else 78) else (if i.val < 19 then 74 else 69)) else (if i.val < 22 then (if i.val < 21 then 71 else 72) else (if i.val < 23 then 73 else 79))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 71 else 38) else (if i.val < 27 then 67 else 73)) else (if i.val < 30 then (if i.val < 29 then 73 else 73) else (if i.val < 31 then 38 else 72))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 42 else 71) else (if i.val < 35 then 94 else 72)) else (if i.val < 38 then (if i.val < 37 then 94 else 79) else (if i.val < 39 then 79 else 77))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 95 else 70) else (if i.val < 43 then 71 else 22)) else (if i.val < 46 then (if i.val < 45 then 74 else 38) else (if i.val < 47 then 38 else 42)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 94 else 94) else (if i.val < 51 then 76 else 38)) else (if i.val < 54 then (if i.val < 53 then 72 else 73) else (if i.val < 55 then 75 else 73))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 73 else 42) else (if i.val < 59 then 73 else 94)) else (if i.val < 62 then (if i.val < 61 then 74 else 71) else (if i.val < 63 then 42 else 78)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 69 else 73) else (if i.val < 67 then 78 else 73)) else (if i.val < 70 then (if i.val < 69 then 74 else 74) else (if i.val < 71 then 71 else 72))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 73 else 79) else (if i.val < 75 then 73 else 94)) else (if i.val < 78 then (if i.val < 77 then 74 else 77) else (if i.val < 79 then 42 else 20)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 94 else 78) else (if i.val < 83 then 73 else 72)) else (if i.val < 86 then (if i.val < 85 then 42 else 79) else (if i.val < 87 then 74 else 94))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 71 else 21) else (if i.val < 91 then 78 else 94)) else (if i.val < 94 then (if i.val < 93 then 95 else 71) else (if i.val < 95 then 78 else 79))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 73 else 79) else (if i.val < 99 then 78 else 94)) else (if i.val < 102 then (if i.val < 101 then 73 else 18) else (if i.val < 103 then 75 else 78))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 18 else 78) else (if i.val < 107 then 69 else 69)) else (if i.val < 110 then (if i.val < 109 then 94 else 72) else (if i.val < 111 then 78 else 71)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 43 else 42) else (if i.val < 115 then 94 else 72)) else (if i.val < 118 then (if i.val < 117 then 70 else 78) else (if i.val < 119 then 73 else 72))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 69 else 94) else (if i.val < 123 then 69 else 94)) else (if i.val < 126 then (if i.val < 125 then 78 else 75) else (if i.val < 127 then 71 else 71))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 71 else 72) else (if i.val < 131 then 77 else 75)) else (if i.val < 134 then (if i.val < 133 then 41 else 73) else (if i.val < 135 then 72 else 78))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 78 else 69) else (if i.val < 139 then 38 else 38)) else (if i.val < 142 then (if i.val < 141 then 78 else 94) else (if i.val < 143 then 78 else 72)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 41 else 38) else (if i.val < 147 then 73 else 42)) else (if i.val < 150 then (if i.val < 149 then 94 else 73) else (if i.val < 151 then 78 else 75))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 74 else 73) else (if i.val < 155 then 78 else 78)) else (if i.val < 158 then (if i.val < 157 then 94 else 78) else (if i.val < 159 then 42 else 72))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 73 else 75) else (if i.val < 163 then 78 else 73)) else (if i.val < 166 then (if i.val < 165 then 79 else 78) else (if i.val < 167 then 78 else 73))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 78 else 74) else (if i.val < 171 then 94 else 94)) else (if i.val < 174 then (if i.val < 173 then 78 else 71) else (if i.val < 175 then 78 else 71)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 77 else 73) else (if i.val < 179 then 77 else 78)) else (if i.val < 182 then (if i.val < 181 then 43 else 94) else (if i.val < 183 then 78 else 94))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 78 else 78) else (if i.val < 187 then 70 else 94)) else (if i.val < 190 then (if i.val < 189 then 94 else 52) else (if i.val < 191 then 47 else 55)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 82 else 45) else (if i.val < 195 then 86 else 45)) else (if i.val < 198 then (if i.val < 197 then 86 else 86) else (if i.val < 199 then 86 else 55))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 84 else 55) else (if i.val < 203 then 81 else 86)) else (if i.val < 206 then (if i.val < 205 then 81 else 81) else (if i.val < 207 then 53 else 86)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 55 else 55) else (if i.val < 211 then 86 else 86)) else (if i.val < 214 then (if i.val < 213 then 55 else 85) else (if i.val < 215 then 81 else 55))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 45 else 52) else (if i.val < 219 then 52 else 46)) else (if i.val < 222 then (if i.val < 221 then 86 else 54) else (if i.val < 223 then 80 else 80))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 86 else 84) else (if i.val < 227 then 83 else 81)) else (if i.val < 230 then (if i.val < 229 then 52 else 11) else (if i.val < 231 then 11 else 55))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 86 else 86) else (if i.val < 235 then 86 else 46)) else (if i.val < 238 then (if i.val < 237 then 84 else 86) else (if i.val < 239 then 55 else 86)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 85 else 45) else (if i.val < 243 then 53 else 54)) else (if i.val < 246 then (if i.val < 245 then 55 else 55) else (if i.val < 247 then 55 else 83))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 84 else 13) else (if i.val < 251 then 86 else 81)) else (if i.val < 254 then (if i.val < 253 then 55 else 85) else (if i.val < 255 then 85 else 54))))))))

theorem g32p_supplierForest_actual_030 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_030 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_030 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_137712
  · exact g32p_supplierForest_actual_137732
  · exact g32p_supplierForest_actual_137821
  · exact g32p_supplierForest_actual_137827
  · exact g32p_supplierForest_actual_137847
  · exact g32p_supplierForest_actual_137917
  · exact g32p_supplierForest_actual_138013
  · exact g32p_supplierForest_actual_138037
  · exact g32p_supplierForest_actual_138084
  · exact g32p_supplierForest_actual_138100
  · exact g32p_supplierForest_actual_138149
  · exact g32p_supplierForest_actual_138157
  · exact g32p_supplierForest_actual_138192
  · exact g32p_supplierForest_actual_138253
  · exact g32p_supplierForest_actual_138283
  · exact g32p_supplierForest_actual_138287
  · exact g32p_supplierForest_actual_138297
  · exact g32p_supplierForest_actual_138308
  · exact g32p_supplierForest_actual_138376
  · exact g32p_supplierForest_actual_138383
  · exact g32p_supplierForest_actual_138389
  · exact g32p_supplierForest_actual_138400
  · exact g32p_supplierForest_actual_138411
  · exact g32p_supplierForest_actual_138434
  · exact g32p_supplierForest_actual_138476
  · exact g32p_supplierForest_actual_138491
  · exact g32p_supplierForest_actual_138535
  · exact g32p_supplierForest_actual_138584
  · exact g32p_supplierForest_actual_138666
  · exact g32p_supplierForest_actual_138763
  · exact g32p_supplierForest_actual_138819
  · exact g32p_supplierForest_actual_138833
  · exact g32p_supplierForest_actual_138838
  · exact g32p_supplierForest_actual_138869
  · exact g32p_supplierForest_actual_138966
  · exact g32p_supplierForest_actual_139011
  · exact g32p_supplierForest_actual_139067
  · exact g32p_supplierForest_actual_139073
  · exact g32p_supplierForest_actual_139111
  · exact g32p_supplierForest_actual_139204
  · exact g32p_supplierForest_actual_139211
  · exact g32p_supplierForest_actual_139248
  · exact g32p_supplierForest_actual_139272
  · exact g32p_supplierForest_actual_139284
  · exact g32p_supplierForest_actual_139334
  · exact g32p_supplierForest_actual_139337
  · exact g32p_supplierForest_actual_139410
  · exact g32p_supplierForest_actual_139458
  · exact g32p_supplierForest_actual_139493
  · exact g32p_supplierForest_actual_139532
  · exact g32p_supplierForest_actual_139543
  · exact g32p_supplierForest_actual_139567
  · exact g32p_supplierForest_actual_139625
  · exact g32p_supplierForest_actual_139658
  · exact g32p_supplierForest_actual_139718
  · exact g32p_supplierForest_actual_139865
  · exact g32p_supplierForest_actual_139866
  · exact g32p_supplierForest_actual_139880
  · exact g32p_supplierForest_actual_139901
  · exact g32p_supplierForest_actual_139988
  · exact g32p_supplierForest_actual_140055
  · exact g32p_supplierForest_actual_140089
  · exact g32p_supplierForest_actual_140112
  · exact g32p_supplierForest_actual_140140
  · exact g32p_supplierForest_actual_140173
  · exact g32p_supplierForest_actual_140196
  · exact g32p_supplierForest_actual_140201
  · exact g32p_supplierForest_actual_140210
  · exact g32p_supplierForest_actual_140223
  · exact g32p_supplierForest_actual_140226
  · exact g32p_supplierForest_actual_140243
  · exact g32p_supplierForest_actual_140295
  · exact g32p_supplierForest_actual_140359
  · exact g32p_supplierForest_actual_140368
  · exact g32p_supplierForest_actual_140390
  · exact g32p_supplierForest_actual_140408
  · exact g32p_supplierForest_actual_140466
  · exact g32p_supplierForest_actual_140556
  · exact g32p_supplierForest_actual_140558
  · exact g32p_supplierForest_actual_140610
  · exact g32p_supplierForest_actual_140799
  · exact g32p_supplierForest_actual_140869
  · exact g32p_supplierForest_actual_140953
  · exact g32p_supplierForest_actual_140977
  · exact g32p_supplierForest_actual_141042
  · exact g32p_supplierForest_actual_141051
  · exact g32p_supplierForest_actual_141092
  · exact g32p_supplierForest_actual_141105
  · exact g32p_supplierForest_actual_141114
  · exact g32p_supplierForest_actual_141118
  · exact g32p_supplierForest_actual_141234
  · exact g32p_supplierForest_actual_141304
  · exact g32p_supplierForest_actual_141311
  · exact g32p_supplierForest_actual_141403
  · exact g32p_supplierForest_actual_141429
  · exact g32p_supplierForest_actual_141437
  · exact g32p_supplierForest_actual_141457
  · exact g32p_supplierForest_actual_141548
  · exact g32p_supplierForest_actual_141556
  · exact g32p_supplierForest_actual_141569
  · exact g32p_supplierForest_actual_141641
  · exact g32p_supplierForest_actual_141678
  · exact g32p_supplierForest_actual_141729
  · exact g32p_supplierForest_actual_141771
  · exact g32p_supplierForest_actual_141826
  · exact g32p_supplierForest_actual_141851
  · exact g32p_supplierForest_actual_141856
  · exact g32p_supplierForest_actual_141885
  · exact g32p_supplierForest_actual_141915
  · exact g32p_supplierForest_actual_141919
  · exact g32p_supplierForest_actual_141949
  · exact g32p_supplierForest_actual_142004
  · exact g32p_supplierForest_actual_142068
  · exact g32p_supplierForest_actual_142127
  · exact g32p_supplierForest_actual_142133
  · exact g32p_supplierForest_actual_142169
  · exact g32p_supplierForest_actual_142172
  · exact g32p_supplierForest_actual_142197
  · exact g32p_supplierForest_actual_142343
  · exact g32p_supplierForest_actual_142368
  · exact g32p_supplierForest_actual_142396
  · exact g32p_supplierForest_actual_142434
  · exact g32p_supplierForest_actual_142524
  · exact g32p_supplierForest_actual_142543
  · exact g32p_supplierForest_actual_142554
  · exact g32p_supplierForest_actual_142670
  · exact g32p_supplierForest_actual_142843
  · exact g32p_supplierForest_actual_142844
  · exact g32p_supplierForest_actual_142851
  · exact g32p_supplierForest_actual_142884
  · exact g32p_supplierForest_actual_142978
  · exact g32p_supplierForest_actual_142998
  · exact g32p_supplierForest_actual_143034
  · exact g32p_supplierForest_actual_143081
  · exact g32p_supplierForest_actual_143145
  · exact g32p_supplierForest_actual_143207
  · exact g32p_supplierForest_actual_143255
  · exact g32p_supplierForest_actual_143265
  · exact g32p_supplierForest_actual_143316
  · exact g32p_supplierForest_actual_143358
  · exact g32p_supplierForest_actual_143375
  · exact g32p_supplierForest_actual_143425
  · exact g32p_supplierForest_actual_143510
  · exact g32p_supplierForest_actual_143535
  · exact g32p_supplierForest_actual_143543
  · exact g32p_supplierForest_actual_143600
  · exact g32p_supplierForest_actual_143619
  · exact g32p_supplierForest_actual_143723
  · exact g32p_supplierForest_actual_143773
  · exact g32p_supplierForest_actual_143810
  · exact g32p_supplierForest_actual_143819
  · exact g32p_supplierForest_actual_143823
  · exact g32p_supplierForest_actual_143850
  · exact g32p_supplierForest_actual_143885
  · exact g32p_supplierForest_actual_143896
  · exact g32p_supplierForest_actual_143922
  · exact g32p_supplierForest_actual_143923
  · exact g32p_supplierForest_actual_143934
  · exact g32p_supplierForest_actual_143939
  · exact g32p_supplierForest_actual_143945
  · exact g32p_supplierForest_actual_143962
  · exact g32p_supplierForest_actual_143967
  · exact g32p_supplierForest_actual_144021
  · exact g32p_supplierForest_actual_144041
  · exact g32p_supplierForest_actual_144103
  · exact g32p_supplierForest_actual_144105
  · exact g32p_supplierForest_actual_144114
  · exact g32p_supplierForest_actual_144141
  · exact g32p_supplierForest_actual_144144
  · exact g32p_supplierForest_actual_144172
  · exact g32p_supplierForest_actual_144180
  · exact g32p_supplierForest_actual_144232
  · exact g32p_supplierForest_actual_144236
  · exact g32p_supplierForest_actual_144259
  · exact g32p_supplierForest_actual_144278
  · exact g32p_supplierForest_actual_144283
  · exact g32p_supplierForest_actual_144285
  · exact g32p_supplierForest_actual_144323
  · exact g32p_supplierForest_actual_144382
  · exact g32p_supplierForest_actual_144383
  · exact g32p_supplierForest_actual_144396
  · exact g32p_supplierForest_actual_144418
  · exact g32p_supplierForest_actual_144461
  · exact g32p_supplierForest_actual_144471
  · exact g32p_supplierForest_actual_144472
  · exact g32p_supplierForest_actual_144502
  · exact g32p_supplierForest_actual_144525
  · exact g32p_supplierForest_actual_144569
  · exact g32p_supplierForest_actual_144594
  · exact g32p_supplierForest_actual_144771
  · exact g32p_supplierForest_actual_144785
  · exact g32p_supplierForest_actual_144853
  · exact g32p_supplierForest_actual_144951
  · exact g32p_supplierForest_actual_144953
  · exact g32p_supplierForest_actual_145133
  · exact g32p_supplierForest_actual_145151
  · exact g32p_supplierForest_actual_145270
  · exact g32p_supplierForest_actual_145332
  · exact g32p_supplierForest_actual_145338
  · exact g32p_supplierForest_actual_145357
  · exact g32p_supplierForest_actual_145360
  · exact g32p_supplierForest_actual_145375
  · exact g32p_supplierForest_actual_145412
  · exact g32p_supplierForest_actual_145442
  · exact g32p_supplierForest_actual_145508
  · exact g32p_supplierForest_actual_145634
  · exact g32p_supplierForest_actual_145656
  · exact g32p_supplierForest_actual_145662
  · exact g32p_supplierForest_actual_145690
  · exact g32p_supplierForest_actual_145701
  · exact g32p_supplierForest_actual_145722
  · exact g32p_supplierForest_actual_145737
  · exact g32p_supplierForest_actual_145800
  · exact g32p_supplierForest_actual_145858
  · exact g32p_supplierForest_actual_145881
  · exact g32p_supplierForest_actual_145910
  · exact g32p_supplierForest_actual_146005
  · exact g32p_supplierForest_actual_146054
  · exact g32p_supplierForest_actual_146071
  · exact g32p_supplierForest_actual_146075
  · exact g32p_supplierForest_actual_146172
  · exact g32p_supplierForest_actual_146174
  · exact g32p_supplierForest_actual_146209
  · exact g32p_supplierForest_actual_146251
  · exact g32p_supplierForest_actual_146281
  · exact g32p_supplierForest_actual_146340
  · exact g32p_supplierForest_actual_146409
  · exact g32p_supplierForest_actual_146463
  · exact g32p_supplierForest_actual_146471
  · exact g32p_supplierForest_actual_146532
  · exact g32p_supplierForest_actual_146543
  · exact g32p_supplierForest_actual_146581
  · exact g32p_supplierForest_actual_146612
  · exact g32p_supplierForest_actual_146645
  · exact g32p_supplierForest_actual_146649
  · exact g32p_supplierForest_actual_146681
  · exact g32p_supplierForest_actual_146916
  · exact g32p_supplierForest_actual_146917
  · exact g32p_supplierForest_actual_146936
  · exact g32p_supplierForest_actual_146950
  · exact g32p_supplierForest_actual_147013
  · exact g32p_supplierForest_actual_147025
  · exact g32p_supplierForest_actual_147122
  · exact g32p_supplierForest_actual_147127
  · exact g32p_supplierForest_actual_147140
  · exact g32p_supplierForest_actual_147176
  · exact g32p_supplierForest_actual_147213
  · exact g32p_supplierForest_actual_147337
  · exact g32p_supplierForest_actual_147358
  · exact g32p_supplierForest_actual_147392
  · exact g32p_supplierForest_actual_147406
  · exact g32p_supplierForest_actual_147465
  · exact g32p_supplierForest_actual_147517
  · exact g32p_supplierForest_actual_147519
  · exact g32p_supplierForest_actual_147638
  · exact g32p_supplierForest_actual_147683

def g32p_supplierForest_nodes_031 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_147775 else g32p_supplierForest_node_147782) else (if i.val < 3 then g32p_supplierForest_node_147922 else g32p_supplierForest_node_147924)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_147977 else g32p_supplierForest_node_148026) else (if i.val < 7 then g32p_supplierForest_node_148027 else g32p_supplierForest_node_148165))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_148246 else g32p_supplierForest_node_148397) else (if i.val < 11 then g32p_supplierForest_node_148408 else g32p_supplierForest_node_148473)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_148488 else g32p_supplierForest_node_148509) else (if i.val < 15 then g32p_supplierForest_node_148531 else g32p_supplierForest_node_148608)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_148619 else g32p_supplierForest_node_148631) else (if i.val < 19 then g32p_supplierForest_node_148665 else g32p_supplierForest_node_148703)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_148780 else g32p_supplierForest_node_148798) else (if i.val < 23 then g32p_supplierForest_node_148853 else g32p_supplierForest_node_148906))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_148933 else g32p_supplierForest_node_149015) else (if i.val < 27 then g32p_supplierForest_node_149017 else g32p_supplierForest_node_149049)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_149095 else g32p_supplierForest_node_149213) else (if i.val < 31 then g32p_supplierForest_node_149228 else g32p_supplierForest_node_149264))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_149388 else g32p_supplierForest_node_149406) else (if i.val < 35 then g32p_supplierForest_node_149526 else g32p_supplierForest_node_149691)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_149694 else g32p_supplierForest_node_149792) else (if i.val < 39 then g32p_supplierForest_node_149807 else g32p_supplierForest_node_149841))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_149919 else g32p_supplierForest_node_149997) else (if i.val < 43 then g32p_supplierForest_node_150003 else g32p_supplierForest_node_150017)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_150040 else g32p_supplierForest_node_150084) else (if i.val < 47 then g32p_supplierForest_node_150089 else g32p_supplierForest_node_150166)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_150169 else g32p_supplierForest_node_150197) else (if i.val < 51 then g32p_supplierForest_node_150312 else g32p_supplierForest_node_150362)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_150395 else g32p_supplierForest_node_150420) else (if i.val < 55 then g32p_supplierForest_node_150421 else g32p_supplierForest_node_150422))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_150667 else g32p_supplierForest_node_150831) else (if i.val < 59 then g32p_supplierForest_node_150844 else g32p_supplierForest_node_150893)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_150918 else g32p_supplierForest_node_150959) else (if i.val < 63 then g32p_supplierForest_node_151040 else g32p_supplierForest_node_151043)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_151058 else g32p_supplierForest_node_151071) else (if i.val < 67 then g32p_supplierForest_node_151117 else g32p_supplierForest_node_151238)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_151297 else g32p_supplierForest_node_151304) else (if i.val < 71 then g32p_supplierForest_node_151379 else g32p_supplierForest_node_151445))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_151452 else g32p_supplierForest_node_151536) else (if i.val < 75 then g32p_supplierForest_node_151538 else g32p_supplierForest_node_151681)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_151812 else g32p_supplierForest_node_151882) else (if i.val < 79 then g32p_supplierForest_node_151927 else g32p_supplierForest_node_151934)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_151972 else g32p_supplierForest_node_152002) else (if i.val < 83 then g32p_supplierForest_node_152039 else g32p_supplierForest_node_152041)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_152064 else g32p_supplierForest_node_152079) else (if i.val < 87 then g32p_supplierForest_node_152091 else g32p_supplierForest_node_152143))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_152162 else g32p_supplierForest_node_152229) else (if i.val < 91 then g32p_supplierForest_node_152255 else g32p_supplierForest_node_152344)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_152374 else g32p_supplierForest_node_152394) else (if i.val < 95 then g32p_supplierForest_node_152524 else g32p_supplierForest_node_152533))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_152582 else g32p_supplierForest_node_152595) else (if i.val < 99 then g32p_supplierForest_node_152628 else g32p_supplierForest_node_152656)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_152659 else g32p_supplierForest_node_152779) else (if i.val < 103 then g32p_supplierForest_node_152793 else g32p_supplierForest_node_152796))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_152842 else g32p_supplierForest_node_152859) else (if i.val < 107 then g32p_supplierForest_node_152870 else g32p_supplierForest_node_153011)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_153113 else g32p_supplierForest_node_153117) else (if i.val < 111 then g32p_supplierForest_node_153127 else g32p_supplierForest_node_153171)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_153184 else g32p_supplierForest_node_153201) else (if i.val < 115 then g32p_supplierForest_node_153238 else g32p_supplierForest_node_153245)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_153288 else g32p_supplierForest_node_153297) else (if i.val < 119 then g32p_supplierForest_node_153298 else g32p_supplierForest_node_153326))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_153407 else g32p_supplierForest_node_153463) else (if i.val < 123 then g32p_supplierForest_node_153487 else g32p_supplierForest_node_153496)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_153542 else g32p_supplierForest_node_153578) else (if i.val < 127 then g32p_supplierForest_node_153587 else g32p_supplierForest_node_153606))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_153678 else g32p_supplierForest_node_153691) else (if i.val < 131 then g32p_supplierForest_node_153717 else g32p_supplierForest_node_153737)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_153784 else g32p_supplierForest_node_153859) else (if i.val < 135 then g32p_supplierForest_node_153877 else g32p_supplierForest_node_153885))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_153887 else g32p_supplierForest_node_153901) else (if i.val < 139 then g32p_supplierForest_node_153953 else g32p_supplierForest_node_153964)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_153994 else g32p_supplierForest_node_153998) else (if i.val < 143 then g32p_supplierForest_node_154021 else g32p_supplierForest_node_154046)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_154069 else g32p_supplierForest_node_154108) else (if i.val < 147 then g32p_supplierForest_node_154115 else g32p_supplierForest_node_154202)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_154218 else g32p_supplierForest_node_154231) else (if i.val < 151 then g32p_supplierForest_node_154245 else g32p_supplierForest_node_154263))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_154296 else g32p_supplierForest_node_154319) else (if i.val < 155 then g32p_supplierForest_node_154395 else g32p_supplierForest_node_154461)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_154474 else g32p_supplierForest_node_154513) else (if i.val < 159 then g32p_supplierForest_node_154514 else g32p_supplierForest_node_154567))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_154574 else g32p_supplierForest_node_154626) else (if i.val < 163 then g32p_supplierForest_node_154643 else g32p_supplierForest_node_154664)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_154705 else g32p_supplierForest_node_154706) else (if i.val < 167 then g32p_supplierForest_node_154724 else g32p_supplierForest_node_154757))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_154798 else g32p_supplierForest_node_154803) else (if i.val < 171 then g32p_supplierForest_node_154856 else g32p_supplierForest_node_154874)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_154885 else g32p_supplierForest_node_154914) else (if i.val < 175 then g32p_supplierForest_node_154954 else g32p_supplierForest_node_155063)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_155071 else g32p_supplierForest_node_155091) else (if i.val < 179 then g32p_supplierForest_node_155110 else g32p_supplierForest_node_155124)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_155147 else g32p_supplierForest_node_155154) else (if i.val < 183 then g32p_supplierForest_node_155158 else g32p_supplierForest_node_155184))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_155189 else g32p_supplierForest_node_155192) else (if i.val < 187 then g32p_supplierForest_node_155214 else g32p_supplierForest_node_155227)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_155243 else g32p_supplierForest_node_155247) else (if i.val < 191 then g32p_supplierForest_node_155254 else g32p_supplierForest_node_155285)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_155311 else g32p_supplierForest_node_155315) else (if i.val < 195 then g32p_supplierForest_node_155326 else g32p_supplierForest_node_155407)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_155428 else g32p_supplierForest_node_155435) else (if i.val < 199 then g32p_supplierForest_node_155463 else g32p_supplierForest_node_155468))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_155477 else g32p_supplierForest_node_155481) else (if i.val < 203 then g32p_supplierForest_node_155487 else g32p_supplierForest_node_155499)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_155501 else g32p_supplierForest_node_155508) else (if i.val < 207 then g32p_supplierForest_node_155514 else g32p_supplierForest_node_000029)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_000038 else g32p_supplierForest_node_000227) else (if i.val < 211 then g32p_supplierForest_node_000329 else g32p_supplierForest_node_000469)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_000476 else g32p_supplierForest_node_000479) else (if i.val < 215 then g32p_supplierForest_node_000487 else g32p_supplierForest_node_000492))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_000552 else g32p_supplierForest_node_000553) else (if i.val < 219 then g32p_supplierForest_node_000567 else g32p_supplierForest_node_000595)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_000601 else g32p_supplierForest_node_000639) else (if i.val < 223 then g32p_supplierForest_node_000702 else g32p_supplierForest_node_000706))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_000713 else g32p_supplierForest_node_000719) else (if i.val < 227 then g32p_supplierForest_node_000722 else g32p_supplierForest_node_000761)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_000765 else g32p_supplierForest_node_000784) else (if i.val < 231 then g32p_supplierForest_node_000785 else g32p_supplierForest_node_000815))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_000828 else g32p_supplierForest_node_000853) else (if i.val < 235 then g32p_supplierForest_node_000974 else g32p_supplierForest_node_001029)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_001091 else g32p_supplierForest_node_001092) else (if i.val < 239 then g32p_supplierForest_node_001165 else g32p_supplierForest_node_001197)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_001208 else g32p_supplierForest_node_001220) else (if i.val < 243 then g32p_supplierForest_node_001271 else g32p_supplierForest_node_001295)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_001302 else g32p_supplierForest_node_001308) else (if i.val < 247 then g32p_supplierForest_node_001322 else g32p_supplierForest_node_001332))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_001342 else g32p_supplierForest_node_001384) else (if i.val < 251 then g32p_supplierForest_node_001425 else g32p_supplierForest_node_001444)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_001447 else g32p_supplierForest_node_001463) else (if i.val < 255 then g32p_supplierForest_node_001502 else g32p_supplierForest_node_001508))))))))

def g32p_supplierForest_classes_031 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 86 else 80) else (if i.val < 3 then 55 else 86)) else (if i.val < 6 then (if i.val < 5 then 81 else 86) else (if i.val < 7 then 80 else 85))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 86 else 86) else (if i.val < 11 then 82 else 83)) else (if i.val < 14 then (if i.val < 13 then 54 else 85) else (if i.val < 15 then 54 else 55)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 52 else 86) else (if i.val < 19 then 55 else 86)) else (if i.val < 22 then (if i.val < 21 then 84 else 55) else (if i.val < 23 then 46 else 55))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 85 else 81) else (if i.val < 27 then 81 else 45)) else (if i.val < 30 then (if i.val < 29 then 45 else 81) else (if i.val < 31 then 52 else 86))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 25 else 55) else (if i.val < 35 then 49 else 86)) else (if i.val < 38 then (if i.val < 37 then 81 else 83) else (if i.val < 39 then 86 else 85))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 55 else 80) else (if i.val < 43 then 47 else 84)) else (if i.val < 46 then (if i.val < 45 then 80 else 45) else (if i.val < 47 then 86 else 86)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 86 else 86) else (if i.val < 51 then 11 else 86)) else (if i.val < 54 then (if i.val < 53 then 86 else 86) else (if i.val < 55 then 11 else 86))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 86 else 80) else (if i.val < 59 then 86 else 86)) else (if i.val < 62 then (if i.val < 61 then 85 else 86) else (if i.val < 63 then 86 else 80)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 84 else 85) else (if i.val < 67 then 86 else 54)) else (if i.val < 70 then (if i.val < 69 then 26 else 84) else (if i.val < 71 then 98 else 98))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 86 else 86) else (if i.val < 75 then 86 else 86)) else (if i.val < 78 then (if i.val < 77 then 86 else 45) else (if i.val < 79 then 86 else 86)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 98 else 86) else (if i.val < 83 then 80 else 86)) else (if i.val < 86 then (if i.val < 85 then 98 else 98) else (if i.val < 87 then 86 else 85))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 86 else 54) else (if i.val < 91 then 55 else 55)) else (if i.val < 94 then (if i.val < 93 then 86 else 86) else (if i.val < 95 then 65 else 92))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 90 else 89) else (if i.val < 99 then 90 else 92)) else (if i.val < 102 then (if i.val < 101 then 66 else 93) else (if i.val < 103 then 89 else 90))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 62 else 92) else (if i.val < 107 then 92 else 92)) else (if i.val < 110 then (if i.val < 109 then 66 else 66) else (if i.val < 111 then 92 else 87)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 61 else 92) else (if i.val < 115 then 92 else 93)) else (if i.val < 118 then (if i.val < 117 then 90 else 90) else (if i.val < 119 then 92 else 92))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 35 else 92) else (if i.val < 123 then 92 else 92)) else (if i.val < 126 then (if i.val < 125 then 91 else 92) else (if i.val < 127 then 92 else 66))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 60 else 35) else (if i.val < 131 then 87 else 61)) else (if i.val < 134 then (if i.val < 133 then 89 else 92) else (if i.val < 135 then 90 else 35))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 35 else 89) else (if i.val < 139 then 92 else 89)) else (if i.val < 142 then (if i.val < 141 then 89 else 90) else (if i.val < 143 then 87 else 62)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 92 else 89) else (if i.val < 147 then 90 else 30)) else (if i.val < 150 then (if i.val < 149 then 90 else 93) else (if i.val < 151 then 89 else 92))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 92 else 90) else (if i.val < 155 then 58 else 62)) else (if i.val < 158 then (if i.val < 157 then 92 else 92) else (if i.val < 159 then 92 else 90))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 92 else 66) else (if i.val < 163 then 92 else 92)) else (if i.val < 166 then (if i.val < 165 then 61 else 90) else (if i.val < 167 then 92 else 60))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 90 else 90) else (if i.val < 171 then 92 else 89)) else (if i.val < 174 then (if i.val < 173 then 93 else 90) else (if i.val < 175 then 92 else 77)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 78 else 78) else (if i.val < 179 then 94 else 78)) else (if i.val < 182 then (if i.val < 181 then 78 else 78) else (if i.val < 183 then 76 else 77))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 76 else 78) else (if i.val < 187 then 76 else 76)) else (if i.val < 190 then (if i.val < 189 then 71 else 76) else (if i.val < 191 then 76 else 78)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 94 else 78) else (if i.val < 195 then 77 else 78)) else (if i.val < 198 then (if i.val < 197 then 77 else 78) else (if i.val < 199 then 94 else 76))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 100 else 100) else (if i.val < 203 then 100 else 100)) else (if i.val < 206 then (if i.val < 205 then 100 else 100) else (if i.val < 207 then 100 else 5)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 5 else 3) else (if i.val < 211 then 3 else 19)) else (if i.val < 214 then (if i.val < 213 then 5 else 5) else (if i.val < 215 then 5 else 5))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 5 else 24) else (if i.val < 219 then 7 else 5)) else (if i.val < 222 then (if i.val < 221 then 24 else 5) else (if i.val < 223 then 19 else 6))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 24 else 19) else (if i.val < 227 then 24 else 7)) else (if i.val < 230 then (if i.val < 229 then 5 else 24) else (if i.val < 231 then 19 else 5))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 22 else 19) else (if i.val < 235 then 19 else 19)) else (if i.val < 238 then (if i.val < 237 then 10 else 9) else (if i.val < 239 then 10 else 10)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 8 else 10) else (if i.val < 243 then 25 else 10)) else (if i.val < 246 then (if i.val < 245 then 10 else 10) else (if i.val < 247 then 10 else 9))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 13 else 8) else (if i.val < 251 then 10 else 10)) else (if i.val < 254 then (if i.val < 253 then 12 else 8) else (if i.val < 255 then 8 else 10))))))))

theorem g32p_supplierForest_actual_031 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_031 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_031 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_147775
  · exact g32p_supplierForest_actual_147782
  · exact g32p_supplierForest_actual_147922
  · exact g32p_supplierForest_actual_147924
  · exact g32p_supplierForest_actual_147977
  · exact g32p_supplierForest_actual_148026
  · exact g32p_supplierForest_actual_148027
  · exact g32p_supplierForest_actual_148165
  · exact g32p_supplierForest_actual_148246
  · exact g32p_supplierForest_actual_148397
  · exact g32p_supplierForest_actual_148408
  · exact g32p_supplierForest_actual_148473
  · exact g32p_supplierForest_actual_148488
  · exact g32p_supplierForest_actual_148509
  · exact g32p_supplierForest_actual_148531
  · exact g32p_supplierForest_actual_148608
  · exact g32p_supplierForest_actual_148619
  · exact g32p_supplierForest_actual_148631
  · exact g32p_supplierForest_actual_148665
  · exact g32p_supplierForest_actual_148703
  · exact g32p_supplierForest_actual_148780
  · exact g32p_supplierForest_actual_148798
  · exact g32p_supplierForest_actual_148853
  · exact g32p_supplierForest_actual_148906
  · exact g32p_supplierForest_actual_148933
  · exact g32p_supplierForest_actual_149015
  · exact g32p_supplierForest_actual_149017
  · exact g32p_supplierForest_actual_149049
  · exact g32p_supplierForest_actual_149095
  · exact g32p_supplierForest_actual_149213
  · exact g32p_supplierForest_actual_149228
  · exact g32p_supplierForest_actual_149264
  · exact g32p_supplierForest_actual_149388
  · exact g32p_supplierForest_actual_149406
  · exact g32p_supplierForest_actual_149526
  · exact g32p_supplierForest_actual_149691
  · exact g32p_supplierForest_actual_149694
  · exact g32p_supplierForest_actual_149792
  · exact g32p_supplierForest_actual_149807
  · exact g32p_supplierForest_actual_149841
  · exact g32p_supplierForest_actual_149919
  · exact g32p_supplierForest_actual_149997
  · exact g32p_supplierForest_actual_150003
  · exact g32p_supplierForest_actual_150017
  · exact g32p_supplierForest_actual_150040
  · exact g32p_supplierForest_actual_150084
  · exact g32p_supplierForest_actual_150089
  · exact g32p_supplierForest_actual_150166
  · exact g32p_supplierForest_actual_150169
  · exact g32p_supplierForest_actual_150197
  · exact g32p_supplierForest_actual_150312
  · exact g32p_supplierForest_actual_150362
  · exact g32p_supplierForest_actual_150395
  · exact g32p_supplierForest_actual_150420
  · exact g32p_supplierForest_actual_150421
  · exact g32p_supplierForest_actual_150422
  · exact g32p_supplierForest_actual_150667
  · exact g32p_supplierForest_actual_150831
  · exact g32p_supplierForest_actual_150844
  · exact g32p_supplierForest_actual_150893
  · exact g32p_supplierForest_actual_150918
  · exact g32p_supplierForest_actual_150959
  · exact g32p_supplierForest_actual_151040
  · exact g32p_supplierForest_actual_151043
  · exact g32p_supplierForest_actual_151058
  · exact g32p_supplierForest_actual_151071
  · exact g32p_supplierForest_actual_151117
  · exact g32p_supplierForest_actual_151238
  · exact g32p_supplierForest_actual_151297
  · exact g32p_supplierForest_actual_151304
  · exact g32p_supplierForest_actual_151379
  · exact g32p_supplierForest_actual_151445
  · exact g32p_supplierForest_actual_151452
  · exact g32p_supplierForest_actual_151536
  · exact g32p_supplierForest_actual_151538
  · exact g32p_supplierForest_actual_151681
  · exact g32p_supplierForest_actual_151812
  · exact g32p_supplierForest_actual_151882
  · exact g32p_supplierForest_actual_151927
  · exact g32p_supplierForest_actual_151934
  · exact g32p_supplierForest_actual_151972
  · exact g32p_supplierForest_actual_152002
  · exact g32p_supplierForest_actual_152039
  · exact g32p_supplierForest_actual_152041
  · exact g32p_supplierForest_actual_152064
  · exact g32p_supplierForest_actual_152079
  · exact g32p_supplierForest_actual_152091
  · exact g32p_supplierForest_actual_152143
  · exact g32p_supplierForest_actual_152162
  · exact g32p_supplierForest_actual_152229
  · exact g32p_supplierForest_actual_152255
  · exact g32p_supplierForest_actual_152344
  · exact g32p_supplierForest_actual_152374
  · exact g32p_supplierForest_actual_152394
  · exact g32p_supplierForest_actual_152524
  · exact g32p_supplierForest_actual_152533
  · exact g32p_supplierForest_actual_152582
  · exact g32p_supplierForest_actual_152595
  · exact g32p_supplierForest_actual_152628
  · exact g32p_supplierForest_actual_152656
  · exact g32p_supplierForest_actual_152659
  · exact g32p_supplierForest_actual_152779
  · exact g32p_supplierForest_actual_152793
  · exact g32p_supplierForest_actual_152796
  · exact g32p_supplierForest_actual_152842
  · exact g32p_supplierForest_actual_152859
  · exact g32p_supplierForest_actual_152870
  · exact g32p_supplierForest_actual_153011
  · exact g32p_supplierForest_actual_153113
  · exact g32p_supplierForest_actual_153117
  · exact g32p_supplierForest_actual_153127
  · exact g32p_supplierForest_actual_153171
  · exact g32p_supplierForest_actual_153184
  · exact g32p_supplierForest_actual_153201
  · exact g32p_supplierForest_actual_153238
  · exact g32p_supplierForest_actual_153245
  · exact g32p_supplierForest_actual_153288
  · exact g32p_supplierForest_actual_153297
  · exact g32p_supplierForest_actual_153298
  · exact g32p_supplierForest_actual_153326
  · exact g32p_supplierForest_actual_153407
  · exact g32p_supplierForest_actual_153463
  · exact g32p_supplierForest_actual_153487
  · exact g32p_supplierForest_actual_153496
  · exact g32p_supplierForest_actual_153542
  · exact g32p_supplierForest_actual_153578
  · exact g32p_supplierForest_actual_153587
  · exact g32p_supplierForest_actual_153606
  · exact g32p_supplierForest_actual_153678
  · exact g32p_supplierForest_actual_153691
  · exact g32p_supplierForest_actual_153717
  · exact g32p_supplierForest_actual_153737
  · exact g32p_supplierForest_actual_153784
  · exact g32p_supplierForest_actual_153859
  · exact g32p_supplierForest_actual_153877
  · exact g32p_supplierForest_actual_153885
  · exact g32p_supplierForest_actual_153887
  · exact g32p_supplierForest_actual_153901
  · exact g32p_supplierForest_actual_153953
  · exact g32p_supplierForest_actual_153964
  · exact g32p_supplierForest_actual_153994
  · exact g32p_supplierForest_actual_153998
  · exact g32p_supplierForest_actual_154021
  · exact g32p_supplierForest_actual_154046
  · exact g32p_supplierForest_actual_154069
  · exact g32p_supplierForest_actual_154108
  · exact g32p_supplierForest_actual_154115
  · exact g32p_supplierForest_actual_154202
  · exact g32p_supplierForest_actual_154218
  · exact g32p_supplierForest_actual_154231
  · exact g32p_supplierForest_actual_154245
  · exact g32p_supplierForest_actual_154263
  · exact g32p_supplierForest_actual_154296
  · exact g32p_supplierForest_actual_154319
  · exact g32p_supplierForest_actual_154395
  · exact g32p_supplierForest_actual_154461
  · exact g32p_supplierForest_actual_154474
  · exact g32p_supplierForest_actual_154513
  · exact g32p_supplierForest_actual_154514
  · exact g32p_supplierForest_actual_154567
  · exact g32p_supplierForest_actual_154574
  · exact g32p_supplierForest_actual_154626
  · exact g32p_supplierForest_actual_154643
  · exact g32p_supplierForest_actual_154664
  · exact g32p_supplierForest_actual_154705
  · exact g32p_supplierForest_actual_154706
  · exact g32p_supplierForest_actual_154724
  · exact g32p_supplierForest_actual_154757
  · exact g32p_supplierForest_actual_154798
  · exact g32p_supplierForest_actual_154803
  · exact g32p_supplierForest_actual_154856
  · exact g32p_supplierForest_actual_154874
  · exact g32p_supplierForest_actual_154885
  · exact g32p_supplierForest_actual_154914
  · exact g32p_supplierForest_actual_154954
  · exact g32p_supplierForest_actual_155063
  · exact g32p_supplierForest_actual_155071
  · exact g32p_supplierForest_actual_155091
  · exact g32p_supplierForest_actual_155110
  · exact g32p_supplierForest_actual_155124
  · exact g32p_supplierForest_actual_155147
  · exact g32p_supplierForest_actual_155154
  · exact g32p_supplierForest_actual_155158
  · exact g32p_supplierForest_actual_155184
  · exact g32p_supplierForest_actual_155189
  · exact g32p_supplierForest_actual_155192
  · exact g32p_supplierForest_actual_155214
  · exact g32p_supplierForest_actual_155227
  · exact g32p_supplierForest_actual_155243
  · exact g32p_supplierForest_actual_155247
  · exact g32p_supplierForest_actual_155254
  · exact g32p_supplierForest_actual_155285
  · exact g32p_supplierForest_actual_155311
  · exact g32p_supplierForest_actual_155315
  · exact g32p_supplierForest_actual_155326
  · exact g32p_supplierForest_actual_155407
  · exact g32p_supplierForest_actual_155428
  · exact g32p_supplierForest_actual_155435
  · exact g32p_supplierForest_actual_155463
  · exact g32p_supplierForest_actual_155468
  · exact g32p_supplierForest_actual_155477
  · exact g32p_supplierForest_actual_155481
  · exact g32p_supplierForest_actual_155487
  · exact g32p_supplierForest_actual_155499
  · exact g32p_supplierForest_actual_155501
  · exact g32p_supplierForest_actual_155508
  · exact g32p_supplierForest_actual_155514
  · exact g32p_supplierForest_actual_000029
  · exact g32p_supplierForest_actual_000038
  · exact g32p_supplierForest_actual_000227
  · exact g32p_supplierForest_actual_000329
  · exact g32p_supplierForest_actual_000469
  · exact g32p_supplierForest_actual_000476
  · exact g32p_supplierForest_actual_000479
  · exact g32p_supplierForest_actual_000487
  · exact g32p_supplierForest_actual_000492
  · exact g32p_supplierForest_actual_000552
  · exact g32p_supplierForest_actual_000553
  · exact g32p_supplierForest_actual_000567
  · exact g32p_supplierForest_actual_000595
  · exact g32p_supplierForest_actual_000601
  · exact g32p_supplierForest_actual_000639
  · exact g32p_supplierForest_actual_000702
  · exact g32p_supplierForest_actual_000706
  · exact g32p_supplierForest_actual_000713
  · exact g32p_supplierForest_actual_000719
  · exact g32p_supplierForest_actual_000722
  · exact g32p_supplierForest_actual_000761
  · exact g32p_supplierForest_actual_000765
  · exact g32p_supplierForest_actual_000784
  · exact g32p_supplierForest_actual_000785
  · exact g32p_supplierForest_actual_000815
  · exact g32p_supplierForest_actual_000828
  · exact g32p_supplierForest_actual_000853
  · exact g32p_supplierForest_actual_000974
  · exact g32p_supplierForest_actual_001029
  · exact g32p_supplierForest_actual_001091
  · exact g32p_supplierForest_actual_001092
  · exact g32p_supplierForest_actual_001165
  · exact g32p_supplierForest_actual_001197
  · exact g32p_supplierForest_actual_001208
  · exact g32p_supplierForest_actual_001220
  · exact g32p_supplierForest_actual_001271
  · exact g32p_supplierForest_actual_001295
  · exact g32p_supplierForest_actual_001302
  · exact g32p_supplierForest_actual_001308
  · exact g32p_supplierForest_actual_001322
  · exact g32p_supplierForest_actual_001332
  · exact g32p_supplierForest_actual_001342
  · exact g32p_supplierForest_actual_001384
  · exact g32p_supplierForest_actual_001425
  · exact g32p_supplierForest_actual_001444
  · exact g32p_supplierForest_actual_001447
  · exact g32p_supplierForest_actual_001463
  · exact g32p_supplierForest_actual_001502
  · exact g32p_supplierForest_actual_001508

end HodgeLean.Foundations.Program

end
end
