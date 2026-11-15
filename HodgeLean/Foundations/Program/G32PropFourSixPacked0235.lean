import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0218
import HodgeLean.Foundations.Program.G32PropFourSixPacked0219
import HodgeLean.Foundations.Program.G32PropFourSixPacked0221
import HodgeLean.Foundations.Program.G32PropFourSixPacked0222
import HodgeLean.Foundations.Program.G32PropFourSixPacked0223
import HodgeLean.Foundations.Program.G32PropFourSixPacked0225
import HodgeLean.Foundations.Program.G32PropFourSixPacked0226
import HodgeLean.Foundations.Program.G32PropFourSixPacked0231
import HodgeLean.Foundations.Program.G32PropFourSixPacked0232
import HodgeLean.Foundations.Program.G32PropFourSixPacked0233
import HodgeLean.Foundations.Program.G32PropFourSixPacked0234

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_092193 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092193 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092193 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082561 := by
  decide +kernel

theorem g32p_supplierForest_actual_092193 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092193) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_092193
    g32p_supplierForest_actual_082561

def g32p_supplierForest_node_092221 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092221 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092221 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_094690 := by
  decide +kernel

theorem g32p_supplierForest_actual_092221 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092221) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_092221
    g32p_supplierForest_actual_094690

def g32p_supplierForest_node_092283 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_092283 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092283 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073452 := by
  decide +kernel

theorem g32p_supplierForest_actual_092283 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092283) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_092283
    g32p_supplierForest_actual_073452

def g32p_supplierForest_node_092336 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092336 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092336 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_080395 := by
  decide +kernel

theorem g32p_supplierForest_actual_092336 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092336) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_092336
    g32p_supplierForest_actual_080395

def g32p_supplierForest_node_092340 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092340 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092340 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019120 := by
  decide +kernel

theorem g32p_supplierForest_actual_092340 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092340) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_092340
    g32p_supplierForest_actual_019120

def g32p_supplierForest_node_092363 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092363 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092363 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_090817 := by
  decide +kernel

theorem g32p_supplierForest_actual_092363 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092363) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_092363
    g32p_supplierForest_actual_090817

def g32p_supplierForest_node_092415 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_092415 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092415 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088054 := by
  decide +kernel

theorem g32p_supplierForest_actual_092415 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092415) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_092415
    g32p_supplierForest_actual_088054

def g32p_supplierForest_node_092439 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_092439 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092439 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_024421 := by
  decide +kernel

theorem g32p_supplierForest_actual_092439 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092439) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_092439
    g32p_supplierForest_actual_024421

def g32p_supplierForest_node_092508 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_092508 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092508 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_091348 := by
  decide +kernel

theorem g32p_supplierForest_actual_092508 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092508) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_092508
    g32p_supplierForest_actual_091348

def g32p_supplierForest_node_092534 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_092534 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092534 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021873 := by
  decide +kernel

theorem g32p_supplierForest_actual_092534 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092534) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_092534
    g32p_supplierForest_actual_021873

def g32p_supplierForest_node_092541 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_092541 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092541 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_089897 := by
  decide +kernel

theorem g32p_supplierForest_actual_092541 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092541) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_092541
    g32p_supplierForest_actual_089897

def g32p_supplierForest_node_092554 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_092554 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092554 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_098617 := by
  decide +kernel

theorem g32p_supplierForest_actual_092554 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092554) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_092554
    g32p_supplierForest_actual_098617

def g32p_supplierForest_node_092557 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092557 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092557 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085065 := by
  decide +kernel

theorem g32p_supplierForest_actual_092557 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092557) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_092557
    g32p_supplierForest_actual_085065

def g32p_supplierForest_node_092577 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_092577 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092577 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075463 := by
  decide +kernel

theorem g32p_supplierForest_actual_092577 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092577) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_092577
    g32p_supplierForest_actual_075463

def g32p_supplierForest_node_092586 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_092586 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092586 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_020376 := by
  decide +kernel

theorem g32p_supplierForest_actual_092586 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092586) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_092586
    g32p_supplierForest_actual_020376

def g32p_supplierForest_node_092592 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_092592 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092592 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_092589 := by
  decide +kernel

theorem g32p_supplierForest_actual_092592 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092592) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_092592
    g32p_supplierForest_actual_092589

def g32p_supplierForest_node_092619 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_092619 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092619 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_087127 := by
  decide +kernel

theorem g32p_supplierForest_actual_092619 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092619) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_092619
    g32p_supplierForest_actual_087127

def g32p_supplierForest_node_092638 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_092638 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092638 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018013 := by
  decide +kernel

theorem g32p_supplierForest_actual_092638 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092638) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 3 g32p_supplierForest_edge_092638
    g32p_supplierForest_actual_018013

def g32p_supplierForest_node_092651 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_092651 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092651 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075855 := by
  decide +kernel

theorem g32p_supplierForest_actual_092651 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092651) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 1 g32p_supplierForest_edge_092651
    g32p_supplierForest_actual_075855

def g32p_supplierForest_node_092686 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092686 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092686 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075214 := by
  decide +kernel

theorem g32p_supplierForest_actual_092686 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092686) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_092686
    g32p_supplierForest_actual_075214

def g32p_supplierForest_node_092758 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_092758 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092758 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097197 := by
  decide +kernel

theorem g32p_supplierForest_actual_092758 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092758) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 2 g32p_supplierForest_edge_092758
    g32p_supplierForest_actual_097197

def g32p_supplierForest_node_092780 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092780 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092780 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_022490 := by
  decide +kernel

theorem g32p_supplierForest_actual_092780 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092780) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_092780
    g32p_supplierForest_actual_022490

def g32p_supplierForest_node_092790 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_092790 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092790 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_013175 := by
  decide +kernel

theorem g32p_supplierForest_actual_092790 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092790) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_092790
    g32p_supplierForest_actual_013175

def g32p_supplierForest_node_092881 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_092881 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092881 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_094384 := by
  decide +kernel

theorem g32p_supplierForest_actual_092881 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092881) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_092881
    g32p_supplierForest_actual_094384

def g32p_supplierForest_node_092884 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092884 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092884 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_095024 := by
  decide +kernel

theorem g32p_supplierForest_actual_092884 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092884) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_092884
    g32p_supplierForest_actual_095024

def g32p_supplierForest_node_092885 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092885 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092885 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075036 := by
  decide +kernel

theorem g32p_supplierForest_actual_092885 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092885) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 0 g32p_supplierForest_edge_092885
    g32p_supplierForest_actual_075036

def g32p_supplierForest_node_092921 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092921 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092921 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_077194 := by
  decide +kernel

theorem g32p_supplierForest_actual_092921 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092921) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 1 g32p_supplierForest_edge_092921
    g32p_supplierForest_actual_077194

def g32p_supplierForest_node_092947 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092947 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092947 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014383 := by
  decide +kernel

theorem g32p_supplierForest_actual_092947 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092947) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_092947
    g32p_supplierForest_actual_014383

def g32p_supplierForest_node_092959 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092959 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092959 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014526 := by
  decide +kernel

theorem g32p_supplierForest_actual_092959 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092959) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_092959
    g32p_supplierForest_actual_014526

def g32p_supplierForest_node_092966 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_092966 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092966 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085276 := by
  decide +kernel

theorem g32p_supplierForest_actual_092966 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092966) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 0 g32p_supplierForest_edge_092966
    g32p_supplierForest_actual_085276

def g32p_supplierForest_node_092967 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_092967 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092967 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_076516 := by
  decide +kernel

theorem g32p_supplierForest_actual_092967 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092967) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_092967
    g32p_supplierForest_actual_076516

def g32p_supplierForest_node_092984 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_092984 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092984 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021537 := by
  decide +kernel

theorem g32p_supplierForest_actual_092984 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092984) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_092984
    g32p_supplierForest_actual_021537

def g32p_supplierForest_node_092988 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092988 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092988 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_101183 := by
  decide +kernel

theorem g32p_supplierForest_actual_092988 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092988) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_092988
    g32p_supplierForest_actual_101183

def g32p_supplierForest_node_092989 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_092989 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092989 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_101182 := by
  decide +kernel

theorem g32p_supplierForest_actual_092989 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092989) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_092989
    g32p_supplierForest_actual_101182

def g32p_supplierForest_node_092992 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092992 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092992 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087668 := by
  decide +kernel

theorem g32p_supplierForest_actual_092992 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092992) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_092992
    g32p_supplierForest_actual_087668

def g32p_supplierForest_node_093019 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093019 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093019 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073891 := by
  decide +kernel

theorem g32p_supplierForest_actual_093019 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093019) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_093019
    g32p_supplierForest_actual_073891

def g32p_supplierForest_node_093031 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_093031 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093031 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093861 := by
  decide +kernel

theorem g32p_supplierForest_actual_093031 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093031) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_093031
    g32p_supplierForest_actual_093861

def g32p_supplierForest_node_093076 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093076 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093076 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096301 := by
  decide +kernel

theorem g32p_supplierForest_actual_093076 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093076) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 2 g32p_supplierForest_edge_093076
    g32p_supplierForest_actual_096301

def g32p_supplierForest_node_093094 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_093094 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093094 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092081 := by
  decide +kernel

theorem g32p_supplierForest_actual_093094 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093094) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_093094
    g32p_supplierForest_actual_092081

def g32p_supplierForest_node_093176 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093176 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093176 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_075176 := by
  decide +kernel

theorem g32p_supplierForest_actual_093176 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093176) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_093176
    g32p_supplierForest_actual_075176

def g32p_supplierForest_node_093201 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_093201 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093201 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073504 := by
  decide +kernel

theorem g32p_supplierForest_actual_093201 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093201) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_093201
    g32p_supplierForest_actual_073504

def g32p_supplierForest_node_093205 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093205 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093205 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_077394 := by
  decide +kernel

theorem g32p_supplierForest_actual_093205 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093205) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_093205
    g32p_supplierForest_actual_077394

def g32p_supplierForest_node_093242 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_093242 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093242 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_074787 := by
  decide +kernel

theorem g32p_supplierForest_actual_093242 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093242) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_093242
    g32p_supplierForest_actual_074787

def g32p_supplierForest_node_093262 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093262 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093262 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_094532 := by
  decide +kernel

theorem g32p_supplierForest_actual_093262 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093262) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_093262
    g32p_supplierForest_actual_094532

def g32p_supplierForest_node_093281 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093281 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093281 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_078700 := by
  decide +kernel

theorem g32p_supplierForest_actual_093281 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093281) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_093281
    g32p_supplierForest_actual_078700

def g32p_supplierForest_node_093311 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093311 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093311 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_094253 := by
  decide +kernel

theorem g32p_supplierForest_actual_093311 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093311) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_093311
    g32p_supplierForest_actual_094253

def g32p_supplierForest_node_093318 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093318 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093318 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075217 := by
  decide +kernel

theorem g32p_supplierForest_actual_093318 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093318) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_093318
    g32p_supplierForest_actual_075217

def g32p_supplierForest_node_093439 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093439 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093439 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_077197 := by
  decide +kernel

theorem g32p_supplierForest_actual_093439 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093439) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_093439
    g32p_supplierForest_actual_077197

def g32p_supplierForest_node_093444 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093444 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093444 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_014209 := by
  decide +kernel

theorem g32p_supplierForest_actual_093444 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093444) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_093444
    g32p_supplierForest_actual_014209

def g32p_supplierForest_node_093509 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_093509 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093509 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012660 := by
  decide +kernel

theorem g32p_supplierForest_actual_093509 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093509) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 3 g32p_supplierForest_edge_093509
    g32p_supplierForest_actual_012660

def g32p_supplierForest_node_093529 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093529 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093529 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100400 := by
  decide +kernel

theorem g32p_supplierForest_actual_093529 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093529) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 2 g32p_supplierForest_edge_093529
    g32p_supplierForest_actual_100400

def g32p_supplierForest_node_093548 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093548 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093548 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021810 := by
  decide +kernel

theorem g32p_supplierForest_actual_093548 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093548) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_093548
    g32p_supplierForest_actual_021810

def g32p_supplierForest_node_093553 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093553 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093553 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_080797 := by
  decide +kernel

theorem g32p_supplierForest_actual_093553 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093553) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_093553
    g32p_supplierForest_actual_080797

def g32p_supplierForest_node_093561 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_093561 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093561 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_094919 := by
  decide +kernel

theorem g32p_supplierForest_actual_093561 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093561) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_093561
    g32p_supplierForest_actual_094919

def g32p_supplierForest_node_093585 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093585 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093585 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093317 := by
  decide +kernel

theorem g32p_supplierForest_actual_093585 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093585) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_093585
    g32p_supplierForest_actual_093317

def g32p_supplierForest_node_093593 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093593 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093593 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_093566 := by
  decide +kernel

theorem g32p_supplierForest_actual_093593 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093593) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 2 g32p_supplierForest_edge_093593
    g32p_supplierForest_actual_093566

def g32p_supplierForest_node_093612 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093612 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093612 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_145412 := by
  decide +kernel

theorem g32p_supplierForest_actual_093612 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093612) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 0 g32p_supplierForest_edge_093612
    g32p_supplierForest_actual_145412

def g32p_supplierForest_node_093655 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093655 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093655 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152344 := by
  decide +kernel

theorem g32p_supplierForest_actual_093655 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093655) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_093655
    g32p_supplierForest_actual_152344

def g32p_supplierForest_node_093662 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093662 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093662 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018222 := by
  decide +kernel

theorem g32p_supplierForest_actual_093662 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093662) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_093662
    g32p_supplierForest_actual_018222

def g32p_supplierForest_node_093669 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093669 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093669 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_081005 := by
  decide +kernel

theorem g32p_supplierForest_actual_093669 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093669) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_093669
    g32p_supplierForest_actual_081005

def g32p_supplierForest_node_093683 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_093683 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093683 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_081149 := by
  decide +kernel

theorem g32p_supplierForest_actual_093683 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093683) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_093683
    g32p_supplierForest_actual_081149

def g32p_supplierForest_node_093715 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_093715 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093715 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_149526 := by
  decide +kernel

theorem g32p_supplierForest_actual_093715 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093715) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_093715
    g32p_supplierForest_actual_149526

def g32p_supplierForest_node_093740 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093740 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093740 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_087127 := by
  decide +kernel

theorem g32p_supplierForest_actual_093740 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093740) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_093740
    g32p_supplierForest_actual_087127

def g32p_supplierForest_node_093752 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_093752 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093752 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076780 := by
  decide +kernel

theorem g32p_supplierForest_actual_093752 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093752) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_093752
    g32p_supplierForest_actual_076780

def g32p_supplierForest_node_093759 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_093759 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093759 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073711 := by
  decide +kernel

theorem g32p_supplierForest_actual_093759 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093759) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_093759
    g32p_supplierForest_actual_073711

def g32p_supplierForest_node_093760 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_093760 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093760 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076516 := by
  decide +kernel

theorem g32p_supplierForest_actual_093760 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093760) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_093760
    g32p_supplierForest_actual_076516

def g32p_supplierForest_node_093776 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_093776 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093776 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_093130 := by
  decide +kernel

theorem g32p_supplierForest_actual_093776 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093776) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_093776
    g32p_supplierForest_actual_093130

def g32p_supplierForest_node_093779 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093779 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093779 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_072820 := by
  decide +kernel

theorem g32p_supplierForest_actual_093779 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093779) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 0 g32p_supplierForest_edge_093779
    g32p_supplierForest_actual_072820

def g32p_supplierForest_node_093789 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_093789 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093789 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075465 := by
  decide +kernel

theorem g32p_supplierForest_actual_093789 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093789) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_093789
    g32p_supplierForest_actual_075465

def g32p_supplierForest_node_093809 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093809 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093809 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095794 := by
  decide +kernel

theorem g32p_supplierForest_actual_093809 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093809) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_093809
    g32p_supplierForest_actual_095794

def g32p_supplierForest_node_093831 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093831 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093831 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_099159 := by
  decide +kernel

theorem g32p_supplierForest_actual_093831 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093831) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_093831
    g32p_supplierForest_actual_099159

def g32p_supplierForest_node_093835 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_093835 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093835 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_080067 := by
  decide +kernel

theorem g32p_supplierForest_actual_093835 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093835) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_093835
    g32p_supplierForest_actual_080067

def g32p_supplierForest_node_093847 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093847 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093847 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_096540 := by
  decide +kernel

theorem g32p_supplierForest_actual_093847 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093847) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 3 g32p_supplierForest_edge_093847
    g32p_supplierForest_actual_096540

def g32p_supplierForest_node_093855 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093855 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093855 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085281 := by
  decide +kernel

theorem g32p_supplierForest_actual_093855 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093855) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 2 g32p_supplierForest_edge_093855
    g32p_supplierForest_actual_085281

def g32p_supplierForest_node_093869 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093869 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093869 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101721 := by
  decide +kernel

theorem g32p_supplierForest_actual_093869 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093869) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_093869
    g32p_supplierForest_actual_101721

def g32p_supplierForest_node_093942 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093942 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093942 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_016771 := by
  decide +kernel

theorem g32p_supplierForest_actual_093942 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093942) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 1 g32p_supplierForest_edge_093942
    g32p_supplierForest_actual_016771

def g32p_supplierForest_node_093959 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_093959 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093959 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095803 := by
  decide +kernel

theorem g32p_supplierForest_actual_093959 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093959) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_093959
    g32p_supplierForest_actual_095803

def g32p_supplierForest_node_094018 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_094018 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094018 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_072616 := by
  decide +kernel

theorem g32p_supplierForest_actual_094018 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094018) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_094018
    g32p_supplierForest_actual_072616

def g32p_supplierForest_node_094047 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_094047 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094047 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076390 := by
  decide +kernel

theorem g32p_supplierForest_actual_094047 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094047) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_094047
    g32p_supplierForest_actual_076390

def g32p_supplierForest_node_094067 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094067 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094067 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092067 := by
  decide +kernel

theorem g32p_supplierForest_actual_094067 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094067) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 3 g32p_supplierForest_edge_094067
    g32p_supplierForest_actual_092067

def g32p_supplierForest_node_094068 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_094068 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094068 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_078404 := by
  decide +kernel

theorem g32p_supplierForest_actual_094068 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094068) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_094068
    g32p_supplierForest_actual_078404

def g32p_supplierForest_node_094089 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094089 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094089 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091124 := by
  decide +kernel

theorem g32p_supplierForest_actual_094089 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094089) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_094089
    g32p_supplierForest_actual_091124

def g32p_supplierForest_node_094110 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_094110 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094110 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091067 := by
  decide +kernel

theorem g32p_supplierForest_actual_094110 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094110) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_094110
    g32p_supplierForest_actual_091067

def g32p_supplierForest_node_094111 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094111 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094111 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_017413 := by
  decide +kernel

theorem g32p_supplierForest_actual_094111 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094111) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_094111
    g32p_supplierForest_actual_017413

def g32p_supplierForest_node_094118 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094118 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094118 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022348 := by
  decide +kernel

theorem g32p_supplierForest_actual_094118 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094118) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_094118
    g32p_supplierForest_actual_022348

def g32p_supplierForest_node_094132 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_094132 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094132 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_096598 := by
  decide +kernel

theorem g32p_supplierForest_actual_094132 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094132) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_094132
    g32p_supplierForest_actual_096598

def g32p_supplierForest_node_094160 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094160 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094160 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_096795 := by
  decide +kernel

theorem g32p_supplierForest_actual_094160 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094160) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_094160
    g32p_supplierForest_actual_096795

def g32p_supplierForest_node_094192 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_094192 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094192 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093214 := by
  decide +kernel

theorem g32p_supplierForest_actual_094192 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094192) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_094192
    g32p_supplierForest_actual_093214

def g32p_supplierForest_node_094276 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094276 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094276 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075405 := by
  decide +kernel

theorem g32p_supplierForest_actual_094276 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094276) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_094276
    g32p_supplierForest_actual_075405

def g32p_supplierForest_node_094291 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_094291 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094291 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_017266 := by
  decide +kernel

theorem g32p_supplierForest_actual_094291 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094291) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_094291
    g32p_supplierForest_actual_017266

def g32p_supplierForest_node_094293 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_094293 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094293 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091092 := by
  decide +kernel

theorem g32p_supplierForest_actual_094293 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094293) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_094293
    g32p_supplierForest_actual_091092

def g32p_supplierForest_node_094294 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_094294 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094294 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_090133 := by
  decide +kernel

theorem g32p_supplierForest_actual_094294 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094294) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_094294
    g32p_supplierForest_actual_090133

def g32p_supplierForest_node_094340 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_094340 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094340 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_021810 := by
  decide +kernel

theorem g32p_supplierForest_actual_094340 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094340) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_094340
    g32p_supplierForest_actual_021810

def g32p_supplierForest_node_094392 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094392 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094392 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_081480 := by
  decide +kernel

theorem g32p_supplierForest_actual_094392 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094392) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_094392
    g32p_supplierForest_actual_081480

def g32p_supplierForest_node_094398 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_094398 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094398 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_091127 := by
  decide +kernel

theorem g32p_supplierForest_actual_094398 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094398) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 1 g32p_supplierForest_edge_094398
    g32p_supplierForest_actual_091127

def g32p_supplierForest_node_094407 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_094407 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094407 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_091178 := by
  decide +kernel

theorem g32p_supplierForest_actual_094407 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094407) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_094407
    g32p_supplierForest_actual_091178

def g32p_supplierForest_node_094433 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_094433 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094433 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073394 := by
  decide +kernel

theorem g32p_supplierForest_actual_094433 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094433) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_094433
    g32p_supplierForest_actual_073394

def g32p_supplierForest_node_094469 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_094469 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094469 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_094651 := by
  decide +kernel

theorem g32p_supplierForest_actual_094469 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094469) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_094469
    g32p_supplierForest_actual_094651

def g32p_supplierForest_node_094470 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094470 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094470 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_084062 := by
  decide +kernel

theorem g32p_supplierForest_actual_094470 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094470) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_094470
    g32p_supplierForest_actual_084062

def g32p_supplierForest_node_094503 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_094503 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094503 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098433 := by
  decide +kernel

theorem g32p_supplierForest_actual_094503 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094503) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_094503
    g32p_supplierForest_actual_098433

def g32p_supplierForest_node_094507 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094507 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094507 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098069 := by
  decide +kernel

theorem g32p_supplierForest_actual_094507 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094507) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_094507
    g32p_supplierForest_actual_098069

def g32p_supplierForest_node_094603 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_094603 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094603 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_084761 := by
  decide +kernel

theorem g32p_supplierForest_actual_094603 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094603) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 0 g32p_supplierForest_edge_094603
    g32p_supplierForest_actual_084761

def g32p_supplierForest_node_094631 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_094631 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094631 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018637 := by
  decide +kernel

theorem g32p_supplierForest_actual_094631 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094631) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_094631
    g32p_supplierForest_actual_018637

def g32p_supplierForest_node_094698 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094698 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094698 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_088692 := by
  decide +kernel

theorem g32p_supplierForest_actual_094698 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094698) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_094698
    g32p_supplierForest_actual_088692

def g32p_supplierForest_node_094735 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_094735 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094735 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_098433 := by
  decide +kernel

theorem g32p_supplierForest_actual_094735 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094735) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_094735
    g32p_supplierForest_actual_098433

def g32p_supplierForest_node_094776 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_094776 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094776 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_078974 := by
  decide +kernel

theorem g32p_supplierForest_actual_094776 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094776) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_094776
    g32p_supplierForest_actual_078974

def g32p_supplierForest_node_094782 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_094782 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094782 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_092187 := by
  decide +kernel

theorem g32p_supplierForest_actual_094782 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094782) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 1 g32p_supplierForest_edge_094782
    g32p_supplierForest_actual_092187

def g32p_supplierForest_node_094847 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_094847 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094847 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083550 := by
  decide +kernel

theorem g32p_supplierForest_actual_094847 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094847) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_094847
    g32p_supplierForest_actual_083550

def g32p_supplierForest_node_094891 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_094891 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094891 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_092390 := by
  decide +kernel

theorem g32p_supplierForest_actual_094891 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094891) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 1 g32p_supplierForest_edge_094891
    g32p_supplierForest_actual_092390

def g32p_supplierForest_node_094913 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_094913 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094913 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093566 := by
  decide +kernel

theorem g32p_supplierForest_actual_094913 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094913) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 3 g32p_supplierForest_edge_094913
    g32p_supplierForest_actual_093566

def g32p_supplierForest_node_094926 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_094926 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094926 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_093323 := by
  decide +kernel

theorem g32p_supplierForest_actual_094926 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094926) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_094926
    g32p_supplierForest_actual_093323

def g32p_supplierForest_node_094970 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094970 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094970 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_020717 := by
  decide +kernel

theorem g32p_supplierForest_actual_094970 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094970) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_094970
    g32p_supplierForest_actual_020717

def g32p_supplierForest_node_094972 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨2, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_094972 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094972 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073606 := by
  decide +kernel

theorem g32p_supplierForest_actual_094972 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094972) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_094972
    g32p_supplierForest_actual_073606

def g32p_supplierForest_node_095010 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_095010 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095010 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_093229 := by
  decide +kernel

theorem g32p_supplierForest_actual_095010 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095010) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_095010
    g32p_supplierForest_actual_093229

def g32p_supplierForest_node_095026 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095026 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095026 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_148853 := by
  decide +kernel

theorem g32p_supplierForest_actual_095026 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095026) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_095026
    g32p_supplierForest_actual_148853

def g32p_supplierForest_node_095069 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_095069 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095069 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015715 := by
  decide +kernel

theorem g32p_supplierForest_actual_095069 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095069) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_095069
    g32p_supplierForest_actual_015715

def g32p_supplierForest_node_095169 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095169 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095169 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_088366 := by
  decide +kernel

theorem g32p_supplierForest_actual_095169 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095169) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_095169
    g32p_supplierForest_actual_088366

def g32p_supplierForest_node_095179 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_095179 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095179 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095727 := by
  decide +kernel

theorem g32p_supplierForest_actual_095179 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095179) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 2 g32p_supplierForest_edge_095179
    g32p_supplierForest_actual_095727

def g32p_supplierForest_node_095187 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095187 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095187 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022351 := by
  decide +kernel

theorem g32p_supplierForest_actual_095187 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095187) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_095187
    g32p_supplierForest_actual_022351

def g32p_supplierForest_node_095309 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_095309 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095309 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019033 := by
  decide +kernel

theorem g32p_supplierForest_actual_095309 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095309) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 2 g32p_supplierForest_edge_095309
    g32p_supplierForest_actual_019033

def g32p_supplierForest_node_095331 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_095331 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095331 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_019081 := by
  decide +kernel

theorem g32p_supplierForest_actual_095331 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095331) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_095331
    g32p_supplierForest_actual_019081

def g32p_supplierForest_node_095338 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095338 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095338 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_092067 := by
  decide +kernel

theorem g32p_supplierForest_actual_095338 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095338) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 1 g32p_supplierForest_edge_095338
    g32p_supplierForest_actual_092067

def g32p_supplierForest_node_095491 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095491 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095491 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_022014 := by
  decide +kernel

theorem g32p_supplierForest_actual_095491 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095491) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_095491
    g32p_supplierForest_actual_022014

def g32p_supplierForest_node_095492 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_095492 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095492 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_101488 := by
  decide +kernel

theorem g32p_supplierForest_actual_095492 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095492) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_095492
    g32p_supplierForest_actual_101488

def g32p_supplierForest_node_095512 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_095512 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095512 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021943 := by
  decide +kernel

theorem g32p_supplierForest_actual_095512 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095512) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_095512
    g32p_supplierForest_actual_021943

def g32p_supplierForest_node_095556 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095556 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095556 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086643 := by
  decide +kernel

theorem g32p_supplierForest_actual_095556 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095556) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 3 g32p_supplierForest_edge_095556
    g32p_supplierForest_actual_086643

def g32p_supplierForest_node_095566 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_095566 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095566 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_093533 := by
  decide +kernel

theorem g32p_supplierForest_actual_095566 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095566) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 1 g32p_supplierForest_edge_095566
    g32p_supplierForest_actual_093533

def g32p_supplierForest_node_095574 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_095574 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095574 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_145858 := by
  decide +kernel

theorem g32p_supplierForest_actual_095574 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095574) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 0 g32p_supplierForest_edge_095574
    g32p_supplierForest_actual_145858

def g32p_supplierForest_node_095587 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_095587 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095587 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091441 := by
  decide +kernel

theorem g32p_supplierForest_actual_095587 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095587) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_095587
    g32p_supplierForest_actual_091441

def g32p_supplierForest_node_095635 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095635 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095635 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_077044 := by
  decide +kernel

theorem g32p_supplierForest_actual_095635 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095635) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_095635
    g32p_supplierForest_actual_077044

def g32p_supplierForest_node_095652 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095652 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095652 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_077474 := by
  decide +kernel

theorem g32p_supplierForest_actual_095652 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095652) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_095652
    g32p_supplierForest_actual_077474

def g32p_supplierForest_node_095670 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095670 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095670 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012669 := by
  decide +kernel

theorem g32p_supplierForest_actual_095670 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095670) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_095670
    g32p_supplierForest_actual_012669

def g32p_supplierForest_node_095711 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095711 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095711 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082596 := by
  decide +kernel

theorem g32p_supplierForest_actual_095711 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095711) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_095711
    g32p_supplierForest_actual_082596

def g32p_supplierForest_node_095802 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_095802 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095802 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_101721 := by
  decide +kernel

theorem g32p_supplierForest_actual_095802 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095802) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_095802
    g32p_supplierForest_actual_101721

def g32p_supplierForest_node_095811 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_095811 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095811 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086644 := by
  decide +kernel

theorem g32p_supplierForest_actual_095811 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095811) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_095811
    g32p_supplierForest_actual_086644

def g32p_supplierForest_node_095845 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095845 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095845 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_096210 := by
  decide +kernel

theorem g32p_supplierForest_actual_095845 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095845) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_095845
    g32p_supplierForest_actual_096210

def g32p_supplierForest_node_095853 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095853 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095853 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_081803 := by
  decide +kernel

theorem g32p_supplierForest_actual_095853 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095853) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_095853
    g32p_supplierForest_actual_081803

def g32p_supplierForest_node_095857 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095857 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095857 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095887 := by
  decide +kernel

theorem g32p_supplierForest_actual_095857 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095857) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_095857
    g32p_supplierForest_actual_095887

def g32p_supplierForest_node_095966 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_095966 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095966 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021182 := by
  decide +kernel

theorem g32p_supplierForest_actual_095966 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095966) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_095966
    g32p_supplierForest_actual_021182

def g32p_supplierForest_node_095972 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095972 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095972 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019122 := by
  decide +kernel

theorem g32p_supplierForest_actual_095972 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095972) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 3 g32p_supplierForest_edge_095972
    g32p_supplierForest_actual_019122

def g32p_supplierForest_node_096037 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096037 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096037 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019844 := by
  decide +kernel

theorem g32p_supplierForest_actual_096037 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096037) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_096037
    g32p_supplierForest_actual_019844

def g32p_supplierForest_node_096087 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096087 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096087 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_148488 := by
  decide +kernel

theorem g32p_supplierForest_actual_096087 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096087) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 2 g32p_supplierForest_edge_096087
    g32p_supplierForest_actual_148488

def g32p_supplierForest_node_096098 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096098 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096098 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_084809 := by
  decide +kernel

theorem g32p_supplierForest_actual_096098 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096098) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_096098
    g32p_supplierForest_actual_084809

def g32p_supplierForest_node_096124 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096124 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096124 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_091090 := by
  decide +kernel

theorem g32p_supplierForest_actual_096124 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096124) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_096124
    g32p_supplierForest_actual_091090

def g32p_supplierForest_node_096134 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096134 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096134 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073606 := by
  decide +kernel

theorem g32p_supplierForest_actual_096134 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096134) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_096134
    g32p_supplierForest_actual_073606

def g32p_supplierForest_node_096145 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_096145 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096145 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_023677 := by
  decide +kernel

theorem g32p_supplierForest_actual_096145 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096145) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_096145
    g32p_supplierForest_actual_023677

def g32p_supplierForest_node_096146 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096146 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096146 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_096508 := by
  decide +kernel

theorem g32p_supplierForest_actual_096146 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096146) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_096146
    g32p_supplierForest_actual_096508

def g32p_supplierForest_node_096163 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_096163 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096163 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073649 := by
  decide +kernel

theorem g32p_supplierForest_actual_096163 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096163) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_096163
    g32p_supplierForest_actual_073649

def g32p_supplierForest_node_096167 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_096167 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096167 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_074205 := by
  decide +kernel

theorem g32p_supplierForest_actual_096167 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096167) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 3 g32p_supplierForest_edge_096167
    g32p_supplierForest_actual_074205

def g32p_supplierForest_node_096174 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_096174 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096174 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097619 := by
  decide +kernel

theorem g32p_supplierForest_actual_096174 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096174) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 2 g32p_supplierForest_edge_096174
    g32p_supplierForest_actual_097619

def g32p_supplierForest_node_096192 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_096192 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096192 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019138 := by
  decide +kernel

theorem g32p_supplierForest_actual_096192 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096192) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_096192
    g32p_supplierForest_actual_019138

def g32p_supplierForest_node_096198 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_096198 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096198 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146916 := by
  decide +kernel

theorem g32p_supplierForest_actual_096198 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096198) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 0 g32p_supplierForest_edge_096198
    g32p_supplierForest_actual_146916

def g32p_supplierForest_node_096201 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096201 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096201 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095024 := by
  decide +kernel

theorem g32p_supplierForest_actual_096201 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096201) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_096201
    g32p_supplierForest_actual_095024

def g32p_supplierForest_node_096207 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096207 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096207 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_080105 := by
  decide +kernel

theorem g32p_supplierForest_actual_096207 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096207) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_096207
    g32p_supplierForest_actual_080105

def g32p_supplierForest_node_096298 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096298 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096298 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_080012 := by
  decide +kernel

theorem g32p_supplierForest_actual_096298 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096298) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_096298
    g32p_supplierForest_actual_080012

def g32p_supplierForest_node_096326 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096326 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096326 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_099755 := by
  decide +kernel

theorem g32p_supplierForest_actual_096326 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096326) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_096326
    g32p_supplierForest_actual_099755

def g32p_supplierForest_node_096333 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_096333 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096333 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_022078 := by
  decide +kernel

theorem g32p_supplierForest_actual_096333 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096333) ∧
        IsConj g (g32p_literalRepresentative 51) := by
  exact g32p_archive_step_lift _ _ 51 3 g32p_supplierForest_edge_096333
    g32p_supplierForest_actual_022078

def g32p_supplierForest_node_096342 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096342 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096342 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_072145 := by
  decide +kernel

theorem g32p_supplierForest_actual_096342 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096342) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_096342
    g32p_supplierForest_actual_072145

def g32p_supplierForest_node_096344 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096344 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096344 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_081972 := by
  decide +kernel

theorem g32p_supplierForest_actual_096344 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096344) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_096344
    g32p_supplierForest_actual_081972

def g32p_supplierForest_node_096347 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_096347 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096347 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021992 := by
  decide +kernel

theorem g32p_supplierForest_actual_096347 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096347) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 3 g32p_supplierForest_edge_096347
    g32p_supplierForest_actual_021992

def g32p_supplierForest_node_096567 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096567 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096567 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078051 := by
  decide +kernel

theorem g32p_supplierForest_actual_096567 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096567) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_096567
    g32p_supplierForest_actual_078051

def g32p_supplierForest_node_096592 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_096592 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096592 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_081595 := by
  decide +kernel

theorem g32p_supplierForest_actual_096592 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096592) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 2 g32p_supplierForest_edge_096592
    g32p_supplierForest_actual_081595

def g32p_supplierForest_node_096597 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096597 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096597 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094806 := by
  decide +kernel

theorem g32p_supplierForest_actual_096597 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096597) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_096597
    g32p_supplierForest_actual_094806

def g32p_supplierForest_node_096601 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_096601 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096601 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075159 := by
  decide +kernel

theorem g32p_supplierForest_actual_096601 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096601) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 0 g32p_supplierForest_edge_096601
    g32p_supplierForest_actual_075159

def g32p_supplierForest_node_096614 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_096614 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096614 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_081728 := by
  decide +kernel

theorem g32p_supplierForest_actual_096614 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096614) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_096614
    g32p_supplierForest_actual_081728

def g32p_supplierForest_node_096655 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096655 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096655 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146681 := by
  decide +kernel

theorem g32p_supplierForest_actual_096655 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096655) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_096655
    g32p_supplierForest_actual_146681

def g32p_supplierForest_node_096686 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_096686 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096686 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_020195 := by
  decide +kernel

theorem g32p_supplierForest_actual_096686 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096686) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_096686
    g32p_supplierForest_actual_020195

def g32p_supplierForest_node_096721 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_096721 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096721 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_096537 := by
  decide +kernel

theorem g32p_supplierForest_actual_096721 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096721) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_096721
    g32p_supplierForest_actual_096537

def g32p_supplierForest_node_096735 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_096735 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096735 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021046 := by
  decide +kernel

theorem g32p_supplierForest_actual_096735 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096735) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 2 g32p_supplierForest_edge_096735
    g32p_supplierForest_actual_021046

def g32p_supplierForest_node_096777 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096777 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096777 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087288 := by
  decide +kernel

theorem g32p_supplierForest_actual_096777 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096777) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_096777
    g32p_supplierForest_actual_087288

def g32p_supplierForest_node_096789 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096789 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096789 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_098992 := by
  decide +kernel

theorem g32p_supplierForest_actual_096789 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096789) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_096789
    g32p_supplierForest_actual_098992

def g32p_supplierForest_node_096868 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096868 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096868 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_147519 := by
  decide +kernel

theorem g32p_supplierForest_actual_096868 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096868) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 0 g32p_supplierForest_edge_096868
    g32p_supplierForest_actual_147519

def g32p_supplierForest_node_096872 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_096872 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096872 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073394 := by
  decide +kernel

theorem g32p_supplierForest_actual_096872 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096872) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_096872
    g32p_supplierForest_actual_073394

def g32p_supplierForest_node_096901 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_096901 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096901 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_099227 := by
  decide +kernel

theorem g32p_supplierForest_actual_096901 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096901) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_096901
    g32p_supplierForest_actual_099227

def g32p_supplierForest_node_096965 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_096965 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096965 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_144771 := by
  decide +kernel

theorem g32p_supplierForest_actual_096965 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096965) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 3 g32p_supplierForest_edge_096965
    g32p_supplierForest_actual_144771

def g32p_supplierForest_node_096982 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096982 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096982 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_096995 := by
  decide +kernel

theorem g32p_supplierForest_actual_096982 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096982) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_096982
    g32p_supplierForest_actual_096995

def g32p_supplierForest_node_096985 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096985 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096985 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096351 := by
  decide +kernel

theorem g32p_supplierForest_actual_096985 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096985) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_096985
    g32p_supplierForest_actual_096351

def g32p_supplierForest_node_097046 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_097046 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097046 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_144951 := by
  decide +kernel

theorem g32p_supplierForest_actual_097046 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097046) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 3 g32p_supplierForest_edge_097046
    g32p_supplierForest_actual_144951

def g32p_supplierForest_node_097063 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097063 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097063 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_088297 := by
  decide +kernel

theorem g32p_supplierForest_actual_097063 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097063) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 0 g32p_supplierForest_edge_097063
    g32p_supplierForest_actual_088297

def g32p_supplierForest_node_097065 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_097065 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097065 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_101680 := by
  decide +kernel

theorem g32p_supplierForest_actual_097065 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097065) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_097065
    g32p_supplierForest_actual_101680

def g32p_supplierForest_node_097110 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097110 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097110 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075655 := by
  decide +kernel

theorem g32p_supplierForest_actual_097110 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097110) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_097110
    g32p_supplierForest_actual_075655

def g32p_supplierForest_node_097199 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097199 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097199 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097197 := by
  decide +kernel

theorem g32p_supplierForest_actual_097199 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097199) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_097199
    g32p_supplierForest_actual_097197

def g32p_supplierForest_node_097245 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097245 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097245 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094919 := by
  decide +kernel

theorem g32p_supplierForest_actual_097245 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097245) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_097245
    g32p_supplierForest_actual_094919

def g32p_supplierForest_node_097254 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097254 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097254 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020594 := by
  decide +kernel

theorem g32p_supplierForest_actual_097254 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097254) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_097254
    g32p_supplierForest_actual_020594

def g32p_supplierForest_node_097268 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097268 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097268 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077921 := by
  decide +kernel

theorem g32p_supplierForest_actual_097268 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097268) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 3 g32p_supplierForest_edge_097268
    g32p_supplierForest_actual_077921

def g32p_supplierForest_node_097286 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097286 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097286 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091994 := by
  decide +kernel

theorem g32p_supplierForest_actual_097286 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097286) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_097286
    g32p_supplierForest_actual_091994

def g32p_supplierForest_node_097323 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097323 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097323 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_099920 := by
  decide +kernel

theorem g32p_supplierForest_actual_097323 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097323) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_097323
    g32p_supplierForest_actual_099920

def g32p_supplierForest_node_097380 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097380 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097380 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086368 := by
  decide +kernel

theorem g32p_supplierForest_actual_097380 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097380) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_097380
    g32p_supplierForest_actual_086368

def g32p_supplierForest_node_097492 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097492 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097492 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_078543 := by
  decide +kernel

theorem g32p_supplierForest_actual_097492 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097492) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_097492
    g32p_supplierForest_actual_078543

def g32p_supplierForest_node_097536 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_097536 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097536 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083702 := by
  decide +kernel

theorem g32p_supplierForest_actual_097536 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097536) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_097536
    g32p_supplierForest_actual_083702

def g32p_supplierForest_node_097539 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_097539 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097539 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091261 := by
  decide +kernel

theorem g32p_supplierForest_actual_097539 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097539) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_097539
    g32p_supplierForest_actual_091261

def g32p_supplierForest_node_097540 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_097540 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097540 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100331 := by
  decide +kernel

theorem g32p_supplierForest_actual_097540 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097540) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_097540
    g32p_supplierForest_actual_100331

def g32p_supplierForest_node_097543 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097543 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097543 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_089390 := by
  decide +kernel

theorem g32p_supplierForest_actual_097543 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097543) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 0 g32p_supplierForest_edge_097543
    g32p_supplierForest_actual_089390

def g32p_supplierForest_node_097564 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097564 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097564 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_093911 := by
  decide +kernel

theorem g32p_supplierForest_actual_097564 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097564) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_097564
    g32p_supplierForest_actual_093911

def g32p_supplierForest_node_097596 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097596 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097596 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095058 := by
  decide +kernel

theorem g32p_supplierForest_actual_097596 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097596) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_097596
    g32p_supplierForest_actual_095058

def g32p_supplierForest_node_097605 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097605 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097605 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_100124 := by
  decide +kernel

theorem g32p_supplierForest_actual_097605 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097605) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 0 g32p_supplierForest_edge_097605
    g32p_supplierForest_actual_100124

def g32p_supplierForest_node_097624 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097624 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097624 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_101537 := by
  decide +kernel

theorem g32p_supplierForest_actual_097624 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097624) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_097624
    g32p_supplierForest_actual_101537

def g32p_supplierForest_node_097699 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097699 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097699 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021077 := by
  decide +kernel

theorem g32p_supplierForest_actual_097699 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097699) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_097699
    g32p_supplierForest_actual_021077

def g32p_supplierForest_node_097741 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097741 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097741 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088329 := by
  decide +kernel

theorem g32p_supplierForest_actual_097741 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097741) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 2 g32p_supplierForest_edge_097741
    g32p_supplierForest_actual_088329

def g32p_supplierForest_node_097765 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097765 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097765 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_099327 := by
  decide +kernel

theorem g32p_supplierForest_actual_097765 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097765) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_097765
    g32p_supplierForest_actual_099327

def g32p_supplierForest_node_097773 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_097773 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097773 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_148027 := by
  decide +kernel

theorem g32p_supplierForest_actual_097773 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097773) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 0 g32p_supplierForest_edge_097773
    g32p_supplierForest_actual_148027

def g32p_supplierForest_node_097805 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097805 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097805 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076326 := by
  decide +kernel

theorem g32p_supplierForest_actual_097805 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097805) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_097805
    g32p_supplierForest_actual_076326

def g32p_supplierForest_node_097847 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097847 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097847 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095788 := by
  decide +kernel

theorem g32p_supplierForest_actual_097847 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097847) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 2 g32p_supplierForest_edge_097847
    g32p_supplierForest_actual_095788

def g32p_supplierForest_node_097870 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_097870 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097870 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100951 := by
  decide +kernel

theorem g32p_supplierForest_actual_097870 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097870) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 2 g32p_supplierForest_edge_097870
    g32p_supplierForest_actual_100951

def g32p_supplierForest_node_097873 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_097873 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097873 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_147013 := by
  decide +kernel

theorem g32p_supplierForest_actual_097873 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097873) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 0 g32p_supplierForest_edge_097873
    g32p_supplierForest_actual_147013

def g32p_supplierForest_node_097895 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097895 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097895 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_091501 := by
  decide +kernel

theorem g32p_supplierForest_actual_097895 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097895) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_097895
    g32p_supplierForest_actual_091501

def g32p_supplierForest_node_097953 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_097953 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097953 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083843 := by
  decide +kernel

theorem g32p_supplierForest_actual_097953 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097953) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_097953
    g32p_supplierForest_actual_083843

def g32p_supplierForest_node_097955 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097955 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097955 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101537 := by
  decide +kernel

theorem g32p_supplierForest_actual_097955 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097955) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_097955
    g32p_supplierForest_actual_101537

def g32p_supplierForest_node_097958 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_097958 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097958 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083702 := by
  decide +kernel

theorem g32p_supplierForest_actual_097958 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097958) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_097958
    g32p_supplierForest_actual_083702

def g32p_supplierForest_node_097973 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_097973 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097973 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_077456 := by
  decide +kernel

theorem g32p_supplierForest_actual_097973 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097973) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_097973
    g32p_supplierForest_actual_077456

def g32p_supplierForest_node_097977 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097977 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097977 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018094 := by
  decide +kernel

theorem g32p_supplierForest_actual_097977 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097977) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_097977
    g32p_supplierForest_actual_018094

def g32p_supplierForest_node_097984 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_097984 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097984 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_078052 := by
  decide +kernel

theorem g32p_supplierForest_actual_097984 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097984) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 0 g32p_supplierForest_edge_097984
    g32p_supplierForest_actual_078052

def g32p_supplierForest_node_097993 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_097993 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097993 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097928 := by
  decide +kernel

theorem g32p_supplierForest_actual_097993 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097993) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 2 g32p_supplierForest_edge_097993
    g32p_supplierForest_actual_097928

def g32p_supplierForest_node_098001 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098001 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098001 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073155 := by
  decide +kernel

theorem g32p_supplierForest_actual_098001 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098001) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 1 g32p_supplierForest_edge_098001
    g32p_supplierForest_actual_073155

def g32p_supplierForest_node_098008 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_098008 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098008 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_096537 := by
  decide +kernel

theorem g32p_supplierForest_actual_098008 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098008) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_098008
    g32p_supplierForest_actual_096537

def g32p_supplierForest_node_098010 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098010 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098010 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093037 := by
  decide +kernel

theorem g32p_supplierForest_actual_098010 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098010) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_098010
    g32p_supplierForest_actual_093037

def g32p_supplierForest_node_098057 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098057 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098057 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_101434 := by
  decide +kernel

theorem g32p_supplierForest_actual_098057 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098057) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_098057
    g32p_supplierForest_actual_101434

def g32p_supplierForest_node_098098 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_098098 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098098 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_148026 := by
  decide +kernel

theorem g32p_supplierForest_actual_098098 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098098) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_098098
    g32p_supplierForest_actual_148026

def g32p_supplierForest_node_098103 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098103 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098103 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_101085 := by
  decide +kernel

theorem g32p_supplierForest_actual_098103 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098103) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_098103
    g32p_supplierForest_actual_101085

def g32p_supplierForest_node_098158 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098158 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098158 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_080983 := by
  decide +kernel

theorem g32p_supplierForest_actual_098158 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098158) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 3 g32p_supplierForest_edge_098158
    g32p_supplierForest_actual_080983

def g32p_supplierForest_node_098189 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098189 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098189 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012456 := by
  decide +kernel

theorem g32p_supplierForest_actual_098189 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098189) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_098189
    g32p_supplierForest_actual_012456

def g32p_supplierForest_node_098194 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_098194 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098194 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_072403 := by
  decide +kernel

theorem g32p_supplierForest_actual_098194 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098194) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 3 g32p_supplierForest_edge_098194
    g32p_supplierForest_actual_072403

def g32p_supplierForest_node_098209 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098209 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098209 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101183 := by
  decide +kernel

theorem g32p_supplierForest_actual_098209 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098209) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_098209
    g32p_supplierForest_actual_101183

def g32p_supplierForest_node_098213 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098213 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098213 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021350 := by
  decide +kernel

theorem g32p_supplierForest_actual_098213 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098213) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_098213
    g32p_supplierForest_actual_021350

def g32p_supplierForest_node_098214 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_098214 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098214 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_090757 := by
  decide +kernel

theorem g32p_supplierForest_actual_098214 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098214) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 0 g32p_supplierForest_edge_098214
    g32p_supplierForest_actual_090757

def g32p_supplierForest_node_098220 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098220 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098220 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_082715 := by
  decide +kernel

theorem g32p_supplierForest_actual_098220 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098220) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_098220
    g32p_supplierForest_actual_082715

def g32p_supplierForest_node_098225 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_098225 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098225 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014548 := by
  decide +kernel

theorem g32p_supplierForest_actual_098225 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098225) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_098225
    g32p_supplierForest_actual_014548

def g32p_supplierForest_node_098250 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098250 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098250 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097336 := by
  decide +kernel

theorem g32p_supplierForest_actual_098250 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098250) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 2 g32p_supplierForest_edge_098250
    g32p_supplierForest_actual_097336

def g32p_supplierForest_node_098267 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_098267 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098267 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_147176 := by
  decide +kernel

theorem g32p_supplierForest_actual_098267 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098267) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 0 g32p_supplierForest_edge_098267
    g32p_supplierForest_actual_147176

def g32p_supplierForest_node_098295 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098295 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098295 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_088707 := by
  decide +kernel

theorem g32p_supplierForest_actual_098295 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098295) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 3 g32p_supplierForest_edge_098295
    g32p_supplierForest_actual_088707

def g32p_supplierForest_node_098319 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098319 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098319 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_101383 := by
  decide +kernel

theorem g32p_supplierForest_actual_098319 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098319) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 1 g32p_supplierForest_edge_098319
    g32p_supplierForest_actual_101383

def g32p_supplierForest_node_098343 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098343 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098343 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_147122 := by
  decide +kernel

theorem g32p_supplierForest_actual_098343 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098343) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_098343
    g32p_supplierForest_actual_147122

def g32p_supplierForest_node_098350 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_098350 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098350 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076898 := by
  decide +kernel

theorem g32p_supplierForest_actual_098350 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098350) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 0 g32p_supplierForest_edge_098350
    g32p_supplierForest_actual_076898

def g32p_supplierForest_node_098370 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098370 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098370 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016693 := by
  decide +kernel

theorem g32p_supplierForest_actual_098370 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098370) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_098370
    g32p_supplierForest_actual_016693

def g32p_supplierForest_node_098457 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_098457 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098457 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_093526 := by
  decide +kernel

theorem g32p_supplierForest_actual_098457 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098457) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_098457
    g32p_supplierForest_actual_093526

def g32p_supplierForest_node_098482 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_098482 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098482 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020295 := by
  decide +kernel

theorem g32p_supplierForest_actual_098482 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098482) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_098482
    g32p_supplierForest_actual_020295

def g32p_supplierForest_node_098485 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098485 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098485 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_101551 := by
  decide +kernel

theorem g32p_supplierForest_actual_098485 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098485) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 1 g32p_supplierForest_edge_098485
    g32p_supplierForest_actual_101551

def g32p_supplierForest_node_098545 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098545 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098545 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020588 := by
  decide +kernel

theorem g32p_supplierForest_actual_098545 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098545) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_098545
    g32p_supplierForest_actual_020588

def g32p_supplierForest_node_098553 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098553 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098553 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_092099 := by
  decide +kernel

theorem g32p_supplierForest_actual_098553 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098553) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_098553
    g32p_supplierForest_actual_092099

def g32p_supplierForest_node_098603 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098603 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098603 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077923 := by
  decide +kernel

theorem g32p_supplierForest_actual_098603 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098603) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 3 g32p_supplierForest_edge_098603
    g32p_supplierForest_actual_077923

def g32p_supplierForest_node_098614 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098614 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098614 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097914 := by
  decide +kernel

theorem g32p_supplierForest_actual_098614 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098614) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_098614
    g32p_supplierForest_actual_097914

def g32p_supplierForest_node_098621 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_098621 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098621 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100991 := by
  decide +kernel

theorem g32p_supplierForest_actual_098621 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098621) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_098621
    g32p_supplierForest_actual_100991

def g32p_supplierForest_node_098622 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_098622 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098622 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_080090 := by
  decide +kernel

theorem g32p_supplierForest_actual_098622 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098622) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_098622
    g32p_supplierForest_actual_080090

def g32p_supplierForest_node_098673 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098673 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098673 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_092986 := by
  decide +kernel

theorem g32p_supplierForest_actual_098673 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098673) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_098673
    g32p_supplierForest_actual_092986

def g32p_supplierForest_node_098697 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098697 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098697 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_098192 := by
  decide +kernel

theorem g32p_supplierForest_actual_098697 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098697) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_098697
    g32p_supplierForest_actual_098192

def g32p_supplierForest_node_098699 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_098699 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098699 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_077250 := by
  decide +kernel

theorem g32p_supplierForest_actual_098699 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098699) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_098699
    g32p_supplierForest_actual_077250

def g32p_supplierForest_node_098709 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098709 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098709 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_072805 := by
  decide +kernel

theorem g32p_supplierForest_actual_098709 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098709) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_098709
    g32p_supplierForest_actual_072805

def g32p_supplierForest_node_098712 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_098712 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098712 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076208 := by
  decide +kernel

theorem g32p_supplierForest_actual_098712 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098712) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_098712
    g32p_supplierForest_actual_076208

def g32p_supplierForest_node_098770 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_098770 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098770 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_145881 := by
  decide +kernel

theorem g32p_supplierForest_actual_098770 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098770) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 0 g32p_supplierForest_edge_098770
    g32p_supplierForest_actual_145881

def g32p_supplierForest_node_098823 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098823 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098823 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_089390 := by
  decide +kernel

theorem g32p_supplierForest_actual_098823 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098823) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_098823
    g32p_supplierForest_actual_089390

def g32p_supplierForest_node_098849 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098849 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098849 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078385 := by
  decide +kernel

theorem g32p_supplierForest_actual_098849 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098849) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_098849
    g32p_supplierForest_actual_078385

def g32p_supplierForest_node_098878 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098878 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098878 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085990 := by
  decide +kernel

theorem g32p_supplierForest_actual_098878 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098878) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_098878
    g32p_supplierForest_actual_085990

def g32p_supplierForest_node_098883 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_098883 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098883 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077576 := by
  decide +kernel

theorem g32p_supplierForest_actual_098883 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098883) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_098883
    g32p_supplierForest_actual_077576

def g32p_supplierForest_node_098896 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098896 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098896 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_152039 := by
  decide +kernel

theorem g32p_supplierForest_actual_098896 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098896) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 1 g32p_supplierForest_edge_098896
    g32p_supplierForest_actual_152039

def g32p_supplierForest_node_098953 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_098953 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098953 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_148408 := by
  decide +kernel

theorem g32p_supplierForest_actual_098953 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098953) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 1 g32p_supplierForest_edge_098953
    g32p_supplierForest_actual_148408

def g32p_supplierForest_node_099005 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_099005 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099005 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_146075 := by
  decide +kernel

theorem g32p_supplierForest_actual_099005 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099005) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_099005
    g32p_supplierForest_actual_146075

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_040 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_051070 else g32p_supplierForest_node_051084) else (if i.val < 3 then g32p_supplierForest_node_051092 else g32p_supplierForest_node_051115)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_051128 else g32p_supplierForest_node_051140) else (if i.val < 7 then g32p_supplierForest_node_051169 else g32p_supplierForest_node_051174))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_051244 else g32p_supplierForest_node_051292) else (if i.val < 11 then g32p_supplierForest_node_051360 else g32p_supplierForest_node_051388)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_051395 else g32p_supplierForest_node_051399) else (if i.val < 15 then g32p_supplierForest_node_051408 else g32p_supplierForest_node_051410)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_051412 else g32p_supplierForest_node_051416) else (if i.val < 19 then g32p_supplierForest_node_051463 else g32p_supplierForest_node_051469)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_051472 else g32p_supplierForest_node_051534) else (if i.val < 23 then g32p_supplierForest_node_051558 else g32p_supplierForest_node_051573))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_051588 else g32p_supplierForest_node_051598) else (if i.val < 27 then g32p_supplierForest_node_051618 else g32p_supplierForest_node_051695)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_051805 else g32p_supplierForest_node_051826) else (if i.val < 31 then g32p_supplierForest_node_051834 else g32p_supplierForest_node_051868))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_051883 else g32p_supplierForest_node_051892) else (if i.val < 35 then g32p_supplierForest_node_051909 else g32p_supplierForest_node_051937)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_051942 else g32p_supplierForest_node_051966) else (if i.val < 39 then g32p_supplierForest_node_052022 else g32p_supplierForest_node_052031))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_052129 else g32p_supplierForest_node_052130) else (if i.val < 43 then g32p_supplierForest_node_052145 else g32p_supplierForest_node_052226)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_052249 else g32p_supplierForest_node_052253) else (if i.val < 47 then g32p_supplierForest_node_052299 else g32p_supplierForest_node_052304)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_052322 else g32p_supplierForest_node_052325) else (if i.val < 51 then g32p_supplierForest_node_052333 else g32p_supplierForest_node_052337)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_052349 else g32p_supplierForest_node_052372) else (if i.val < 55 then g32p_supplierForest_node_052389 else g32p_supplierForest_node_052427))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_052475 else g32p_supplierForest_node_052484) else (if i.val < 59 then g32p_supplierForest_node_052499 else g32p_supplierForest_node_052536)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_052544 else g32p_supplierForest_node_052560) else (if i.val < 63 then g32p_supplierForest_node_052563 else g32p_supplierForest_node_052573)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_052577 else g32p_supplierForest_node_052610) else (if i.val < 67 then g32p_supplierForest_node_052625 else g32p_supplierForest_node_052649)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_052745 else g32p_supplierForest_node_052790) else (if i.val < 71 then g32p_supplierForest_node_052822 else g32p_supplierForest_node_052825))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_052866 else g32p_supplierForest_node_052880) else (if i.val < 75 then g32p_supplierForest_node_052896 else g32p_supplierForest_node_052898)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_052903 else g32p_supplierForest_node_052916) else (if i.val < 79 then g32p_supplierForest_node_052918 else g32p_supplierForest_node_052925)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_052990 else g32p_supplierForest_node_052994) else (if i.val < 83 then g32p_supplierForest_node_053004 else g32p_supplierForest_node_053028)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_053040 else g32p_supplierForest_node_053050) else (if i.val < 87 then g32p_supplierForest_node_053075 else g32p_supplierForest_node_053076))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_053087 else g32p_supplierForest_node_053103) else (if i.val < 91 then g32p_supplierForest_node_053138 else g32p_supplierForest_node_053178)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_053208 else g32p_supplierForest_node_053283) else (if i.val < 95 then g32p_supplierForest_node_053289 else g32p_supplierForest_node_053305))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_053390 else g32p_supplierForest_node_053426) else (if i.val < 99 then g32p_supplierForest_node_053452 else g32p_supplierForest_node_053456)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_053510 else g32p_supplierForest_node_053524) else (if i.val < 103 then g32p_supplierForest_node_053529 else g32p_supplierForest_node_053565))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_053569 else g32p_supplierForest_node_053573) else (if i.val < 107 then g32p_supplierForest_node_053575 else g32p_supplierForest_node_053590)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_053605 else g32p_supplierForest_node_053612) else (if i.val < 111 then g32p_supplierForest_node_053632 else g32p_supplierForest_node_053665)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_053680 else g32p_supplierForest_node_053715) else (if i.val < 115 then g32p_supplierForest_node_053718 else g32p_supplierForest_node_053721)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_053754 else g32p_supplierForest_node_053800) else (if i.val < 119 then g32p_supplierForest_node_053833 else g32p_supplierForest_node_053841))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_053902 else g32p_supplierForest_node_053929) else (if i.val < 123 then g32p_supplierForest_node_053950 else g32p_supplierForest_node_053987)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_053988 else g32p_supplierForest_node_054018) else (if i.val < 127 then g32p_supplierForest_node_054023 else g32p_supplierForest_node_054030))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_054031 else g32p_supplierForest_node_054038) else (if i.val < 131 then g32p_supplierForest_node_054045 else g32p_supplierForest_node_054059)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_054061 else g32p_supplierForest_node_054187) else (if i.val < 135 then g32p_supplierForest_node_054194 else g32p_supplierForest_node_054231))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_054234 else g32p_supplierForest_node_054254) else (if i.val < 139 then g32p_supplierForest_node_054259 else g32p_supplierForest_node_054266)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_054290 else g32p_supplierForest_node_054304) else (if i.val < 143 then g32p_supplierForest_node_054334 else g32p_supplierForest_node_054338)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_054372 else g32p_supplierForest_node_054470) else (if i.val < 147 then g32p_supplierForest_node_054471 else g32p_supplierForest_node_054496)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_054505 else g32p_supplierForest_node_054507) else (if i.val < 151 then g32p_supplierForest_node_054527 else g32p_supplierForest_node_054528))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_054588 else g32p_supplierForest_node_054638) else (if i.val < 155 then g32p_supplierForest_node_054665 else g32p_supplierForest_node_054717)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_054749 else g32p_supplierForest_node_054751) else (if i.val < 159 then g32p_supplierForest_node_054753 else g32p_supplierForest_node_054798))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_054839 else g32p_supplierForest_node_054896) else (if i.val < 163 then g32p_supplierForest_node_054919 else g32p_supplierForest_node_054964)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_054971 else g32p_supplierForest_node_054993) else (if i.val < 167 then g32p_supplierForest_node_055001 else g32p_supplierForest_node_055008))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_055011 else g32p_supplierForest_node_055015) else (if i.val < 171 then g32p_supplierForest_node_055024 else g32p_supplierForest_node_055029)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_055057 else g32p_supplierForest_node_055061) else (if i.val < 175 then g32p_supplierForest_node_055113 else g32p_supplierForest_node_055114)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_055160 else g32p_supplierForest_node_055173) else (if i.val < 179 then g32p_supplierForest_node_055247 else g32p_supplierForest_node_055253)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_055264 else g32p_supplierForest_node_055289) else (if i.val < 183 then g32p_supplierForest_node_055299 else g32p_supplierForest_node_055329))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_055342 else g32p_supplierForest_node_055388) else (if i.val < 187 then g32p_supplierForest_node_055407 else g32p_supplierForest_node_055426)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_055437 else g32p_supplierForest_node_055441) else (if i.val < 191 then g32p_supplierForest_node_055483 else g32p_supplierForest_node_055489)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_055563 else g32p_supplierForest_node_055569) else (if i.val < 195 then g32p_supplierForest_node_055578 else g32p_supplierForest_node_055592)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_055598 else g32p_supplierForest_node_055623) else (if i.val < 199 then g32p_supplierForest_node_055655 else g32p_supplierForest_node_055686))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_055691 else g32p_supplierForest_node_055693) else (if i.val < 203 then g32p_supplierForest_node_055706 else g32p_supplierForest_node_055711)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_055725 else g32p_supplierForest_node_055741) else (if i.val < 207 then g32p_supplierForest_node_055753 else g32p_supplierForest_node_055810)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_055829 else g32p_supplierForest_node_055847) else (if i.val < 211 then g32p_supplierForest_node_055871 else g32p_supplierForest_node_055998)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_056025 else g32p_supplierForest_node_056027) else (if i.val < 215 then g32p_supplierForest_node_056036 else g32p_supplierForest_node_056066))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_056067 else g32p_supplierForest_node_056082) else (if i.val < 219 then g32p_supplierForest_node_056096 else g32p_supplierForest_node_056133)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_056154 else g32p_supplierForest_node_056155) else (if i.val < 223 then g32p_supplierForest_node_056172 else g32p_supplierForest_node_056176))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_056194 else g32p_supplierForest_node_056206) else (if i.val < 227 then g32p_supplierForest_node_056215 else g32p_supplierForest_node_056235)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_056238 else g32p_supplierForest_node_056302) else (if i.val < 231 then g32p_supplierForest_node_056347 else g32p_supplierForest_node_056367))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_056370 else g32p_supplierForest_node_056417) else (if i.val < 235 then g32p_supplierForest_node_056449 else g32p_supplierForest_node_056461)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_056468 else g32p_supplierForest_node_056473) else (if i.val < 239 then g32p_supplierForest_node_056477 else g32p_supplierForest_node_056528)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_056564 else g32p_supplierForest_node_056603) else (if i.val < 243 then g32p_supplierForest_node_056671 else g32p_supplierForest_node_056735)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_056793 else g32p_supplierForest_node_056801) else (if i.val < 247 then g32p_supplierForest_node_056803 else g32p_supplierForest_node_056810))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_056884 else g32p_supplierForest_node_056897) else (if i.val < 251 then g32p_supplierForest_node_056907 else g32p_supplierForest_node_056916)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_056918 else g32p_supplierForest_node_056963) else (if i.val < 255 then g32p_supplierForest_node_056968 else g32p_supplierForest_node_056977))))))))

def g32p_supplierForest_classes_040 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 20) else (if i.val < 3 then 21 else 21)) else (if i.val < 6 then (if i.val < 5 then 40 else 6) else (if i.val < 7 then 22 else 70))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 69 else 7) else (if i.val < 11 then 74 else 38)) else (if i.val < 14 then (if i.val < 13 then 22 else 70) else (if i.val < 15 then 21 else 74)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 39 else 70) else (if i.val < 19 then 43 else 22)) else (if i.val < 22 then (if i.val < 21 then 21 else 7) else (if i.val < 23 then 6 else 22))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 42 else 40) else (if i.val < 27 then 40 else 20)) else (if i.val < 30 then (if i.val < 29 then 7 else 74) else (if i.val < 31 then 6 else 7))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 38 else 69) else (if i.val < 35 then 70 else 69)) else (if i.val < 38 then (if i.val < 37 then 21 else 21) else (if i.val < 39 then 39 else 74))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 39 else 69) else (if i.val < 43 then 75 else 69)) else (if i.val < 46 then (if i.val < 45 then 21 else 73) else (if i.val < 47 then 22 else 22)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 68 else 38) else (if i.val < 51 then 38 else 39)) else (if i.val < 54 then (if i.val < 53 then 40 else 69) else (if i.val < 55 then 74 else 41))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 41 else 74) else (if i.val < 59 then 68 else 69)) else (if i.val < 62 then (if i.val < 61 then 73 else 70) else (if i.val < 63 then 43 else 38)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 38 else 20) else (if i.val < 67 then 75 else 6)) else (if i.val < 70 then (if i.val < 69 then 39 else 40) else (if i.val < 71 then 70 else 38))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 70 else 24) else (if i.val < 75 then 20 else 21)) else (if i.val < 78 then (if i.val < 77 then 38 else 70) else (if i.val < 79 then 71 else 70)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 38 else 70) else (if i.val < 83 then 21 else 72)) else (if i.val < 86 then (if i.val < 85 then 21 else 38) else (if i.val < 87 then 79 else 68))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 38 else 38) else (if i.val < 91 then 21 else 22)) else (if i.val < 94 then (if i.val < 93 then 69 else 22) else (if i.val < 95 then 69 else 75))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 70 else 42) else (if i.val < 99 then 68 else 38)) else (if i.val < 102 then (if i.val < 101 then 69 else 38) else (if i.val < 103 then 21 else 38))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 40 else 38) else (if i.val < 107 then 38 else 6)) else (if i.val < 110 then (if i.val < 109 then 73 else 39) else (if i.val < 111 then 7 else 24)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 38 else 38) else (if i.val < 115 then 72 else 38)) else (if i.val < 118 then (if i.val < 117 then 68 else 41) else (if i.val < 119 then 21 else 38))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 43 else 21) else (if i.val < 123 then 71 else 22)) else (if i.val < 126 then (if i.val < 125 then 38 else 6) else (if i.val < 127 then 22 else 40))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 21 else 38) else (if i.val < 131 then 38 else 69)) else (if i.val < 134 then (if i.val < 133 then 75 else 7) else (if i.val < 135 then 68 else 38))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 69 else 21) else (if i.val < 139 then 38 else 68)) else (if i.val < 142 then (if i.val < 141 then 18 else 6) else (if i.val < 143 then 70 else 24)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 38 else 39) else (if i.val < 147 then 21 else 68)) else (if i.val < 150 then (if i.val < 149 then 41 else 43) else (if i.val < 151 then 38 else 78))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 74 else 22) else (if i.val < 155 then 73 else 21)) else (if i.val < 158 then (if i.val < 157 then 40 else 69) else (if i.val < 159 then 69 else 43))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 21 else 7) else (if i.val < 163 then 68 else 21)) else (if i.val < 166 then (if i.val < 165 then 71 else 43) else (if i.val < 167 then 43 else 7))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 38 else 43) else (if i.val < 171 then 41 else 20)) else (if i.val < 174 then (if i.val < 173 then 22 else 21) else (if i.val < 175 then 73 else 21)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 68 else 6) else (if i.val < 179 then 18 else 69)) else (if i.val < 182 then (if i.val < 181 then 6 else 6) else (if i.val < 183 then 21 else 68))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 21 else 70) else (if i.val < 187 then 41 else 67)) else (if i.val < 190 then (if i.val < 189 then 73 else 41) else (if i.val < 191 then 69 else 69)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 43 else 6) else (if i.val < 195 then 21 else 69)) else (if i.val < 198 then (if i.val < 197 then 70 else 75) else (if i.val < 199 then 38 else 40))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 20 else 38) else (if i.val < 203 then 40 else 40)) else (if i.val < 206 then (if i.val < 205 then 74 else 41) else (if i.val < 207 then 21 else 74)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 69 else 38) else (if i.val < 211 then 20 else 68)) else (if i.val < 214 then (if i.val < 213 then 22 else 74) else (if i.val < 215 then 74 else 40))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 43 else 69) else (if i.val < 219 then 69 else 68)) else (if i.val < 222 then (if i.val < 221 then 69 else 43) else (if i.val < 223 then 69 else 68))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 75 else 40) else (if i.val < 227 then 40 else 75)) else (if i.val < 230 then (if i.val < 229 then 69 else 20) else (if i.val < 231 then 39 else 22))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 69 else 69) else (if i.val < 235 then 38 else 39)) else (if i.val < 238 then (if i.val < 237 then 68 else 6) else (if i.val < 239 then 68 else 72)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 21 else 38) else (if i.val < 243 then 68 else 73)) else (if i.val < 246 then (if i.val < 245 then 43 else 21) else (if i.val < 247 then 74 else 74))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 42 else 22) else (if i.val < 251 then 21 else 71)) else (if i.val < 254 then (if i.val < 253 then 41 else 69) else (if i.val < 255 then 38 else 71))))))))

theorem g32p_supplierForest_actual_040 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_040 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_040 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_051070
  · exact g32p_supplierForest_actual_051084
  · exact g32p_supplierForest_actual_051092
  · exact g32p_supplierForest_actual_051115
  · exact g32p_supplierForest_actual_051128
  · exact g32p_supplierForest_actual_051140
  · exact g32p_supplierForest_actual_051169
  · exact g32p_supplierForest_actual_051174
  · exact g32p_supplierForest_actual_051244
  · exact g32p_supplierForest_actual_051292
  · exact g32p_supplierForest_actual_051360
  · exact g32p_supplierForest_actual_051388
  · exact g32p_supplierForest_actual_051395
  · exact g32p_supplierForest_actual_051399
  · exact g32p_supplierForest_actual_051408
  · exact g32p_supplierForest_actual_051410
  · exact g32p_supplierForest_actual_051412
  · exact g32p_supplierForest_actual_051416
  · exact g32p_supplierForest_actual_051463
  · exact g32p_supplierForest_actual_051469
  · exact g32p_supplierForest_actual_051472
  · exact g32p_supplierForest_actual_051534
  · exact g32p_supplierForest_actual_051558
  · exact g32p_supplierForest_actual_051573
  · exact g32p_supplierForest_actual_051588
  · exact g32p_supplierForest_actual_051598
  · exact g32p_supplierForest_actual_051618
  · exact g32p_supplierForest_actual_051695
  · exact g32p_supplierForest_actual_051805
  · exact g32p_supplierForest_actual_051826
  · exact g32p_supplierForest_actual_051834
  · exact g32p_supplierForest_actual_051868
  · exact g32p_supplierForest_actual_051883
  · exact g32p_supplierForest_actual_051892
  · exact g32p_supplierForest_actual_051909
  · exact g32p_supplierForest_actual_051937
  · exact g32p_supplierForest_actual_051942
  · exact g32p_supplierForest_actual_051966
  · exact g32p_supplierForest_actual_052022
  · exact g32p_supplierForest_actual_052031
  · exact g32p_supplierForest_actual_052129
  · exact g32p_supplierForest_actual_052130
  · exact g32p_supplierForest_actual_052145
  · exact g32p_supplierForest_actual_052226
  · exact g32p_supplierForest_actual_052249
  · exact g32p_supplierForest_actual_052253
  · exact g32p_supplierForest_actual_052299
  · exact g32p_supplierForest_actual_052304
  · exact g32p_supplierForest_actual_052322
  · exact g32p_supplierForest_actual_052325
  · exact g32p_supplierForest_actual_052333
  · exact g32p_supplierForest_actual_052337
  · exact g32p_supplierForest_actual_052349
  · exact g32p_supplierForest_actual_052372
  · exact g32p_supplierForest_actual_052389
  · exact g32p_supplierForest_actual_052427
  · exact g32p_supplierForest_actual_052475
  · exact g32p_supplierForest_actual_052484
  · exact g32p_supplierForest_actual_052499
  · exact g32p_supplierForest_actual_052536
  · exact g32p_supplierForest_actual_052544
  · exact g32p_supplierForest_actual_052560
  · exact g32p_supplierForest_actual_052563
  · exact g32p_supplierForest_actual_052573
  · exact g32p_supplierForest_actual_052577
  · exact g32p_supplierForest_actual_052610
  · exact g32p_supplierForest_actual_052625
  · exact g32p_supplierForest_actual_052649
  · exact g32p_supplierForest_actual_052745
  · exact g32p_supplierForest_actual_052790
  · exact g32p_supplierForest_actual_052822
  · exact g32p_supplierForest_actual_052825
  · exact g32p_supplierForest_actual_052866
  · exact g32p_supplierForest_actual_052880
  · exact g32p_supplierForest_actual_052896
  · exact g32p_supplierForest_actual_052898
  · exact g32p_supplierForest_actual_052903
  · exact g32p_supplierForest_actual_052916
  · exact g32p_supplierForest_actual_052918
  · exact g32p_supplierForest_actual_052925
  · exact g32p_supplierForest_actual_052990
  · exact g32p_supplierForest_actual_052994
  · exact g32p_supplierForest_actual_053004
  · exact g32p_supplierForest_actual_053028
  · exact g32p_supplierForest_actual_053040
  · exact g32p_supplierForest_actual_053050
  · exact g32p_supplierForest_actual_053075
  · exact g32p_supplierForest_actual_053076
  · exact g32p_supplierForest_actual_053087
  · exact g32p_supplierForest_actual_053103
  · exact g32p_supplierForest_actual_053138
  · exact g32p_supplierForest_actual_053178
  · exact g32p_supplierForest_actual_053208
  · exact g32p_supplierForest_actual_053283
  · exact g32p_supplierForest_actual_053289
  · exact g32p_supplierForest_actual_053305
  · exact g32p_supplierForest_actual_053390
  · exact g32p_supplierForest_actual_053426
  · exact g32p_supplierForest_actual_053452
  · exact g32p_supplierForest_actual_053456
  · exact g32p_supplierForest_actual_053510
  · exact g32p_supplierForest_actual_053524
  · exact g32p_supplierForest_actual_053529
  · exact g32p_supplierForest_actual_053565
  · exact g32p_supplierForest_actual_053569
  · exact g32p_supplierForest_actual_053573
  · exact g32p_supplierForest_actual_053575
  · exact g32p_supplierForest_actual_053590
  · exact g32p_supplierForest_actual_053605
  · exact g32p_supplierForest_actual_053612
  · exact g32p_supplierForest_actual_053632
  · exact g32p_supplierForest_actual_053665
  · exact g32p_supplierForest_actual_053680
  · exact g32p_supplierForest_actual_053715
  · exact g32p_supplierForest_actual_053718
  · exact g32p_supplierForest_actual_053721
  · exact g32p_supplierForest_actual_053754
  · exact g32p_supplierForest_actual_053800
  · exact g32p_supplierForest_actual_053833
  · exact g32p_supplierForest_actual_053841
  · exact g32p_supplierForest_actual_053902
  · exact g32p_supplierForest_actual_053929
  · exact g32p_supplierForest_actual_053950
  · exact g32p_supplierForest_actual_053987
  · exact g32p_supplierForest_actual_053988
  · exact g32p_supplierForest_actual_054018
  · exact g32p_supplierForest_actual_054023
  · exact g32p_supplierForest_actual_054030
  · exact g32p_supplierForest_actual_054031
  · exact g32p_supplierForest_actual_054038
  · exact g32p_supplierForest_actual_054045
  · exact g32p_supplierForest_actual_054059
  · exact g32p_supplierForest_actual_054061
  · exact g32p_supplierForest_actual_054187
  · exact g32p_supplierForest_actual_054194
  · exact g32p_supplierForest_actual_054231
  · exact g32p_supplierForest_actual_054234
  · exact g32p_supplierForest_actual_054254
  · exact g32p_supplierForest_actual_054259
  · exact g32p_supplierForest_actual_054266
  · exact g32p_supplierForest_actual_054290
  · exact g32p_supplierForest_actual_054304
  · exact g32p_supplierForest_actual_054334
  · exact g32p_supplierForest_actual_054338
  · exact g32p_supplierForest_actual_054372
  · exact g32p_supplierForest_actual_054470
  · exact g32p_supplierForest_actual_054471
  · exact g32p_supplierForest_actual_054496
  · exact g32p_supplierForest_actual_054505
  · exact g32p_supplierForest_actual_054507
  · exact g32p_supplierForest_actual_054527
  · exact g32p_supplierForest_actual_054528
  · exact g32p_supplierForest_actual_054588
  · exact g32p_supplierForest_actual_054638
  · exact g32p_supplierForest_actual_054665
  · exact g32p_supplierForest_actual_054717
  · exact g32p_supplierForest_actual_054749
  · exact g32p_supplierForest_actual_054751
  · exact g32p_supplierForest_actual_054753
  · exact g32p_supplierForest_actual_054798
  · exact g32p_supplierForest_actual_054839
  · exact g32p_supplierForest_actual_054896
  · exact g32p_supplierForest_actual_054919
  · exact g32p_supplierForest_actual_054964
  · exact g32p_supplierForest_actual_054971
  · exact g32p_supplierForest_actual_054993
  · exact g32p_supplierForest_actual_055001
  · exact g32p_supplierForest_actual_055008
  · exact g32p_supplierForest_actual_055011
  · exact g32p_supplierForest_actual_055015
  · exact g32p_supplierForest_actual_055024
  · exact g32p_supplierForest_actual_055029
  · exact g32p_supplierForest_actual_055057
  · exact g32p_supplierForest_actual_055061
  · exact g32p_supplierForest_actual_055113
  · exact g32p_supplierForest_actual_055114
  · exact g32p_supplierForest_actual_055160
  · exact g32p_supplierForest_actual_055173
  · exact g32p_supplierForest_actual_055247
  · exact g32p_supplierForest_actual_055253
  · exact g32p_supplierForest_actual_055264
  · exact g32p_supplierForest_actual_055289
  · exact g32p_supplierForest_actual_055299
  · exact g32p_supplierForest_actual_055329
  · exact g32p_supplierForest_actual_055342
  · exact g32p_supplierForest_actual_055388
  · exact g32p_supplierForest_actual_055407
  · exact g32p_supplierForest_actual_055426
  · exact g32p_supplierForest_actual_055437
  · exact g32p_supplierForest_actual_055441
  · exact g32p_supplierForest_actual_055483
  · exact g32p_supplierForest_actual_055489
  · exact g32p_supplierForest_actual_055563
  · exact g32p_supplierForest_actual_055569
  · exact g32p_supplierForest_actual_055578
  · exact g32p_supplierForest_actual_055592
  · exact g32p_supplierForest_actual_055598
  · exact g32p_supplierForest_actual_055623
  · exact g32p_supplierForest_actual_055655
  · exact g32p_supplierForest_actual_055686
  · exact g32p_supplierForest_actual_055691
  · exact g32p_supplierForest_actual_055693
  · exact g32p_supplierForest_actual_055706
  · exact g32p_supplierForest_actual_055711
  · exact g32p_supplierForest_actual_055725
  · exact g32p_supplierForest_actual_055741
  · exact g32p_supplierForest_actual_055753
  · exact g32p_supplierForest_actual_055810
  · exact g32p_supplierForest_actual_055829
  · exact g32p_supplierForest_actual_055847
  · exact g32p_supplierForest_actual_055871
  · exact g32p_supplierForest_actual_055998
  · exact g32p_supplierForest_actual_056025
  · exact g32p_supplierForest_actual_056027
  · exact g32p_supplierForest_actual_056036
  · exact g32p_supplierForest_actual_056066
  · exact g32p_supplierForest_actual_056067
  · exact g32p_supplierForest_actual_056082
  · exact g32p_supplierForest_actual_056096
  · exact g32p_supplierForest_actual_056133
  · exact g32p_supplierForest_actual_056154
  · exact g32p_supplierForest_actual_056155
  · exact g32p_supplierForest_actual_056172
  · exact g32p_supplierForest_actual_056176
  · exact g32p_supplierForest_actual_056194
  · exact g32p_supplierForest_actual_056206
  · exact g32p_supplierForest_actual_056215
  · exact g32p_supplierForest_actual_056235
  · exact g32p_supplierForest_actual_056238
  · exact g32p_supplierForest_actual_056302
  · exact g32p_supplierForest_actual_056347
  · exact g32p_supplierForest_actual_056367
  · exact g32p_supplierForest_actual_056370
  · exact g32p_supplierForest_actual_056417
  · exact g32p_supplierForest_actual_056449
  · exact g32p_supplierForest_actual_056461
  · exact g32p_supplierForest_actual_056468
  · exact g32p_supplierForest_actual_056473
  · exact g32p_supplierForest_actual_056477
  · exact g32p_supplierForest_actual_056528
  · exact g32p_supplierForest_actual_056564
  · exact g32p_supplierForest_actual_056603
  · exact g32p_supplierForest_actual_056671
  · exact g32p_supplierForest_actual_056735
  · exact g32p_supplierForest_actual_056793
  · exact g32p_supplierForest_actual_056801
  · exact g32p_supplierForest_actual_056803
  · exact g32p_supplierForest_actual_056810
  · exact g32p_supplierForest_actual_056884
  · exact g32p_supplierForest_actual_056897
  · exact g32p_supplierForest_actual_056907
  · exact g32p_supplierForest_actual_056916
  · exact g32p_supplierForest_actual_056918
  · exact g32p_supplierForest_actual_056963
  · exact g32p_supplierForest_actual_056968
  · exact g32p_supplierForest_actual_056977

def g32p_supplierForest_nodes_041 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_056982 else g32p_supplierForest_node_057061) else (if i.val < 3 then g32p_supplierForest_node_057138 else g32p_supplierForest_node_057141)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_057159 else g32p_supplierForest_node_057166) else (if i.val < 7 then g32p_supplierForest_node_057169 else g32p_supplierForest_node_057170))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_057181 else g32p_supplierForest_node_057193) else (if i.val < 11 then g32p_supplierForest_node_057211 else g32p_supplierForest_node_057219)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_057248 else g32p_supplierForest_node_057251) else (if i.val < 15 then g32p_supplierForest_node_057264 else g32p_supplierForest_node_057294)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_057303 else g32p_supplierForest_node_057310) else (if i.val < 19 then g32p_supplierForest_node_057327 else g32p_supplierForest_node_057329)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_057334 else g32p_supplierForest_node_057336) else (if i.val < 23 then g32p_supplierForest_node_057362 else g32p_supplierForest_node_057369))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_057375 else g32p_supplierForest_node_057401) else (if i.val < 27 then g32p_supplierForest_node_057403 else g32p_supplierForest_node_057460)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_057474 else g32p_supplierForest_node_057525) else (if i.val < 31 then g32p_supplierForest_node_057545 else g32p_supplierForest_node_057559))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_057584 else g32p_supplierForest_node_057604) else (if i.val < 35 then g32p_supplierForest_node_057657 else g32p_supplierForest_node_057663)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_057703 else g32p_supplierForest_node_057732) else (if i.val < 39 then g32p_supplierForest_node_057739 else g32p_supplierForest_node_057753))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_057768 else g32p_supplierForest_node_057790) else (if i.val < 43 then g32p_supplierForest_node_057805 else g32p_supplierForest_node_057813)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_057819 else g32p_supplierForest_node_057828) else (if i.val < 47 then g32p_supplierForest_node_057835 else g32p_supplierForest_node_057836)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_057840 else g32p_supplierForest_node_057844) else (if i.val < 51 then g32p_supplierForest_node_057875 else g32p_supplierForest_node_057899)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_057925 else g32p_supplierForest_node_057937) else (if i.val < 55 then g32p_supplierForest_node_057970 else g32p_supplierForest_node_057999))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_058016 else g32p_supplierForest_node_058035) else (if i.val < 59 then g32p_supplierForest_node_058079 else g32p_supplierForest_node_058092)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_058167 else g32p_supplierForest_node_058177) else (if i.val < 63 then g32p_supplierForest_node_058185 else g32p_supplierForest_node_058188)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_058266 else g32p_supplierForest_node_058387) else (if i.val < 67 then g32p_supplierForest_node_058424 else g32p_supplierForest_node_058429)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_058430 else g32p_supplierForest_node_058452) else (if i.val < 71 then g32p_supplierForest_node_058494 else g32p_supplierForest_node_058601))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_058603 else g32p_supplierForest_node_058605) else (if i.val < 75 then g32p_supplierForest_node_058607 else g32p_supplierForest_node_058633)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_058690 else g32p_supplierForest_node_058831) else (if i.val < 79 then g32p_supplierForest_node_058882 else g32p_supplierForest_node_058898)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_058945 else g32p_supplierForest_node_058954) else (if i.val < 83 then g32p_supplierForest_node_058972 else g32p_supplierForest_node_058982)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_059001 else g32p_supplierForest_node_059042) else (if i.val < 87 then g32p_supplierForest_node_059062 else g32p_supplierForest_node_059091))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_059167 else g32p_supplierForest_node_059196) else (if i.val < 91 then g32p_supplierForest_node_059216 else g32p_supplierForest_node_059217)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_059256 else g32p_supplierForest_node_059258) else (if i.val < 95 then g32p_supplierForest_node_059270 else g32p_supplierForest_node_059295))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_059305 else g32p_supplierForest_node_059336) else (if i.val < 99 then g32p_supplierForest_node_059419 else g32p_supplierForest_node_059475)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_059486 else g32p_supplierForest_node_059498) else (if i.val < 103 then g32p_supplierForest_node_059509 else g32p_supplierForest_node_059514))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_059518 else g32p_supplierForest_node_059603) else (if i.val < 107 then g32p_supplierForest_node_059639 else g32p_supplierForest_node_059644)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_059722 else g32p_supplierForest_node_059733) else (if i.val < 111 then g32p_supplierForest_node_059734 else g32p_supplierForest_node_059766)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_059783 else g32p_supplierForest_node_059799) else (if i.val < 115 then g32p_supplierForest_node_059823 else g32p_supplierForest_node_059824)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_059830 else g32p_supplierForest_node_059850) else (if i.val < 119 then g32p_supplierForest_node_059925 else g32p_supplierForest_node_059928))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_059939 else g32p_supplierForest_node_060016) else (if i.val < 123 then g32p_supplierForest_node_060032 else g32p_supplierForest_node_060057)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_060089 else g32p_supplierForest_node_060095) else (if i.val < 127 then g32p_supplierForest_node_060101 else g32p_supplierForest_node_060140))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_060155 else g32p_supplierForest_node_060165) else (if i.val < 131 then g32p_supplierForest_node_060202 else g32p_supplierForest_node_060227)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_060253 else g32p_supplierForest_node_060257) else (if i.val < 135 then g32p_supplierForest_node_060276 else g32p_supplierForest_node_060284))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_060294 else g32p_supplierForest_node_060348) else (if i.val < 139 then g32p_supplierForest_node_060349 else g32p_supplierForest_node_060372)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_060397 else g32p_supplierForest_node_060455) else (if i.val < 143 then g32p_supplierForest_node_060583 else g32p_supplierForest_node_060611)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_060618 else g32p_supplierForest_node_060637) else (if i.val < 147 then g32p_supplierForest_node_060645 else g32p_supplierForest_node_060662)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_060675 else g32p_supplierForest_node_060711) else (if i.val < 151 then g32p_supplierForest_node_060735 else g32p_supplierForest_node_060738))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_060740 else g32p_supplierForest_node_060745) else (if i.val < 155 then g32p_supplierForest_node_060800 else g32p_supplierForest_node_060801)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_060871 else g32p_supplierForest_node_060902) else (if i.val < 159 then g32p_supplierForest_node_060929 else g32p_supplierForest_node_060944))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_060980 else g32p_supplierForest_node_060999) else (if i.val < 163 then g32p_supplierForest_node_061017 else g32p_supplierForest_node_061024)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_061043 else g32p_supplierForest_node_061081) else (if i.val < 167 then g32p_supplierForest_node_061088 else g32p_supplierForest_node_061103))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_061149 else g32p_supplierForest_node_061169) else (if i.val < 171 then g32p_supplierForest_node_061194 else g32p_supplierForest_node_061231)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_061251 else g32p_supplierForest_node_061289) else (if i.val < 175 then g32p_supplierForest_node_061310 else g32p_supplierForest_node_061360)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_061387 else g32p_supplierForest_node_061401) else (if i.val < 179 then g32p_supplierForest_node_061444 else g32p_supplierForest_node_061521)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_061523 else g32p_supplierForest_node_061529) else (if i.val < 183 then g32p_supplierForest_node_061531 else g32p_supplierForest_node_061534))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_061539 else g32p_supplierForest_node_061543) else (if i.val < 187 then g32p_supplierForest_node_061548 else g32p_supplierForest_node_061550)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_061566 else g32p_supplierForest_node_061606) else (if i.val < 191 then g32p_supplierForest_node_061625 else g32p_supplierForest_node_061632)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_061764 else g32p_supplierForest_node_061771) else (if i.val < 195 then g32p_supplierForest_node_061782 else g32p_supplierForest_node_061783)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_061789 else g32p_supplierForest_node_061804) else (if i.val < 199 then g32p_supplierForest_node_061852 else g32p_supplierForest_node_061854))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_061855 else g32p_supplierForest_node_061899) else (if i.val < 203 then g32p_supplierForest_node_061900 else g32p_supplierForest_node_061903)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_061941 else g32p_supplierForest_node_061947) else (if i.val < 207 then g32p_supplierForest_node_061991 else g32p_supplierForest_node_061993)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_062019 else g32p_supplierForest_node_062031) else (if i.val < 211 then g32p_supplierForest_node_062068 else g32p_supplierForest_node_062095)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_062152 else g32p_supplierForest_node_062187) else (if i.val < 215 then g32p_supplierForest_node_062203 else g32p_supplierForest_node_062219))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_062224 else g32p_supplierForest_node_062280) else (if i.val < 219 then g32p_supplierForest_node_062290 else g32p_supplierForest_node_062301)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_062317 else g32p_supplierForest_node_062324) else (if i.val < 223 then g32p_supplierForest_node_062337 else g32p_supplierForest_node_062338))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_062340 else g32p_supplierForest_node_062374) else (if i.val < 227 then g32p_supplierForest_node_062400 else g32p_supplierForest_node_062463)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_062495 else g32p_supplierForest_node_062501) else (if i.val < 231 then g32p_supplierForest_node_062556 else g32p_supplierForest_node_062575))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_062635 else g32p_supplierForest_node_062659) else (if i.val < 235 then g32p_supplierForest_node_062792 else g32p_supplierForest_node_062797)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_062856 else g32p_supplierForest_node_062868) else (if i.val < 239 then g32p_supplierForest_node_062901 else g32p_supplierForest_node_062917)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_062955 else g32p_supplierForest_node_062991) else (if i.val < 243 then g32p_supplierForest_node_063007 else g32p_supplierForest_node_063057)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_063059 else g32p_supplierForest_node_063078) else (if i.val < 247 then g32p_supplierForest_node_063104 else g32p_supplierForest_node_063113))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_063128 else g32p_supplierForest_node_063133) else (if i.val < 251 then g32p_supplierForest_node_063154 else g32p_supplierForest_node_063168)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_063197 else g32p_supplierForest_node_063206) else (if i.val < 255 then g32p_supplierForest_node_063214 else g32p_supplierForest_node_063222))))))))

def g32p_supplierForest_classes_041 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 69 else 43) else (if i.val < 3 then 21 else 74)) else (if i.val < 6 then (if i.val < 5 then 40 else 69) else (if i.val < 7 then 69 else 75))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 39) else (if i.val < 11 then 40 else 74)) else (if i.val < 14 then (if i.val < 13 then 73 else 75) else (if i.val < 15 then 68 else 74)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 69 else 42) else (if i.val < 19 then 73 else 78)) else (if i.val < 22 then (if i.val < 21 then 71 else 75) else (if i.val < 23 then 40 else 74))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 38 else 69) else (if i.val < 27 then 74 else 69)) else (if i.val < 30 then (if i.val < 29 then 73 else 75) else (if i.val < 31 then 79 else 73))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 69 else 74) else (if i.val < 35 then 21 else 72)) else (if i.val < 38 then (if i.val < 37 then 43 else 74) else (if i.val < 39 then 75 else 6))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 39 else 22) else (if i.val < 43 then 38 else 22)) else (if i.val < 46 then (if i.val < 45 then 21 else 38) else (if i.val < 47 then 40 else 68)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 22 else 69) else (if i.val < 51 then 71 else 22)) else (if i.val < 54 then (if i.val < 53 then 40 else 40) else (if i.val < 55 then 68 else 73))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 22 else 69) else (if i.val < 59 then 42 else 21)) else (if i.val < 62 then (if i.val < 61 then 75 else 68) else (if i.val < 63 then 22 else 38)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 43 else 40) else (if i.val < 67 then 41 else 22)) else (if i.val < 70 then (if i.val < 69 then 22 else 21) else (if i.val < 71 then 21 else 38))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 75 else 43) else (if i.val < 75 then 38 else 69)) else (if i.val < 78 then (if i.val < 77 then 42 else 40) else (if i.val < 79 then 21 else 21)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 43 else 7) else (if i.val < 83 then 41 else 71)) else (if i.val < 86 then (if i.val < 85 then 79 else 21) else (if i.val < 87 then 20 else 69))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 41 else 39) else (if i.val < 91 then 21 else 21)) else (if i.val < 94 then (if i.val < 93 then 5 else 42) else (if i.val < 95 then 67 else 5))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 21 else 68) else (if i.val < 99 then 71 else 21)) else (if i.val < 102 then (if i.val < 101 then 73 else 74) else (if i.val < 103 then 41 else 21))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 43 else 21) else (if i.val < 107 then 39 else 75)) else (if i.val < 110 then (if i.val < 109 then 40 else 21) else (if i.val < 111 then 21 else 75)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 20 else 69) else (if i.val < 115 then 21 else 43)) else (if i.val < 118 then (if i.val < 117 then 74 else 40) else (if i.val < 119 then 22 else 6))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 41 else 41) else (if i.val < 123 then 38 else 6)) else (if i.val < 126 then (if i.val < 125 then 22 else 77) else (if i.val < 127 then 21 else 22))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 6 else 21) else (if i.val < 131 then 43 else 21)) else (if i.val < 134 then (if i.val < 133 then 41 else 43) else (if i.val < 135 then 71 else 70))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 19 else 38) else (if i.val < 139 then 21 else 38)) else (if i.val < 142 then (if i.val < 141 then 69 else 22) else (if i.val < 143 then 43 else 6)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 7 else 38) else (if i.val < 147 then 22 else 74)) else (if i.val < 150 then (if i.val < 149 then 71 else 21) else (if i.val < 151 then 22 else 38))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 43 else 21) else (if i.val < 155 then 42 else 23)) else (if i.val < 158 then (if i.val < 157 then 71 else 7) else (if i.val < 159 then 69 else 74))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 38 else 74) else (if i.val < 163 then 69 else 70)) else (if i.val < 166 then (if i.val < 165 then 19 else 68) else (if i.val < 167 then 21 else 40))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 38 else 68) else (if i.val < 171 then 69 else 38)) else (if i.val < 174 then (if i.val < 173 then 70 else 72) else (if i.val < 175 then 42 else 43)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 6 else 21) else (if i.val < 179 then 7 else 41)) else (if i.val < 182 then (if i.val < 181 then 40 else 38) else (if i.val < 183 then 39 else 38))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 43 else 39) else (if i.val < 187 then 40 else 43)) else (if i.val < 190 then (if i.val < 189 then 40 else 43) else (if i.val < 191 then 43 else 43)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 21 else 7) else (if i.val < 195 then 7 else 41)) else (if i.val < 198 then (if i.val < 197 then 79 else 41) else (if i.val < 199 then 74 else 21))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 75 else 74) else (if i.val < 203 then 21 else 21)) else (if i.val < 206 then (if i.val < 205 then 69 else 38) else (if i.val < 207 then 22 else 74)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 43 else 74) else (if i.val < 211 then 41 else 41)) else (if i.val < 214 then (if i.val < 213 then 18 else 22) else (if i.val < 215 then 38 else 38))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 78 else 43) else (if i.val < 219 then 69 else 69)) else (if i.val < 222 then (if i.val < 221 then 73 else 6) else (if i.val < 223 then 73 else 69))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 73 else 43) else (if i.val < 227 then 68 else 43)) else (if i.val < 230 then (if i.val < 229 then 38 else 69) else (if i.val < 231 then 78 else 74))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 72 else 75) else (if i.val < 235 then 69 else 43)) else (if i.val < 238 then (if i.val < 237 then 22 else 71) else (if i.val < 239 then 71 else 43)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 43 else 74) else (if i.val < 243 then 43 else 74)) else (if i.val < 246 then (if i.val < 245 then 22 else 71) else (if i.val < 247 then 23 else 38))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 73 else 70) else (if i.val < 251 then 38 else 69)) else (if i.val < 254 then (if i.val < 253 then 43 else 6) else (if i.val < 255 then 20 else 24))))))))

theorem g32p_supplierForest_actual_041 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_041 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_041 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_056982
  · exact g32p_supplierForest_actual_057061
  · exact g32p_supplierForest_actual_057138
  · exact g32p_supplierForest_actual_057141
  · exact g32p_supplierForest_actual_057159
  · exact g32p_supplierForest_actual_057166
  · exact g32p_supplierForest_actual_057169
  · exact g32p_supplierForest_actual_057170
  · exact g32p_supplierForest_actual_057181
  · exact g32p_supplierForest_actual_057193
  · exact g32p_supplierForest_actual_057211
  · exact g32p_supplierForest_actual_057219
  · exact g32p_supplierForest_actual_057248
  · exact g32p_supplierForest_actual_057251
  · exact g32p_supplierForest_actual_057264
  · exact g32p_supplierForest_actual_057294
  · exact g32p_supplierForest_actual_057303
  · exact g32p_supplierForest_actual_057310
  · exact g32p_supplierForest_actual_057327
  · exact g32p_supplierForest_actual_057329
  · exact g32p_supplierForest_actual_057334
  · exact g32p_supplierForest_actual_057336
  · exact g32p_supplierForest_actual_057362
  · exact g32p_supplierForest_actual_057369
  · exact g32p_supplierForest_actual_057375
  · exact g32p_supplierForest_actual_057401
  · exact g32p_supplierForest_actual_057403
  · exact g32p_supplierForest_actual_057460
  · exact g32p_supplierForest_actual_057474
  · exact g32p_supplierForest_actual_057525
  · exact g32p_supplierForest_actual_057545
  · exact g32p_supplierForest_actual_057559
  · exact g32p_supplierForest_actual_057584
  · exact g32p_supplierForest_actual_057604
  · exact g32p_supplierForest_actual_057657
  · exact g32p_supplierForest_actual_057663
  · exact g32p_supplierForest_actual_057703
  · exact g32p_supplierForest_actual_057732
  · exact g32p_supplierForest_actual_057739
  · exact g32p_supplierForest_actual_057753
  · exact g32p_supplierForest_actual_057768
  · exact g32p_supplierForest_actual_057790
  · exact g32p_supplierForest_actual_057805
  · exact g32p_supplierForest_actual_057813
  · exact g32p_supplierForest_actual_057819
  · exact g32p_supplierForest_actual_057828
  · exact g32p_supplierForest_actual_057835
  · exact g32p_supplierForest_actual_057836
  · exact g32p_supplierForest_actual_057840
  · exact g32p_supplierForest_actual_057844
  · exact g32p_supplierForest_actual_057875
  · exact g32p_supplierForest_actual_057899
  · exact g32p_supplierForest_actual_057925
  · exact g32p_supplierForest_actual_057937
  · exact g32p_supplierForest_actual_057970
  · exact g32p_supplierForest_actual_057999
  · exact g32p_supplierForest_actual_058016
  · exact g32p_supplierForest_actual_058035
  · exact g32p_supplierForest_actual_058079
  · exact g32p_supplierForest_actual_058092
  · exact g32p_supplierForest_actual_058167
  · exact g32p_supplierForest_actual_058177
  · exact g32p_supplierForest_actual_058185
  · exact g32p_supplierForest_actual_058188
  · exact g32p_supplierForest_actual_058266
  · exact g32p_supplierForest_actual_058387
  · exact g32p_supplierForest_actual_058424
  · exact g32p_supplierForest_actual_058429
  · exact g32p_supplierForest_actual_058430
  · exact g32p_supplierForest_actual_058452
  · exact g32p_supplierForest_actual_058494
  · exact g32p_supplierForest_actual_058601
  · exact g32p_supplierForest_actual_058603
  · exact g32p_supplierForest_actual_058605
  · exact g32p_supplierForest_actual_058607
  · exact g32p_supplierForest_actual_058633
  · exact g32p_supplierForest_actual_058690
  · exact g32p_supplierForest_actual_058831
  · exact g32p_supplierForest_actual_058882
  · exact g32p_supplierForest_actual_058898
  · exact g32p_supplierForest_actual_058945
  · exact g32p_supplierForest_actual_058954
  · exact g32p_supplierForest_actual_058972
  · exact g32p_supplierForest_actual_058982
  · exact g32p_supplierForest_actual_059001
  · exact g32p_supplierForest_actual_059042
  · exact g32p_supplierForest_actual_059062
  · exact g32p_supplierForest_actual_059091
  · exact g32p_supplierForest_actual_059167
  · exact g32p_supplierForest_actual_059196
  · exact g32p_supplierForest_actual_059216
  · exact g32p_supplierForest_actual_059217
  · exact g32p_supplierForest_actual_059256
  · exact g32p_supplierForest_actual_059258
  · exact g32p_supplierForest_actual_059270
  · exact g32p_supplierForest_actual_059295
  · exact g32p_supplierForest_actual_059305
  · exact g32p_supplierForest_actual_059336
  · exact g32p_supplierForest_actual_059419
  · exact g32p_supplierForest_actual_059475
  · exact g32p_supplierForest_actual_059486
  · exact g32p_supplierForest_actual_059498
  · exact g32p_supplierForest_actual_059509
  · exact g32p_supplierForest_actual_059514
  · exact g32p_supplierForest_actual_059518
  · exact g32p_supplierForest_actual_059603
  · exact g32p_supplierForest_actual_059639
  · exact g32p_supplierForest_actual_059644
  · exact g32p_supplierForest_actual_059722
  · exact g32p_supplierForest_actual_059733
  · exact g32p_supplierForest_actual_059734
  · exact g32p_supplierForest_actual_059766
  · exact g32p_supplierForest_actual_059783
  · exact g32p_supplierForest_actual_059799
  · exact g32p_supplierForest_actual_059823
  · exact g32p_supplierForest_actual_059824
  · exact g32p_supplierForest_actual_059830
  · exact g32p_supplierForest_actual_059850
  · exact g32p_supplierForest_actual_059925
  · exact g32p_supplierForest_actual_059928
  · exact g32p_supplierForest_actual_059939
  · exact g32p_supplierForest_actual_060016
  · exact g32p_supplierForest_actual_060032
  · exact g32p_supplierForest_actual_060057
  · exact g32p_supplierForest_actual_060089
  · exact g32p_supplierForest_actual_060095
  · exact g32p_supplierForest_actual_060101
  · exact g32p_supplierForest_actual_060140
  · exact g32p_supplierForest_actual_060155
  · exact g32p_supplierForest_actual_060165
  · exact g32p_supplierForest_actual_060202
  · exact g32p_supplierForest_actual_060227
  · exact g32p_supplierForest_actual_060253
  · exact g32p_supplierForest_actual_060257
  · exact g32p_supplierForest_actual_060276
  · exact g32p_supplierForest_actual_060284
  · exact g32p_supplierForest_actual_060294
  · exact g32p_supplierForest_actual_060348
  · exact g32p_supplierForest_actual_060349
  · exact g32p_supplierForest_actual_060372
  · exact g32p_supplierForest_actual_060397
  · exact g32p_supplierForest_actual_060455
  · exact g32p_supplierForest_actual_060583
  · exact g32p_supplierForest_actual_060611
  · exact g32p_supplierForest_actual_060618
  · exact g32p_supplierForest_actual_060637
  · exact g32p_supplierForest_actual_060645
  · exact g32p_supplierForest_actual_060662
  · exact g32p_supplierForest_actual_060675
  · exact g32p_supplierForest_actual_060711
  · exact g32p_supplierForest_actual_060735
  · exact g32p_supplierForest_actual_060738
  · exact g32p_supplierForest_actual_060740
  · exact g32p_supplierForest_actual_060745
  · exact g32p_supplierForest_actual_060800
  · exact g32p_supplierForest_actual_060801
  · exact g32p_supplierForest_actual_060871
  · exact g32p_supplierForest_actual_060902
  · exact g32p_supplierForest_actual_060929
  · exact g32p_supplierForest_actual_060944
  · exact g32p_supplierForest_actual_060980
  · exact g32p_supplierForest_actual_060999
  · exact g32p_supplierForest_actual_061017
  · exact g32p_supplierForest_actual_061024
  · exact g32p_supplierForest_actual_061043
  · exact g32p_supplierForest_actual_061081
  · exact g32p_supplierForest_actual_061088
  · exact g32p_supplierForest_actual_061103
  · exact g32p_supplierForest_actual_061149
  · exact g32p_supplierForest_actual_061169
  · exact g32p_supplierForest_actual_061194
  · exact g32p_supplierForest_actual_061231
  · exact g32p_supplierForest_actual_061251
  · exact g32p_supplierForest_actual_061289
  · exact g32p_supplierForest_actual_061310
  · exact g32p_supplierForest_actual_061360
  · exact g32p_supplierForest_actual_061387
  · exact g32p_supplierForest_actual_061401
  · exact g32p_supplierForest_actual_061444
  · exact g32p_supplierForest_actual_061521
  · exact g32p_supplierForest_actual_061523
  · exact g32p_supplierForest_actual_061529
  · exact g32p_supplierForest_actual_061531
  · exact g32p_supplierForest_actual_061534
  · exact g32p_supplierForest_actual_061539
  · exact g32p_supplierForest_actual_061543
  · exact g32p_supplierForest_actual_061548
  · exact g32p_supplierForest_actual_061550
  · exact g32p_supplierForest_actual_061566
  · exact g32p_supplierForest_actual_061606
  · exact g32p_supplierForest_actual_061625
  · exact g32p_supplierForest_actual_061632
  · exact g32p_supplierForest_actual_061764
  · exact g32p_supplierForest_actual_061771
  · exact g32p_supplierForest_actual_061782
  · exact g32p_supplierForest_actual_061783
  · exact g32p_supplierForest_actual_061789
  · exact g32p_supplierForest_actual_061804
  · exact g32p_supplierForest_actual_061852
  · exact g32p_supplierForest_actual_061854
  · exact g32p_supplierForest_actual_061855
  · exact g32p_supplierForest_actual_061899
  · exact g32p_supplierForest_actual_061900
  · exact g32p_supplierForest_actual_061903
  · exact g32p_supplierForest_actual_061941
  · exact g32p_supplierForest_actual_061947
  · exact g32p_supplierForest_actual_061991
  · exact g32p_supplierForest_actual_061993
  · exact g32p_supplierForest_actual_062019
  · exact g32p_supplierForest_actual_062031
  · exact g32p_supplierForest_actual_062068
  · exact g32p_supplierForest_actual_062095
  · exact g32p_supplierForest_actual_062152
  · exact g32p_supplierForest_actual_062187
  · exact g32p_supplierForest_actual_062203
  · exact g32p_supplierForest_actual_062219
  · exact g32p_supplierForest_actual_062224
  · exact g32p_supplierForest_actual_062280
  · exact g32p_supplierForest_actual_062290
  · exact g32p_supplierForest_actual_062301
  · exact g32p_supplierForest_actual_062317
  · exact g32p_supplierForest_actual_062324
  · exact g32p_supplierForest_actual_062337
  · exact g32p_supplierForest_actual_062338
  · exact g32p_supplierForest_actual_062340
  · exact g32p_supplierForest_actual_062374
  · exact g32p_supplierForest_actual_062400
  · exact g32p_supplierForest_actual_062463
  · exact g32p_supplierForest_actual_062495
  · exact g32p_supplierForest_actual_062501
  · exact g32p_supplierForest_actual_062556
  · exact g32p_supplierForest_actual_062575
  · exact g32p_supplierForest_actual_062635
  · exact g32p_supplierForest_actual_062659
  · exact g32p_supplierForest_actual_062792
  · exact g32p_supplierForest_actual_062797
  · exact g32p_supplierForest_actual_062856
  · exact g32p_supplierForest_actual_062868
  · exact g32p_supplierForest_actual_062901
  · exact g32p_supplierForest_actual_062917
  · exact g32p_supplierForest_actual_062955
  · exact g32p_supplierForest_actual_062991
  · exact g32p_supplierForest_actual_063007
  · exact g32p_supplierForest_actual_063057
  · exact g32p_supplierForest_actual_063059
  · exact g32p_supplierForest_actual_063078
  · exact g32p_supplierForest_actual_063104
  · exact g32p_supplierForest_actual_063113
  · exact g32p_supplierForest_actual_063128
  · exact g32p_supplierForest_actual_063133
  · exact g32p_supplierForest_actual_063154
  · exact g32p_supplierForest_actual_063168
  · exact g32p_supplierForest_actual_063197
  · exact g32p_supplierForest_actual_063206
  · exact g32p_supplierForest_actual_063214
  · exact g32p_supplierForest_actual_063222

def g32p_supplierForest_nodes_042 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_063224 else g32p_supplierForest_node_063266) else (if i.val < 3 then g32p_supplierForest_node_063272 else g32p_supplierForest_node_063273)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_063293 else g32p_supplierForest_node_063307) else (if i.val < 7 then g32p_supplierForest_node_063310 else g32p_supplierForest_node_063333))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_063356 else g32p_supplierForest_node_063417) else (if i.val < 11 then g32p_supplierForest_node_063440 else g32p_supplierForest_node_063481)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_063482 else g32p_supplierForest_node_063484) else (if i.val < 15 then g32p_supplierForest_node_063495 else g32p_supplierForest_node_063502)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_063510 else g32p_supplierForest_node_063513) else (if i.val < 19 then g32p_supplierForest_node_063527 else g32p_supplierForest_node_063566)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_063589 else g32p_supplierForest_node_063605) else (if i.val < 23 then g32p_supplierForest_node_063629 else g32p_supplierForest_node_063655))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_063671 else g32p_supplierForest_node_063674) else (if i.val < 27 then g32p_supplierForest_node_063676 else g32p_supplierForest_node_063688)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_063693 else g32p_supplierForest_node_063722) else (if i.val < 31 then g32p_supplierForest_node_063729 else g32p_supplierForest_node_063900))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_063920 else g32p_supplierForest_node_064028) else (if i.val < 35 then g32p_supplierForest_node_064041 else g32p_supplierForest_node_064045)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_064056 else g32p_supplierForest_node_064075) else (if i.val < 39 then g32p_supplierForest_node_064183 else g32p_supplierForest_node_064202))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_064205 else g32p_supplierForest_node_064207) else (if i.val < 43 then g32p_supplierForest_node_064270 else g32p_supplierForest_node_064287)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_064355 else g32p_supplierForest_node_064360) else (if i.val < 47 then g32p_supplierForest_node_064379 else g32p_supplierForest_node_064412)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_064420 else g32p_supplierForest_node_064426) else (if i.val < 51 then g32p_supplierForest_node_064465 else g32p_supplierForest_node_064486)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_064526 else g32p_supplierForest_node_064531) else (if i.val < 55 then g32p_supplierForest_node_064546 else g32p_supplierForest_node_064592))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_064606 else g32p_supplierForest_node_064626) else (if i.val < 59 then g32p_supplierForest_node_064639 else g32p_supplierForest_node_064645)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_064666 else g32p_supplierForest_node_064674) else (if i.val < 63 then g32p_supplierForest_node_064718 else g32p_supplierForest_node_064721)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_064732 else g32p_supplierForest_node_064750) else (if i.val < 67 then g32p_supplierForest_node_064782 else g32p_supplierForest_node_064785)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_064832 else g32p_supplierForest_node_064838) else (if i.val < 71 then g32p_supplierForest_node_064868 else g32p_supplierForest_node_064886))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_064907 else g32p_supplierForest_node_064977) else (if i.val < 75 then g32p_supplierForest_node_064990 else g32p_supplierForest_node_065036)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_065129 else g32p_supplierForest_node_065190) else (if i.val < 79 then g32p_supplierForest_node_065202 else g32p_supplierForest_node_065213)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_065315 else g32p_supplierForest_node_065357) else (if i.val < 83 then g32p_supplierForest_node_065361 else g32p_supplierForest_node_065402)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_065412 else g32p_supplierForest_node_065413) else (if i.val < 87 then g32p_supplierForest_node_065419 else g32p_supplierForest_node_065421))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_065430 else g32p_supplierForest_node_065440) else (if i.val < 91 then g32p_supplierForest_node_065473 else g32p_supplierForest_node_065478)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_065494 else g32p_supplierForest_node_065500) else (if i.val < 95 then g32p_supplierForest_node_065506 else g32p_supplierForest_node_065520))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_065534 else g32p_supplierForest_node_065568) else (if i.val < 99 then g32p_supplierForest_node_065569 else g32p_supplierForest_node_065580)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_065587 else g32p_supplierForest_node_065610) else (if i.val < 103 then g32p_supplierForest_node_065633 else g32p_supplierForest_node_065636))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_065664 else g32p_supplierForest_node_065668) else (if i.val < 107 then g32p_supplierForest_node_065689 else g32p_supplierForest_node_065696)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_065709 else g32p_supplierForest_node_065716) else (if i.val < 111 then g32p_supplierForest_node_065719 else g32p_supplierForest_node_065731)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_065749 else g32p_supplierForest_node_065773) else (if i.val < 115 then g32p_supplierForest_node_065798 else g32p_supplierForest_node_065807)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_065818 else g32p_supplierForest_node_065866) else (if i.val < 119 then g32p_supplierForest_node_065877 else g32p_supplierForest_node_065888))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_065925 else g32p_supplierForest_node_065933) else (if i.val < 123 then g32p_supplierForest_node_065935 else g32p_supplierForest_node_065942)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_066003 else g32p_supplierForest_node_066034) else (if i.val < 127 then g32p_supplierForest_node_066035 else g32p_supplierForest_node_066091))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_066107 else g32p_supplierForest_node_066114) else (if i.val < 131 then g32p_supplierForest_node_066147 else g32p_supplierForest_node_066159)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_066175 else g32p_supplierForest_node_066202) else (if i.val < 135 then g32p_supplierForest_node_066241 else g32p_supplierForest_node_066246))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_066247 else g32p_supplierForest_node_066317) else (if i.val < 139 then g32p_supplierForest_node_066322 else g32p_supplierForest_node_066330)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_066371 else g32p_supplierForest_node_066414) else (if i.val < 143 then g32p_supplierForest_node_066453 else g32p_supplierForest_node_066469)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_066545 else g32p_supplierForest_node_066569) else (if i.val < 147 then g32p_supplierForest_node_066570 else g32p_supplierForest_node_066572)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_066573 else g32p_supplierForest_node_066587) else (if i.val < 151 then g32p_supplierForest_node_066592 else g32p_supplierForest_node_066609))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_066612 else g32p_supplierForest_node_066637) else (if i.val < 155 then g32p_supplierForest_node_066738 else g32p_supplierForest_node_066742)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_066754 else g32p_supplierForest_node_066756) else (if i.val < 159 then g32p_supplierForest_node_066808 else g32p_supplierForest_node_066824))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_066836 else g32p_supplierForest_node_066886) else (if i.val < 163 then g32p_supplierForest_node_066894 else g32p_supplierForest_node_066910)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_066913 else g32p_supplierForest_node_066927) else (if i.val < 167 then g32p_supplierForest_node_066978 else g32p_supplierForest_node_066989))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_066993 else g32p_supplierForest_node_067033) else (if i.val < 171 then g32p_supplierForest_node_067057 else g32p_supplierForest_node_067059)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_067096 else g32p_supplierForest_node_067134) else (if i.val < 175 then g32p_supplierForest_node_067185 else g32p_supplierForest_node_067198)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_067226 else g32p_supplierForest_node_067227) else (if i.val < 179 then g32p_supplierForest_node_067244 else g32p_supplierForest_node_067272)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_067284 else g32p_supplierForest_node_067316) else (if i.val < 183 then g32p_supplierForest_node_067385 else g32p_supplierForest_node_067396))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_067416 else g32p_supplierForest_node_067419) else (if i.val < 187 then g32p_supplierForest_node_067480 else g32p_supplierForest_node_067483)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_067514 else g32p_supplierForest_node_067535) else (if i.val < 191 then g32p_supplierForest_node_067562 else g32p_supplierForest_node_067585)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_067605 else g32p_supplierForest_node_067608) else (if i.val < 195 then g32p_supplierForest_node_067620 else g32p_supplierForest_node_067621)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_067681 else g32p_supplierForest_node_067685) else (if i.val < 199 then g32p_supplierForest_node_067690 else g32p_supplierForest_node_067697))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_067708 else g32p_supplierForest_node_067746) else (if i.val < 203 then g32p_supplierForest_node_067806 else g32p_supplierForest_node_067845)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_067847 else g32p_supplierForest_node_067849) else (if i.val < 207 then g32p_supplierForest_node_067852 else g32p_supplierForest_node_067854)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_067914 else g32p_supplierForest_node_067915) else (if i.val < 211 then g32p_supplierForest_node_067927 else g32p_supplierForest_node_067953)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_067961 else g32p_supplierForest_node_067966) else (if i.val < 215 then g32p_supplierForest_node_067972 else g32p_supplierForest_node_067987))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_068042 else g32p_supplierForest_node_068059) else (if i.val < 219 then g32p_supplierForest_node_068119 else g32p_supplierForest_node_068156)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_068197 else g32p_supplierForest_node_068209) else (if i.val < 223 then g32p_supplierForest_node_068231 else g32p_supplierForest_node_068246))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_068263 else g32p_supplierForest_node_068267) else (if i.val < 227 then g32p_supplierForest_node_068270 else g32p_supplierForest_node_068273)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_068288 else g32p_supplierForest_node_068290) else (if i.val < 231 then g32p_supplierForest_node_068297 else g32p_supplierForest_node_068306))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_068338 else g32p_supplierForest_node_068378) else (if i.val < 235 then g32p_supplierForest_node_068380 else g32p_supplierForest_node_068396)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_068427 else g32p_supplierForest_node_068429) else (if i.val < 239 then g32p_supplierForest_node_068450 else g32p_supplierForest_node_068464)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_068515 else g32p_supplierForest_node_068519) else (if i.val < 243 then g32p_supplierForest_node_068523 else g32p_supplierForest_node_068529)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_068552 else g32p_supplierForest_node_068558) else (if i.val < 247 then g32p_supplierForest_node_068563 else g32p_supplierForest_node_068568))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_068569 else g32p_supplierForest_node_068586) else (if i.val < 251 then g32p_supplierForest_node_068590 else g32p_supplierForest_node_068633)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_068635 else g32p_supplierForest_node_068636) else (if i.val < 255 then g32p_supplierForest_node_068664 else g32p_supplierForest_node_068667))))))))

def g32p_supplierForest_classes_042 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 23 else 40) else (if i.val < 3 then 20 else 41)) else (if i.val < 6 then (if i.val < 5 then 68 else 21) else (if i.val < 7 then 21 else 41))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 70 else 19) else (if i.val < 11 then 38 else 38)) else (if i.val < 14 then (if i.val < 13 then 38 else 69) else (if i.val < 15 then 42 else 23)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 71 else 22) else (if i.val < 19 then 38 else 22)) else (if i.val < 22 then (if i.val < 21 then 69 else 41) else (if i.val < 23 then 40 else 72))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 22 else 72) else (if i.val < 27 then 38 else 24)) else (if i.val < 30 then (if i.val < 29 then 22 else 42) else (if i.val < 31 then 20 else 41))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 5 else 23) else (if i.val < 35 then 72 else 6)) else (if i.val < 38 then (if i.val < 37 then 38 else 38) else (if i.val < 39 then 41 else 69))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 20 else 21) else (if i.val < 43 then 21 else 73)) else (if i.val < 46 then (if i.val < 45 then 20 else 38) else (if i.val < 47 then 73 else 7)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 23 else 74) else (if i.val < 51 then 22 else 72)) else (if i.val < 54 then (if i.val < 53 then 23 else 21) else (if i.val < 55 then 69 else 20))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 40) else (if i.val < 59 then 19 else 21)) else (if i.val < 62 then (if i.val < 61 then 68 else 38) else (if i.val < 63 then 68 else 78)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 68 else 69) else (if i.val < 67 then 20 else 74)) else (if i.val < 70 then (if i.val < 69 then 72 else 22) else (if i.val < 71 then 21 else 20))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 70 else 38) else (if i.val < 75 then 38 else 71)) else (if i.val < 78 then (if i.val < 77 then 73 else 70) else (if i.val < 79 then 43 else 39)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 43 else 38) else (if i.val < 83 then 69 else 43)) else (if i.val < 86 then (if i.val < 85 then 43 else 42) else (if i.val < 87 then 73 else 75))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 20 else 74) else (if i.val < 91 then 74 else 38)) else (if i.val < 94 then (if i.val < 93 then 43 else 43) else (if i.val < 95 then 21 else 21))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 24 else 6) else (if i.val < 99 then 71 else 21)) else (if i.val < 102 then (if i.val < 101 then 71 else 69) else (if i.val < 103 then 69 else 38))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 74 else 23) else (if i.val < 107 then 40 else 38)) else (if i.val < 110 then (if i.val < 109 then 21 else 38) else (if i.val < 111 then 43 else 73)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 73 else 68) else (if i.val < 115 then 73 else 21)) else (if i.val < 118 then (if i.val < 117 then 74 else 40) else (if i.val < 119 then 42 else 6))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 41 else 43) else (if i.val < 123 then 20 else 20)) else (if i.val < 126 then (if i.val < 125 then 42 else 22) else (if i.val < 127 then 74 else 43))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 38 else 38) else (if i.val < 131 then 38 else 21)) else (if i.val < 134 then (if i.val < 133 then 21 else 38) else (if i.val < 135 then 6 else 21))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 21 else 70) else (if i.val < 139 then 38 else 22)) else (if i.val < 142 then (if i.val < 141 then 43 else 21) else (if i.val < 143 then 69 else 70)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 69 else 74) else (if i.val < 147 then 74 else 6)) else (if i.val < 150 then (if i.val < 149 then 74 else 69) else (if i.val < 151 then 73 else 74))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 73 else 70) else (if i.val < 155 then 38 else 38)) else (if i.val < 158 then (if i.val < 157 then 43 else 41) else (if i.val < 159 then 74 else 68))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 69 else 38) else (if i.val < 163 then 20 else 69)) else (if i.val < 166 then (if i.val < 165 then 73 else 75) else (if i.val < 167 then 75 else 74))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 21 else 21) else (if i.val < 171 then 74 else 74)) else (if i.val < 174 then (if i.val < 173 then 41 else 70) else (if i.val < 175 then 38 else 21)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 38 else 42) else (if i.val < 179 then 21 else 69)) else (if i.val < 182 then (if i.val < 181 then 38 else 24) else (if i.val < 183 then 72 else 69))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 38 else 72) else (if i.val < 187 then 21 else 69)) else (if i.val < 190 then (if i.val < 189 then 21 else 42) else (if i.val < 191 then 74 else 18)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 43 else 43) else (if i.val < 195 then 43 else 43)) else (if i.val < 198 then (if i.val < 197 then 43 else 74) else (if i.val < 199 then 43 else 38))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 21 else 72) else (if i.val < 203 then 41 else 38)) else (if i.val < 206 then (if i.val < 205 then 74 else 71) else (if i.val < 207 then 38 else 74)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 68 else 21) else (if i.val < 211 then 69 else 43)) else (if i.val < 214 then (if i.val < 213 then 38 else 43) else (if i.val < 215 then 41 else 43))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 43 else 42) else (if i.val < 219 then 38 else 69)) else (if i.val < 222 then (if i.val < 221 then 41 else 38) else (if i.val < 223 then 21 else 72))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 6 else 69) else (if i.val < 227 then 75 else 38)) else (if i.val < 230 then (if i.val < 229 then 7 else 22) else (if i.val < 231 then 22 else 71))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 73 else 22) else (if i.val < 235 then 38 else 69)) else (if i.val < 238 then (if i.val < 237 then 43 else 43) else (if i.val < 239 then 73 else 21)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 74 else 68) else (if i.val < 243 then 73 else 21)) else (if i.val < 246 then (if i.val < 245 then 69 else 69) else (if i.val < 247 then 40 else 21))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 75 else 21) else (if i.val < 251 then 21 else 73)) else (if i.val < 254 then (if i.val < 253 then 69 else 22) else (if i.val < 255 then 69 else 7))))))))

theorem g32p_supplierForest_actual_042 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_042 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_042 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_063224
  · exact g32p_supplierForest_actual_063266
  · exact g32p_supplierForest_actual_063272
  · exact g32p_supplierForest_actual_063273
  · exact g32p_supplierForest_actual_063293
  · exact g32p_supplierForest_actual_063307
  · exact g32p_supplierForest_actual_063310
  · exact g32p_supplierForest_actual_063333
  · exact g32p_supplierForest_actual_063356
  · exact g32p_supplierForest_actual_063417
  · exact g32p_supplierForest_actual_063440
  · exact g32p_supplierForest_actual_063481
  · exact g32p_supplierForest_actual_063482
  · exact g32p_supplierForest_actual_063484
  · exact g32p_supplierForest_actual_063495
  · exact g32p_supplierForest_actual_063502
  · exact g32p_supplierForest_actual_063510
  · exact g32p_supplierForest_actual_063513
  · exact g32p_supplierForest_actual_063527
  · exact g32p_supplierForest_actual_063566
  · exact g32p_supplierForest_actual_063589
  · exact g32p_supplierForest_actual_063605
  · exact g32p_supplierForest_actual_063629
  · exact g32p_supplierForest_actual_063655
  · exact g32p_supplierForest_actual_063671
  · exact g32p_supplierForest_actual_063674
  · exact g32p_supplierForest_actual_063676
  · exact g32p_supplierForest_actual_063688
  · exact g32p_supplierForest_actual_063693
  · exact g32p_supplierForest_actual_063722
  · exact g32p_supplierForest_actual_063729
  · exact g32p_supplierForest_actual_063900
  · exact g32p_supplierForest_actual_063920
  · exact g32p_supplierForest_actual_064028
  · exact g32p_supplierForest_actual_064041
  · exact g32p_supplierForest_actual_064045
  · exact g32p_supplierForest_actual_064056
  · exact g32p_supplierForest_actual_064075
  · exact g32p_supplierForest_actual_064183
  · exact g32p_supplierForest_actual_064202
  · exact g32p_supplierForest_actual_064205
  · exact g32p_supplierForest_actual_064207
  · exact g32p_supplierForest_actual_064270
  · exact g32p_supplierForest_actual_064287
  · exact g32p_supplierForest_actual_064355
  · exact g32p_supplierForest_actual_064360
  · exact g32p_supplierForest_actual_064379
  · exact g32p_supplierForest_actual_064412
  · exact g32p_supplierForest_actual_064420
  · exact g32p_supplierForest_actual_064426
  · exact g32p_supplierForest_actual_064465
  · exact g32p_supplierForest_actual_064486
  · exact g32p_supplierForest_actual_064526
  · exact g32p_supplierForest_actual_064531
  · exact g32p_supplierForest_actual_064546
  · exact g32p_supplierForest_actual_064592
  · exact g32p_supplierForest_actual_064606
  · exact g32p_supplierForest_actual_064626
  · exact g32p_supplierForest_actual_064639
  · exact g32p_supplierForest_actual_064645
  · exact g32p_supplierForest_actual_064666
  · exact g32p_supplierForest_actual_064674
  · exact g32p_supplierForest_actual_064718
  · exact g32p_supplierForest_actual_064721
  · exact g32p_supplierForest_actual_064732
  · exact g32p_supplierForest_actual_064750
  · exact g32p_supplierForest_actual_064782
  · exact g32p_supplierForest_actual_064785
  · exact g32p_supplierForest_actual_064832
  · exact g32p_supplierForest_actual_064838
  · exact g32p_supplierForest_actual_064868
  · exact g32p_supplierForest_actual_064886
  · exact g32p_supplierForest_actual_064907
  · exact g32p_supplierForest_actual_064977
  · exact g32p_supplierForest_actual_064990
  · exact g32p_supplierForest_actual_065036
  · exact g32p_supplierForest_actual_065129
  · exact g32p_supplierForest_actual_065190
  · exact g32p_supplierForest_actual_065202
  · exact g32p_supplierForest_actual_065213
  · exact g32p_supplierForest_actual_065315
  · exact g32p_supplierForest_actual_065357
  · exact g32p_supplierForest_actual_065361
  · exact g32p_supplierForest_actual_065402
  · exact g32p_supplierForest_actual_065412
  · exact g32p_supplierForest_actual_065413
  · exact g32p_supplierForest_actual_065419
  · exact g32p_supplierForest_actual_065421
  · exact g32p_supplierForest_actual_065430
  · exact g32p_supplierForest_actual_065440
  · exact g32p_supplierForest_actual_065473
  · exact g32p_supplierForest_actual_065478
  · exact g32p_supplierForest_actual_065494
  · exact g32p_supplierForest_actual_065500
  · exact g32p_supplierForest_actual_065506
  · exact g32p_supplierForest_actual_065520
  · exact g32p_supplierForest_actual_065534
  · exact g32p_supplierForest_actual_065568
  · exact g32p_supplierForest_actual_065569
  · exact g32p_supplierForest_actual_065580
  · exact g32p_supplierForest_actual_065587
  · exact g32p_supplierForest_actual_065610
  · exact g32p_supplierForest_actual_065633
  · exact g32p_supplierForest_actual_065636
  · exact g32p_supplierForest_actual_065664
  · exact g32p_supplierForest_actual_065668
  · exact g32p_supplierForest_actual_065689
  · exact g32p_supplierForest_actual_065696
  · exact g32p_supplierForest_actual_065709
  · exact g32p_supplierForest_actual_065716
  · exact g32p_supplierForest_actual_065719
  · exact g32p_supplierForest_actual_065731
  · exact g32p_supplierForest_actual_065749
  · exact g32p_supplierForest_actual_065773
  · exact g32p_supplierForest_actual_065798
  · exact g32p_supplierForest_actual_065807
  · exact g32p_supplierForest_actual_065818
  · exact g32p_supplierForest_actual_065866
  · exact g32p_supplierForest_actual_065877
  · exact g32p_supplierForest_actual_065888
  · exact g32p_supplierForest_actual_065925
  · exact g32p_supplierForest_actual_065933
  · exact g32p_supplierForest_actual_065935
  · exact g32p_supplierForest_actual_065942
  · exact g32p_supplierForest_actual_066003
  · exact g32p_supplierForest_actual_066034
  · exact g32p_supplierForest_actual_066035
  · exact g32p_supplierForest_actual_066091
  · exact g32p_supplierForest_actual_066107
  · exact g32p_supplierForest_actual_066114
  · exact g32p_supplierForest_actual_066147
  · exact g32p_supplierForest_actual_066159
  · exact g32p_supplierForest_actual_066175
  · exact g32p_supplierForest_actual_066202
  · exact g32p_supplierForest_actual_066241
  · exact g32p_supplierForest_actual_066246
  · exact g32p_supplierForest_actual_066247
  · exact g32p_supplierForest_actual_066317
  · exact g32p_supplierForest_actual_066322
  · exact g32p_supplierForest_actual_066330
  · exact g32p_supplierForest_actual_066371
  · exact g32p_supplierForest_actual_066414
  · exact g32p_supplierForest_actual_066453
  · exact g32p_supplierForest_actual_066469
  · exact g32p_supplierForest_actual_066545
  · exact g32p_supplierForest_actual_066569
  · exact g32p_supplierForest_actual_066570
  · exact g32p_supplierForest_actual_066572
  · exact g32p_supplierForest_actual_066573
  · exact g32p_supplierForest_actual_066587
  · exact g32p_supplierForest_actual_066592
  · exact g32p_supplierForest_actual_066609
  · exact g32p_supplierForest_actual_066612
  · exact g32p_supplierForest_actual_066637
  · exact g32p_supplierForest_actual_066738
  · exact g32p_supplierForest_actual_066742
  · exact g32p_supplierForest_actual_066754
  · exact g32p_supplierForest_actual_066756
  · exact g32p_supplierForest_actual_066808
  · exact g32p_supplierForest_actual_066824
  · exact g32p_supplierForest_actual_066836
  · exact g32p_supplierForest_actual_066886
  · exact g32p_supplierForest_actual_066894
  · exact g32p_supplierForest_actual_066910
  · exact g32p_supplierForest_actual_066913
  · exact g32p_supplierForest_actual_066927
  · exact g32p_supplierForest_actual_066978
  · exact g32p_supplierForest_actual_066989
  · exact g32p_supplierForest_actual_066993
  · exact g32p_supplierForest_actual_067033
  · exact g32p_supplierForest_actual_067057
  · exact g32p_supplierForest_actual_067059
  · exact g32p_supplierForest_actual_067096
  · exact g32p_supplierForest_actual_067134
  · exact g32p_supplierForest_actual_067185
  · exact g32p_supplierForest_actual_067198
  · exact g32p_supplierForest_actual_067226
  · exact g32p_supplierForest_actual_067227
  · exact g32p_supplierForest_actual_067244
  · exact g32p_supplierForest_actual_067272
  · exact g32p_supplierForest_actual_067284
  · exact g32p_supplierForest_actual_067316
  · exact g32p_supplierForest_actual_067385
  · exact g32p_supplierForest_actual_067396
  · exact g32p_supplierForest_actual_067416
  · exact g32p_supplierForest_actual_067419
  · exact g32p_supplierForest_actual_067480
  · exact g32p_supplierForest_actual_067483
  · exact g32p_supplierForest_actual_067514
  · exact g32p_supplierForest_actual_067535
  · exact g32p_supplierForest_actual_067562
  · exact g32p_supplierForest_actual_067585
  · exact g32p_supplierForest_actual_067605
  · exact g32p_supplierForest_actual_067608
  · exact g32p_supplierForest_actual_067620
  · exact g32p_supplierForest_actual_067621
  · exact g32p_supplierForest_actual_067681
  · exact g32p_supplierForest_actual_067685
  · exact g32p_supplierForest_actual_067690
  · exact g32p_supplierForest_actual_067697
  · exact g32p_supplierForest_actual_067708
  · exact g32p_supplierForest_actual_067746
  · exact g32p_supplierForest_actual_067806
  · exact g32p_supplierForest_actual_067845
  · exact g32p_supplierForest_actual_067847
  · exact g32p_supplierForest_actual_067849
  · exact g32p_supplierForest_actual_067852
  · exact g32p_supplierForest_actual_067854
  · exact g32p_supplierForest_actual_067914
  · exact g32p_supplierForest_actual_067915
  · exact g32p_supplierForest_actual_067927
  · exact g32p_supplierForest_actual_067953
  · exact g32p_supplierForest_actual_067961
  · exact g32p_supplierForest_actual_067966
  · exact g32p_supplierForest_actual_067972
  · exact g32p_supplierForest_actual_067987
  · exact g32p_supplierForest_actual_068042
  · exact g32p_supplierForest_actual_068059
  · exact g32p_supplierForest_actual_068119
  · exact g32p_supplierForest_actual_068156
  · exact g32p_supplierForest_actual_068197
  · exact g32p_supplierForest_actual_068209
  · exact g32p_supplierForest_actual_068231
  · exact g32p_supplierForest_actual_068246
  · exact g32p_supplierForest_actual_068263
  · exact g32p_supplierForest_actual_068267
  · exact g32p_supplierForest_actual_068270
  · exact g32p_supplierForest_actual_068273
  · exact g32p_supplierForest_actual_068288
  · exact g32p_supplierForest_actual_068290
  · exact g32p_supplierForest_actual_068297
  · exact g32p_supplierForest_actual_068306
  · exact g32p_supplierForest_actual_068338
  · exact g32p_supplierForest_actual_068378
  · exact g32p_supplierForest_actual_068380
  · exact g32p_supplierForest_actual_068396
  · exact g32p_supplierForest_actual_068427
  · exact g32p_supplierForest_actual_068429
  · exact g32p_supplierForest_actual_068450
  · exact g32p_supplierForest_actual_068464
  · exact g32p_supplierForest_actual_068515
  · exact g32p_supplierForest_actual_068519
  · exact g32p_supplierForest_actual_068523
  · exact g32p_supplierForest_actual_068529
  · exact g32p_supplierForest_actual_068552
  · exact g32p_supplierForest_actual_068558
  · exact g32p_supplierForest_actual_068563
  · exact g32p_supplierForest_actual_068568
  · exact g32p_supplierForest_actual_068569
  · exact g32p_supplierForest_actual_068586
  · exact g32p_supplierForest_actual_068590
  · exact g32p_supplierForest_actual_068633
  · exact g32p_supplierForest_actual_068635
  · exact g32p_supplierForest_actual_068636
  · exact g32p_supplierForest_actual_068664
  · exact g32p_supplierForest_actual_068667

def g32p_supplierForest_nodes_043 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_068680 else g32p_supplierForest_node_068688) else (if i.val < 3 then g32p_supplierForest_node_068717 else g32p_supplierForest_node_068865)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_068869 else g32p_supplierForest_node_068928) else (if i.val < 7 then g32p_supplierForest_node_068931 else g32p_supplierForest_node_068975))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_068978 else g32p_supplierForest_node_068988) else (if i.val < 11 then g32p_supplierForest_node_069014 else g32p_supplierForest_node_069045)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_069103 else g32p_supplierForest_node_069109) else (if i.val < 15 then g32p_supplierForest_node_069140 else g32p_supplierForest_node_069146)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_069148 else g32p_supplierForest_node_069163) else (if i.val < 19 then g32p_supplierForest_node_069174 else g32p_supplierForest_node_069176)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_069178 else g32p_supplierForest_node_069216) else (if i.val < 23 then g32p_supplierForest_node_069236 else g32p_supplierForest_node_069247))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_069279 else g32p_supplierForest_node_069377) else (if i.val < 27 then g32p_supplierForest_node_069445 else g32p_supplierForest_node_069457)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_069517 else g32p_supplierForest_node_069524) else (if i.val < 31 then g32p_supplierForest_node_069584 else g32p_supplierForest_node_069586))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_069610 else g32p_supplierForest_node_069617) else (if i.val < 35 then g32p_supplierForest_node_069638 else g32p_supplierForest_node_069680)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_069764 else g32p_supplierForest_node_069787) else (if i.val < 39 then g32p_supplierForest_node_069792 else g32p_supplierForest_node_069831))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_069853 else g32p_supplierForest_node_069867) else (if i.val < 43 then g32p_supplierForest_node_069906 else g32p_supplierForest_node_069909)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_069929 else g32p_supplierForest_node_069943) else (if i.val < 47 then g32p_supplierForest_node_069945 else g32p_supplierForest_node_069955)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_069995 else g32p_supplierForest_node_070014) else (if i.val < 51 then g32p_supplierForest_node_070027 else g32p_supplierForest_node_070069)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_070071 else g32p_supplierForest_node_070086) else (if i.val < 55 then g32p_supplierForest_node_070119 else g32p_supplierForest_node_070197))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_070218 else g32p_supplierForest_node_070219) else (if i.val < 59 then g32p_supplierForest_node_070269 else g32p_supplierForest_node_070284)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_070295 else g32p_supplierForest_node_070326) else (if i.val < 63 then g32p_supplierForest_node_070339 else g32p_supplierForest_node_070352)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_070389 else g32p_supplierForest_node_070397) else (if i.val < 67 then g32p_supplierForest_node_070554 else g32p_supplierForest_node_070588)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_070591 else g32p_supplierForest_node_070592) else (if i.val < 71 then g32p_supplierForest_node_070595 else g32p_supplierForest_node_070605))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_070626 else g32p_supplierForest_node_070633) else (if i.val < 75 then g32p_supplierForest_node_070646 else g32p_supplierForest_node_070652)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_070690 else g32p_supplierForest_node_070693) else (if i.val < 79 then g32p_supplierForest_node_070733 else g32p_supplierForest_node_070760)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_070805 else g32p_supplierForest_node_070825) else (if i.val < 83 then g32p_supplierForest_node_070850 else g32p_supplierForest_node_070852)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_070889 else g32p_supplierForest_node_070896) else (if i.val < 87 then g32p_supplierForest_node_070997 else g32p_supplierForest_node_071040))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_071059 else g32p_supplierForest_node_071091) else (if i.val < 91 then g32p_supplierForest_node_071092 else g32p_supplierForest_node_071096)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_071121 else g32p_supplierForest_node_071143) else (if i.val < 95 then g32p_supplierForest_node_071175 else g32p_supplierForest_node_071193))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_071205 else g32p_supplierForest_node_071211) else (if i.val < 99 then g32p_supplierForest_node_071214 else g32p_supplierForest_node_071218)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_071221 else g32p_supplierForest_node_071240) else (if i.val < 103 then g32p_supplierForest_node_071278 else g32p_supplierForest_node_071286))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_071290 else g32p_supplierForest_node_071314) else (if i.val < 107 then g32p_supplierForest_node_071316 else g32p_supplierForest_node_071321)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_071326 else g32p_supplierForest_node_071329) else (if i.val < 111 then g32p_supplierForest_node_071335 else g32p_supplierForest_node_071365)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_071377 else g32p_supplierForest_node_071415) else (if i.val < 115 then g32p_supplierForest_node_071417 else g32p_supplierForest_node_071430)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_071456 else g32p_supplierForest_node_071490) else (if i.val < 119 then g32p_supplierForest_node_071539 else g32p_supplierForest_node_071556))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_071562 else g32p_supplierForest_node_071583) else (if i.val < 123 then g32p_supplierForest_node_071602 else g32p_supplierForest_node_071607)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_071688 else g32p_supplierForest_node_071692) else (if i.val < 127 then g32p_supplierForest_node_071741 else g32p_supplierForest_node_071790))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_071799 else g32p_supplierForest_node_071814) else (if i.val < 131 then g32p_supplierForest_node_071836 else g32p_supplierForest_node_071839)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_071844 else g32p_supplierForest_node_071856) else (if i.val < 135 then g32p_supplierForest_node_071874 else g32p_supplierForest_node_071879))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_071890 else g32p_supplierForest_node_071897) else (if i.val < 139 then g32p_supplierForest_node_071955 else g32p_supplierForest_node_071984)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_071995 else g32p_supplierForest_node_071997) else (if i.val < 143 then g32p_supplierForest_node_072024 else g32p_supplierForest_node_072069)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_072079 else g32p_supplierForest_node_072093) else (if i.val < 147 then g32p_supplierForest_node_072121 else g32p_supplierForest_node_072142)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_072172 else g32p_supplierForest_node_072180) else (if i.val < 151 then g32p_supplierForest_node_072226 else g32p_supplierForest_node_072227))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_072239 else g32p_supplierForest_node_072249) else (if i.val < 155 then g32p_supplierForest_node_072302 else g32p_supplierForest_node_072322)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_072346 else g32p_supplierForest_node_072361) else (if i.val < 159 then g32p_supplierForest_node_072399 else g32p_supplierForest_node_072404))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_072416 else g32p_supplierForest_node_072466) else (if i.val < 163 then g32p_supplierForest_node_072574 else g32p_supplierForest_node_072577)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_072583 else g32p_supplierForest_node_072618) else (if i.val < 167 then g32p_supplierForest_node_072636 else g32p_supplierForest_node_072647))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_072661 else g32p_supplierForest_node_072668) else (if i.val < 171 then g32p_supplierForest_node_072710 else g32p_supplierForest_node_072711)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_072781 else g32p_supplierForest_node_072784) else (if i.val < 175 then g32p_supplierForest_node_072801 else g32p_supplierForest_node_072804)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_072815 else g32p_supplierForest_node_072822) else (if i.val < 179 then g32p_supplierForest_node_072829 else g32p_supplierForest_node_072847)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_072895 else g32p_supplierForest_node_072962) else (if i.val < 183 then g32p_supplierForest_node_072982 else g32p_supplierForest_node_073034))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_073042 else g32p_supplierForest_node_073049) else (if i.val < 187 then g32p_supplierForest_node_073055 else g32p_supplierForest_node_073078)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_073091 else g32p_supplierForest_node_073107) else (if i.val < 191 then g32p_supplierForest_node_073123 else g32p_supplierForest_node_073146)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_073166 else g32p_supplierForest_node_073176) else (if i.val < 195 then g32p_supplierForest_node_073209 else g32p_supplierForest_node_073255)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_073283 else g32p_supplierForest_node_073292) else (if i.val < 199 then g32p_supplierForest_node_073299 else g32p_supplierForest_node_073311))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_073338 else g32p_supplierForest_node_073350) else (if i.val < 203 then g32p_supplierForest_node_073360 else g32p_supplierForest_node_073366)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_073368 else g32p_supplierForest_node_073393) else (if i.val < 207 then g32p_supplierForest_node_073398 else g32p_supplierForest_node_073453)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_073465 else g32p_supplierForest_node_073496) else (if i.val < 211 then g32p_supplierForest_node_073516 else g32p_supplierForest_node_073518)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_073528 else g32p_supplierForest_node_073545) else (if i.val < 215 then g32p_supplierForest_node_073588 else g32p_supplierForest_node_073592))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_073618 else g32p_supplierForest_node_073636) else (if i.val < 219 then g32p_supplierForest_node_073646 else g32p_supplierForest_node_073660)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_073662 else g32p_supplierForest_node_073675) else (if i.val < 223 then g32p_supplierForest_node_073699 else g32p_supplierForest_node_073733))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_073775 else g32p_supplierForest_node_073804) else (if i.val < 227 then g32p_supplierForest_node_073815 else g32p_supplierForest_node_073821)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_073893 else g32p_supplierForest_node_073974) else (if i.val < 231 then g32p_supplierForest_node_073978 else g32p_supplierForest_node_073991))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_073992 else g32p_supplierForest_node_074017) else (if i.val < 235 then g32p_supplierForest_node_074026 else g32p_supplierForest_node_074027)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_074032 else g32p_supplierForest_node_074045) else (if i.val < 239 then g32p_supplierForest_node_074079 else g32p_supplierForest_node_074091)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_074115 else g32p_supplierForest_node_074144) else (if i.val < 243 then g32p_supplierForest_node_074196 else g32p_supplierForest_node_074224)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_074282 else g32p_supplierForest_node_074286) else (if i.val < 247 then g32p_supplierForest_node_074308 else g32p_supplierForest_node_074311))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_074349 else g32p_supplierForest_node_074409) else (if i.val < 251 then g32p_supplierForest_node_074413 else g32p_supplierForest_node_074481)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_074499 else g32p_supplierForest_node_074597) else (if i.val < 255 then g32p_supplierForest_node_074605 else g32p_supplierForest_node_074611))))))))

def g32p_supplierForest_classes_043 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 6 else 38) else (if i.val < 3 then 20 else 71)) else (if i.val < 6 then (if i.val < 5 then 20 else 20) else (if i.val < 7 then 22 else 43))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 73 else 73) else (if i.val < 11 then 69 else 38)) else (if i.val < 14 then (if i.val < 13 then 71 else 6) else (if i.val < 15 then 43 else 43)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 42 else 22) else (if i.val < 19 then 21 else 20)) else (if i.val < 22 then (if i.val < 21 then 41 else 38) else (if i.val < 23 then 23 else 21))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 22 else 23) else (if i.val < 27 then 73 else 21)) else (if i.val < 30 then (if i.val < 29 then 74 else 21) else (if i.val < 31 then 73 else 75))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 41 else 21) else (if i.val < 35 then 69 else 75)) else (if i.val < 38 then (if i.val < 37 then 75 else 69) else (if i.val < 39 then 42 else 21))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 21 else 75) else (if i.val < 43 then 42 else 73)) else (if i.val < 46 then (if i.val < 45 then 6 else 38) else (if i.val < 47 then 21 else 39)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 22 else 38) else (if i.val < 51 then 42 else 43)) else (if i.val < 54 then (if i.val < 53 then 20 else 72) else (if i.val < 55 then 22 else 38))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 7 else 43) else (if i.val < 59 then 43 else 38)) else (if i.val < 62 then (if i.val < 61 then 7 else 69) else (if i.val < 63 then 42 else 43)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 21 else 21) else (if i.val < 67 then 43 else 43)) else (if i.val < 70 then (if i.val < 69 then 40 else 40) else (if i.val < 71 then 73 else 38))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 41 else 38) else (if i.val < 75 then 18 else 38)) else (if i.val < 78 then (if i.val < 77 then 43 else 74) else (if i.val < 79 then 67 else 43)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 70 else 41) else (if i.val < 83 then 38 else 67)) else (if i.val < 86 then (if i.val < 85 then 43 else 73) else (if i.val < 87 then 69 else 68))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 75 else 21) else (if i.val < 91 then 75 else 21)) else (if i.val < 94 then (if i.val < 93 then 75 else 69) else (if i.val < 95 then 43 else 38))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 21 else 43) else (if i.val < 99 then 21 else 73)) else (if i.val < 102 then (if i.val < 101 then 73 else 77) else (if i.val < 103 then 43 else 38))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 39 else 74) else (if i.val < 107 then 22 else 68)) else (if i.val < 110 then (if i.val < 109 then 71 else 43) else (if i.val < 111 then 73 else 22)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 21 else 38) else (if i.val < 115 then 20 else 6)) else (if i.val < 118 then (if i.val < 117 then 73 else 38) else (if i.val < 119 then 73 else 72))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 69 else 73) else (if i.val < 123 then 72 else 79)) else (if i.val < 126 then (if i.val < 125 then 23 else 20) else (if i.val < 127 then 20 else 47))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 49 else 26) else (if i.val < 131 then 45 else 13)) else (if i.val < 134 then (if i.val < 133 then 11 else 47) else (if i.val < 135 then 49 else 13))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 11 else 47) else (if i.val < 139 then 50 else 50)) else (if i.val < 142 then (if i.val < 141 then 53 else 49) else (if i.val < 143 then 49 else 50)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 50 else 13) else (if i.val < 147 then 50 else 48)) else (if i.val < 150 then (if i.val < 149 then 13 else 46) else (if i.val < 151 then 47 else 52))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 50 else 46) else (if i.val < 155 then 49 else 25)) else (if i.val < 158 then (if i.val < 157 then 83 else 11) else (if i.val < 159 then 53 else 13))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 52 else 50) else (if i.val < 163 then 49 else 56)) else (if i.val < 166 then (if i.val < 165 then 49 else 46) else (if i.val < 167 then 49 else 49))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 46 else 49) else (if i.val < 171 then 46 else 52)) else (if i.val < 174 then (if i.val < 173 then 49 else 46) else (if i.val < 175 then 49 else 50)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 13 else 49) else (if i.val < 179 then 49 else 49)) else (if i.val < 182 then (if i.val < 181 then 25 else 56) else (if i.val < 183 then 56 else 49))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 46 else 46) else (if i.val < 187 then 50 else 45)) else (if i.val < 190 then (if i.val < 189 then 49 else 10) else (if i.val < 191 then 46 else 13)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 12 else 48) else (if i.val < 195 then 48 else 27)) else (if i.val < 198 then (if i.val < 197 then 56 else 81) else (if i.val < 199 then 13 else 48))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 46 else 82) else (if i.val < 203 then 50 else 49)) else (if i.val < 206 then (if i.val < 205 then 49 else 13) else (if i.val < 207 then 83 else 46)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 13 else 53) else (if i.val < 211 then 46 else 50)) else (if i.val < 214 then (if i.val < 213 then 49 else 47) else (if i.val < 215 then 49 else 10))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 13 else 83) else (if i.val < 219 then 83 else 84)) else (if i.val < 222 then (if i.val < 221 then 46 else 27) else (if i.val < 223 then 26 else 10))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 83 else 49) else (if i.val < 227 then 25 else 13)) else (if i.val < 230 then (if i.val < 229 then 49 else 54) else (if i.val < 231 then 50 else 26))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 27 else 50) else (if i.val < 235 then 83 else 46)) else (if i.val < 238 then (if i.val < 237 then 13 else 25) else (if i.val < 239 then 13 else 13)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 46 else 13) else (if i.val < 243 then 83 else 46)) else (if i.val < 246 then (if i.val < 245 then 49 else 46) else (if i.val < 247 then 47 else 46))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 45 else 49) else (if i.val < 251 then 11 else 46)) else (if i.val < 254 then (if i.val < 253 then 11 else 46) else (if i.val < 255 then 26 else 10))))))))

theorem g32p_supplierForest_actual_043 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_043 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_043 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_068680
  · exact g32p_supplierForest_actual_068688
  · exact g32p_supplierForest_actual_068717
  · exact g32p_supplierForest_actual_068865
  · exact g32p_supplierForest_actual_068869
  · exact g32p_supplierForest_actual_068928
  · exact g32p_supplierForest_actual_068931
  · exact g32p_supplierForest_actual_068975
  · exact g32p_supplierForest_actual_068978
  · exact g32p_supplierForest_actual_068988
  · exact g32p_supplierForest_actual_069014
  · exact g32p_supplierForest_actual_069045
  · exact g32p_supplierForest_actual_069103
  · exact g32p_supplierForest_actual_069109
  · exact g32p_supplierForest_actual_069140
  · exact g32p_supplierForest_actual_069146
  · exact g32p_supplierForest_actual_069148
  · exact g32p_supplierForest_actual_069163
  · exact g32p_supplierForest_actual_069174
  · exact g32p_supplierForest_actual_069176
  · exact g32p_supplierForest_actual_069178
  · exact g32p_supplierForest_actual_069216
  · exact g32p_supplierForest_actual_069236
  · exact g32p_supplierForest_actual_069247
  · exact g32p_supplierForest_actual_069279
  · exact g32p_supplierForest_actual_069377
  · exact g32p_supplierForest_actual_069445
  · exact g32p_supplierForest_actual_069457
  · exact g32p_supplierForest_actual_069517
  · exact g32p_supplierForest_actual_069524
  · exact g32p_supplierForest_actual_069584
  · exact g32p_supplierForest_actual_069586
  · exact g32p_supplierForest_actual_069610
  · exact g32p_supplierForest_actual_069617
  · exact g32p_supplierForest_actual_069638
  · exact g32p_supplierForest_actual_069680
  · exact g32p_supplierForest_actual_069764
  · exact g32p_supplierForest_actual_069787
  · exact g32p_supplierForest_actual_069792
  · exact g32p_supplierForest_actual_069831
  · exact g32p_supplierForest_actual_069853
  · exact g32p_supplierForest_actual_069867
  · exact g32p_supplierForest_actual_069906
  · exact g32p_supplierForest_actual_069909
  · exact g32p_supplierForest_actual_069929
  · exact g32p_supplierForest_actual_069943
  · exact g32p_supplierForest_actual_069945
  · exact g32p_supplierForest_actual_069955
  · exact g32p_supplierForest_actual_069995
  · exact g32p_supplierForest_actual_070014
  · exact g32p_supplierForest_actual_070027
  · exact g32p_supplierForest_actual_070069
  · exact g32p_supplierForest_actual_070071
  · exact g32p_supplierForest_actual_070086
  · exact g32p_supplierForest_actual_070119
  · exact g32p_supplierForest_actual_070197
  · exact g32p_supplierForest_actual_070218
  · exact g32p_supplierForest_actual_070219
  · exact g32p_supplierForest_actual_070269
  · exact g32p_supplierForest_actual_070284
  · exact g32p_supplierForest_actual_070295
  · exact g32p_supplierForest_actual_070326
  · exact g32p_supplierForest_actual_070339
  · exact g32p_supplierForest_actual_070352
  · exact g32p_supplierForest_actual_070389
  · exact g32p_supplierForest_actual_070397
  · exact g32p_supplierForest_actual_070554
  · exact g32p_supplierForest_actual_070588
  · exact g32p_supplierForest_actual_070591
  · exact g32p_supplierForest_actual_070592
  · exact g32p_supplierForest_actual_070595
  · exact g32p_supplierForest_actual_070605
  · exact g32p_supplierForest_actual_070626
  · exact g32p_supplierForest_actual_070633
  · exact g32p_supplierForest_actual_070646
  · exact g32p_supplierForest_actual_070652
  · exact g32p_supplierForest_actual_070690
  · exact g32p_supplierForest_actual_070693
  · exact g32p_supplierForest_actual_070733
  · exact g32p_supplierForest_actual_070760
  · exact g32p_supplierForest_actual_070805
  · exact g32p_supplierForest_actual_070825
  · exact g32p_supplierForest_actual_070850
  · exact g32p_supplierForest_actual_070852
  · exact g32p_supplierForest_actual_070889
  · exact g32p_supplierForest_actual_070896
  · exact g32p_supplierForest_actual_070997
  · exact g32p_supplierForest_actual_071040
  · exact g32p_supplierForest_actual_071059
  · exact g32p_supplierForest_actual_071091
  · exact g32p_supplierForest_actual_071092
  · exact g32p_supplierForest_actual_071096
  · exact g32p_supplierForest_actual_071121
  · exact g32p_supplierForest_actual_071143
  · exact g32p_supplierForest_actual_071175
  · exact g32p_supplierForest_actual_071193
  · exact g32p_supplierForest_actual_071205
  · exact g32p_supplierForest_actual_071211
  · exact g32p_supplierForest_actual_071214
  · exact g32p_supplierForest_actual_071218
  · exact g32p_supplierForest_actual_071221
  · exact g32p_supplierForest_actual_071240
  · exact g32p_supplierForest_actual_071278
  · exact g32p_supplierForest_actual_071286
  · exact g32p_supplierForest_actual_071290
  · exact g32p_supplierForest_actual_071314
  · exact g32p_supplierForest_actual_071316
  · exact g32p_supplierForest_actual_071321
  · exact g32p_supplierForest_actual_071326
  · exact g32p_supplierForest_actual_071329
  · exact g32p_supplierForest_actual_071335
  · exact g32p_supplierForest_actual_071365
  · exact g32p_supplierForest_actual_071377
  · exact g32p_supplierForest_actual_071415
  · exact g32p_supplierForest_actual_071417
  · exact g32p_supplierForest_actual_071430
  · exact g32p_supplierForest_actual_071456
  · exact g32p_supplierForest_actual_071490
  · exact g32p_supplierForest_actual_071539
  · exact g32p_supplierForest_actual_071556
  · exact g32p_supplierForest_actual_071562
  · exact g32p_supplierForest_actual_071583
  · exact g32p_supplierForest_actual_071602
  · exact g32p_supplierForest_actual_071607
  · exact g32p_supplierForest_actual_071688
  · exact g32p_supplierForest_actual_071692
  · exact g32p_supplierForest_actual_071741
  · exact g32p_supplierForest_actual_071790
  · exact g32p_supplierForest_actual_071799
  · exact g32p_supplierForest_actual_071814
  · exact g32p_supplierForest_actual_071836
  · exact g32p_supplierForest_actual_071839
  · exact g32p_supplierForest_actual_071844
  · exact g32p_supplierForest_actual_071856
  · exact g32p_supplierForest_actual_071874
  · exact g32p_supplierForest_actual_071879
  · exact g32p_supplierForest_actual_071890
  · exact g32p_supplierForest_actual_071897
  · exact g32p_supplierForest_actual_071955
  · exact g32p_supplierForest_actual_071984
  · exact g32p_supplierForest_actual_071995
  · exact g32p_supplierForest_actual_071997
  · exact g32p_supplierForest_actual_072024
  · exact g32p_supplierForest_actual_072069
  · exact g32p_supplierForest_actual_072079
  · exact g32p_supplierForest_actual_072093
  · exact g32p_supplierForest_actual_072121
  · exact g32p_supplierForest_actual_072142
  · exact g32p_supplierForest_actual_072172
  · exact g32p_supplierForest_actual_072180
  · exact g32p_supplierForest_actual_072226
  · exact g32p_supplierForest_actual_072227
  · exact g32p_supplierForest_actual_072239
  · exact g32p_supplierForest_actual_072249
  · exact g32p_supplierForest_actual_072302
  · exact g32p_supplierForest_actual_072322
  · exact g32p_supplierForest_actual_072346
  · exact g32p_supplierForest_actual_072361
  · exact g32p_supplierForest_actual_072399
  · exact g32p_supplierForest_actual_072404
  · exact g32p_supplierForest_actual_072416
  · exact g32p_supplierForest_actual_072466
  · exact g32p_supplierForest_actual_072574
  · exact g32p_supplierForest_actual_072577
  · exact g32p_supplierForest_actual_072583
  · exact g32p_supplierForest_actual_072618
  · exact g32p_supplierForest_actual_072636
  · exact g32p_supplierForest_actual_072647
  · exact g32p_supplierForest_actual_072661
  · exact g32p_supplierForest_actual_072668
  · exact g32p_supplierForest_actual_072710
  · exact g32p_supplierForest_actual_072711
  · exact g32p_supplierForest_actual_072781
  · exact g32p_supplierForest_actual_072784
  · exact g32p_supplierForest_actual_072801
  · exact g32p_supplierForest_actual_072804
  · exact g32p_supplierForest_actual_072815
  · exact g32p_supplierForest_actual_072822
  · exact g32p_supplierForest_actual_072829
  · exact g32p_supplierForest_actual_072847
  · exact g32p_supplierForest_actual_072895
  · exact g32p_supplierForest_actual_072962
  · exact g32p_supplierForest_actual_072982
  · exact g32p_supplierForest_actual_073034
  · exact g32p_supplierForest_actual_073042
  · exact g32p_supplierForest_actual_073049
  · exact g32p_supplierForest_actual_073055
  · exact g32p_supplierForest_actual_073078
  · exact g32p_supplierForest_actual_073091
  · exact g32p_supplierForest_actual_073107
  · exact g32p_supplierForest_actual_073123
  · exact g32p_supplierForest_actual_073146
  · exact g32p_supplierForest_actual_073166
  · exact g32p_supplierForest_actual_073176
  · exact g32p_supplierForest_actual_073209
  · exact g32p_supplierForest_actual_073255
  · exact g32p_supplierForest_actual_073283
  · exact g32p_supplierForest_actual_073292
  · exact g32p_supplierForest_actual_073299
  · exact g32p_supplierForest_actual_073311
  · exact g32p_supplierForest_actual_073338
  · exact g32p_supplierForest_actual_073350
  · exact g32p_supplierForest_actual_073360
  · exact g32p_supplierForest_actual_073366
  · exact g32p_supplierForest_actual_073368
  · exact g32p_supplierForest_actual_073393
  · exact g32p_supplierForest_actual_073398
  · exact g32p_supplierForest_actual_073453
  · exact g32p_supplierForest_actual_073465
  · exact g32p_supplierForest_actual_073496
  · exact g32p_supplierForest_actual_073516
  · exact g32p_supplierForest_actual_073518
  · exact g32p_supplierForest_actual_073528
  · exact g32p_supplierForest_actual_073545
  · exact g32p_supplierForest_actual_073588
  · exact g32p_supplierForest_actual_073592
  · exact g32p_supplierForest_actual_073618
  · exact g32p_supplierForest_actual_073636
  · exact g32p_supplierForest_actual_073646
  · exact g32p_supplierForest_actual_073660
  · exact g32p_supplierForest_actual_073662
  · exact g32p_supplierForest_actual_073675
  · exact g32p_supplierForest_actual_073699
  · exact g32p_supplierForest_actual_073733
  · exact g32p_supplierForest_actual_073775
  · exact g32p_supplierForest_actual_073804
  · exact g32p_supplierForest_actual_073815
  · exact g32p_supplierForest_actual_073821
  · exact g32p_supplierForest_actual_073893
  · exact g32p_supplierForest_actual_073974
  · exact g32p_supplierForest_actual_073978
  · exact g32p_supplierForest_actual_073991
  · exact g32p_supplierForest_actual_073992
  · exact g32p_supplierForest_actual_074017
  · exact g32p_supplierForest_actual_074026
  · exact g32p_supplierForest_actual_074027
  · exact g32p_supplierForest_actual_074032
  · exact g32p_supplierForest_actual_074045
  · exact g32p_supplierForest_actual_074079
  · exact g32p_supplierForest_actual_074091
  · exact g32p_supplierForest_actual_074115
  · exact g32p_supplierForest_actual_074144
  · exact g32p_supplierForest_actual_074196
  · exact g32p_supplierForest_actual_074224
  · exact g32p_supplierForest_actual_074282
  · exact g32p_supplierForest_actual_074286
  · exact g32p_supplierForest_actual_074308
  · exact g32p_supplierForest_actual_074311
  · exact g32p_supplierForest_actual_074349
  · exact g32p_supplierForest_actual_074409
  · exact g32p_supplierForest_actual_074413
  · exact g32p_supplierForest_actual_074481
  · exact g32p_supplierForest_actual_074499
  · exact g32p_supplierForest_actual_074597
  · exact g32p_supplierForest_actual_074605
  · exact g32p_supplierForest_actual_074611

def g32p_supplierForest_nodes_044 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_074634 else g32p_supplierForest_node_074673) else (if i.val < 3 then g32p_supplierForest_node_074692 else g32p_supplierForest_node_074737)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_074779 else g32p_supplierForest_node_074780) else (if i.val < 7 then g32p_supplierForest_node_074785 else g32p_supplierForest_node_074792))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_074797 else g32p_supplierForest_node_074803) else (if i.val < 11 then g32p_supplierForest_node_074807 else g32p_supplierForest_node_074808)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_074848 else g32p_supplierForest_node_074856) else (if i.val < 15 then g32p_supplierForest_node_074870 else g32p_supplierForest_node_074879)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_074912 else g32p_supplierForest_node_074937) else (if i.val < 19 then g32p_supplierForest_node_074966 else g32p_supplierForest_node_074981)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_075031 else g32p_supplierForest_node_075077) else (if i.val < 23 then g32p_supplierForest_node_075123 else g32p_supplierForest_node_075133))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_075143 else g32p_supplierForest_node_075154) else (if i.val < 27 then g32p_supplierForest_node_075186 else g32p_supplierForest_node_075198)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_075262 else g32p_supplierForest_node_075263) else (if i.val < 31 then g32p_supplierForest_node_075265 else g32p_supplierForest_node_075303))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_075304 else g32p_supplierForest_node_075389) else (if i.val < 35 then g32p_supplierForest_node_075390 else g32p_supplierForest_node_075403)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_075408 else g32p_supplierForest_node_075434) else (if i.val < 39 then g32p_supplierForest_node_075444 else g32p_supplierForest_node_075445))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_075449 else g32p_supplierForest_node_075452) else (if i.val < 43 then g32p_supplierForest_node_075472 else g32p_supplierForest_node_075528)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_075533 else g32p_supplierForest_node_075540) else (if i.val < 47 then g32p_supplierForest_node_075576 else g32p_supplierForest_node_075593)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_075607 else g32p_supplierForest_node_075611) else (if i.val < 51 then g32p_supplierForest_node_075641 else g32p_supplierForest_node_075650)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_075652 else g32p_supplierForest_node_075657) else (if i.val < 55 then g32p_supplierForest_node_075724 else g32p_supplierForest_node_075793))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_075802 else g32p_supplierForest_node_075806) else (if i.val < 59 then g32p_supplierForest_node_075818 else g32p_supplierForest_node_075838)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_075848 else g32p_supplierForest_node_075875) else (if i.val < 63 then g32p_supplierForest_node_075881 else g32p_supplierForest_node_075912)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_075913 else g32p_supplierForest_node_075930) else (if i.val < 67 then g32p_supplierForest_node_075948 else g32p_supplierForest_node_075949)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_075961 else g32p_supplierForest_node_075962) else (if i.val < 71 then g32p_supplierForest_node_075966 else g32p_supplierForest_node_075976))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_075980 else g32p_supplierForest_node_075982) else (if i.val < 75 then g32p_supplierForest_node_075990 else g32p_supplierForest_node_076020)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_076045 else g32p_supplierForest_node_076070) else (if i.val < 79 then g32p_supplierForest_node_076109 else g32p_supplierForest_node_076117)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_076135 else g32p_supplierForest_node_076206) else (if i.val < 83 then g32p_supplierForest_node_076215 else g32p_supplierForest_node_076238)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_076246 else g32p_supplierForest_node_076249) else (if i.val < 87 then g32p_supplierForest_node_076250 else g32p_supplierForest_node_076404))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_076416 else g32p_supplierForest_node_076487) else (if i.val < 91 then g32p_supplierForest_node_076491 else g32p_supplierForest_node_076494)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_076543 else g32p_supplierForest_node_076589) else (if i.val < 95 then g32p_supplierForest_node_076594 else g32p_supplierForest_node_076596))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_076616 else g32p_supplierForest_node_076711) else (if i.val < 99 then g32p_supplierForest_node_076738 else g32p_supplierForest_node_076743)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_076744 else g32p_supplierForest_node_076752) else (if i.val < 103 then g32p_supplierForest_node_076755 else g32p_supplierForest_node_076824))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_076850 else g32p_supplierForest_node_076871) else (if i.val < 107 then g32p_supplierForest_node_076960 else g32p_supplierForest_node_076970)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_076997 else g32p_supplierForest_node_076999) else (if i.val < 111 then g32p_supplierForest_node_077031 else g32p_supplierForest_node_077055)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_077061 else g32p_supplierForest_node_077074) else (if i.val < 115 then g32p_supplierForest_node_077078 else g32p_supplierForest_node_077159)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_077171 else g32p_supplierForest_node_077179) else (if i.val < 119 then g32p_supplierForest_node_077193 else g32p_supplierForest_node_077223))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_077226 else g32p_supplierForest_node_077228) else (if i.val < 123 then g32p_supplierForest_node_077245 else g32p_supplierForest_node_077257)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_077263 else g32p_supplierForest_node_077285) else (if i.val < 127 then g32p_supplierForest_node_077329 else g32p_supplierForest_node_077341))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_077342 else g32p_supplierForest_node_077392) else (if i.val < 131 then g32p_supplierForest_node_077393 else g32p_supplierForest_node_077400)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_077440 else g32p_supplierForest_node_077538) else (if i.val < 135 then g32p_supplierForest_node_077589 else g32p_supplierForest_node_077608))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_077627 else g32p_supplierForest_node_077635) else (if i.val < 139 then g32p_supplierForest_node_077639 else g32p_supplierForest_node_077647)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_077684 else g32p_supplierForest_node_077701) else (if i.val < 143 then g32p_supplierForest_node_077722 else g32p_supplierForest_node_077735)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_077736 else g32p_supplierForest_node_077750) else (if i.val < 147 then g32p_supplierForest_node_077763 else g32p_supplierForest_node_077779)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_077784 else g32p_supplierForest_node_077788) else (if i.val < 151 then g32p_supplierForest_node_077797 else g32p_supplierForest_node_077818))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_077825 else g32p_supplierForest_node_077840) else (if i.val < 155 then g32p_supplierForest_node_077856 else g32p_supplierForest_node_077875)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_077894 else g32p_supplierForest_node_077917) else (if i.val < 159 then g32p_supplierForest_node_077980 else g32p_supplierForest_node_078024))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_078042 else g32p_supplierForest_node_078077) else (if i.val < 163 then g32p_supplierForest_node_078078 else g32p_supplierForest_node_078178)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_078215 else g32p_supplierForest_node_078267) else (if i.val < 167 then g32p_supplierForest_node_078269 else g32p_supplierForest_node_078282))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_078294 else g32p_supplierForest_node_078298) else (if i.val < 171 then g32p_supplierForest_node_078300 else g32p_supplierForest_node_078303)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_078343 else g32p_supplierForest_node_078373) else (if i.val < 175 then g32p_supplierForest_node_078375 else g32p_supplierForest_node_078382)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_078424 else g32p_supplierForest_node_078435) else (if i.val < 179 then g32p_supplierForest_node_078447 else g32p_supplierForest_node_078452)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_078465 else g32p_supplierForest_node_078510) else (if i.val < 183 then g32p_supplierForest_node_078527 else g32p_supplierForest_node_078535))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_078536 else g32p_supplierForest_node_078538) else (if i.val < 187 then g32p_supplierForest_node_078556 else g32p_supplierForest_node_078568)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_078587 else g32p_supplierForest_node_078592) else (if i.val < 191 then g32p_supplierForest_node_078599 else g32p_supplierForest_node_078621)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_078641 else g32p_supplierForest_node_078646) else (if i.val < 195 then g32p_supplierForest_node_078647 else g32p_supplierForest_node_078670)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_078721 else g32p_supplierForest_node_078755) else (if i.val < 199 then g32p_supplierForest_node_078760 else g32p_supplierForest_node_078779))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_078841 else g32p_supplierForest_node_078856) else (if i.val < 203 then g32p_supplierForest_node_078866 else g32p_supplierForest_node_078871)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_078872 else g32p_supplierForest_node_078908) else (if i.val < 207 then g32p_supplierForest_node_078939 else g32p_supplierForest_node_079015)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_079053 else g32p_supplierForest_node_079057) else (if i.val < 211 then g32p_supplierForest_node_079103 else g32p_supplierForest_node_079127)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_079140 else g32p_supplierForest_node_079148) else (if i.val < 215 then g32p_supplierForest_node_079169 else g32p_supplierForest_node_079184))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_079201 else g32p_supplierForest_node_079260) else (if i.val < 219 then g32p_supplierForest_node_079305 else g32p_supplierForest_node_079318)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_079321 else g32p_supplierForest_node_079388) else (if i.val < 223 then g32p_supplierForest_node_079431 else g32p_supplierForest_node_079448))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_079455 else g32p_supplierForest_node_079460) else (if i.val < 227 then g32p_supplierForest_node_079484 else g32p_supplierForest_node_079485)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_079596 else g32p_supplierForest_node_079617) else (if i.val < 231 then g32p_supplierForest_node_079683 else g32p_supplierForest_node_079689))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_079724 else g32p_supplierForest_node_079755) else (if i.val < 235 then g32p_supplierForest_node_079779 else g32p_supplierForest_node_079811)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_079833 else g32p_supplierForest_node_079849) else (if i.val < 239 then g32p_supplierForest_node_079873 else g32p_supplierForest_node_079907)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_079909 else g32p_supplierForest_node_079916) else (if i.val < 243 then g32p_supplierForest_node_079931 else g32p_supplierForest_node_079943)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_079982 else g32p_supplierForest_node_080010) else (if i.val < 247 then g32p_supplierForest_node_080014 else g32p_supplierForest_node_080021))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_080039 else g32p_supplierForest_node_080049) else (if i.val < 251 then g32p_supplierForest_node_080063 else g32p_supplierForest_node_080071)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_080095 else g32p_supplierForest_node_080142) else (if i.val < 255 then g32p_supplierForest_node_080158 else g32p_supplierForest_node_080168))))))))

def g32p_supplierForest_classes_044 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 27 else 50) else (if i.val < 3 then 84 else 46)) else (if i.val < 6 then (if i.val < 5 then 50 else 49) else (if i.val < 7 then 26 else 26))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 49 else 13) else (if i.val < 11 then 9 else 46)) else (if i.val < 14 then (if i.val < 13 then 46 else 51) else (if i.val < 15 then 84 else 11)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 49 else 47) else (if i.val < 19 then 55 else 45)) else (if i.val < 22 then (if i.val < 21 then 84 else 13) else (if i.val < 23 then 26 else 84))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 9) else (if i.val < 27 then 46 else 12)) else (if i.val < 30 then (if i.val < 29 then 46 else 49) else (if i.val < 31 then 46 else 9))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 49 else 45) else (if i.val < 35 then 53 else 47)) else (if i.val < 38 then (if i.val < 37 then 10 else 46) else (if i.val < 39 then 26 else 46))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 83 else 25) else (if i.val < 43 then 25 else 45)) else (if i.val < 46 then (if i.val < 45 then 53 else 46) else (if i.val < 47 then 46 else 11)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 47 else 26) else (if i.val < 51 then 25 else 9)) else (if i.val < 54 then (if i.val < 53 then 50 else 56) else (if i.val < 55 then 83 else 26))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 26 else 48) else (if i.val < 59 then 80 else 9)) else (if i.val < 62 then (if i.val < 61 then 46 else 83) else (if i.val < 63 then 11 else 48)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 50 else 10) else (if i.val < 67 then 80 else 54)) else (if i.val < 70 then (if i.val < 69 then 46 else 46) else (if i.val < 71 then 46 else 50))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 49 else 27) else (if i.val < 75 then 82 else 85)) else (if i.val < 78 then (if i.val < 77 then 49 else 46) else (if i.val < 79 then 25 else 25)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 9 else 25) else (if i.val < 83 then 47 else 25)) else (if i.val < 86 then (if i.val < 85 then 49 else 13) else (if i.val < 87 then 84 else 54))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 49 else 49) else (if i.val < 91 then 27 else 8)) else (if i.val < 94 then (if i.val < 93 then 46 else 11) else (if i.val < 95 then 56 else 25))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 48 else 49) else (if i.val < 99 then 25 else 46)) else (if i.val < 102 then (if i.val < 101 then 52 else 13) else (if i.val < 103 then 46 else 46))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 53 else 47) else (if i.val < 107 then 52 else 49)) else (if i.val < 110 then (if i.val < 109 then 84 else 46) else (if i.val < 111 then 13 else 49)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 46 else 11) else (if i.val < 115 then 85 else 9)) else (if i.val < 118 then (if i.val < 117 then 49 else 11) else (if i.val < 119 then 46 else 46))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 84 else 54) else (if i.val < 123 then 25 else 47)) else (if i.val < 126 then (if i.val < 125 then 49 else 80) else (if i.val < 127 then 25 else 11))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 13 else 47) else (if i.val < 131 then 56 else 10)) else (if i.val < 134 then (if i.val < 133 then 25 else 46) else (if i.val < 135 then 54 else 50))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 55 else 46) else (if i.val < 139 then 46 else 55)) else (if i.val < 142 then (if i.val < 141 then 83 else 10) else (if i.val < 143 then 13 else 47)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 13 else 46) else (if i.val < 147 then 46 else 46)) else (if i.val < 150 then (if i.val < 149 then 83 else 49) else (if i.val < 151 then 47 else 26))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 84 else 84) else (if i.val < 155 then 46 else 27)) else (if i.val < 158 then (if i.val < 157 then 46 else 26) else (if i.val < 159 then 80 else 55))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 80 else 27) else (if i.val < 163 then 26 else 54)) else (if i.val < 166 then (if i.val < 165 then 56 else 46) else (if i.val < 167 then 49 else 56))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 46 else 45) else (if i.val < 171 then 47 else 56)) else (if i.val < 174 then (if i.val < 173 then 49 else 84) else (if i.val < 175 then 48 else 51)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 50 else 53) else (if i.val < 179 then 13 else 53)) else (if i.val < 182 then (if i.val < 181 then 45 else 55) else (if i.val < 183 then 27 else 46))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 46 else 46) else (if i.val < 187 then 11 else 46)) else (if i.val < 190 then (if i.val < 189 then 27 else 26) else (if i.val < 191 then 11 else 84)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 53 else 80) else (if i.val < 195 then 80 else 84)) else (if i.val < 198 then (if i.val < 197 then 26 else 46) else (if i.val < 199 then 49 else 9))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 53 else 46) else (if i.val < 203 then 46 else 45)) else (if i.val < 206 then (if i.val < 205 then 53 else 49) else (if i.val < 207 then 26 else 27)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 49 else 47) else (if i.val < 211 then 84 else 83)) else (if i.val < 214 then (if i.val < 213 then 13 else 46) else (if i.val < 215 then 48 else 12))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 56 else 84) else (if i.val < 219 then 13 else 55)) else (if i.val < 222 then (if i.val < 221 then 47 else 10) else (if i.val < 223 then 50 else 56))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 48 else 56) else (if i.val < 227 then 26 else 84)) else (if i.val < 230 then (if i.val < 229 then 25 else 84) else (if i.val < 231 then 46 else 9))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 49 else 27) else (if i.val < 235 then 26 else 13)) else (if i.val < 238 then (if i.val < 237 then 13 else 84) else (if i.val < 239 then 83 else 45)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 49 else 46) else (if i.val < 243 then 11 else 9)) else (if i.val < 246 then (if i.val < 245 then 80 else 50) else (if i.val < 247 then 46 else 48))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 49 else 13) else (if i.val < 251 then 45 else 13)) else (if i.val < 254 then (if i.val < 253 then 50 else 49) else (if i.val < 255 then 47 else 55))))))))

theorem g32p_supplierForest_actual_044 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_044 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_044 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_074634
  · exact g32p_supplierForest_actual_074673
  · exact g32p_supplierForest_actual_074692
  · exact g32p_supplierForest_actual_074737
  · exact g32p_supplierForest_actual_074779
  · exact g32p_supplierForest_actual_074780
  · exact g32p_supplierForest_actual_074785
  · exact g32p_supplierForest_actual_074792
  · exact g32p_supplierForest_actual_074797
  · exact g32p_supplierForest_actual_074803
  · exact g32p_supplierForest_actual_074807
  · exact g32p_supplierForest_actual_074808
  · exact g32p_supplierForest_actual_074848
  · exact g32p_supplierForest_actual_074856
  · exact g32p_supplierForest_actual_074870
  · exact g32p_supplierForest_actual_074879
  · exact g32p_supplierForest_actual_074912
  · exact g32p_supplierForest_actual_074937
  · exact g32p_supplierForest_actual_074966
  · exact g32p_supplierForest_actual_074981
  · exact g32p_supplierForest_actual_075031
  · exact g32p_supplierForest_actual_075077
  · exact g32p_supplierForest_actual_075123
  · exact g32p_supplierForest_actual_075133
  · exact g32p_supplierForest_actual_075143
  · exact g32p_supplierForest_actual_075154
  · exact g32p_supplierForest_actual_075186
  · exact g32p_supplierForest_actual_075198
  · exact g32p_supplierForest_actual_075262
  · exact g32p_supplierForest_actual_075263
  · exact g32p_supplierForest_actual_075265
  · exact g32p_supplierForest_actual_075303
  · exact g32p_supplierForest_actual_075304
  · exact g32p_supplierForest_actual_075389
  · exact g32p_supplierForest_actual_075390
  · exact g32p_supplierForest_actual_075403
  · exact g32p_supplierForest_actual_075408
  · exact g32p_supplierForest_actual_075434
  · exact g32p_supplierForest_actual_075444
  · exact g32p_supplierForest_actual_075445
  · exact g32p_supplierForest_actual_075449
  · exact g32p_supplierForest_actual_075452
  · exact g32p_supplierForest_actual_075472
  · exact g32p_supplierForest_actual_075528
  · exact g32p_supplierForest_actual_075533
  · exact g32p_supplierForest_actual_075540
  · exact g32p_supplierForest_actual_075576
  · exact g32p_supplierForest_actual_075593
  · exact g32p_supplierForest_actual_075607
  · exact g32p_supplierForest_actual_075611
  · exact g32p_supplierForest_actual_075641
  · exact g32p_supplierForest_actual_075650
  · exact g32p_supplierForest_actual_075652
  · exact g32p_supplierForest_actual_075657
  · exact g32p_supplierForest_actual_075724
  · exact g32p_supplierForest_actual_075793
  · exact g32p_supplierForest_actual_075802
  · exact g32p_supplierForest_actual_075806
  · exact g32p_supplierForest_actual_075818
  · exact g32p_supplierForest_actual_075838
  · exact g32p_supplierForest_actual_075848
  · exact g32p_supplierForest_actual_075875
  · exact g32p_supplierForest_actual_075881
  · exact g32p_supplierForest_actual_075912
  · exact g32p_supplierForest_actual_075913
  · exact g32p_supplierForest_actual_075930
  · exact g32p_supplierForest_actual_075948
  · exact g32p_supplierForest_actual_075949
  · exact g32p_supplierForest_actual_075961
  · exact g32p_supplierForest_actual_075962
  · exact g32p_supplierForest_actual_075966
  · exact g32p_supplierForest_actual_075976
  · exact g32p_supplierForest_actual_075980
  · exact g32p_supplierForest_actual_075982
  · exact g32p_supplierForest_actual_075990
  · exact g32p_supplierForest_actual_076020
  · exact g32p_supplierForest_actual_076045
  · exact g32p_supplierForest_actual_076070
  · exact g32p_supplierForest_actual_076109
  · exact g32p_supplierForest_actual_076117
  · exact g32p_supplierForest_actual_076135
  · exact g32p_supplierForest_actual_076206
  · exact g32p_supplierForest_actual_076215
  · exact g32p_supplierForest_actual_076238
  · exact g32p_supplierForest_actual_076246
  · exact g32p_supplierForest_actual_076249
  · exact g32p_supplierForest_actual_076250
  · exact g32p_supplierForest_actual_076404
  · exact g32p_supplierForest_actual_076416
  · exact g32p_supplierForest_actual_076487
  · exact g32p_supplierForest_actual_076491
  · exact g32p_supplierForest_actual_076494
  · exact g32p_supplierForest_actual_076543
  · exact g32p_supplierForest_actual_076589
  · exact g32p_supplierForest_actual_076594
  · exact g32p_supplierForest_actual_076596
  · exact g32p_supplierForest_actual_076616
  · exact g32p_supplierForest_actual_076711
  · exact g32p_supplierForest_actual_076738
  · exact g32p_supplierForest_actual_076743
  · exact g32p_supplierForest_actual_076744
  · exact g32p_supplierForest_actual_076752
  · exact g32p_supplierForest_actual_076755
  · exact g32p_supplierForest_actual_076824
  · exact g32p_supplierForest_actual_076850
  · exact g32p_supplierForest_actual_076871
  · exact g32p_supplierForest_actual_076960
  · exact g32p_supplierForest_actual_076970
  · exact g32p_supplierForest_actual_076997
  · exact g32p_supplierForest_actual_076999
  · exact g32p_supplierForest_actual_077031
  · exact g32p_supplierForest_actual_077055
  · exact g32p_supplierForest_actual_077061
  · exact g32p_supplierForest_actual_077074
  · exact g32p_supplierForest_actual_077078
  · exact g32p_supplierForest_actual_077159
  · exact g32p_supplierForest_actual_077171
  · exact g32p_supplierForest_actual_077179
  · exact g32p_supplierForest_actual_077193
  · exact g32p_supplierForest_actual_077223
  · exact g32p_supplierForest_actual_077226
  · exact g32p_supplierForest_actual_077228
  · exact g32p_supplierForest_actual_077245
  · exact g32p_supplierForest_actual_077257
  · exact g32p_supplierForest_actual_077263
  · exact g32p_supplierForest_actual_077285
  · exact g32p_supplierForest_actual_077329
  · exact g32p_supplierForest_actual_077341
  · exact g32p_supplierForest_actual_077342
  · exact g32p_supplierForest_actual_077392
  · exact g32p_supplierForest_actual_077393
  · exact g32p_supplierForest_actual_077400
  · exact g32p_supplierForest_actual_077440
  · exact g32p_supplierForest_actual_077538
  · exact g32p_supplierForest_actual_077589
  · exact g32p_supplierForest_actual_077608
  · exact g32p_supplierForest_actual_077627
  · exact g32p_supplierForest_actual_077635
  · exact g32p_supplierForest_actual_077639
  · exact g32p_supplierForest_actual_077647
  · exact g32p_supplierForest_actual_077684
  · exact g32p_supplierForest_actual_077701
  · exact g32p_supplierForest_actual_077722
  · exact g32p_supplierForest_actual_077735
  · exact g32p_supplierForest_actual_077736
  · exact g32p_supplierForest_actual_077750
  · exact g32p_supplierForest_actual_077763
  · exact g32p_supplierForest_actual_077779
  · exact g32p_supplierForest_actual_077784
  · exact g32p_supplierForest_actual_077788
  · exact g32p_supplierForest_actual_077797
  · exact g32p_supplierForest_actual_077818
  · exact g32p_supplierForest_actual_077825
  · exact g32p_supplierForest_actual_077840
  · exact g32p_supplierForest_actual_077856
  · exact g32p_supplierForest_actual_077875
  · exact g32p_supplierForest_actual_077894
  · exact g32p_supplierForest_actual_077917
  · exact g32p_supplierForest_actual_077980
  · exact g32p_supplierForest_actual_078024
  · exact g32p_supplierForest_actual_078042
  · exact g32p_supplierForest_actual_078077
  · exact g32p_supplierForest_actual_078078
  · exact g32p_supplierForest_actual_078178
  · exact g32p_supplierForest_actual_078215
  · exact g32p_supplierForest_actual_078267
  · exact g32p_supplierForest_actual_078269
  · exact g32p_supplierForest_actual_078282
  · exact g32p_supplierForest_actual_078294
  · exact g32p_supplierForest_actual_078298
  · exact g32p_supplierForest_actual_078300
  · exact g32p_supplierForest_actual_078303
  · exact g32p_supplierForest_actual_078343
  · exact g32p_supplierForest_actual_078373
  · exact g32p_supplierForest_actual_078375
  · exact g32p_supplierForest_actual_078382
  · exact g32p_supplierForest_actual_078424
  · exact g32p_supplierForest_actual_078435
  · exact g32p_supplierForest_actual_078447
  · exact g32p_supplierForest_actual_078452
  · exact g32p_supplierForest_actual_078465
  · exact g32p_supplierForest_actual_078510
  · exact g32p_supplierForest_actual_078527
  · exact g32p_supplierForest_actual_078535
  · exact g32p_supplierForest_actual_078536
  · exact g32p_supplierForest_actual_078538
  · exact g32p_supplierForest_actual_078556
  · exact g32p_supplierForest_actual_078568
  · exact g32p_supplierForest_actual_078587
  · exact g32p_supplierForest_actual_078592
  · exact g32p_supplierForest_actual_078599
  · exact g32p_supplierForest_actual_078621
  · exact g32p_supplierForest_actual_078641
  · exact g32p_supplierForest_actual_078646
  · exact g32p_supplierForest_actual_078647
  · exact g32p_supplierForest_actual_078670
  · exact g32p_supplierForest_actual_078721
  · exact g32p_supplierForest_actual_078755
  · exact g32p_supplierForest_actual_078760
  · exact g32p_supplierForest_actual_078779
  · exact g32p_supplierForest_actual_078841
  · exact g32p_supplierForest_actual_078856
  · exact g32p_supplierForest_actual_078866
  · exact g32p_supplierForest_actual_078871
  · exact g32p_supplierForest_actual_078872
  · exact g32p_supplierForest_actual_078908
  · exact g32p_supplierForest_actual_078939
  · exact g32p_supplierForest_actual_079015
  · exact g32p_supplierForest_actual_079053
  · exact g32p_supplierForest_actual_079057
  · exact g32p_supplierForest_actual_079103
  · exact g32p_supplierForest_actual_079127
  · exact g32p_supplierForest_actual_079140
  · exact g32p_supplierForest_actual_079148
  · exact g32p_supplierForest_actual_079169
  · exact g32p_supplierForest_actual_079184
  · exact g32p_supplierForest_actual_079201
  · exact g32p_supplierForest_actual_079260
  · exact g32p_supplierForest_actual_079305
  · exact g32p_supplierForest_actual_079318
  · exact g32p_supplierForest_actual_079321
  · exact g32p_supplierForest_actual_079388
  · exact g32p_supplierForest_actual_079431
  · exact g32p_supplierForest_actual_079448
  · exact g32p_supplierForest_actual_079455
  · exact g32p_supplierForest_actual_079460
  · exact g32p_supplierForest_actual_079484
  · exact g32p_supplierForest_actual_079485
  · exact g32p_supplierForest_actual_079596
  · exact g32p_supplierForest_actual_079617
  · exact g32p_supplierForest_actual_079683
  · exact g32p_supplierForest_actual_079689
  · exact g32p_supplierForest_actual_079724
  · exact g32p_supplierForest_actual_079755
  · exact g32p_supplierForest_actual_079779
  · exact g32p_supplierForest_actual_079811
  · exact g32p_supplierForest_actual_079833
  · exact g32p_supplierForest_actual_079849
  · exact g32p_supplierForest_actual_079873
  · exact g32p_supplierForest_actual_079907
  · exact g32p_supplierForest_actual_079909
  · exact g32p_supplierForest_actual_079916
  · exact g32p_supplierForest_actual_079931
  · exact g32p_supplierForest_actual_079943
  · exact g32p_supplierForest_actual_079982
  · exact g32p_supplierForest_actual_080010
  · exact g32p_supplierForest_actual_080014
  · exact g32p_supplierForest_actual_080021
  · exact g32p_supplierForest_actual_080039
  · exact g32p_supplierForest_actual_080049
  · exact g32p_supplierForest_actual_080063
  · exact g32p_supplierForest_actual_080071
  · exact g32p_supplierForest_actual_080095
  · exact g32p_supplierForest_actual_080142
  · exact g32p_supplierForest_actual_080158
  · exact g32p_supplierForest_actual_080168

def g32p_supplierForest_nodes_045 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_080183 else g32p_supplierForest_node_080222) else (if i.val < 3 then g32p_supplierForest_node_080378 else g32p_supplierForest_node_080394)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_080524 else g32p_supplierForest_node_080535) else (if i.val < 7 then g32p_supplierForest_node_080547 else g32p_supplierForest_node_080558))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_080560 else g32p_supplierForest_node_080680) else (if i.val < 11 then g32p_supplierForest_node_080758 else g32p_supplierForest_node_080771)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_080775 else g32p_supplierForest_node_080795) else (if i.val < 15 then g32p_supplierForest_node_080887 else g32p_supplierForest_node_080891)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_080916 else g32p_supplierForest_node_080933) else (if i.val < 19 then g32p_supplierForest_node_080992 else g32p_supplierForest_node_081003)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_081082 else g32p_supplierForest_node_081086) else (if i.val < 23 then g32p_supplierForest_node_081088 else g32p_supplierForest_node_081094))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_081127 else g32p_supplierForest_node_081143) else (if i.val < 27 then g32p_supplierForest_node_081148 else g32p_supplierForest_node_081153)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_081164 else g32p_supplierForest_node_081199) else (if i.val < 31 then g32p_supplierForest_node_081206 else g32p_supplierForest_node_081215))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_081217 else g32p_supplierForest_node_081221) else (if i.val < 35 then g32p_supplierForest_node_081277 else g32p_supplierForest_node_081297)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_081320 else g32p_supplierForest_node_081359) else (if i.val < 39 then g32p_supplierForest_node_081365 else g32p_supplierForest_node_081371))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_081379 else g32p_supplierForest_node_081408) else (if i.val < 43 then g32p_supplierForest_node_081434 else g32p_supplierForest_node_081518)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_081525 else g32p_supplierForest_node_081527) else (if i.val < 47 then g32p_supplierForest_node_081584 else g32p_supplierForest_node_081586)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_081598 else g32p_supplierForest_node_081603) else (if i.val < 51 then g32p_supplierForest_node_081605 else g32p_supplierForest_node_081609)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_081641 else g32p_supplierForest_node_081674) else (if i.val < 55 then g32p_supplierForest_node_081676 else g32p_supplierForest_node_081741))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_081795 else g32p_supplierForest_node_081814) else (if i.val < 59 then g32p_supplierForest_node_081830 else g32p_supplierForest_node_081832)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_081881 else g32p_supplierForest_node_081927) else (if i.val < 63 then g32p_supplierForest_node_081938 else g32p_supplierForest_node_081940)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_082000 else g32p_supplierForest_node_082001) else (if i.val < 67 then g32p_supplierForest_node_082020 else g32p_supplierForest_node_082055)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_082057 else g32p_supplierForest_node_082084) else (if i.val < 71 then g32p_supplierForest_node_082106 else g32p_supplierForest_node_082111))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_082112 else g32p_supplierForest_node_082130) else (if i.val < 75 then g32p_supplierForest_node_082132 else g32p_supplierForest_node_082138)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_082147 else g32p_supplierForest_node_082149) else (if i.val < 79 then g32p_supplierForest_node_082150 else g32p_supplierForest_node_082164)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_082182 else g32p_supplierForest_node_082237) else (if i.val < 83 then g32p_supplierForest_node_082336 else g32p_supplierForest_node_082350)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_082361 else g32p_supplierForest_node_082413) else (if i.val < 87 then g32p_supplierForest_node_082414 else g32p_supplierForest_node_082440))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_082456 else g32p_supplierForest_node_082466) else (if i.val < 91 then g32p_supplierForest_node_082480 else g32p_supplierForest_node_082494)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_082511 else g32p_supplierForest_node_082552) else (if i.val < 95 then g32p_supplierForest_node_082553 else g32p_supplierForest_node_082568))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_082591 else g32p_supplierForest_node_082594) else (if i.val < 99 then g32p_supplierForest_node_082609 else g32p_supplierForest_node_082619)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_082620 else g32p_supplierForest_node_082623) else (if i.val < 103 then g32p_supplierForest_node_082639 else g32p_supplierForest_node_082655))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_082658 else g32p_supplierForest_node_082660) else (if i.val < 107 then g32p_supplierForest_node_082661 else g32p_supplierForest_node_082684)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_082690 else g32p_supplierForest_node_082718) else (if i.val < 111 then g32p_supplierForest_node_082719 else g32p_supplierForest_node_082746)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_082788 else g32p_supplierForest_node_082817) else (if i.val < 115 then g32p_supplierForest_node_082831 else g32p_supplierForest_node_082887)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_082890 else g32p_supplierForest_node_082892) else (if i.val < 119 then g32p_supplierForest_node_082931 else g32p_supplierForest_node_082959))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_082975 else g32p_supplierForest_node_082988) else (if i.val < 123 then g32p_supplierForest_node_082997 else g32p_supplierForest_node_083023)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_083089 else g32p_supplierForest_node_083129) else (if i.val < 127 then g32p_supplierForest_node_083152 else g32p_supplierForest_node_083160))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_083165 else g32p_supplierForest_node_083168) else (if i.val < 131 then g32p_supplierForest_node_083188 else g32p_supplierForest_node_083236)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_083238 else g32p_supplierForest_node_083244) else (if i.val < 135 then g32p_supplierForest_node_083258 else g32p_supplierForest_node_083266))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_083279 else g32p_supplierForest_node_083281) else (if i.val < 139 then g32p_supplierForest_node_083282 else g32p_supplierForest_node_083290)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_083299 else g32p_supplierForest_node_083319) else (if i.val < 143 then g32p_supplierForest_node_083338 else g32p_supplierForest_node_083343)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_083349 else g32p_supplierForest_node_083394) else (if i.val < 147 then g32p_supplierForest_node_083405 else g32p_supplierForest_node_083407)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_083414 else g32p_supplierForest_node_083420) else (if i.val < 151 then g32p_supplierForest_node_083464 else g32p_supplierForest_node_083465))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_083493 else g32p_supplierForest_node_083513) else (if i.val < 155 then g32p_supplierForest_node_083538 else g32p_supplierForest_node_083551)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_083552 else g32p_supplierForest_node_083566) else (if i.val < 159 then g32p_supplierForest_node_083596 else g32p_supplierForest_node_083619))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_083621 else g32p_supplierForest_node_083645) else (if i.val < 163 then g32p_supplierForest_node_083652 else g32p_supplierForest_node_083671)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_083730 else g32p_supplierForest_node_083740) else (if i.val < 167 then g32p_supplierForest_node_083760 else g32p_supplierForest_node_083791))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_083792 else g32p_supplierForest_node_083802) else (if i.val < 171 then g32p_supplierForest_node_083827 else g32p_supplierForest_node_083829)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_083860 else g32p_supplierForest_node_083870) else (if i.val < 175 then g32p_supplierForest_node_083892 else g32p_supplierForest_node_083925)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_083935 else g32p_supplierForest_node_083940) else (if i.val < 179 then g32p_supplierForest_node_083983 else g32p_supplierForest_node_084068)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_084077 else g32p_supplierForest_node_084092) else (if i.val < 183 then g32p_supplierForest_node_084097 else g32p_supplierForest_node_084105))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_084111 else g32p_supplierForest_node_084129) else (if i.val < 187 then g32p_supplierForest_node_084159 else g32p_supplierForest_node_084184)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_084186 else g32p_supplierForest_node_084195) else (if i.val < 191 then g32p_supplierForest_node_084198 else g32p_supplierForest_node_084200)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_084249 else g32p_supplierForest_node_084259) else (if i.val < 195 then g32p_supplierForest_node_084291 else g32p_supplierForest_node_084319)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_084330 else g32p_supplierForest_node_084374) else (if i.val < 199 then g32p_supplierForest_node_084377 else g32p_supplierForest_node_084387))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_084402 else g32p_supplierForest_node_084507) else (if i.val < 203 then g32p_supplierForest_node_084526 else g32p_supplierForest_node_084576)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_084612 else g32p_supplierForest_node_084620) else (if i.val < 207 then g32p_supplierForest_node_084636 else g32p_supplierForest_node_084641)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_084693 else g32p_supplierForest_node_084704) else (if i.val < 211 then g32p_supplierForest_node_084762 else g32p_supplierForest_node_084770)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_084778 else g32p_supplierForest_node_084791) else (if i.val < 215 then g32p_supplierForest_node_084794 else g32p_supplierForest_node_084800))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_084821 else g32p_supplierForest_node_084832) else (if i.val < 219 then g32p_supplierForest_node_084855 else g32p_supplierForest_node_084874)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_084911 else g32p_supplierForest_node_084915) else (if i.val < 223 then g32p_supplierForest_node_084920 else g32p_supplierForest_node_084942))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_084988 else g32p_supplierForest_node_084989) else (if i.val < 227 then g32p_supplierForest_node_085038 else g32p_supplierForest_node_085046)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_085056 else g32p_supplierForest_node_085071) else (if i.val < 231 then g32p_supplierForest_node_085088 else g32p_supplierForest_node_085096))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_085111 else g32p_supplierForest_node_085151) else (if i.val < 235 then g32p_supplierForest_node_085227 else g32p_supplierForest_node_085230)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_085247 else g32p_supplierForest_node_085259) else (if i.val < 239 then g32p_supplierForest_node_085262 else g32p_supplierForest_node_085273)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_085285 else g32p_supplierForest_node_085288) else (if i.val < 243 then g32p_supplierForest_node_085316 else g32p_supplierForest_node_085326)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_085346 else g32p_supplierForest_node_085352) else (if i.val < 247 then g32p_supplierForest_node_085360 else g32p_supplierForest_node_085387))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_085388 else g32p_supplierForest_node_085390) else (if i.val < 251 then g32p_supplierForest_node_085399 else g32p_supplierForest_node_085404)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_085405 else g32p_supplierForest_node_085406) else (if i.val < 255 then g32p_supplierForest_node_085448 else g32p_supplierForest_node_085453))))))))

def g32p_supplierForest_classes_045 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 52 else 26) else (if i.val < 3 then 56 else 49)) else (if i.val < 6 then (if i.val < 5 then 47 else 13) else (if i.val < 7 then 56 else 25))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 47 else 48) else (if i.val < 11 then 52 else 25)) else (if i.val < 14 then (if i.val < 13 then 8 else 51) else (if i.val < 15 then 46 else 84)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 25 else 80) else (if i.val < 19 then 49 else 48)) else (if i.val < 22 then (if i.val < 21 then 49 else 26) else (if i.val < 23 then 9 else 13))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 27 else 25) else (if i.val < 27 then 46 else 46)) else (if i.val < 30 then (if i.val < 29 then 9 else 12) else (if i.val < 31 then 49 else 84))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 13 else 25) else (if i.val < 35 then 12 else 50)) else (if i.val < 38 then (if i.val < 37 then 13 else 49) else (if i.val < 39 then 9 else 49))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 26 else 50) else (if i.val < 43 then 53 else 46)) else (if i.val < 46 then (if i.val < 45 then 26 else 48) else (if i.val < 47 then 25 else 12)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 49 else 50) else (if i.val < 51 then 27 else 49)) else (if i.val < 54 then (if i.val < 53 then 47 else 26) else (if i.val < 55 then 46 else 83))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 49 else 52) else (if i.val < 59 then 49 else 46)) else (if i.val < 62 then (if i.val < 61 then 49 else 25) else (if i.val < 63 then 45 else 49)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 54 else 84) else (if i.val < 67 then 47 else 46)) else (if i.val < 70 then (if i.val < 69 then 84 else 49) else (if i.val < 71 then 45 else 50))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 49 else 49) else (if i.val < 75 then 47 else 49)) else (if i.val < 78 then (if i.val < 77 then 25 else 49) else (if i.val < 79 then 25 else 49)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 46 else 10) else (if i.val < 83 then 53 else 47)) else (if i.val < 86 then (if i.val < 85 then 56 else 47) else (if i.val < 87 then 56 else 25))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 80 else 81) else (if i.val < 91 then 13 else 9)) else (if i.val < 94 then (if i.val < 93 then 48 else 49) else (if i.val < 95 then 49 else 9))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 82 else 53) else (if i.val < 99 then 45 else 50)) else (if i.val < 102 then (if i.val < 101 then 9 else 46) else (if i.val < 103 then 56 else 12))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 50 else 50) else (if i.val < 107 then 47 else 45)) else (if i.val < 110 then (if i.val < 109 then 52 else 46) else (if i.val < 111 then 50 else 49)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 25 else 84) else (if i.val < 115 then 52 else 49)) else (if i.val < 118 then (if i.val < 117 then 49 else 85) else (if i.val < 119 then 49 else 49))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 53 else 45) else (if i.val < 123 then 46 else 45)) else (if i.val < 126 then (if i.val < 125 then 49 else 50) else (if i.val < 127 then 82 else 49))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 50 else 49) else (if i.val < 131 then 81 else 47)) else (if i.val < 134 then (if i.val < 133 then 45 else 49) else (if i.val < 135 then 46 else 82))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 46 else 45) else (if i.val < 139 then 13 else 45)) else (if i.val < 142 then (if i.val < 141 then 46 else 46) else (if i.val < 143 then 46 else 56)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 50 else 46) else (if i.val < 147 then 84 else 84)) else (if i.val < 150 then (if i.val < 149 then 46 else 46) else (if i.val < 151 then 84 else 46))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 84 else 54) else (if i.val < 155 then 27 else 47)) else (if i.val < 158 then (if i.val < 157 then 56 else 26) else (if i.val < 159 then 83 else 26))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 54 else 82) else (if i.val < 163 then 85 else 11)) else (if i.val < 166 then (if i.val < 165 then 48 else 53) else (if i.val < 167 then 82 else 48))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 47 else 53) else (if i.val < 171 then 12 else 49)) else (if i.val < 174 then (if i.val < 173 then 84 else 25) else (if i.val < 175 then 49 else 25)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 25 else 10) else (if i.val < 179 then 83 else 50)) else (if i.val < 182 then (if i.val < 181 then 25 else 47) else (if i.val < 183 then 25 else 84))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 13 else 55) else (if i.val < 187 then 83 else 46)) else (if i.val < 190 then (if i.val < 189 then 46 else 46) else (if i.val < 191 then 46 else 13)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 26 else 46) else (if i.val < 195 then 47 else 49)) else (if i.val < 198 then (if i.val < 197 then 25 else 82) else (if i.val < 199 then 46 else 45))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 46 else 55) else (if i.val < 203 then 85 else 84)) else (if i.val < 206 then (if i.val < 205 then 46 else 49) else (if i.val < 207 then 49 else 49)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 46 else 56) else (if i.val < 211 then 47 else 50)) else (if i.val < 214 then (if i.val < 213 then 46 else 11) else (if i.val < 215 then 49 else 49))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 45 else 49) else (if i.val < 219 then 26 else 10)) else (if i.val < 222 then (if i.val < 221 then 13 else 26) else (if i.val < 223 then 49 else 26))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 47 else 45) else (if i.val < 227 then 10 else 25)) else (if i.val < 230 then (if i.val < 229 then 85 else 49) else (if i.val < 231 then 13 else 56))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 46 else 49) else (if i.val < 235 then 84 else 45)) else (if i.val < 238 then (if i.val < 237 then 46 else 49) else (if i.val < 239 then 84 else 11)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 46 else 26) else (if i.val < 243 then 46 else 26)) else (if i.val < 246 then (if i.val < 245 then 54 else 47) else (if i.val < 247 then 46 else 47))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 56 else 26) else (if i.val < 251 then 49 else 49)) else (if i.val < 254 then (if i.val < 253 then 48 else 47) else (if i.val < 255 then 46 else 45))))))))

theorem g32p_supplierForest_actual_045 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_045 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_045 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_080183
  · exact g32p_supplierForest_actual_080222
  · exact g32p_supplierForest_actual_080378
  · exact g32p_supplierForest_actual_080394
  · exact g32p_supplierForest_actual_080524
  · exact g32p_supplierForest_actual_080535
  · exact g32p_supplierForest_actual_080547
  · exact g32p_supplierForest_actual_080558
  · exact g32p_supplierForest_actual_080560
  · exact g32p_supplierForest_actual_080680
  · exact g32p_supplierForest_actual_080758
  · exact g32p_supplierForest_actual_080771
  · exact g32p_supplierForest_actual_080775
  · exact g32p_supplierForest_actual_080795
  · exact g32p_supplierForest_actual_080887
  · exact g32p_supplierForest_actual_080891
  · exact g32p_supplierForest_actual_080916
  · exact g32p_supplierForest_actual_080933
  · exact g32p_supplierForest_actual_080992
  · exact g32p_supplierForest_actual_081003
  · exact g32p_supplierForest_actual_081082
  · exact g32p_supplierForest_actual_081086
  · exact g32p_supplierForest_actual_081088
  · exact g32p_supplierForest_actual_081094
  · exact g32p_supplierForest_actual_081127
  · exact g32p_supplierForest_actual_081143
  · exact g32p_supplierForest_actual_081148
  · exact g32p_supplierForest_actual_081153
  · exact g32p_supplierForest_actual_081164
  · exact g32p_supplierForest_actual_081199
  · exact g32p_supplierForest_actual_081206
  · exact g32p_supplierForest_actual_081215
  · exact g32p_supplierForest_actual_081217
  · exact g32p_supplierForest_actual_081221
  · exact g32p_supplierForest_actual_081277
  · exact g32p_supplierForest_actual_081297
  · exact g32p_supplierForest_actual_081320
  · exact g32p_supplierForest_actual_081359
  · exact g32p_supplierForest_actual_081365
  · exact g32p_supplierForest_actual_081371
  · exact g32p_supplierForest_actual_081379
  · exact g32p_supplierForest_actual_081408
  · exact g32p_supplierForest_actual_081434
  · exact g32p_supplierForest_actual_081518
  · exact g32p_supplierForest_actual_081525
  · exact g32p_supplierForest_actual_081527
  · exact g32p_supplierForest_actual_081584
  · exact g32p_supplierForest_actual_081586
  · exact g32p_supplierForest_actual_081598
  · exact g32p_supplierForest_actual_081603
  · exact g32p_supplierForest_actual_081605
  · exact g32p_supplierForest_actual_081609
  · exact g32p_supplierForest_actual_081641
  · exact g32p_supplierForest_actual_081674
  · exact g32p_supplierForest_actual_081676
  · exact g32p_supplierForest_actual_081741
  · exact g32p_supplierForest_actual_081795
  · exact g32p_supplierForest_actual_081814
  · exact g32p_supplierForest_actual_081830
  · exact g32p_supplierForest_actual_081832
  · exact g32p_supplierForest_actual_081881
  · exact g32p_supplierForest_actual_081927
  · exact g32p_supplierForest_actual_081938
  · exact g32p_supplierForest_actual_081940
  · exact g32p_supplierForest_actual_082000
  · exact g32p_supplierForest_actual_082001
  · exact g32p_supplierForest_actual_082020
  · exact g32p_supplierForest_actual_082055
  · exact g32p_supplierForest_actual_082057
  · exact g32p_supplierForest_actual_082084
  · exact g32p_supplierForest_actual_082106
  · exact g32p_supplierForest_actual_082111
  · exact g32p_supplierForest_actual_082112
  · exact g32p_supplierForest_actual_082130
  · exact g32p_supplierForest_actual_082132
  · exact g32p_supplierForest_actual_082138
  · exact g32p_supplierForest_actual_082147
  · exact g32p_supplierForest_actual_082149
  · exact g32p_supplierForest_actual_082150
  · exact g32p_supplierForest_actual_082164
  · exact g32p_supplierForest_actual_082182
  · exact g32p_supplierForest_actual_082237
  · exact g32p_supplierForest_actual_082336
  · exact g32p_supplierForest_actual_082350
  · exact g32p_supplierForest_actual_082361
  · exact g32p_supplierForest_actual_082413
  · exact g32p_supplierForest_actual_082414
  · exact g32p_supplierForest_actual_082440
  · exact g32p_supplierForest_actual_082456
  · exact g32p_supplierForest_actual_082466
  · exact g32p_supplierForest_actual_082480
  · exact g32p_supplierForest_actual_082494
  · exact g32p_supplierForest_actual_082511
  · exact g32p_supplierForest_actual_082552
  · exact g32p_supplierForest_actual_082553
  · exact g32p_supplierForest_actual_082568
  · exact g32p_supplierForest_actual_082591
  · exact g32p_supplierForest_actual_082594
  · exact g32p_supplierForest_actual_082609
  · exact g32p_supplierForest_actual_082619
  · exact g32p_supplierForest_actual_082620
  · exact g32p_supplierForest_actual_082623
  · exact g32p_supplierForest_actual_082639
  · exact g32p_supplierForest_actual_082655
  · exact g32p_supplierForest_actual_082658
  · exact g32p_supplierForest_actual_082660
  · exact g32p_supplierForest_actual_082661
  · exact g32p_supplierForest_actual_082684
  · exact g32p_supplierForest_actual_082690
  · exact g32p_supplierForest_actual_082718
  · exact g32p_supplierForest_actual_082719
  · exact g32p_supplierForest_actual_082746
  · exact g32p_supplierForest_actual_082788
  · exact g32p_supplierForest_actual_082817
  · exact g32p_supplierForest_actual_082831
  · exact g32p_supplierForest_actual_082887
  · exact g32p_supplierForest_actual_082890
  · exact g32p_supplierForest_actual_082892
  · exact g32p_supplierForest_actual_082931
  · exact g32p_supplierForest_actual_082959
  · exact g32p_supplierForest_actual_082975
  · exact g32p_supplierForest_actual_082988
  · exact g32p_supplierForest_actual_082997
  · exact g32p_supplierForest_actual_083023
  · exact g32p_supplierForest_actual_083089
  · exact g32p_supplierForest_actual_083129
  · exact g32p_supplierForest_actual_083152
  · exact g32p_supplierForest_actual_083160
  · exact g32p_supplierForest_actual_083165
  · exact g32p_supplierForest_actual_083168
  · exact g32p_supplierForest_actual_083188
  · exact g32p_supplierForest_actual_083236
  · exact g32p_supplierForest_actual_083238
  · exact g32p_supplierForest_actual_083244
  · exact g32p_supplierForest_actual_083258
  · exact g32p_supplierForest_actual_083266
  · exact g32p_supplierForest_actual_083279
  · exact g32p_supplierForest_actual_083281
  · exact g32p_supplierForest_actual_083282
  · exact g32p_supplierForest_actual_083290
  · exact g32p_supplierForest_actual_083299
  · exact g32p_supplierForest_actual_083319
  · exact g32p_supplierForest_actual_083338
  · exact g32p_supplierForest_actual_083343
  · exact g32p_supplierForest_actual_083349
  · exact g32p_supplierForest_actual_083394
  · exact g32p_supplierForest_actual_083405
  · exact g32p_supplierForest_actual_083407
  · exact g32p_supplierForest_actual_083414
  · exact g32p_supplierForest_actual_083420
  · exact g32p_supplierForest_actual_083464
  · exact g32p_supplierForest_actual_083465
  · exact g32p_supplierForest_actual_083493
  · exact g32p_supplierForest_actual_083513
  · exact g32p_supplierForest_actual_083538
  · exact g32p_supplierForest_actual_083551
  · exact g32p_supplierForest_actual_083552
  · exact g32p_supplierForest_actual_083566
  · exact g32p_supplierForest_actual_083596
  · exact g32p_supplierForest_actual_083619
  · exact g32p_supplierForest_actual_083621
  · exact g32p_supplierForest_actual_083645
  · exact g32p_supplierForest_actual_083652
  · exact g32p_supplierForest_actual_083671
  · exact g32p_supplierForest_actual_083730
  · exact g32p_supplierForest_actual_083740
  · exact g32p_supplierForest_actual_083760
  · exact g32p_supplierForest_actual_083791
  · exact g32p_supplierForest_actual_083792
  · exact g32p_supplierForest_actual_083802
  · exact g32p_supplierForest_actual_083827
  · exact g32p_supplierForest_actual_083829
  · exact g32p_supplierForest_actual_083860
  · exact g32p_supplierForest_actual_083870
  · exact g32p_supplierForest_actual_083892
  · exact g32p_supplierForest_actual_083925
  · exact g32p_supplierForest_actual_083935
  · exact g32p_supplierForest_actual_083940
  · exact g32p_supplierForest_actual_083983
  · exact g32p_supplierForest_actual_084068
  · exact g32p_supplierForest_actual_084077
  · exact g32p_supplierForest_actual_084092
  · exact g32p_supplierForest_actual_084097
  · exact g32p_supplierForest_actual_084105
  · exact g32p_supplierForest_actual_084111
  · exact g32p_supplierForest_actual_084129
  · exact g32p_supplierForest_actual_084159
  · exact g32p_supplierForest_actual_084184
  · exact g32p_supplierForest_actual_084186
  · exact g32p_supplierForest_actual_084195
  · exact g32p_supplierForest_actual_084198
  · exact g32p_supplierForest_actual_084200
  · exact g32p_supplierForest_actual_084249
  · exact g32p_supplierForest_actual_084259
  · exact g32p_supplierForest_actual_084291
  · exact g32p_supplierForest_actual_084319
  · exact g32p_supplierForest_actual_084330
  · exact g32p_supplierForest_actual_084374
  · exact g32p_supplierForest_actual_084377
  · exact g32p_supplierForest_actual_084387
  · exact g32p_supplierForest_actual_084402
  · exact g32p_supplierForest_actual_084507
  · exact g32p_supplierForest_actual_084526
  · exact g32p_supplierForest_actual_084576
  · exact g32p_supplierForest_actual_084612
  · exact g32p_supplierForest_actual_084620
  · exact g32p_supplierForest_actual_084636
  · exact g32p_supplierForest_actual_084641
  · exact g32p_supplierForest_actual_084693
  · exact g32p_supplierForest_actual_084704
  · exact g32p_supplierForest_actual_084762
  · exact g32p_supplierForest_actual_084770
  · exact g32p_supplierForest_actual_084778
  · exact g32p_supplierForest_actual_084791
  · exact g32p_supplierForest_actual_084794
  · exact g32p_supplierForest_actual_084800
  · exact g32p_supplierForest_actual_084821
  · exact g32p_supplierForest_actual_084832
  · exact g32p_supplierForest_actual_084855
  · exact g32p_supplierForest_actual_084874
  · exact g32p_supplierForest_actual_084911
  · exact g32p_supplierForest_actual_084915
  · exact g32p_supplierForest_actual_084920
  · exact g32p_supplierForest_actual_084942
  · exact g32p_supplierForest_actual_084988
  · exact g32p_supplierForest_actual_084989
  · exact g32p_supplierForest_actual_085038
  · exact g32p_supplierForest_actual_085046
  · exact g32p_supplierForest_actual_085056
  · exact g32p_supplierForest_actual_085071
  · exact g32p_supplierForest_actual_085088
  · exact g32p_supplierForest_actual_085096
  · exact g32p_supplierForest_actual_085111
  · exact g32p_supplierForest_actual_085151
  · exact g32p_supplierForest_actual_085227
  · exact g32p_supplierForest_actual_085230
  · exact g32p_supplierForest_actual_085247
  · exact g32p_supplierForest_actual_085259
  · exact g32p_supplierForest_actual_085262
  · exact g32p_supplierForest_actual_085273
  · exact g32p_supplierForest_actual_085285
  · exact g32p_supplierForest_actual_085288
  · exact g32p_supplierForest_actual_085316
  · exact g32p_supplierForest_actual_085326
  · exact g32p_supplierForest_actual_085346
  · exact g32p_supplierForest_actual_085352
  · exact g32p_supplierForest_actual_085360
  · exact g32p_supplierForest_actual_085387
  · exact g32p_supplierForest_actual_085388
  · exact g32p_supplierForest_actual_085390
  · exact g32p_supplierForest_actual_085399
  · exact g32p_supplierForest_actual_085404
  · exact g32p_supplierForest_actual_085405
  · exact g32p_supplierForest_actual_085406
  · exact g32p_supplierForest_actual_085448
  · exact g32p_supplierForest_actual_085453

def g32p_supplierForest_nodes_046 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_085479 else g32p_supplierForest_node_085492) else (if i.val < 3 then g32p_supplierForest_node_085529 else g32p_supplierForest_node_085553)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_085556 else g32p_supplierForest_node_085564) else (if i.val < 7 then g32p_supplierForest_node_085573 else g32p_supplierForest_node_085590))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_085597 else g32p_supplierForest_node_085618) else (if i.val < 11 then g32p_supplierForest_node_085626 else g32p_supplierForest_node_085634)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_085685 else g32p_supplierForest_node_085686) else (if i.val < 15 then g32p_supplierForest_node_085695 else g32p_supplierForest_node_085699)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_085703 else g32p_supplierForest_node_085716) else (if i.val < 19 then g32p_supplierForest_node_085737 else g32p_supplierForest_node_085774)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_085778 else g32p_supplierForest_node_085782) else (if i.val < 23 then g32p_supplierForest_node_085785 else g32p_supplierForest_node_085839))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_085874 else g32p_supplierForest_node_085875) else (if i.val < 27 then g32p_supplierForest_node_085963 else g32p_supplierForest_node_085966)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_085987 else g32p_supplierForest_node_085988) else (if i.val < 31 then g32p_supplierForest_node_086009 else g32p_supplierForest_node_086016))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_086017 else g32p_supplierForest_node_086048) else (if i.val < 35 then g32p_supplierForest_node_086050 else g32p_supplierForest_node_086054)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_086083 else g32p_supplierForest_node_086135) else (if i.val < 39 then g32p_supplierForest_node_086168 else g32p_supplierForest_node_086208))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_086238 else g32p_supplierForest_node_086245) else (if i.val < 43 then g32p_supplierForest_node_086263 else g32p_supplierForest_node_086267)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_086337 else g32p_supplierForest_node_086385) else (if i.val < 47 then g32p_supplierForest_node_086389 else g32p_supplierForest_node_086394)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_086399 else g32p_supplierForest_node_086453) else (if i.val < 51 then g32p_supplierForest_node_086455 else g32p_supplierForest_node_086490)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_086530 else g32p_supplierForest_node_086536) else (if i.val < 55 then g32p_supplierForest_node_086551 else g32p_supplierForest_node_086554))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_086555 else g32p_supplierForest_node_086560) else (if i.val < 59 then g32p_supplierForest_node_086562 else g32p_supplierForest_node_086589)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_086604 else g32p_supplierForest_node_086605) else (if i.val < 63 then g32p_supplierForest_node_086622 else g32p_supplierForest_node_086669)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_086733 else g32p_supplierForest_node_086779) else (if i.val < 67 then g32p_supplierForest_node_086787 else g32p_supplierForest_node_086870)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_086932 else g32p_supplierForest_node_086941) else (if i.val < 71 then g32p_supplierForest_node_086976 else g32p_supplierForest_node_086998))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_086999 else g32p_supplierForest_node_087019) else (if i.val < 75 then g32p_supplierForest_node_087058 else g32p_supplierForest_node_087070)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_087077 else g32p_supplierForest_node_087101) else (if i.val < 79 then g32p_supplierForest_node_087124 else g32p_supplierForest_node_087138)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_087257 else g32p_supplierForest_node_087296) else (if i.val < 83 then g32p_supplierForest_node_087304 else g32p_supplierForest_node_087324)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_087360 else g32p_supplierForest_node_087376) else (if i.val < 87 then g32p_supplierForest_node_087422 else g32p_supplierForest_node_087430))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_087456 else g32p_supplierForest_node_087458) else (if i.val < 91 then g32p_supplierForest_node_087608 else g32p_supplierForest_node_087617)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_087625 else g32p_supplierForest_node_087645) else (if i.val < 95 then g32p_supplierForest_node_087661 else g32p_supplierForest_node_087671))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_087694 else g32p_supplierForest_node_087696) else (if i.val < 99 then g32p_supplierForest_node_087722 else g32p_supplierForest_node_087735)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_087740 else g32p_supplierForest_node_087748) else (if i.val < 103 then g32p_supplierForest_node_087787 else g32p_supplierForest_node_087793))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_087797 else g32p_supplierForest_node_087822) else (if i.val < 107 then g32p_supplierForest_node_087842 else g32p_supplierForest_node_087852)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_087876 else g32p_supplierForest_node_087879) else (if i.val < 111 then g32p_supplierForest_node_087902 else g32p_supplierForest_node_087965)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_088050 else g32p_supplierForest_node_088074) else (if i.val < 115 then g32p_supplierForest_node_088083 else g32p_supplierForest_node_088090)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_088101 else g32p_supplierForest_node_088157) else (if i.val < 119 then g32p_supplierForest_node_088158 else g32p_supplierForest_node_088180))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_088197 else g32p_supplierForest_node_088202) else (if i.val < 123 then g32p_supplierForest_node_088218 else g32p_supplierForest_node_088265)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_088275 else g32p_supplierForest_node_088284) else (if i.val < 127 then g32p_supplierForest_node_088307 else g32p_supplierForest_node_088314))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_088322 else g32p_supplierForest_node_088326) else (if i.val < 131 then g32p_supplierForest_node_088330 else g32p_supplierForest_node_088338)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_088339 else g32p_supplierForest_node_088362) else (if i.val < 135 then g32p_supplierForest_node_088420 else g32p_supplierForest_node_088476))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_088489 else g32p_supplierForest_node_088512) else (if i.val < 139 then g32p_supplierForest_node_088524 else g32p_supplierForest_node_088550)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_088551 else g32p_supplierForest_node_088553) else (if i.val < 143 then g32p_supplierForest_node_088695 else g32p_supplierForest_node_088696)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_088760 else g32p_supplierForest_node_088770) else (if i.val < 147 then g32p_supplierForest_node_088813 else g32p_supplierForest_node_088855)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_088885 else g32p_supplierForest_node_088906) else (if i.val < 151 then g32p_supplierForest_node_088917 else g32p_supplierForest_node_088924))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_088927 else g32p_supplierForest_node_088934) else (if i.val < 155 then g32p_supplierForest_node_088945 else g32p_supplierForest_node_088956)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_088965 else g32p_supplierForest_node_088997) else (if i.val < 159 then g32p_supplierForest_node_089001 else g32p_supplierForest_node_089019))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_089022 else g32p_supplierForest_node_089045) else (if i.val < 163 then g32p_supplierForest_node_089070 else g32p_supplierForest_node_089117)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_089118 else g32p_supplierForest_node_089170) else (if i.val < 167 then g32p_supplierForest_node_089219 else g32p_supplierForest_node_089223))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_089322 else g32p_supplierForest_node_089358) else (if i.val < 171 then g32p_supplierForest_node_089365 else g32p_supplierForest_node_089375)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_089408 else g32p_supplierForest_node_089441) else (if i.val < 175 then g32p_supplierForest_node_089460 else g32p_supplierForest_node_089478)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_089493 else g32p_supplierForest_node_089499) else (if i.val < 179 then g32p_supplierForest_node_089539 else g32p_supplierForest_node_089556)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_089562 else g32p_supplierForest_node_089576) else (if i.val < 183 then g32p_supplierForest_node_089610 else g32p_supplierForest_node_089613))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_089633 else g32p_supplierForest_node_089652) else (if i.val < 187 then g32p_supplierForest_node_089681 else g32p_supplierForest_node_089741)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_089758 else g32p_supplierForest_node_089790) else (if i.val < 191 then g32p_supplierForest_node_089847 else g32p_supplierForest_node_089905)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_089924 else g32p_supplierForest_node_089936) else (if i.val < 195 then g32p_supplierForest_node_089974 else g32p_supplierForest_node_090011)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_090054 else g32p_supplierForest_node_090055) else (if i.val < 199 then g32p_supplierForest_node_090149 else g32p_supplierForest_node_090158))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_090177 else g32p_supplierForest_node_090239) else (if i.val < 203 then g32p_supplierForest_node_090263 else g32p_supplierForest_node_090326)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_090357 else g32p_supplierForest_node_090362) else (if i.val < 207 then g32p_supplierForest_node_090378 else g32p_supplierForest_node_090386)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_090418 else g32p_supplierForest_node_090446) else (if i.val < 211 then g32p_supplierForest_node_090462 else g32p_supplierForest_node_090491)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_090535 else g32p_supplierForest_node_090549) else (if i.val < 215 then g32p_supplierForest_node_090569 else g32p_supplierForest_node_090622))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_090694 else g32p_supplierForest_node_090740) else (if i.val < 219 then g32p_supplierForest_node_090773 else g32p_supplierForest_node_090786)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_090843 else g32p_supplierForest_node_090851) else (if i.val < 223 then g32p_supplierForest_node_090860 else g32p_supplierForest_node_090865))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_090936 else g32p_supplierForest_node_090937) else (if i.val < 227 then g32p_supplierForest_node_090940 else g32p_supplierForest_node_090945)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_090986 else g32p_supplierForest_node_091055) else (if i.val < 231 then g32p_supplierForest_node_091087 else g32p_supplierForest_node_091150))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_091263 else g32p_supplierForest_node_091396) else (if i.val < 235 then g32p_supplierForest_node_091410 else g32p_supplierForest_node_091413)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_091423 else g32p_supplierForest_node_091429) else (if i.val < 239 then g32p_supplierForest_node_091480 else g32p_supplierForest_node_091498)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_091522 else g32p_supplierForest_node_091535) else (if i.val < 243 then g32p_supplierForest_node_091617 else g32p_supplierForest_node_091665)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_091671 else g32p_supplierForest_node_091691) else (if i.val < 247 then g32p_supplierForest_node_091814 else g32p_supplierForest_node_091854))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_091916 else g32p_supplierForest_node_091948) else (if i.val < 251 then g32p_supplierForest_node_092002 else g32p_supplierForest_node_092070)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_092084 else g32p_supplierForest_node_092120) else (if i.val < 255 then g32p_supplierForest_node_092139 else g32p_supplierForest_node_092189))))))))

def g32p_supplierForest_classes_046 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 13 else 81) else (if i.val < 3 then 52 else 80)) else (if i.val < 6 then (if i.val < 5 then 46 else 46) else (if i.val < 7 then 48 else 46))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 46 else 56) else (if i.val < 11 then 46 else 26)) else (if i.val < 14 then (if i.val < 13 then 83 else 83) else (if i.val < 15 then 46 else 45)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 54 else 83) else (if i.val < 19 then 54 else 54)) else (if i.val < 22 then (if i.val < 21 then 13 else 45) else (if i.val < 23 then 47 else 83))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 46) else (if i.val < 27 then 46 else 46)) else (if i.val < 30 then (if i.val < 29 then 50 else 50) else (if i.val < 31 then 50 else 50))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 47 else 84) else (if i.val < 35 then 45 else 49)) else (if i.val < 38 then (if i.val < 37 then 84 else 45) else (if i.val < 39 then 47 else 26))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 54 else 56) else (if i.val < 43 then 49 else 13)) else (if i.val < 46 then (if i.val < 45 then 84 else 85) else (if i.val < 47 then 54 else 13)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 80 else 55) else (if i.val < 51 then 50 else 46)) else (if i.val < 54 then (if i.val < 53 then 26 else 54) else (if i.val < 55 then 54 else 49))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 49 else 46) else (if i.val < 59 then 50 else 25)) else (if i.val < 62 then (if i.val < 61 then 46 else 49) else (if i.val < 63 then 46 else 56)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 12) else (if i.val < 67 then 25 else 50)) else (if i.val < 70 then (if i.val < 69 then 49 else 49) else (if i.val < 71 then 56 else 46))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 86 else 56) else (if i.val < 75 then 80 else 47)) else (if i.val < 78 then (if i.val < 77 then 48 else 9) else (if i.val < 79 then 83 else 50)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 48 else 53) else (if i.val < 83 then 49 else 46)) else (if i.val < 86 then (if i.val < 85 then 56 else 84) else (if i.val < 87 then 46 else 46))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 52 else 47) else (if i.val < 91 then 47 else 46)) else (if i.val < 94 then (if i.val < 93 then 46 else 27) else (if i.val < 95 then 47 else 53))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 47 else 56) else (if i.val < 99 then 53 else 48)) else (if i.val < 102 then (if i.val < 101 then 53 else 46) else (if i.val < 103 then 49 else 80))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 46 else 56) else (if i.val < 107 then 49 else 10)) else (if i.val < 110 then (if i.val < 109 then 53 else 46) else (if i.val < 111 then 51 else 26)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 53 else 49) else (if i.val < 115 then 80 else 27)) else (if i.val < 118 then (if i.val < 117 then 46 else 52) else (if i.val < 119 then 49 else 50))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 54 else 84) else (if i.val < 123 then 52 else 53)) else (if i.val < 126 then (if i.val < 125 then 50 else 49) else (if i.val < 127 then 46 else 81))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 50 else 47) else (if i.val < 131 then 47 else 50)) else (if i.val < 134 then (if i.val < 133 then 27 else 11) else (if i.val < 135 then 47 else 45))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 46 else 47) else (if i.val < 139 then 46 else 54)) else (if i.val < 142 then (if i.val < 141 then 25 else 25) else (if i.val < 143 then 53 else 9)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 46 else 45) else (if i.val < 147 then 55 else 83)) else (if i.val < 150 then (if i.val < 149 then 45 else 84) else (if i.val < 151 then 50 else 46))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 46 else 26) else (if i.val < 155 then 56 else 80)) else (if i.val < 158 then (if i.val < 157 then 54 else 47) else (if i.val < 159 then 56 else 45))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 84 else 55) else (if i.val < 163 then 46 else 46)) else (if i.val < 166 then (if i.val < 165 then 83 else 49) else (if i.val < 167 then 47 else 49))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 46 else 52) else (if i.val < 171 then 47 else 86)) else (if i.val < 174 then (if i.val < 173 then 48 else 80) else (if i.val < 175 then 46 else 52)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 55 else 56) else (if i.val < 179 then 48 else 26)) else (if i.val < 182 then (if i.val < 181 then 11 else 46) else (if i.val < 183 then 46 else 50))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 49 else 45) else (if i.val < 187 then 26 else 49)) else (if i.val < 190 then (if i.val < 189 then 52 else 56) else (if i.val < 191 then 45 else 84)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 55 else 11) else (if i.val < 195 then 49 else 84)) else (if i.val < 198 then (if i.val < 197 then 13 else 25) else (if i.val < 199 then 13 else 56))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 46 else 11) else (if i.val < 203 then 48 else 84)) else (if i.val < 206 then (if i.val < 205 then 26 else 50) else (if i.val < 207 then 53 else 54)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 27 else 12) else (if i.val < 211 then 13 else 46)) else (if i.val < 214 then (if i.val < 213 then 49 else 52) else (if i.val < 215 then 80 else 47))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 13 else 11) else (if i.val < 219 then 26 else 26)) else (if i.val < 222 then (if i.val < 221 then 25 else 55) else (if i.val < 223 then 54 else 55))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 26 else 46) else (if i.val < 227 then 81 else 13)) else (if i.val < 230 then (if i.val < 229 then 12 else 25) else (if i.val < 231 then 12 else 25))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 46 else 53) else (if i.val < 235 then 27 else 49)) else (if i.val < 238 then (if i.val < 237 then 82 else 53) else (if i.val < 239 then 47 else 49)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 84 else 53) else (if i.val < 243 then 46 else 46)) else (if i.val < 246 then (if i.val < 245 then 47 else 25) else (if i.val < 247 then 46 else 26))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 86 else 49) else (if i.val < 251 then 9 else 84)) else (if i.val < 254 then (if i.val < 253 then 25 else 84) else (if i.val < 255 then 54 else 13))))))))

theorem g32p_supplierForest_actual_046 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_046 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_046 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_085479
  · exact g32p_supplierForest_actual_085492
  · exact g32p_supplierForest_actual_085529
  · exact g32p_supplierForest_actual_085553
  · exact g32p_supplierForest_actual_085556
  · exact g32p_supplierForest_actual_085564
  · exact g32p_supplierForest_actual_085573
  · exact g32p_supplierForest_actual_085590
  · exact g32p_supplierForest_actual_085597
  · exact g32p_supplierForest_actual_085618
  · exact g32p_supplierForest_actual_085626
  · exact g32p_supplierForest_actual_085634
  · exact g32p_supplierForest_actual_085685
  · exact g32p_supplierForest_actual_085686
  · exact g32p_supplierForest_actual_085695
  · exact g32p_supplierForest_actual_085699
  · exact g32p_supplierForest_actual_085703
  · exact g32p_supplierForest_actual_085716
  · exact g32p_supplierForest_actual_085737
  · exact g32p_supplierForest_actual_085774
  · exact g32p_supplierForest_actual_085778
  · exact g32p_supplierForest_actual_085782
  · exact g32p_supplierForest_actual_085785
  · exact g32p_supplierForest_actual_085839
  · exact g32p_supplierForest_actual_085874
  · exact g32p_supplierForest_actual_085875
  · exact g32p_supplierForest_actual_085963
  · exact g32p_supplierForest_actual_085966
  · exact g32p_supplierForest_actual_085987
  · exact g32p_supplierForest_actual_085988
  · exact g32p_supplierForest_actual_086009
  · exact g32p_supplierForest_actual_086016
  · exact g32p_supplierForest_actual_086017
  · exact g32p_supplierForest_actual_086048
  · exact g32p_supplierForest_actual_086050
  · exact g32p_supplierForest_actual_086054
  · exact g32p_supplierForest_actual_086083
  · exact g32p_supplierForest_actual_086135
  · exact g32p_supplierForest_actual_086168
  · exact g32p_supplierForest_actual_086208
  · exact g32p_supplierForest_actual_086238
  · exact g32p_supplierForest_actual_086245
  · exact g32p_supplierForest_actual_086263
  · exact g32p_supplierForest_actual_086267
  · exact g32p_supplierForest_actual_086337
  · exact g32p_supplierForest_actual_086385
  · exact g32p_supplierForest_actual_086389
  · exact g32p_supplierForest_actual_086394
  · exact g32p_supplierForest_actual_086399
  · exact g32p_supplierForest_actual_086453
  · exact g32p_supplierForest_actual_086455
  · exact g32p_supplierForest_actual_086490
  · exact g32p_supplierForest_actual_086530
  · exact g32p_supplierForest_actual_086536
  · exact g32p_supplierForest_actual_086551
  · exact g32p_supplierForest_actual_086554
  · exact g32p_supplierForest_actual_086555
  · exact g32p_supplierForest_actual_086560
  · exact g32p_supplierForest_actual_086562
  · exact g32p_supplierForest_actual_086589
  · exact g32p_supplierForest_actual_086604
  · exact g32p_supplierForest_actual_086605
  · exact g32p_supplierForest_actual_086622
  · exact g32p_supplierForest_actual_086669
  · exact g32p_supplierForest_actual_086733
  · exact g32p_supplierForest_actual_086779
  · exact g32p_supplierForest_actual_086787
  · exact g32p_supplierForest_actual_086870
  · exact g32p_supplierForest_actual_086932
  · exact g32p_supplierForest_actual_086941
  · exact g32p_supplierForest_actual_086976
  · exact g32p_supplierForest_actual_086998
  · exact g32p_supplierForest_actual_086999
  · exact g32p_supplierForest_actual_087019
  · exact g32p_supplierForest_actual_087058
  · exact g32p_supplierForest_actual_087070
  · exact g32p_supplierForest_actual_087077
  · exact g32p_supplierForest_actual_087101
  · exact g32p_supplierForest_actual_087124
  · exact g32p_supplierForest_actual_087138
  · exact g32p_supplierForest_actual_087257
  · exact g32p_supplierForest_actual_087296
  · exact g32p_supplierForest_actual_087304
  · exact g32p_supplierForest_actual_087324
  · exact g32p_supplierForest_actual_087360
  · exact g32p_supplierForest_actual_087376
  · exact g32p_supplierForest_actual_087422
  · exact g32p_supplierForest_actual_087430
  · exact g32p_supplierForest_actual_087456
  · exact g32p_supplierForest_actual_087458
  · exact g32p_supplierForest_actual_087608
  · exact g32p_supplierForest_actual_087617
  · exact g32p_supplierForest_actual_087625
  · exact g32p_supplierForest_actual_087645
  · exact g32p_supplierForest_actual_087661
  · exact g32p_supplierForest_actual_087671
  · exact g32p_supplierForest_actual_087694
  · exact g32p_supplierForest_actual_087696
  · exact g32p_supplierForest_actual_087722
  · exact g32p_supplierForest_actual_087735
  · exact g32p_supplierForest_actual_087740
  · exact g32p_supplierForest_actual_087748
  · exact g32p_supplierForest_actual_087787
  · exact g32p_supplierForest_actual_087793
  · exact g32p_supplierForest_actual_087797
  · exact g32p_supplierForest_actual_087822
  · exact g32p_supplierForest_actual_087842
  · exact g32p_supplierForest_actual_087852
  · exact g32p_supplierForest_actual_087876
  · exact g32p_supplierForest_actual_087879
  · exact g32p_supplierForest_actual_087902
  · exact g32p_supplierForest_actual_087965
  · exact g32p_supplierForest_actual_088050
  · exact g32p_supplierForest_actual_088074
  · exact g32p_supplierForest_actual_088083
  · exact g32p_supplierForest_actual_088090
  · exact g32p_supplierForest_actual_088101
  · exact g32p_supplierForest_actual_088157
  · exact g32p_supplierForest_actual_088158
  · exact g32p_supplierForest_actual_088180
  · exact g32p_supplierForest_actual_088197
  · exact g32p_supplierForest_actual_088202
  · exact g32p_supplierForest_actual_088218
  · exact g32p_supplierForest_actual_088265
  · exact g32p_supplierForest_actual_088275
  · exact g32p_supplierForest_actual_088284
  · exact g32p_supplierForest_actual_088307
  · exact g32p_supplierForest_actual_088314
  · exact g32p_supplierForest_actual_088322
  · exact g32p_supplierForest_actual_088326
  · exact g32p_supplierForest_actual_088330
  · exact g32p_supplierForest_actual_088338
  · exact g32p_supplierForest_actual_088339
  · exact g32p_supplierForest_actual_088362
  · exact g32p_supplierForest_actual_088420
  · exact g32p_supplierForest_actual_088476
  · exact g32p_supplierForest_actual_088489
  · exact g32p_supplierForest_actual_088512
  · exact g32p_supplierForest_actual_088524
  · exact g32p_supplierForest_actual_088550
  · exact g32p_supplierForest_actual_088551
  · exact g32p_supplierForest_actual_088553
  · exact g32p_supplierForest_actual_088695
  · exact g32p_supplierForest_actual_088696
  · exact g32p_supplierForest_actual_088760
  · exact g32p_supplierForest_actual_088770
  · exact g32p_supplierForest_actual_088813
  · exact g32p_supplierForest_actual_088855
  · exact g32p_supplierForest_actual_088885
  · exact g32p_supplierForest_actual_088906
  · exact g32p_supplierForest_actual_088917
  · exact g32p_supplierForest_actual_088924
  · exact g32p_supplierForest_actual_088927
  · exact g32p_supplierForest_actual_088934
  · exact g32p_supplierForest_actual_088945
  · exact g32p_supplierForest_actual_088956
  · exact g32p_supplierForest_actual_088965
  · exact g32p_supplierForest_actual_088997
  · exact g32p_supplierForest_actual_089001
  · exact g32p_supplierForest_actual_089019
  · exact g32p_supplierForest_actual_089022
  · exact g32p_supplierForest_actual_089045
  · exact g32p_supplierForest_actual_089070
  · exact g32p_supplierForest_actual_089117
  · exact g32p_supplierForest_actual_089118
  · exact g32p_supplierForest_actual_089170
  · exact g32p_supplierForest_actual_089219
  · exact g32p_supplierForest_actual_089223
  · exact g32p_supplierForest_actual_089322
  · exact g32p_supplierForest_actual_089358
  · exact g32p_supplierForest_actual_089365
  · exact g32p_supplierForest_actual_089375
  · exact g32p_supplierForest_actual_089408
  · exact g32p_supplierForest_actual_089441
  · exact g32p_supplierForest_actual_089460
  · exact g32p_supplierForest_actual_089478
  · exact g32p_supplierForest_actual_089493
  · exact g32p_supplierForest_actual_089499
  · exact g32p_supplierForest_actual_089539
  · exact g32p_supplierForest_actual_089556
  · exact g32p_supplierForest_actual_089562
  · exact g32p_supplierForest_actual_089576
  · exact g32p_supplierForest_actual_089610
  · exact g32p_supplierForest_actual_089613
  · exact g32p_supplierForest_actual_089633
  · exact g32p_supplierForest_actual_089652
  · exact g32p_supplierForest_actual_089681
  · exact g32p_supplierForest_actual_089741
  · exact g32p_supplierForest_actual_089758
  · exact g32p_supplierForest_actual_089790
  · exact g32p_supplierForest_actual_089847
  · exact g32p_supplierForest_actual_089905
  · exact g32p_supplierForest_actual_089924
  · exact g32p_supplierForest_actual_089936
  · exact g32p_supplierForest_actual_089974
  · exact g32p_supplierForest_actual_090011
  · exact g32p_supplierForest_actual_090054
  · exact g32p_supplierForest_actual_090055
  · exact g32p_supplierForest_actual_090149
  · exact g32p_supplierForest_actual_090158
  · exact g32p_supplierForest_actual_090177
  · exact g32p_supplierForest_actual_090239
  · exact g32p_supplierForest_actual_090263
  · exact g32p_supplierForest_actual_090326
  · exact g32p_supplierForest_actual_090357
  · exact g32p_supplierForest_actual_090362
  · exact g32p_supplierForest_actual_090378
  · exact g32p_supplierForest_actual_090386
  · exact g32p_supplierForest_actual_090418
  · exact g32p_supplierForest_actual_090446
  · exact g32p_supplierForest_actual_090462
  · exact g32p_supplierForest_actual_090491
  · exact g32p_supplierForest_actual_090535
  · exact g32p_supplierForest_actual_090549
  · exact g32p_supplierForest_actual_090569
  · exact g32p_supplierForest_actual_090622
  · exact g32p_supplierForest_actual_090694
  · exact g32p_supplierForest_actual_090740
  · exact g32p_supplierForest_actual_090773
  · exact g32p_supplierForest_actual_090786
  · exact g32p_supplierForest_actual_090843
  · exact g32p_supplierForest_actual_090851
  · exact g32p_supplierForest_actual_090860
  · exact g32p_supplierForest_actual_090865
  · exact g32p_supplierForest_actual_090936
  · exact g32p_supplierForest_actual_090937
  · exact g32p_supplierForest_actual_090940
  · exact g32p_supplierForest_actual_090945
  · exact g32p_supplierForest_actual_090986
  · exact g32p_supplierForest_actual_091055
  · exact g32p_supplierForest_actual_091087
  · exact g32p_supplierForest_actual_091150
  · exact g32p_supplierForest_actual_091263
  · exact g32p_supplierForest_actual_091396
  · exact g32p_supplierForest_actual_091410
  · exact g32p_supplierForest_actual_091413
  · exact g32p_supplierForest_actual_091423
  · exact g32p_supplierForest_actual_091429
  · exact g32p_supplierForest_actual_091480
  · exact g32p_supplierForest_actual_091498
  · exact g32p_supplierForest_actual_091522
  · exact g32p_supplierForest_actual_091535
  · exact g32p_supplierForest_actual_091617
  · exact g32p_supplierForest_actual_091665
  · exact g32p_supplierForest_actual_091671
  · exact g32p_supplierForest_actual_091691
  · exact g32p_supplierForest_actual_091814
  · exact g32p_supplierForest_actual_091854
  · exact g32p_supplierForest_actual_091916
  · exact g32p_supplierForest_actual_091948
  · exact g32p_supplierForest_actual_092002
  · exact g32p_supplierForest_actual_092070
  · exact g32p_supplierForest_actual_092084
  · exact g32p_supplierForest_actual_092120
  · exact g32p_supplierForest_actual_092139
  · exact g32p_supplierForest_actual_092189

def g32p_supplierForest_nodes_047 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_092193 else g32p_supplierForest_node_092221) else (if i.val < 3 then g32p_supplierForest_node_092283 else g32p_supplierForest_node_092336)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_092340 else g32p_supplierForest_node_092363) else (if i.val < 7 then g32p_supplierForest_node_092415 else g32p_supplierForest_node_092439))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_092508 else g32p_supplierForest_node_092534) else (if i.val < 11 then g32p_supplierForest_node_092541 else g32p_supplierForest_node_092554)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_092557 else g32p_supplierForest_node_092577) else (if i.val < 15 then g32p_supplierForest_node_092586 else g32p_supplierForest_node_092592)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_092619 else g32p_supplierForest_node_092638) else (if i.val < 19 then g32p_supplierForest_node_092651 else g32p_supplierForest_node_092686)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_092758 else g32p_supplierForest_node_092780) else (if i.val < 23 then g32p_supplierForest_node_092790 else g32p_supplierForest_node_092881))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_092884 else g32p_supplierForest_node_092885) else (if i.val < 27 then g32p_supplierForest_node_092921 else g32p_supplierForest_node_092947)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_092959 else g32p_supplierForest_node_092966) else (if i.val < 31 then g32p_supplierForest_node_092967 else g32p_supplierForest_node_092984))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_092988 else g32p_supplierForest_node_092989) else (if i.val < 35 then g32p_supplierForest_node_092992 else g32p_supplierForest_node_093019)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_093031 else g32p_supplierForest_node_093076) else (if i.val < 39 then g32p_supplierForest_node_093094 else g32p_supplierForest_node_093176))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_093201 else g32p_supplierForest_node_093205) else (if i.val < 43 then g32p_supplierForest_node_093242 else g32p_supplierForest_node_093262)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_093281 else g32p_supplierForest_node_093311) else (if i.val < 47 then g32p_supplierForest_node_093318 else g32p_supplierForest_node_093439)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_093444 else g32p_supplierForest_node_093509) else (if i.val < 51 then g32p_supplierForest_node_093529 else g32p_supplierForest_node_093548)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_093553 else g32p_supplierForest_node_093561) else (if i.val < 55 then g32p_supplierForest_node_093585 else g32p_supplierForest_node_093593))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_093612 else g32p_supplierForest_node_093655) else (if i.val < 59 then g32p_supplierForest_node_093662 else g32p_supplierForest_node_093669)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_093683 else g32p_supplierForest_node_093715) else (if i.val < 63 then g32p_supplierForest_node_093740 else g32p_supplierForest_node_093752)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_093759 else g32p_supplierForest_node_093760) else (if i.val < 67 then g32p_supplierForest_node_093776 else g32p_supplierForest_node_093779)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_093789 else g32p_supplierForest_node_093809) else (if i.val < 71 then g32p_supplierForest_node_093831 else g32p_supplierForest_node_093835))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_093847 else g32p_supplierForest_node_093855) else (if i.val < 75 then g32p_supplierForest_node_093869 else g32p_supplierForest_node_093942)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_093959 else g32p_supplierForest_node_094018) else (if i.val < 79 then g32p_supplierForest_node_094047 else g32p_supplierForest_node_094067)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_094068 else g32p_supplierForest_node_094089) else (if i.val < 83 then g32p_supplierForest_node_094110 else g32p_supplierForest_node_094111)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_094118 else g32p_supplierForest_node_094132) else (if i.val < 87 then g32p_supplierForest_node_094160 else g32p_supplierForest_node_094192))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_094276 else g32p_supplierForest_node_094291) else (if i.val < 91 then g32p_supplierForest_node_094293 else g32p_supplierForest_node_094294)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_094340 else g32p_supplierForest_node_094392) else (if i.val < 95 then g32p_supplierForest_node_094398 else g32p_supplierForest_node_094407))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_094433 else g32p_supplierForest_node_094469) else (if i.val < 99 then g32p_supplierForest_node_094470 else g32p_supplierForest_node_094503)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_094507 else g32p_supplierForest_node_094603) else (if i.val < 103 then g32p_supplierForest_node_094631 else g32p_supplierForest_node_094698))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_094735 else g32p_supplierForest_node_094776) else (if i.val < 107 then g32p_supplierForest_node_094782 else g32p_supplierForest_node_094847)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_094891 else g32p_supplierForest_node_094913) else (if i.val < 111 then g32p_supplierForest_node_094926 else g32p_supplierForest_node_094970)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_094972 else g32p_supplierForest_node_095010) else (if i.val < 115 then g32p_supplierForest_node_095026 else g32p_supplierForest_node_095069)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_095169 else g32p_supplierForest_node_095179) else (if i.val < 119 then g32p_supplierForest_node_095187 else g32p_supplierForest_node_095309))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_095331 else g32p_supplierForest_node_095338) else (if i.val < 123 then g32p_supplierForest_node_095491 else g32p_supplierForest_node_095492)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_095512 else g32p_supplierForest_node_095556) else (if i.val < 127 then g32p_supplierForest_node_095566 else g32p_supplierForest_node_095574))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_095587 else g32p_supplierForest_node_095635) else (if i.val < 131 then g32p_supplierForest_node_095652 else g32p_supplierForest_node_095670)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_095711 else g32p_supplierForest_node_095802) else (if i.val < 135 then g32p_supplierForest_node_095811 else g32p_supplierForest_node_095845))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_095853 else g32p_supplierForest_node_095857) else (if i.val < 139 then g32p_supplierForest_node_095966 else g32p_supplierForest_node_095972)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_096037 else g32p_supplierForest_node_096087) else (if i.val < 143 then g32p_supplierForest_node_096098 else g32p_supplierForest_node_096124)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_096134 else g32p_supplierForest_node_096145) else (if i.val < 147 then g32p_supplierForest_node_096146 else g32p_supplierForest_node_096163)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_096167 else g32p_supplierForest_node_096174) else (if i.val < 151 then g32p_supplierForest_node_096192 else g32p_supplierForest_node_096198))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_096201 else g32p_supplierForest_node_096207) else (if i.val < 155 then g32p_supplierForest_node_096298 else g32p_supplierForest_node_096326)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_096333 else g32p_supplierForest_node_096342) else (if i.val < 159 then g32p_supplierForest_node_096344 else g32p_supplierForest_node_096347))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_096567 else g32p_supplierForest_node_096592) else (if i.val < 163 then g32p_supplierForest_node_096597 else g32p_supplierForest_node_096601)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_096614 else g32p_supplierForest_node_096655) else (if i.val < 167 then g32p_supplierForest_node_096686 else g32p_supplierForest_node_096721))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_096735 else g32p_supplierForest_node_096777) else (if i.val < 171 then g32p_supplierForest_node_096789 else g32p_supplierForest_node_096868)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_096872 else g32p_supplierForest_node_096901) else (if i.val < 175 then g32p_supplierForest_node_096965 else g32p_supplierForest_node_096982)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_096985 else g32p_supplierForest_node_097046) else (if i.val < 179 then g32p_supplierForest_node_097063 else g32p_supplierForest_node_097065)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_097110 else g32p_supplierForest_node_097199) else (if i.val < 183 then g32p_supplierForest_node_097245 else g32p_supplierForest_node_097254))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_097268 else g32p_supplierForest_node_097286) else (if i.val < 187 then g32p_supplierForest_node_097323 else g32p_supplierForest_node_097380)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_097492 else g32p_supplierForest_node_097536) else (if i.val < 191 then g32p_supplierForest_node_097539 else g32p_supplierForest_node_097540)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_097543 else g32p_supplierForest_node_097564) else (if i.val < 195 then g32p_supplierForest_node_097596 else g32p_supplierForest_node_097605)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_097624 else g32p_supplierForest_node_097699) else (if i.val < 199 then g32p_supplierForest_node_097741 else g32p_supplierForest_node_097765))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_097773 else g32p_supplierForest_node_097805) else (if i.val < 203 then g32p_supplierForest_node_097847 else g32p_supplierForest_node_097870)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_097873 else g32p_supplierForest_node_097895) else (if i.val < 207 then g32p_supplierForest_node_097953 else g32p_supplierForest_node_097955)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_097958 else g32p_supplierForest_node_097973) else (if i.val < 211 then g32p_supplierForest_node_097977 else g32p_supplierForest_node_097984)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_097993 else g32p_supplierForest_node_098001) else (if i.val < 215 then g32p_supplierForest_node_098008 else g32p_supplierForest_node_098010))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_098057 else g32p_supplierForest_node_098098) else (if i.val < 219 then g32p_supplierForest_node_098103 else g32p_supplierForest_node_098158)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_098189 else g32p_supplierForest_node_098194) else (if i.val < 223 then g32p_supplierForest_node_098209 else g32p_supplierForest_node_098213))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_098214 else g32p_supplierForest_node_098220) else (if i.val < 227 then g32p_supplierForest_node_098225 else g32p_supplierForest_node_098250)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_098267 else g32p_supplierForest_node_098295) else (if i.val < 231 then g32p_supplierForest_node_098319 else g32p_supplierForest_node_098343))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_098350 else g32p_supplierForest_node_098370) else (if i.val < 235 then g32p_supplierForest_node_098457 else g32p_supplierForest_node_098482)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_098485 else g32p_supplierForest_node_098545) else (if i.val < 239 then g32p_supplierForest_node_098553 else g32p_supplierForest_node_098603)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_098614 else g32p_supplierForest_node_098621) else (if i.val < 243 then g32p_supplierForest_node_098622 else g32p_supplierForest_node_098673)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_098697 else g32p_supplierForest_node_098699) else (if i.val < 247 then g32p_supplierForest_node_098709 else g32p_supplierForest_node_098712))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_098770 else g32p_supplierForest_node_098823) else (if i.val < 251 then g32p_supplierForest_node_098849 else g32p_supplierForest_node_098878)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_098883 else g32p_supplierForest_node_098896) else (if i.val < 255 then g32p_supplierForest_node_098953 else g32p_supplierForest_node_099005))))))))

def g32p_supplierForest_classes_047 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 50 else 26) else (if i.val < 3 then 50 else 48)) else (if i.val < 6 then (if i.val < 5 then 49 else 55) else (if i.val < 7 then 47 else 13))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 80 else 49) else (if i.val < 11 then 50 else 25)) else (if i.val < 14 then (if i.val < 13 then 25 else 46) else (if i.val < 15 then 9 else 25)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 49 else 11) else (if i.val < 19 then 83 else 46)) else (if i.val < 22 then (if i.val < 21 then 54 else 26) else (if i.val < 23 then 26 else 13))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 46 else 84) else (if i.val < 27 then 83 else 46)) else (if i.val < 30 then (if i.val < 29 then 49 else 56) else (if i.val < 31 then 50 else 47))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 45 else 47) else (if i.val < 35 then 46 else 26)) else (if i.val < 38 then (if i.val < 37 then 46 else 56) else (if i.val < 39 then 80 else 25))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 46 else 47) else (if i.val < 43 then 46 else 84)) else (if i.val < 46 then (if i.val < 45 then 47 else 49) else (if i.val < 47 then 46 else 13)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 13 else 9) else (if i.val < 51 then 54 else 49)) else (if i.val < 54 then (if i.val < 53 then 50 else 46) else (if i.val < 55 then 49 else 56))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 81 else 55) else (if i.val < 59 then 50 else 49)) else (if i.val < 62 then (if i.val < 61 then 84 else 49) else (if i.val < 63 then 49 else 50)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 13 else 50) else (if i.val < 67 then 53 else 80)) else (if i.val < 70 then (if i.val < 69 then 45 else 49) else (if i.val < 71 then 46 else 25))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 56 else 52) else (if i.val < 75 then 25 else 12)) else (if i.val < 78 then (if i.val < 77 then 46 else 49) else (if i.val < 79 then 54 else 82)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 50 else 47) else (if i.val < 83 then 80 else 27)) else (if i.val < 86 then (if i.val < 85 then 50 else 45) else (if i.val < 87 then 49 else 47))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 46 else 13) else (if i.val < 91 then 49 else 49)) else (if i.val < 94 then (if i.val < 93 then 49 else 47) else (if i.val < 95 then 81 else 47))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 26 else 13) else (if i.val < 99 then 46 else 46)) else (if i.val < 102 then (if i.val < 101 then 46 else 56) else (if i.val < 103 then 50 else 13))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 46 else 13) else (if i.val < 107 then 53 else 49)) else (if i.val < 110 then (if i.val < 109 then 80 else 56) else (if i.val < 111 then 84 else 54)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 46 else 25) else (if i.val < 115 then 46 else 26)) else (if i.val < 118 then (if i.val < 117 then 49 else 9) else (if i.val < 119 then 49 else 11))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 13 else 82) else (if i.val < 123 then 49 else 25)) else (if i.val < 126 then (if i.val < 125 then 26 else 82) else (if i.val < 127 then 81 else 85))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 13 else 46) else (if i.val < 131 then 45 else 13)) else (if i.val < 134 then (if i.val < 133 then 49 else 25) else (if i.val < 135 then 49 else 26))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 49 else 26) else (if i.val < 139 then 26 else 9)) else (if i.val < 142 then (if i.val < 141 then 13 else 54) else (if i.val < 143 then 49 else 50)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 46 else 47) else (if i.val < 147 then 45 else 26)) else (if i.val < 150 then (if i.val < 149 then 83 else 85) else (if i.val < 151 then 13 else 84))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 46 else 48) else (if i.val < 155 then 47 else 46)) else (if i.val < 158 then (if i.val < 157 then 51 else 47) else (if i.val < 159 then 46 else 48))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 80 else 9) else (if i.val < 163 then 26 else 84)) else (if i.val < 166 then (if i.val < 165 then 26 else 46) else (if i.val < 167 then 13 else 45))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 11 else 46) else (if i.val < 171 then 45 else 85)) else (if i.val < 174 then (if i.val < 173 then 26 else 46) else (if i.val < 175 then 52 else 13)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 46 else 82) else (if i.val < 179 then 81 else 25)) else (if i.val < 182 then (if i.val < 181 then 50 else 54) else (if i.val < 183 then 46 else 13))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 83 else 26) else (if i.val < 187 then 26 else 13)) else (if i.val < 190 then (if i.val < 189 then 49 else 13) else (if i.val < 191 then 55 else 55)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 80 else 50) else (if i.val < 195 then 25 else 55)) else (if i.val < 198 then (if i.val < 197 then 53 else 47) else (if i.val < 199 then 56 else 46))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 80 else 84) else (if i.val < 203 then 48 else 54)) else (if i.val < 206 then (if i.val < 205 then 85 else 49) else (if i.val < 207 then 49 else 53)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 13 else 25) else (if i.val < 211 then 47 else 80)) else (if i.val < 214 then (if i.val < 213 then 83 else 52) else (if i.val < 215 then 45 else 84))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 47 else 86) else (if i.val < 219 then 86 else 11)) else (if i.val < 222 then (if i.val < 221 then 45 else 52) else (if i.val < 223 then 45 else 49))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 56 else 45) else (if i.val < 227 then 49 else 54)) else (if i.val < 230 then (if i.val < 229 then 55 else 56) else (if i.val < 231 then 80 else 53))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 52 else 25) else (if i.val < 235 then 53 else 46)) else (if i.val < 238 then (if i.val < 237 then 53 else 26) else (if i.val < 239 then 50 else 83)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 53 else 26) else (if i.val < 243 then 49 else 45)) else (if i.val < 246 then (if i.val < 245 then 80 else 46) else (if i.val < 247 then 26 else 49))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 81 else 80) else (if i.val < 251 then 50 else 80)) else (if i.val < 254 then (if i.val < 253 then 47 else 80) else (if i.val < 255 then 82 else 46))))))))

theorem g32p_supplierForest_actual_047 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_047 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_047 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_092193
  · exact g32p_supplierForest_actual_092221
  · exact g32p_supplierForest_actual_092283
  · exact g32p_supplierForest_actual_092336
  · exact g32p_supplierForest_actual_092340
  · exact g32p_supplierForest_actual_092363
  · exact g32p_supplierForest_actual_092415
  · exact g32p_supplierForest_actual_092439
  · exact g32p_supplierForest_actual_092508
  · exact g32p_supplierForest_actual_092534
  · exact g32p_supplierForest_actual_092541
  · exact g32p_supplierForest_actual_092554
  · exact g32p_supplierForest_actual_092557
  · exact g32p_supplierForest_actual_092577
  · exact g32p_supplierForest_actual_092586
  · exact g32p_supplierForest_actual_092592
  · exact g32p_supplierForest_actual_092619
  · exact g32p_supplierForest_actual_092638
  · exact g32p_supplierForest_actual_092651
  · exact g32p_supplierForest_actual_092686
  · exact g32p_supplierForest_actual_092758
  · exact g32p_supplierForest_actual_092780
  · exact g32p_supplierForest_actual_092790
  · exact g32p_supplierForest_actual_092881
  · exact g32p_supplierForest_actual_092884
  · exact g32p_supplierForest_actual_092885
  · exact g32p_supplierForest_actual_092921
  · exact g32p_supplierForest_actual_092947
  · exact g32p_supplierForest_actual_092959
  · exact g32p_supplierForest_actual_092966
  · exact g32p_supplierForest_actual_092967
  · exact g32p_supplierForest_actual_092984
  · exact g32p_supplierForest_actual_092988
  · exact g32p_supplierForest_actual_092989
  · exact g32p_supplierForest_actual_092992
  · exact g32p_supplierForest_actual_093019
  · exact g32p_supplierForest_actual_093031
  · exact g32p_supplierForest_actual_093076
  · exact g32p_supplierForest_actual_093094
  · exact g32p_supplierForest_actual_093176
  · exact g32p_supplierForest_actual_093201
  · exact g32p_supplierForest_actual_093205
  · exact g32p_supplierForest_actual_093242
  · exact g32p_supplierForest_actual_093262
  · exact g32p_supplierForest_actual_093281
  · exact g32p_supplierForest_actual_093311
  · exact g32p_supplierForest_actual_093318
  · exact g32p_supplierForest_actual_093439
  · exact g32p_supplierForest_actual_093444
  · exact g32p_supplierForest_actual_093509
  · exact g32p_supplierForest_actual_093529
  · exact g32p_supplierForest_actual_093548
  · exact g32p_supplierForest_actual_093553
  · exact g32p_supplierForest_actual_093561
  · exact g32p_supplierForest_actual_093585
  · exact g32p_supplierForest_actual_093593
  · exact g32p_supplierForest_actual_093612
  · exact g32p_supplierForest_actual_093655
  · exact g32p_supplierForest_actual_093662
  · exact g32p_supplierForest_actual_093669
  · exact g32p_supplierForest_actual_093683
  · exact g32p_supplierForest_actual_093715
  · exact g32p_supplierForest_actual_093740
  · exact g32p_supplierForest_actual_093752
  · exact g32p_supplierForest_actual_093759
  · exact g32p_supplierForest_actual_093760
  · exact g32p_supplierForest_actual_093776
  · exact g32p_supplierForest_actual_093779
  · exact g32p_supplierForest_actual_093789
  · exact g32p_supplierForest_actual_093809
  · exact g32p_supplierForest_actual_093831
  · exact g32p_supplierForest_actual_093835
  · exact g32p_supplierForest_actual_093847
  · exact g32p_supplierForest_actual_093855
  · exact g32p_supplierForest_actual_093869
  · exact g32p_supplierForest_actual_093942
  · exact g32p_supplierForest_actual_093959
  · exact g32p_supplierForest_actual_094018
  · exact g32p_supplierForest_actual_094047
  · exact g32p_supplierForest_actual_094067
  · exact g32p_supplierForest_actual_094068
  · exact g32p_supplierForest_actual_094089
  · exact g32p_supplierForest_actual_094110
  · exact g32p_supplierForest_actual_094111
  · exact g32p_supplierForest_actual_094118
  · exact g32p_supplierForest_actual_094132
  · exact g32p_supplierForest_actual_094160
  · exact g32p_supplierForest_actual_094192
  · exact g32p_supplierForest_actual_094276
  · exact g32p_supplierForest_actual_094291
  · exact g32p_supplierForest_actual_094293
  · exact g32p_supplierForest_actual_094294
  · exact g32p_supplierForest_actual_094340
  · exact g32p_supplierForest_actual_094392
  · exact g32p_supplierForest_actual_094398
  · exact g32p_supplierForest_actual_094407
  · exact g32p_supplierForest_actual_094433
  · exact g32p_supplierForest_actual_094469
  · exact g32p_supplierForest_actual_094470
  · exact g32p_supplierForest_actual_094503
  · exact g32p_supplierForest_actual_094507
  · exact g32p_supplierForest_actual_094603
  · exact g32p_supplierForest_actual_094631
  · exact g32p_supplierForest_actual_094698
  · exact g32p_supplierForest_actual_094735
  · exact g32p_supplierForest_actual_094776
  · exact g32p_supplierForest_actual_094782
  · exact g32p_supplierForest_actual_094847
  · exact g32p_supplierForest_actual_094891
  · exact g32p_supplierForest_actual_094913
  · exact g32p_supplierForest_actual_094926
  · exact g32p_supplierForest_actual_094970
  · exact g32p_supplierForest_actual_094972
  · exact g32p_supplierForest_actual_095010
  · exact g32p_supplierForest_actual_095026
  · exact g32p_supplierForest_actual_095069
  · exact g32p_supplierForest_actual_095169
  · exact g32p_supplierForest_actual_095179
  · exact g32p_supplierForest_actual_095187
  · exact g32p_supplierForest_actual_095309
  · exact g32p_supplierForest_actual_095331
  · exact g32p_supplierForest_actual_095338
  · exact g32p_supplierForest_actual_095491
  · exact g32p_supplierForest_actual_095492
  · exact g32p_supplierForest_actual_095512
  · exact g32p_supplierForest_actual_095556
  · exact g32p_supplierForest_actual_095566
  · exact g32p_supplierForest_actual_095574
  · exact g32p_supplierForest_actual_095587
  · exact g32p_supplierForest_actual_095635
  · exact g32p_supplierForest_actual_095652
  · exact g32p_supplierForest_actual_095670
  · exact g32p_supplierForest_actual_095711
  · exact g32p_supplierForest_actual_095802
  · exact g32p_supplierForest_actual_095811
  · exact g32p_supplierForest_actual_095845
  · exact g32p_supplierForest_actual_095853
  · exact g32p_supplierForest_actual_095857
  · exact g32p_supplierForest_actual_095966
  · exact g32p_supplierForest_actual_095972
  · exact g32p_supplierForest_actual_096037
  · exact g32p_supplierForest_actual_096087
  · exact g32p_supplierForest_actual_096098
  · exact g32p_supplierForest_actual_096124
  · exact g32p_supplierForest_actual_096134
  · exact g32p_supplierForest_actual_096145
  · exact g32p_supplierForest_actual_096146
  · exact g32p_supplierForest_actual_096163
  · exact g32p_supplierForest_actual_096167
  · exact g32p_supplierForest_actual_096174
  · exact g32p_supplierForest_actual_096192
  · exact g32p_supplierForest_actual_096198
  · exact g32p_supplierForest_actual_096201
  · exact g32p_supplierForest_actual_096207
  · exact g32p_supplierForest_actual_096298
  · exact g32p_supplierForest_actual_096326
  · exact g32p_supplierForest_actual_096333
  · exact g32p_supplierForest_actual_096342
  · exact g32p_supplierForest_actual_096344
  · exact g32p_supplierForest_actual_096347
  · exact g32p_supplierForest_actual_096567
  · exact g32p_supplierForest_actual_096592
  · exact g32p_supplierForest_actual_096597
  · exact g32p_supplierForest_actual_096601
  · exact g32p_supplierForest_actual_096614
  · exact g32p_supplierForest_actual_096655
  · exact g32p_supplierForest_actual_096686
  · exact g32p_supplierForest_actual_096721
  · exact g32p_supplierForest_actual_096735
  · exact g32p_supplierForest_actual_096777
  · exact g32p_supplierForest_actual_096789
  · exact g32p_supplierForest_actual_096868
  · exact g32p_supplierForest_actual_096872
  · exact g32p_supplierForest_actual_096901
  · exact g32p_supplierForest_actual_096965
  · exact g32p_supplierForest_actual_096982
  · exact g32p_supplierForest_actual_096985
  · exact g32p_supplierForest_actual_097046
  · exact g32p_supplierForest_actual_097063
  · exact g32p_supplierForest_actual_097065
  · exact g32p_supplierForest_actual_097110
  · exact g32p_supplierForest_actual_097199
  · exact g32p_supplierForest_actual_097245
  · exact g32p_supplierForest_actual_097254
  · exact g32p_supplierForest_actual_097268
  · exact g32p_supplierForest_actual_097286
  · exact g32p_supplierForest_actual_097323
  · exact g32p_supplierForest_actual_097380
  · exact g32p_supplierForest_actual_097492
  · exact g32p_supplierForest_actual_097536
  · exact g32p_supplierForest_actual_097539
  · exact g32p_supplierForest_actual_097540
  · exact g32p_supplierForest_actual_097543
  · exact g32p_supplierForest_actual_097564
  · exact g32p_supplierForest_actual_097596
  · exact g32p_supplierForest_actual_097605
  · exact g32p_supplierForest_actual_097624
  · exact g32p_supplierForest_actual_097699
  · exact g32p_supplierForest_actual_097741
  · exact g32p_supplierForest_actual_097765
  · exact g32p_supplierForest_actual_097773
  · exact g32p_supplierForest_actual_097805
  · exact g32p_supplierForest_actual_097847
  · exact g32p_supplierForest_actual_097870
  · exact g32p_supplierForest_actual_097873
  · exact g32p_supplierForest_actual_097895
  · exact g32p_supplierForest_actual_097953
  · exact g32p_supplierForest_actual_097955
  · exact g32p_supplierForest_actual_097958
  · exact g32p_supplierForest_actual_097973
  · exact g32p_supplierForest_actual_097977
  · exact g32p_supplierForest_actual_097984
  · exact g32p_supplierForest_actual_097993
  · exact g32p_supplierForest_actual_098001
  · exact g32p_supplierForest_actual_098008
  · exact g32p_supplierForest_actual_098010
  · exact g32p_supplierForest_actual_098057
  · exact g32p_supplierForest_actual_098098
  · exact g32p_supplierForest_actual_098103
  · exact g32p_supplierForest_actual_098158
  · exact g32p_supplierForest_actual_098189
  · exact g32p_supplierForest_actual_098194
  · exact g32p_supplierForest_actual_098209
  · exact g32p_supplierForest_actual_098213
  · exact g32p_supplierForest_actual_098214
  · exact g32p_supplierForest_actual_098220
  · exact g32p_supplierForest_actual_098225
  · exact g32p_supplierForest_actual_098250
  · exact g32p_supplierForest_actual_098267
  · exact g32p_supplierForest_actual_098295
  · exact g32p_supplierForest_actual_098319
  · exact g32p_supplierForest_actual_098343
  · exact g32p_supplierForest_actual_098350
  · exact g32p_supplierForest_actual_098370
  · exact g32p_supplierForest_actual_098457
  · exact g32p_supplierForest_actual_098482
  · exact g32p_supplierForest_actual_098485
  · exact g32p_supplierForest_actual_098545
  · exact g32p_supplierForest_actual_098553
  · exact g32p_supplierForest_actual_098603
  · exact g32p_supplierForest_actual_098614
  · exact g32p_supplierForest_actual_098621
  · exact g32p_supplierForest_actual_098622
  · exact g32p_supplierForest_actual_098673
  · exact g32p_supplierForest_actual_098697
  · exact g32p_supplierForest_actual_098699
  · exact g32p_supplierForest_actual_098709
  · exact g32p_supplierForest_actual_098712
  · exact g32p_supplierForest_actual_098770
  · exact g32p_supplierForest_actual_098823
  · exact g32p_supplierForest_actual_098849
  · exact g32p_supplierForest_actual_098878
  · exact g32p_supplierForest_actual_098883
  · exact g32p_supplierForest_actual_098896
  · exact g32p_supplierForest_actual_098953
  · exact g32p_supplierForest_actual_099005

end HodgeLean.Foundations.Program

end
end
