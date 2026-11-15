import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0228
import HodgeLean.Foundations.Program.G32PropFourSixPacked0229
import HodgeLean.Foundations.Program.G32PropFourSixPacked0230
import HodgeLean.Foundations.Program.G32PropFourSixPacked0236
import HodgeLean.Foundations.Program.G32PropFourSixPacked0237
import HodgeLean.Foundations.Program.G32PropFourSixPacked0238
import HodgeLean.Foundations.Program.G32PropFourSixPacked0240

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_108117 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_108117 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108117 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_026857 := by
  decide +kernel

theorem g32p_supplierForest_actual_108117 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108117) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_108117
    g32p_supplierForest_actual_026857

def g32p_supplierForest_node_108135 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108135 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108135 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_118731 := by
  decide +kernel

theorem g32p_supplierForest_actual_108135 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108135) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_108135
    g32p_supplierForest_actual_118731

def g32p_supplierForest_node_108176 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108176 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108176 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_117463 := by
  decide +kernel

theorem g32p_supplierForest_actual_108176 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108176) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_108176
    g32p_supplierForest_actual_117463

def g32p_supplierForest_node_108321 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108321 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108321 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_041550 := by
  decide +kernel

theorem g32p_supplierForest_actual_108321 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108321) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 0 g32p_supplierForest_edge_108321
    g32p_supplierForest_actual_041550

def g32p_supplierForest_node_108330 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_108330 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108330 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_038303 := by
  decide +kernel

theorem g32p_supplierForest_actual_108330 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108330) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_108330
    g32p_supplierForest_actual_038303

def g32p_supplierForest_node_108344 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108344 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108344 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_040429 := by
  decide +kernel

theorem g32p_supplierForest_actual_108344 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108344) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_108344
    g32p_supplierForest_actual_040429

def g32p_supplierForest_node_108383 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_108383 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108383 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117237 := by
  decide +kernel

theorem g32p_supplierForest_actual_108383 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108383) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_108383
    g32p_supplierForest_actual_117237

def g32p_supplierForest_node_108405 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_108405 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108405 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122174 := by
  decide +kernel

theorem g32p_supplierForest_actual_108405 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108405) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_108405
    g32p_supplierForest_actual_122174

def g32p_supplierForest_node_108409 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_108409 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108409 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_126342 := by
  decide +kernel

theorem g32p_supplierForest_actual_108409 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108409) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_108409
    g32p_supplierForest_actual_126342

def g32p_supplierForest_node_108471 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_108471 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108471 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_106715 := by
  decide +kernel

theorem g32p_supplierForest_actual_108471 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108471) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 1 g32p_supplierForest_edge_108471
    g32p_supplierForest_actual_106715

def g32p_supplierForest_node_108507 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_108507 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108507 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_119089 := by
  decide +kernel

theorem g32p_supplierForest_actual_108507 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108507) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_108507
    g32p_supplierForest_actual_119089

def g32p_supplierForest_node_108510 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_108510 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108510 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_107033 := by
  decide +kernel

theorem g32p_supplierForest_actual_108510 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108510) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 0 g32p_supplierForest_edge_108510
    g32p_supplierForest_actual_107033

def g32p_supplierForest_node_108520 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_108520 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108520 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_026261 := by
  decide +kernel

theorem g32p_supplierForest_actual_108520 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108520) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_108520
    g32p_supplierForest_actual_026261

def g32p_supplierForest_node_108523 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_108523 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108523 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153712 := by
  decide +kernel

theorem g32p_supplierForest_actual_108523 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108523) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_108523
    g32p_supplierForest_actual_153712

def g32p_supplierForest_node_108528 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108528 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108528 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117076 := by
  decide +kernel

theorem g32p_supplierForest_actual_108528 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108528) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_108528
    g32p_supplierForest_actual_117076

def g32p_supplierForest_node_108531 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_108531 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108531 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_116990 := by
  decide +kernel

theorem g32p_supplierForest_actual_108531 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108531) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_108531
    g32p_supplierForest_actual_116990

def g32p_supplierForest_node_108545 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_108545 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108545 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_108546 := by
  decide +kernel

theorem g32p_supplierForest_actual_108545 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108545) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_108545
    g32p_supplierForest_actual_108546

def g32p_supplierForest_node_108560 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108560 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108560 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_109300 := by
  decide +kernel

theorem g32p_supplierForest_actual_108560 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108560) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_108560
    g32p_supplierForest_actual_109300

def g32p_supplierForest_node_108606 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108606 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108606 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117437 := by
  decide +kernel

theorem g32p_supplierForest_actual_108606 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108606) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_108606
    g32p_supplierForest_actual_117437

def g32p_supplierForest_node_108617 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_108617 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108617 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_119167 := by
  decide +kernel

theorem g32p_supplierForest_actual_108617 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108617) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_108617
    g32p_supplierForest_actual_119167

def g32p_supplierForest_node_108623 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108623 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108623 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_038468 := by
  decide +kernel

theorem g32p_supplierForest_actual_108623 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108623) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_108623
    g32p_supplierForest_actual_038468

def g32p_supplierForest_node_108635 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108635 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108635 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102769 := by
  decide +kernel

theorem g32p_supplierForest_actual_108635 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108635) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_108635
    g32p_supplierForest_actual_102769

def g32p_supplierForest_node_108638 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_108638 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108638 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117801 := by
  decide +kernel

theorem g32p_supplierForest_actual_108638 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108638) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_108638
    g32p_supplierForest_actual_117801

def g32p_supplierForest_node_108640 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108640 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108640 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_038453 := by
  decide +kernel

theorem g32p_supplierForest_actual_108640 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108640) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_108640
    g32p_supplierForest_actual_038453

def g32p_supplierForest_node_108641 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_108641 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108641 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_033304 := by
  decide +kernel

theorem g32p_supplierForest_actual_108641 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108641) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_108641
    g32p_supplierForest_actual_033304

def g32p_supplierForest_node_108692 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108692 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108692 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_120389 := by
  decide +kernel

theorem g32p_supplierForest_actual_108692 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108692) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_108692
    g32p_supplierForest_actual_120389

def g32p_supplierForest_node_108696 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_108696 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108696 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108316 := by
  decide +kernel

theorem g32p_supplierForest_actual_108696 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108696) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_108696
    g32p_supplierForest_actual_108316

def g32p_supplierForest_node_108720 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_108720 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108720 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_042524 := by
  decide +kernel

theorem g32p_supplierForest_actual_108720 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108720) ∧
        IsConj g (g32p_literalRepresentative 64) := by
  exact g32p_archive_step_lift _ _ 64 3 g32p_supplierForest_edge_108720
    g32p_supplierForest_actual_042524

def g32p_supplierForest_node_108750 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_108750 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108750 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118365 := by
  decide +kernel

theorem g32p_supplierForest_actual_108750 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108750) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_108750
    g32p_supplierForest_actual_118365

def g32p_supplierForest_node_108780 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_108780 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108780 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_035111 := by
  decide +kernel

theorem g32p_supplierForest_actual_108780 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108780) ∧
        IsConj g (g32p_literalRepresentative 64) := by
  exact g32p_archive_step_lift _ _ 64 1 g32p_supplierForest_edge_108780
    g32p_supplierForest_actual_035111

def g32p_supplierForest_node_108783 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_108783 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108783 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_111184 := by
  decide +kernel

theorem g32p_supplierForest_actual_108783 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108783) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_108783
    g32p_supplierForest_actual_111184

def g32p_supplierForest_node_108787 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_108787 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108787 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_031233 := by
  decide +kernel

theorem g32p_supplierForest_actual_108787 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108787) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_108787
    g32p_supplierForest_actual_031233

def g32p_supplierForest_node_108789 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_108789 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108789 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102088 := by
  decide +kernel

theorem g32p_supplierForest_actual_108789 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108789) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_108789
    g32p_supplierForest_actual_102088

def g32p_supplierForest_node_108821 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108821 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108821 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_102398 := by
  decide +kernel

theorem g32p_supplierForest_actual_108821 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108821) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_108821
    g32p_supplierForest_actual_102398

def g32p_supplierForest_node_108837 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_108837 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108837 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037008 := by
  decide +kernel

theorem g32p_supplierForest_actual_108837 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108837) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_108837
    g32p_supplierForest_actual_037008

def g32p_supplierForest_node_108840 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108840 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108840 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112423 := by
  decide +kernel

theorem g32p_supplierForest_actual_108840 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108840) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_108840
    g32p_supplierForest_actual_112423

def g32p_supplierForest_node_108858 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_108858 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108858 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102257 := by
  decide +kernel

theorem g32p_supplierForest_actual_108858 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108858) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_108858
    g32p_supplierForest_actual_102257

def g32p_supplierForest_node_108866 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_108866 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108866 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_152605 := by
  decide +kernel

theorem g32p_supplierForest_actual_108866 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108866) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_108866
    g32p_supplierForest_actual_152605

def g32p_supplierForest_node_108884 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108884 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108884 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_038293 := by
  decide +kernel

theorem g32p_supplierForest_actual_108884 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108884) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_108884
    g32p_supplierForest_actual_038293

def g32p_supplierForest_node_108885 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108885 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108885 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_031947 := by
  decide +kernel

theorem g32p_supplierForest_actual_108885 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108885) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_108885
    g32p_supplierForest_actual_031947

def g32p_supplierForest_node_108899 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_108899 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108899 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_024949 := by
  decide +kernel

theorem g32p_supplierForest_actual_108899 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108899) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_108899
    g32p_supplierForest_actual_024949

def g32p_supplierForest_node_108925 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_108925 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108925 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029601 := by
  decide +kernel

theorem g32p_supplierForest_actual_108925 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108925) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_108925
    g32p_supplierForest_actual_029601

def g32p_supplierForest_node_108954 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_108954 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108954 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_024991 := by
  decide +kernel

theorem g32p_supplierForest_actual_108954 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108954) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_108954
    g32p_supplierForest_actual_024991

def g32p_supplierForest_node_108963 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_108963 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108963 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_042551 := by
  decide +kernel

theorem g32p_supplierForest_actual_108963 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108963) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_108963
    g32p_supplierForest_actual_042551

def g32p_supplierForest_node_108991 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_108991 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_108991 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_103923 := by
  decide +kernel

theorem g32p_supplierForest_actual_108991 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_108991) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_108991
    g32p_supplierForest_actual_103923

def g32p_supplierForest_node_109010 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_109010 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109010 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_119517 := by
  decide +kernel

theorem g32p_supplierForest_actual_109010 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109010) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_109010
    g32p_supplierForest_actual_119517

def g32p_supplierForest_node_109063 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_109063 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109063 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104169 := by
  decide +kernel

theorem g32p_supplierForest_actual_109063 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109063) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_109063
    g32p_supplierForest_actual_104169

def g32p_supplierForest_node_109064 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109064 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109064 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_036488 := by
  decide +kernel

theorem g32p_supplierForest_actual_109064 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109064) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_109064
    g32p_supplierForest_actual_036488

def g32p_supplierForest_node_109068 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_109068 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109068 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_042583 := by
  decide +kernel

theorem g32p_supplierForest_actual_109068 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109068) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_109068
    g32p_supplierForest_actual_042583

def g32p_supplierForest_node_109082 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_109082 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109082 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_025077 := by
  decide +kernel

theorem g32p_supplierForest_actual_109082 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109082) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_109082
    g32p_supplierForest_actual_025077

def g32p_supplierForest_node_109106 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_109106 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109106 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122025 := by
  decide +kernel

theorem g32p_supplierForest_actual_109106 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109106) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_109106
    g32p_supplierForest_actual_122025

def g32p_supplierForest_node_109109 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_109109 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109109 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_108121 := by
  decide +kernel

theorem g32p_supplierForest_actual_109109 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109109) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_109109
    g32p_supplierForest_actual_108121

def g32p_supplierForest_node_109156 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_109156 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109156 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112037 := by
  decide +kernel

theorem g32p_supplierForest_actual_109156 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109156) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_109156
    g32p_supplierForest_actual_112037

def g32p_supplierForest_node_109166 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_109166 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109166 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122044 := by
  decide +kernel

theorem g32p_supplierForest_actual_109166 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109166) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_109166
    g32p_supplierForest_actual_122044

def g32p_supplierForest_node_109172 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_109172 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109172 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122047 := by
  decide +kernel

theorem g32p_supplierForest_actual_109172 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109172) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 3 g32p_supplierForest_edge_109172
    g32p_supplierForest_actual_122047

def g32p_supplierForest_node_109174 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_109174 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109174 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_105168 := by
  decide +kernel

theorem g32p_supplierForest_actual_109174 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109174) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_109174
    g32p_supplierForest_actual_105168

def g32p_supplierForest_node_109176 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109176 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109176 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_115648 := by
  decide +kernel

theorem g32p_supplierForest_actual_109176 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109176) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_109176
    g32p_supplierForest_actual_115648

def g32p_supplierForest_node_109178 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_109178 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109178 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109196 := by
  decide +kernel

theorem g32p_supplierForest_actual_109178 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109178) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_109178
    g32p_supplierForest_actual_109196

def g32p_supplierForest_node_109179 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_109179 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109179 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109197 := by
  decide +kernel

theorem g32p_supplierForest_actual_109179 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109179) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_109179
    g32p_supplierForest_actual_109197

def g32p_supplierForest_node_109187 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109187 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109187 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_041215 := by
  decide +kernel

theorem g32p_supplierForest_actual_109187 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109187) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_109187
    g32p_supplierForest_actual_041215

def g32p_supplierForest_node_109214 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109214 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109214 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112995 := by
  decide +kernel

theorem g32p_supplierForest_actual_109214 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109214) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_109214
    g32p_supplierForest_actual_112995

def g32p_supplierForest_node_109267 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109267 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109267 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104899 := by
  decide +kernel

theorem g32p_supplierForest_actual_109267 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109267) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_109267
    g32p_supplierForest_actual_104899

def g32p_supplierForest_node_109345 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109345 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109345 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109220 := by
  decide +kernel

theorem g32p_supplierForest_actual_109345 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109345) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_109345
    g32p_supplierForest_actual_109220

def g32p_supplierForest_node_109356 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_109356 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109356 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_038347 := by
  decide +kernel

theorem g32p_supplierForest_actual_109356 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109356) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 1 g32p_supplierForest_edge_109356
    g32p_supplierForest_actual_038347

def g32p_supplierForest_node_109366 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109366 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109366 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123568 := by
  decide +kernel

theorem g32p_supplierForest_actual_109366 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109366) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_109366
    g32p_supplierForest_actual_123568

def g32p_supplierForest_node_109416 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109416 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109416 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_118145 := by
  decide +kernel

theorem g32p_supplierForest_actual_109416 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109416) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_109416
    g32p_supplierForest_actual_118145

def g32p_supplierForest_node_109438 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109438 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109438 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_125617 := by
  decide +kernel

theorem g32p_supplierForest_actual_109438 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109438) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 1 g32p_supplierForest_edge_109438
    g32p_supplierForest_actual_125617

def g32p_supplierForest_node_109469 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109469 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109469 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104421 := by
  decide +kernel

theorem g32p_supplierForest_actual_109469 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109469) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_109469
    g32p_supplierForest_actual_104421

def g32p_supplierForest_node_109479 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109479 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109479 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_030659 := by
  decide +kernel

theorem g32p_supplierForest_actual_109479 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109479) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_109479
    g32p_supplierForest_actual_030659

def g32p_supplierForest_node_109500 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109500 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109500 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037976 := by
  decide +kernel

theorem g32p_supplierForest_actual_109500 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109500) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_109500
    g32p_supplierForest_actual_037976

def g32p_supplierForest_node_109579 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_109579 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109579 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_025679 := by
  decide +kernel

theorem g32p_supplierForest_actual_109579 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109579) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_109579
    g32p_supplierForest_actual_025679

def g32p_supplierForest_node_109614 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_109614 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109614 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_034809 := by
  decide +kernel

theorem g32p_supplierForest_actual_109614 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109614) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_109614
    g32p_supplierForest_actual_034809

def g32p_supplierForest_node_109615 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109615 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109615 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037269 := by
  decide +kernel

theorem g32p_supplierForest_actual_109615 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109615) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_109615
    g32p_supplierForest_actual_037269

def g32p_supplierForest_node_109631 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109631 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109631 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_025702 := by
  decide +kernel

theorem g32p_supplierForest_actual_109631 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109631) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_109631
    g32p_supplierForest_actual_025702

def g32p_supplierForest_node_109634 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_109634 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109634 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_115786 := by
  decide +kernel

theorem g32p_supplierForest_actual_109634 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109634) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_109634
    g32p_supplierForest_actual_115786

def g32p_supplierForest_node_109639 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_109639 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109639 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_105816 := by
  decide +kernel

theorem g32p_supplierForest_actual_109639 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109639) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 1 g32p_supplierForest_edge_109639
    g32p_supplierForest_actual_105816

def g32p_supplierForest_node_109648 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_109648 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109648 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038262 := by
  decide +kernel

theorem g32p_supplierForest_actual_109648 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109648) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_109648
    g32p_supplierForest_actual_038262

def g32p_supplierForest_node_109675 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_109675 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109675 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_105168 := by
  decide +kernel

theorem g32p_supplierForest_actual_109675 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109675) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_109675
    g32p_supplierForest_actual_105168

def g32p_supplierForest_node_109683 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109683 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109683 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_107762 := by
  decide +kernel

theorem g32p_supplierForest_actual_109683 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109683) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_109683
    g32p_supplierForest_actual_107762

def g32p_supplierForest_node_109685 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109685 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109685 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_107259 := by
  decide +kernel

theorem g32p_supplierForest_actual_109685 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109685) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_109685
    g32p_supplierForest_actual_107259

def g32p_supplierForest_node_109696 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109696 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109696 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153712 := by
  decide +kernel

theorem g32p_supplierForest_actual_109696 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109696) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_109696
    g32p_supplierForest_actual_153712

def g32p_supplierForest_node_109721 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_109721 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109721 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104898 := by
  decide +kernel

theorem g32p_supplierForest_actual_109721 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109721) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_109721
    g32p_supplierForest_actual_104898

def g32p_supplierForest_node_109731 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109731 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109731 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_032442 := by
  decide +kernel

theorem g32p_supplierForest_actual_109731 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109731) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 0 g32p_supplierForest_edge_109731
    g32p_supplierForest_actual_032442

def g32p_supplierForest_node_109782 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109782 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109782 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_110806 := by
  decide +kernel

theorem g32p_supplierForest_actual_109782 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109782) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_109782
    g32p_supplierForest_actual_110806

def g32p_supplierForest_node_109783 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109783 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109783 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_116799 := by
  decide +kernel

theorem g32p_supplierForest_actual_109783 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109783) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 0 g32p_supplierForest_edge_109783
    g32p_supplierForest_actual_116799

def g32p_supplierForest_node_109800 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_109800 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109800 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153361 := by
  decide +kernel

theorem g32p_supplierForest_actual_109800 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109800) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 1 g32p_supplierForest_edge_109800
    g32p_supplierForest_actual_153361

def g32p_supplierForest_node_109930 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_109930 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109930 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_108579 := by
  decide +kernel

theorem g32p_supplierForest_actual_109930 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109930) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_109930
    g32p_supplierForest_actual_108579

def g32p_supplierForest_node_109934 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_109934 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109934 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_026469 := by
  decide +kernel

theorem g32p_supplierForest_actual_109934 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109934) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_109934
    g32p_supplierForest_actual_026469

def g32p_supplierForest_node_109949 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_109949 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109949 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_026486 := by
  decide +kernel

theorem g32p_supplierForest_actual_109949 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109949) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_109949
    g32p_supplierForest_actual_026486

def g32p_supplierForest_node_109990 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109990 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109990 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_105146 := by
  decide +kernel

theorem g32p_supplierForest_actual_109990 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109990) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_109990
    g32p_supplierForest_actual_105146

def g32p_supplierForest_node_109991 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_109991 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109991 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_115654 := by
  decide +kernel

theorem g32p_supplierForest_actual_109991 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109991) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_109991
    g32p_supplierForest_actual_115654

def g32p_supplierForest_node_110008 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110008 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110008 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_110619 := by
  decide +kernel

theorem g32p_supplierForest_actual_110008 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110008) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_110008
    g32p_supplierForest_actual_110619

def g32p_supplierForest_node_110021 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110021 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110021 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_111925 := by
  decide +kernel

theorem g32p_supplierForest_actual_110021 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110021) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_110021
    g32p_supplierForest_actual_111925

def g32p_supplierForest_node_110026 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110026 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110026 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_031929 := by
  decide +kernel

theorem g32p_supplierForest_actual_110026 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110026) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_110026
    g32p_supplierForest_actual_031929

def g32p_supplierForest_node_110032 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110032 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110032 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_040417 := by
  decide +kernel

theorem g32p_supplierForest_actual_110032 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110032) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_110032
    g32p_supplierForest_actual_040417

def g32p_supplierForest_node_110055 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_110055 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110055 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108870 := by
  decide +kernel

theorem g32p_supplierForest_actual_110055 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110055) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_110055
    g32p_supplierForest_actual_108870

def g32p_supplierForest_node_110058 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_110058 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110058 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122316 := by
  decide +kernel

theorem g32p_supplierForest_actual_110058 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110058) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 3 g32p_supplierForest_edge_110058
    g32p_supplierForest_actual_122316

def g32p_supplierForest_node_110091 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110091 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110091 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_120354 := by
  decide +kernel

theorem g32p_supplierForest_actual_110091 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110091) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_110091
    g32p_supplierForest_actual_120354

def g32p_supplierForest_node_110103 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_110103 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110103 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_032694 := by
  decide +kernel

theorem g32p_supplierForest_actual_110103 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110103) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_110103
    g32p_supplierForest_actual_032694

def g32p_supplierForest_node_110134 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110134 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110134 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_026196 := by
  decide +kernel

theorem g32p_supplierForest_actual_110134 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110134) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_110134
    g32p_supplierForest_actual_026196

def g32p_supplierForest_node_110169 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_110169 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110169 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_041580 := by
  decide +kernel

theorem g32p_supplierForest_actual_110169 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110169) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_110169
    g32p_supplierForest_actual_041580

def g32p_supplierForest_node_110201 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110201 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110201 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154009 := by
  decide +kernel

theorem g32p_supplierForest_actual_110201 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110201) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 3 g32p_supplierForest_edge_110201
    g32p_supplierForest_actual_154009

def g32p_supplierForest_node_110238 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110238 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110238 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154806 := by
  decide +kernel

theorem g32p_supplierForest_actual_110238 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110238) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_110238
    g32p_supplierForest_actual_154806

def g32p_supplierForest_node_110245 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_110245 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110245 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_110050 := by
  decide +kernel

theorem g32p_supplierForest_actual_110245 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110245) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_110245
    g32p_supplierForest_actual_110050

def g32p_supplierForest_node_110271 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110271 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110271 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102972 := by
  decide +kernel

theorem g32p_supplierForest_actual_110271 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110271) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_110271
    g32p_supplierForest_actual_102972

def g32p_supplierForest_node_110272 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110272 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110272 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108107 := by
  decide +kernel

theorem g32p_supplierForest_actual_110272 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110272) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_110272
    g32p_supplierForest_actual_108107

def g32p_supplierForest_node_110306 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_110306 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110306 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_118702 := by
  decide +kernel

theorem g32p_supplierForest_actual_110306 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110306) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_110306
    g32p_supplierForest_actual_118702

def g32p_supplierForest_node_110310 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110310 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110310 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_113615 := by
  decide +kernel

theorem g32p_supplierForest_actual_110310 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110310) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_110310
    g32p_supplierForest_actual_113615

def g32p_supplierForest_node_110329 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_110329 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110329 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_120933 := by
  decide +kernel

theorem g32p_supplierForest_actual_110329 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110329) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_110329
    g32p_supplierForest_actual_120933

def g32p_supplierForest_node_110398 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_110398 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110398 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_106444 := by
  decide +kernel

theorem g32p_supplierForest_actual_110398 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110398) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_110398
    g32p_supplierForest_actual_106444

def g32p_supplierForest_node_110403 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110403 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110403 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_026560 := by
  decide +kernel

theorem g32p_supplierForest_actual_110403 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110403) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_110403
    g32p_supplierForest_actual_026560

def g32p_supplierForest_node_110409 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110409 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110409 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_029568 := by
  decide +kernel

theorem g32p_supplierForest_actual_110409 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110409) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_110409
    g32p_supplierForest_actual_029568

def g32p_supplierForest_node_110436 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110436 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110436 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_114564 := by
  decide +kernel

theorem g32p_supplierForest_actual_110436 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110436) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_110436
    g32p_supplierForest_actual_114564

def g32p_supplierForest_node_110501 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_110501 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110501 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_109784 := by
  decide +kernel

theorem g32p_supplierForest_actual_110501 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110501) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_110501
    g32p_supplierForest_actual_109784

def g32p_supplierForest_node_110537 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110537 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110537 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_113463 := by
  decide +kernel

theorem g32p_supplierForest_actual_110537 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110537) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_110537
    g32p_supplierForest_actual_113463

def g32p_supplierForest_node_110584 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110584 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110584 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_106450 := by
  decide +kernel

theorem g32p_supplierForest_actual_110584 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110584) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_110584
    g32p_supplierForest_actual_106450

def g32p_supplierForest_node_110601 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110601 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110601 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_040883 := by
  decide +kernel

theorem g32p_supplierForest_actual_110601 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110601) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_110601
    g32p_supplierForest_actual_040883

def g32p_supplierForest_node_110613 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110613 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110613 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_029514 := by
  decide +kernel

theorem g32p_supplierForest_actual_110613 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110613) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_110613
    g32p_supplierForest_actual_029514

def g32p_supplierForest_node_110617 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_110617 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110617 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_034715 := by
  decide +kernel

theorem g32p_supplierForest_actual_110617 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110617) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_110617
    g32p_supplierForest_actual_034715

def g32p_supplierForest_node_110672 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110672 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110672 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_111310 := by
  decide +kernel

theorem g32p_supplierForest_actual_110672 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110672) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_110672
    g32p_supplierForest_actual_111310

def g32p_supplierForest_node_110690 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_110690 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110690 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038133 := by
  decide +kernel

theorem g32p_supplierForest_actual_110690 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110690) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_110690
    g32p_supplierForest_actual_038133

def g32p_supplierForest_node_110732 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_110732 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110732 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_103213 := by
  decide +kernel

theorem g32p_supplierForest_actual_110732 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110732) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 3 g32p_supplierForest_edge_110732
    g32p_supplierForest_actual_103213

def g32p_supplierForest_node_110734 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110734 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110734 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118008 := by
  decide +kernel

theorem g32p_supplierForest_actual_110734 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110734) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_110734
    g32p_supplierForest_actual_118008

def g32p_supplierForest_node_110751 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110751 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110751 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_120803 := by
  decide +kernel

theorem g32p_supplierForest_actual_110751 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110751) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_110751
    g32p_supplierForest_actual_120803

def g32p_supplierForest_node_110802 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_110802 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110802 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_027684 := by
  decide +kernel

theorem g32p_supplierForest_actual_110802 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110802) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_110802
    g32p_supplierForest_actual_027684

def g32p_supplierForest_node_110859 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110859 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110859 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117833 := by
  decide +kernel

theorem g32p_supplierForest_actual_110859 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110859) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_110859
    g32p_supplierForest_actual_117833

def g32p_supplierForest_node_110892 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110892 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110892 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_116639 := by
  decide +kernel

theorem g32p_supplierForest_actual_110892 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110892) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_110892
    g32p_supplierForest_actual_116639

def g32p_supplierForest_node_110949 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_110949 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110949 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_032820 := by
  decide +kernel

theorem g32p_supplierForest_actual_110949 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110949) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_110949
    g32p_supplierForest_actual_032820

def g32p_supplierForest_node_110959 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110959 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110959 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118676 := by
  decide +kernel

theorem g32p_supplierForest_actual_110959 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110959) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 3 g32p_supplierForest_edge_110959
    g32p_supplierForest_actual_118676

def g32p_supplierForest_node_110964 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_110964 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110964 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112035 := by
  decide +kernel

theorem g32p_supplierForest_actual_110964 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110964) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_110964
    g32p_supplierForest_actual_112035

def g32p_supplierForest_node_111009 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_111009 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111009 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112100 := by
  decide +kernel

theorem g32p_supplierForest_actual_111009 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111009) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_111009
    g32p_supplierForest_actual_112100

def g32p_supplierForest_node_111038 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111038 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111038 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112144 := by
  decide +kernel

theorem g32p_supplierForest_actual_111038 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111038) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_111038
    g32p_supplierForest_actual_112144

def g32p_supplierForest_node_111043 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_111043 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111043 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_117208 := by
  decide +kernel

theorem g32p_supplierForest_actual_111043 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111043) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_111043
    g32p_supplierForest_actual_117208

def g32p_supplierForest_node_111111 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111111 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111111 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_041000 := by
  decide +kernel

theorem g32p_supplierForest_actual_111111 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111111) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_111111
    g32p_supplierForest_actual_041000

def g32p_supplierForest_node_111141 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_111141 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111141 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_106590 := by
  decide +kernel

theorem g32p_supplierForest_actual_111141 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111141) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_111141
    g32p_supplierForest_actual_106590

def g32p_supplierForest_node_111146 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_111146 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111146 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_106732 := by
  decide +kernel

theorem g32p_supplierForest_actual_111146 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111146) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_111146
    g32p_supplierForest_actual_106732

def g32p_supplierForest_node_111175 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111175 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111175 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118257 := by
  decide +kernel

theorem g32p_supplierForest_actual_111175 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111175) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_111175
    g32p_supplierForest_actual_118257

def g32p_supplierForest_node_111191 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_111191 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111191 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112503 := by
  decide +kernel

theorem g32p_supplierForest_actual_111191 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111191) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_111191
    g32p_supplierForest_actual_112503

def g32p_supplierForest_node_111201 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111201 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111201 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_029249 := by
  decide +kernel

theorem g32p_supplierForest_actual_111201 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111201) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_111201
    g32p_supplierForest_actual_029249

def g32p_supplierForest_node_111225 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111225 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111225 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108521 := by
  decide +kernel

theorem g32p_supplierForest_actual_111225 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111225) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_111225
    g32p_supplierForest_actual_108521

def g32p_supplierForest_node_111226 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_111226 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111226 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112605 := by
  decide +kernel

theorem g32p_supplierForest_actual_111226 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111226) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_111226
    g32p_supplierForest_actual_112605

def g32p_supplierForest_node_111230 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111230 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111230 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_102251 := by
  decide +kernel

theorem g32p_supplierForest_actual_111230 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111230) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_111230
    g32p_supplierForest_actual_102251

def g32p_supplierForest_node_111238 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111238 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111238 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_111277 := by
  decide +kernel

theorem g32p_supplierForest_actual_111238 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111238) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 3 g32p_supplierForest_edge_111238
    g32p_supplierForest_actual_111277

def g32p_supplierForest_node_111249 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_111249 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111249 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_042250 := by
  decide +kernel

theorem g32p_supplierForest_actual_111249 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111249) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_111249
    g32p_supplierForest_actual_042250

def g32p_supplierForest_node_111265 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_111265 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111265 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_107590 := by
  decide +kernel

theorem g32p_supplierForest_actual_111265 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111265) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_111265
    g32p_supplierForest_actual_107590

def g32p_supplierForest_node_111274 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_111274 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111274 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121191 := by
  decide +kernel

theorem g32p_supplierForest_actual_111274 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111274) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_111274
    g32p_supplierForest_actual_121191

def g32p_supplierForest_node_111297 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111297 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111297 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112774 := by
  decide +kernel

theorem g32p_supplierForest_actual_111297 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111297) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_111297
    g32p_supplierForest_actual_112774

def g32p_supplierForest_node_111306 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111306 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111306 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112387 := by
  decide +kernel

theorem g32p_supplierForest_actual_111306 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111306) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_111306
    g32p_supplierForest_actual_112387

def g32p_supplierForest_node_111309 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111309 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111309 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121120 := by
  decide +kernel

theorem g32p_supplierForest_actual_111309 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111309) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 0 g32p_supplierForest_edge_111309
    g32p_supplierForest_actual_121120

def g32p_supplierForest_node_111319 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111319 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111319 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112868 := by
  decide +kernel

theorem g32p_supplierForest_actual_111319 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111319) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_111319
    g32p_supplierForest_actual_112868

def g32p_supplierForest_node_111320 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_111320 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111320 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037454 := by
  decide +kernel

theorem g32p_supplierForest_actual_111320 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111320) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_111320
    g32p_supplierForest_actual_037454

def g32p_supplierForest_node_111372 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111372 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111372 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112874 := by
  decide +kernel

theorem g32p_supplierForest_actual_111372 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111372) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_111372
    g32p_supplierForest_actual_112874

def g32p_supplierForest_node_111375 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111375 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111375 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_034430 := by
  decide +kernel

theorem g32p_supplierForest_actual_111375 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111375) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_111375
    g32p_supplierForest_actual_034430

def g32p_supplierForest_node_111419 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111419 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111419 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112958 := by
  decide +kernel

theorem g32p_supplierForest_actual_111419 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111419) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_111419
    g32p_supplierForest_actual_112958

def g32p_supplierForest_node_111443 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111443 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111443 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122349 := by
  decide +kernel

theorem g32p_supplierForest_actual_111443 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111443) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 1 g32p_supplierForest_edge_111443
    g32p_supplierForest_actual_122349

def g32p_supplierForest_node_111481 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_111481 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111481 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_116452 := by
  decide +kernel

theorem g32p_supplierForest_actual_111481 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111481) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_111481
    g32p_supplierForest_actual_116452

def g32p_supplierForest_node_111482 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_111482 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111482 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_040391 := by
  decide +kernel

theorem g32p_supplierForest_actual_111482 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111482) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_111482
    g32p_supplierForest_actual_040391

def g32p_supplierForest_node_111511 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_111511 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111511 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113930 := by
  decide +kernel

theorem g32p_supplierForest_actual_111511 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111511) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_111511
    g32p_supplierForest_actual_113930

def g32p_supplierForest_node_111531 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_111531 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111531 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_027051 := by
  decide +kernel

theorem g32p_supplierForest_actual_111531 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111531) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_111531
    g32p_supplierForest_actual_027051

def g32p_supplierForest_node_111539 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111539 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111539 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_124082 := by
  decide +kernel

theorem g32p_supplierForest_actual_111539 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111539) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_111539
    g32p_supplierForest_actual_124082

def g32p_supplierForest_node_111606 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_111606 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111606 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108058 := by
  decide +kernel

theorem g32p_supplierForest_actual_111606 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111606) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_111606
    g32p_supplierForest_actual_108058

def g32p_supplierForest_node_111655 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111655 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111655 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_111657 := by
  decide +kernel

theorem g32p_supplierForest_actual_111655 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111655) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_111655
    g32p_supplierForest_actual_111657

def g32p_supplierForest_node_111713 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111713 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111713 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_119327 := by
  decide +kernel

theorem g32p_supplierForest_actual_111713 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111713) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_111713
    g32p_supplierForest_actual_119327

def g32p_supplierForest_node_111714 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111714 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111714 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_110804 := by
  decide +kernel

theorem g32p_supplierForest_actual_111714 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111714) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_111714
    g32p_supplierForest_actual_110804

def g32p_supplierForest_node_111730 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_111730 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111730 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_110733 := by
  decide +kernel

theorem g32p_supplierForest_actual_111730 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111730) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 2 g32p_supplierForest_edge_111730
    g32p_supplierForest_actual_110733

def g32p_supplierForest_node_111740 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111740 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111740 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_117545 := by
  decide +kernel

theorem g32p_supplierForest_actual_111740 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111740) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_111740
    g32p_supplierForest_actual_117545

def g32p_supplierForest_node_111768 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_111768 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111768 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108145 := by
  decide +kernel

theorem g32p_supplierForest_actual_111768 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111768) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_111768
    g32p_supplierForest_actual_108145

def g32p_supplierForest_node_111789 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111789 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111789 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_115365 := by
  decide +kernel

theorem g32p_supplierForest_actual_111789 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111789) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_111789
    g32p_supplierForest_actual_115365

def g32p_supplierForest_node_111857 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_111857 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111857 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_032300 := by
  decide +kernel

theorem g32p_supplierForest_actual_111857 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111857) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_111857
    g32p_supplierForest_actual_032300

def g32p_supplierForest_node_111897 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_111897 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111897 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_102143 := by
  decide +kernel

theorem g32p_supplierForest_actual_111897 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111897) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_111897
    g32p_supplierForest_actual_102143

def g32p_supplierForest_node_111907 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_111907 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111907 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_110491 := by
  decide +kernel

theorem g32p_supplierForest_actual_111907 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111907) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_111907
    g32p_supplierForest_actual_110491

def g32p_supplierForest_node_111928 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111928 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111928 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_104404 := by
  decide +kernel

theorem g32p_supplierForest_actual_111928 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111928) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_111928
    g32p_supplierForest_actual_104404

def g32p_supplierForest_node_111946 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111946 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111946 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112894 := by
  decide +kernel

theorem g32p_supplierForest_actual_111946 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111946) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_111946
    g32p_supplierForest_actual_112894

def g32p_supplierForest_node_111972 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_111972 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111972 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108579 := by
  decide +kernel

theorem g32p_supplierForest_actual_111972 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111972) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_111972
    g32p_supplierForest_actual_108579

def g32p_supplierForest_node_111979 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111979 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111979 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121697 := by
  decide +kernel

theorem g32p_supplierForest_actual_111979 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111979) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_111979
    g32p_supplierForest_actual_121697

def g32p_supplierForest_node_111991 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_111991 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111991 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_102070 := by
  decide +kernel

theorem g32p_supplierForest_actual_111991 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111991) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_111991
    g32p_supplierForest_actual_102070

def g32p_supplierForest_node_112006 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_112006 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112006 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117230 := by
  decide +kernel

theorem g32p_supplierForest_actual_112006 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112006) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_112006
    g32p_supplierForest_actual_117230

def g32p_supplierForest_node_112039 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_112039 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112039 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122764 := by
  decide +kernel

theorem g32p_supplierForest_actual_112039 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112039) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_112039
    g32p_supplierForest_actual_122764

def g32p_supplierForest_node_112098 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_112098 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112098 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118047 := by
  decide +kernel

theorem g32p_supplierForest_actual_112098 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112098) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_112098
    g32p_supplierForest_actual_118047

def g32p_supplierForest_node_112118 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112118 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112118 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121424 := by
  decide +kernel

theorem g32p_supplierForest_actual_112118 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112118) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_112118
    g32p_supplierForest_actual_121424

def g32p_supplierForest_node_112127 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112127 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112127 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_107509 := by
  decide +kernel

theorem g32p_supplierForest_actual_112127 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112127) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_112127
    g32p_supplierForest_actual_107509

def g32p_supplierForest_node_112138 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_112138 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112138 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122334 := by
  decide +kernel

theorem g32p_supplierForest_actual_112138 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112138) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_112138
    g32p_supplierForest_actual_122334

def g32p_supplierForest_node_112146 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_112146 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112146 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_035841 := by
  decide +kernel

theorem g32p_supplierForest_actual_112146 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112146) ∧
        IsConj g (g32p_literalRepresentative 65) := by
  exact g32p_archive_step_lift _ _ 65 2 g32p_supplierForest_edge_112146
    g32p_supplierForest_actual_035841

def g32p_supplierForest_node_112148 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_112148 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112148 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_035391 := by
  decide +kernel

theorem g32p_supplierForest_actual_112148 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112148) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_112148
    g32p_supplierForest_actual_035391

def g32p_supplierForest_node_112172 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_112172 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112172 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121567 := by
  decide +kernel

theorem g32p_supplierForest_actual_112172 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112172) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 0 g32p_supplierForest_edge_112172
    g32p_supplierForest_actual_121567

def g32p_supplierForest_node_112181 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_112181 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112181 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121854 := by
  decide +kernel

theorem g32p_supplierForest_actual_112181 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112181) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 0 g32p_supplierForest_edge_112181
    g32p_supplierForest_actual_121854

def g32p_supplierForest_node_112206 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112206 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112206 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_039994 := by
  decide +kernel

theorem g32p_supplierForest_actual_112206 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112206) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_112206
    g32p_supplierForest_actual_039994

def g32p_supplierForest_node_112246 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_112246 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112246 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_041904 := by
  decide +kernel

theorem g32p_supplierForest_actual_112246 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112246) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_112246
    g32p_supplierForest_actual_041904

def g32p_supplierForest_node_112267 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_112267 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112267 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118848 := by
  decide +kernel

theorem g32p_supplierForest_actual_112267 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112267) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_112267
    g32p_supplierForest_actual_118848

def g32p_supplierForest_node_112271 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112271 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112271 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_038588 := by
  decide +kernel

theorem g32p_supplierForest_actual_112271 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112271) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 3 g32p_supplierForest_edge_112271
    g32p_supplierForest_actual_038588

def g32p_supplierForest_node_112284 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112284 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112284 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118113 := by
  decide +kernel

theorem g32p_supplierForest_actual_112284 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112284) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_112284
    g32p_supplierForest_actual_118113

def g32p_supplierForest_node_112285 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112285 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112285 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_043264 := by
  decide +kernel

theorem g32p_supplierForest_actual_112285 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112285) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_112285
    g32p_supplierForest_actual_043264

def g32p_supplierForest_node_112300 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_112300 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112300 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118862 := by
  decide +kernel

theorem g32p_supplierForest_actual_112300 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112300) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_112300
    g32p_supplierForest_actual_118862

def g32p_supplierForest_node_112307 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112307 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112307 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121935 := by
  decide +kernel

theorem g32p_supplierForest_actual_112307 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112307) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_112307
    g32p_supplierForest_actual_121935

def g32p_supplierForest_node_112338 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_112338 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112338 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_033950 := by
  decide +kernel

theorem g32p_supplierForest_actual_112338 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112338) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_112338
    g32p_supplierForest_actual_033950

def g32p_supplierForest_node_112343 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_112343 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112343 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_111311 := by
  decide +kernel

theorem g32p_supplierForest_actual_112343 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112343) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_112343
    g32p_supplierForest_actual_111311

def g32p_supplierForest_node_112426 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112426 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112426 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_127802 := by
  decide +kernel

theorem g32p_supplierForest_actual_112426 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112426) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_112426
    g32p_supplierForest_actual_127802

def g32p_supplierForest_node_112432 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_112432 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112432 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_116877 := by
  decide +kernel

theorem g32p_supplierForest_actual_112432 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112432) ∧
        IsConj g (g32p_literalRepresentative 93) := by
  exact g32p_archive_step_lift _ _ 93 1 g32p_supplierForest_edge_112432
    g32p_supplierForest_actual_116877

def g32p_supplierForest_node_112443 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112443 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112443 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_112315 := by
  decide +kernel

theorem g32p_supplierForest_actual_112443 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112443) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_112443
    g32p_supplierForest_actual_112315

def g32p_supplierForest_node_112450 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112450 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112450 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_110591 := by
  decide +kernel

theorem g32p_supplierForest_actual_112450 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112450) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 2 g32p_supplierForest_edge_112450
    g32p_supplierForest_actual_110591

def g32p_supplierForest_node_112552 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112552 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112552 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_108204 := by
  decide +kernel

theorem g32p_supplierForest_actual_112552 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112552) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 1 g32p_supplierForest_edge_112552
    g32p_supplierForest_actual_108204

def g32p_supplierForest_node_112554 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112554 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112554 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_121935 := by
  decide +kernel

theorem g32p_supplierForest_actual_112554 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112554) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_112554
    g32p_supplierForest_actual_121935

def g32p_supplierForest_node_112558 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_112558 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112558 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_103009 := by
  decide +kernel

theorem g32p_supplierForest_actual_112558 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112558) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_112558
    g32p_supplierForest_actual_103009

def g32p_supplierForest_node_112622 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112622 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112622 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122124 := by
  decide +kernel

theorem g32p_supplierForest_actual_112622 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112622) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_112622
    g32p_supplierForest_actual_122124

def g32p_supplierForest_node_112694 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112694 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112694 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_103055 := by
  decide +kernel

theorem g32p_supplierForest_actual_112694 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112694) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_112694
    g32p_supplierForest_actual_103055

def g32p_supplierForest_node_112699 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112699 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112699 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_113809 := by
  decide +kernel

theorem g32p_supplierForest_actual_112699 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112699) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_112699
    g32p_supplierForest_actual_113809

def g32p_supplierForest_node_112719 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_112719 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112719 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_112846 := by
  decide +kernel

theorem g32p_supplierForest_actual_112719 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112719) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_112719
    g32p_supplierForest_actual_112846

def g32p_supplierForest_node_112738 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_112738 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112738 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120219 := by
  decide +kernel

theorem g32p_supplierForest_actual_112738 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112738) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_112738
    g32p_supplierForest_actual_120219

def g32p_supplierForest_node_112777 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_112777 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112777 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_031712 := by
  decide +kernel

theorem g32p_supplierForest_actual_112777 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112777) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_112777
    g32p_supplierForest_actual_031712

def g32p_supplierForest_node_112780 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112780 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112780 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122167 := by
  decide +kernel

theorem g32p_supplierForest_actual_112780 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112780) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_112780
    g32p_supplierForest_actual_122167

def g32p_supplierForest_node_112790 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112790 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112790 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_106935 := by
  decide +kernel

theorem g32p_supplierForest_actual_112790 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112790) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_112790
    g32p_supplierForest_actual_106935

def g32p_supplierForest_node_112794 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112794 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112794 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_029184 := by
  decide +kernel

theorem g32p_supplierForest_actual_112794 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112794) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_112794
    g32p_supplierForest_actual_029184

def g32p_supplierForest_node_112824 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_112824 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112824 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122244 := by
  decide +kernel

theorem g32p_supplierForest_actual_112824 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112824) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_112824
    g32p_supplierForest_actual_122244

def g32p_supplierForest_node_112875 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_112875 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112875 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112874 := by
  decide +kernel

theorem g32p_supplierForest_actual_112875 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112875) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_112875
    g32p_supplierForest_actual_112874

def g32p_supplierForest_node_112886 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112886 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112886 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_034928 := by
  decide +kernel

theorem g32p_supplierForest_actual_112886 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112886) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_112886
    g32p_supplierForest_actual_034928

def g32p_supplierForest_node_112899 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112899 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112899 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123834 := by
  decide +kernel

theorem g32p_supplierForest_actual_112899 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112899) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_112899
    g32p_supplierForest_actual_123834

def g32p_supplierForest_node_112900 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112900 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112900 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122240 := by
  decide +kernel

theorem g32p_supplierForest_actual_112900 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112900) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 0 g32p_supplierForest_edge_112900
    g32p_supplierForest_actual_122240

def g32p_supplierForest_node_112901 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112901 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112901 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_107029 := by
  decide +kernel

theorem g32p_supplierForest_actual_112901 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112901) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_112901
    g32p_supplierForest_actual_107029

def g32p_supplierForest_node_112904 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112904 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112904 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043090 := by
  decide +kernel

theorem g32p_supplierForest_actual_112904 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112904) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_112904
    g32p_supplierForest_actual_043090

def g32p_supplierForest_node_112911 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_112911 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112911 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_025744 := by
  decide +kernel

theorem g32p_supplierForest_actual_112911 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112911) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_112911
    g32p_supplierForest_actual_025744

def g32p_supplierForest_node_112928 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112928 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112928 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_037557 := by
  decide +kernel

theorem g32p_supplierForest_actual_112928 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112928) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_112928
    g32p_supplierForest_actual_037557

def g32p_supplierForest_node_112937 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_112937 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112937 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122323 := by
  decide +kernel

theorem g32p_supplierForest_actual_112937 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112937) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_112937
    g32p_supplierForest_actual_122323

def g32p_supplierForest_node_112993 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_112993 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112993 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_104958 := by
  decide +kernel

theorem g32p_supplierForest_actual_112993 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112993) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_112993
    g32p_supplierForest_actual_104958

def g32p_supplierForest_node_112994 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_112994 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112994 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122556 := by
  decide +kernel

theorem g32p_supplierForest_actual_112994 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112994) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_112994
    g32p_supplierForest_actual_122556

def g32p_supplierForest_node_113013 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113013 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113013 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_032126 := by
  decide +kernel

theorem g32p_supplierForest_actual_113013 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113013) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_113013
    g32p_supplierForest_actual_032126

def g32p_supplierForest_node_113018 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113018 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113018 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_101897 := by
  decide +kernel

theorem g32p_supplierForest_actual_113018 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113018) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_113018
    g32p_supplierForest_actual_101897

def g32p_supplierForest_node_113042 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113042 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113042 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_035591 := by
  decide +kernel

theorem g32p_supplierForest_actual_113042 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113042) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_113042
    g32p_supplierForest_actual_035591

def g32p_supplierForest_node_113048 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113048 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113048 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_104556 := by
  decide +kernel

theorem g32p_supplierForest_actual_113048 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113048) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 3 g32p_supplierForest_edge_113048
    g32p_supplierForest_actual_104556

def g32p_supplierForest_node_113071 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113071 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113071 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113068 := by
  decide +kernel

theorem g32p_supplierForest_actual_113071 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113071) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_113071
    g32p_supplierForest_actual_113068

def g32p_supplierForest_node_113081 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_113081 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113081 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_103168 := by
  decide +kernel

theorem g32p_supplierForest_actual_113081 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113081) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 1 g32p_supplierForest_edge_113081
    g32p_supplierForest_actual_103168

def g32p_supplierForest_node_113084 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_113084 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113084 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_039190 := by
  decide +kernel

theorem g32p_supplierForest_actual_113084 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113084) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 3 g32p_supplierForest_edge_113084
    g32p_supplierForest_actual_039190

def g32p_supplierForest_node_113092 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113092 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113092 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_031358 := by
  decide +kernel

theorem g32p_supplierForest_actual_113092 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113092) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_113092
    g32p_supplierForest_actual_031358

def g32p_supplierForest_node_113096 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_113096 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113096 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122422 := by
  decide +kernel

theorem g32p_supplierForest_actual_113096 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113096) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_113096
    g32p_supplierForest_actual_122422

def g32p_supplierForest_node_113104 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113104 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113104 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113539 := by
  decide +kernel

theorem g32p_supplierForest_actual_113104 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113104) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_113104
    g32p_supplierForest_actual_113539

def g32p_supplierForest_node_113114 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113114 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113114 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_039614 := by
  decide +kernel

theorem g32p_supplierForest_actual_113114 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113114) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 1 g32p_supplierForest_edge_113114
    g32p_supplierForest_actual_039614

def g32p_supplierForest_node_113165 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_113165 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113165 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_036534 := by
  decide +kernel

theorem g32p_supplierForest_actual_113165 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113165) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_113165
    g32p_supplierForest_actual_036534

def g32p_supplierForest_node_113177 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_113177 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113177 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_120354 := by
  decide +kernel

theorem g32p_supplierForest_actual_113177 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113177) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_113177
    g32p_supplierForest_actual_120354

def g32p_supplierForest_node_113196 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_113196 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113196 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_102050 := by
  decide +kernel

theorem g32p_supplierForest_actual_113196 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113196) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_113196
    g32p_supplierForest_actual_102050

def g32p_supplierForest_node_113205 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113205 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113205 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122505 := by
  decide +kernel

theorem g32p_supplierForest_actual_113205 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113205) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_113205
    g32p_supplierForest_actual_122505

def g32p_supplierForest_node_113221 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113221 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113221 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_120041 := by
  decide +kernel

theorem g32p_supplierForest_actual_113221 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113221) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_113221
    g32p_supplierForest_actual_120041

def g32p_supplierForest_node_113231 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113231 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113231 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_113552 := by
  decide +kernel

theorem g32p_supplierForest_actual_113231 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113231) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 0 g32p_supplierForest_edge_113231
    g32p_supplierForest_actual_113552

def g32p_supplierForest_node_113269 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_113269 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113269 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_024944 := by
  decide +kernel

theorem g32p_supplierForest_actual_113269 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113269) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_113269
    g32p_supplierForest_actual_024944

def g32p_supplierForest_node_113274 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113274 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113274 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_103710 := by
  decide +kernel

theorem g32p_supplierForest_actual_113274 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113274) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_113274
    g32p_supplierForest_actual_103710

def g32p_supplierForest_node_113297 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_113297 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113297 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_105076 := by
  decide +kernel

theorem g32p_supplierForest_actual_113297 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113297) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_113297
    g32p_supplierForest_actual_105076

def g32p_supplierForest_node_113304 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113304 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113304 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_117686 := by
  decide +kernel

theorem g32p_supplierForest_actual_113304 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113304) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_113304
    g32p_supplierForest_actual_117686

def g32p_supplierForest_node_113319 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113319 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113319 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_102144 := by
  decide +kernel

theorem g32p_supplierForest_actual_113319 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113319) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_113319
    g32p_supplierForest_actual_102144

def g32p_supplierForest_node_113323 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_113323 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113323 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_114041 := by
  decide +kernel

theorem g32p_supplierForest_actual_113323 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113323) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_113323
    g32p_supplierForest_actual_114041

def g32p_supplierForest_node_113327 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_113327 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113327 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113605 := by
  decide +kernel

theorem g32p_supplierForest_actual_113327 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113327) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_113327
    g32p_supplierForest_actual_113605

def g32p_supplierForest_node_113360 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_113360 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113360 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_104066 := by
  decide +kernel

theorem g32p_supplierForest_actual_113360 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113360) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_113360
    g32p_supplierForest_actual_104066

def g32p_supplierForest_node_113400 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_113400 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113400 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_115543 := by
  decide +kernel

theorem g32p_supplierForest_actual_113400 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113400) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_113400
    g32p_supplierForest_actual_115543

def g32p_supplierForest_node_113408 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_113408 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113408 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_104225 := by
  decide +kernel

theorem g32p_supplierForest_actual_113408 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113408) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_113408
    g32p_supplierForest_actual_104225

def g32p_supplierForest_node_113413 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_113413 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113413 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_102890 := by
  decide +kernel

theorem g32p_supplierForest_actual_113413 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113413) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_113413
    g32p_supplierForest_actual_102890

def g32p_supplierForest_node_113418 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_113418 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113418 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_116790 := by
  decide +kernel

theorem g32p_supplierForest_actual_113418 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113418) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_113418
    g32p_supplierForest_actual_116790

def g32p_supplierForest_node_113434 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_113434 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113434 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_104292 := by
  decide +kernel

theorem g32p_supplierForest_actual_113434 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113434) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_113434
    g32p_supplierForest_actual_104292

def g32p_supplierForest_node_113446 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113446 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113446 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_114757 := by
  decide +kernel

theorem g32p_supplierForest_actual_113446 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113446) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_113446
    g32p_supplierForest_actual_114757

def g32p_supplierForest_node_113481 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_113481 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113481 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_028476 := by
  decide +kernel

theorem g32p_supplierForest_actual_113481 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113481) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_113481
    g32p_supplierForest_actual_028476

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_113483 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113483 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113483 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_105226 := by
  decide +kernel

theorem g32p_supplierForest_actual_113483 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113483) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_113483
    g32p_supplierForest_actual_105226

def g32p_supplierForest_node_113551 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113551 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113551 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_126383 := by
  decide +kernel

theorem g32p_supplierForest_actual_113551 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113551) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_113551
    g32p_supplierForest_actual_126383

def g32p_supplierForest_node_113590 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_113590 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113590 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_114351 := by
  decide +kernel

theorem g32p_supplierForest_actual_113590 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113590) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_113590
    g32p_supplierForest_actual_114351

def g32p_supplierForest_node_113600 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113600 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113600 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109009 := by
  decide +kernel

theorem g32p_supplierForest_actual_113600 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113600) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_113600
    g32p_supplierForest_actual_109009

def g32p_supplierForest_node_113607 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_113607 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113607 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122385 := by
  decide +kernel

theorem g32p_supplierForest_actual_113607 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113607) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_113607
    g32p_supplierForest_actual_122385

def g32p_supplierForest_node_113608 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_113608 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113608 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038070 := by
  decide +kernel

theorem g32p_supplierForest_actual_113608 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113608) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_113608
    g32p_supplierForest_actual_038070

def g32p_supplierForest_node_113633 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113633 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113633 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_114325 := by
  decide +kernel

theorem g32p_supplierForest_actual_113633 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113633) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_113633
    g32p_supplierForest_actual_114325

def g32p_supplierForest_node_113637 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113637 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113637 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_103172 := by
  decide +kernel

theorem g32p_supplierForest_actual_113637 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113637) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_113637
    g32p_supplierForest_actual_103172

def g32p_supplierForest_node_113690 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113690 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113690 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115648 := by
  decide +kernel

theorem g32p_supplierForest_actual_113690 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113690) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_113690
    g32p_supplierForest_actual_115648

def g32p_supplierForest_node_113692 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_113692 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113692 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_118654 := by
  decide +kernel

theorem g32p_supplierForest_actual_113692 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113692) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_113692
    g32p_supplierForest_actual_118654

def g32p_supplierForest_node_113694 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113694 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113694 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122868 := by
  decide +kernel

theorem g32p_supplierForest_actual_113694 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113694) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_113694
    g32p_supplierForest_actual_122868

def g32p_supplierForest_node_113697 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_113697 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113697 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115654 := by
  decide +kernel

theorem g32p_supplierForest_actual_113697 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113697) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_113697
    g32p_supplierForest_actual_115654

def g32p_supplierForest_node_113707 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113707 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113707 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109096 := by
  decide +kernel

theorem g32p_supplierForest_actual_113707 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113707) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 1 g32p_supplierForest_edge_113707
    g32p_supplierForest_actual_109096

def g32p_supplierForest_node_113720 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_113720 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113720 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_035210 := by
  decide +kernel

theorem g32p_supplierForest_actual_113720 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113720) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_113720
    g32p_supplierForest_actual_035210

def g32p_supplierForest_node_113736 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113736 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113736 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_036978 := by
  decide +kernel

theorem g32p_supplierForest_actual_113736 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113736) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_113736
    g32p_supplierForest_actual_036978

def g32p_supplierForest_node_113742 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_113742 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113742 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038157 := by
  decide +kernel

theorem g32p_supplierForest_actual_113742 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113742) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_113742
    g32p_supplierForest_actual_038157

def g32p_supplierForest_node_113790 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113790 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113790 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122951 := by
  decide +kernel

theorem g32p_supplierForest_actual_113790 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113790) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_113790
    g32p_supplierForest_actual_122951

def g32p_supplierForest_node_113797 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_113797 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113797 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_109013 := by
  decide +kernel

theorem g32p_supplierForest_actual_113797 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113797) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_113797
    g32p_supplierForest_actual_109013

def g32p_supplierForest_node_113816 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_113816 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113816 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_044023 := by
  decide +kernel

theorem g32p_supplierForest_actual_113816 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113816) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_113816
    g32p_supplierForest_actual_044023

def g32p_supplierForest_node_113819 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113819 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113819 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_114557 := by
  decide +kernel

theorem g32p_supplierForest_actual_113819 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113819) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_113819
    g32p_supplierForest_actual_114557

def g32p_supplierForest_node_113838 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_113838 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113838 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_121410 := by
  decide +kernel

theorem g32p_supplierForest_actual_113838 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113838) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_113838
    g32p_supplierForest_actual_121410

def g32p_supplierForest_node_113841 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113841 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113841 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043121 := by
  decide +kernel

theorem g32p_supplierForest_actual_113841 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113841) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_113841
    g32p_supplierForest_actual_043121

def g32p_supplierForest_node_113844 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113844 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113844 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_108604 := by
  decide +kernel

theorem g32p_supplierForest_actual_113844 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113844) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 1 g32p_supplierForest_edge_113844
    g32p_supplierForest_actual_108604

def g32p_supplierForest_node_113859 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113859 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113859 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_110854 := by
  decide +kernel

theorem g32p_supplierForest_actual_113859 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113859) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_113859
    g32p_supplierForest_actual_110854

def g32p_supplierForest_node_113879 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113879 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113879 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109501 := by
  decide +kernel

theorem g32p_supplierForest_actual_113879 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113879) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_113879
    g32p_supplierForest_actual_109501

def g32p_supplierForest_node_113889 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113889 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113889 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_032103 := by
  decide +kernel

theorem g32p_supplierForest_actual_113889 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113889) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_113889
    g32p_supplierForest_actual_032103

def g32p_supplierForest_node_113926 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113926 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113926 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_119731 := by
  decide +kernel

theorem g32p_supplierForest_actual_113926 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113926) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_113926
    g32p_supplierForest_actual_119731

def g32p_supplierForest_node_113933 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_113933 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113933 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_030505 := by
  decide +kernel

theorem g32p_supplierForest_actual_113933 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113933) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_113933
    g32p_supplierForest_actual_030505

def g32p_supplierForest_node_113969 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113969 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113969 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_027521 := by
  decide +kernel

theorem g32p_supplierForest_actual_113969 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113969) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_113969
    g32p_supplierForest_actual_027521

def g32p_supplierForest_node_113974 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_113974 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113974 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_116249 := by
  decide +kernel

theorem g32p_supplierForest_actual_113974 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113974) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_113974
    g32p_supplierForest_actual_116249

def g32p_supplierForest_node_114014 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_114014 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114014 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_044303 := by
  decide +kernel

theorem g32p_supplierForest_actual_114014 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114014) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 1 g32p_supplierForest_edge_114014
    g32p_supplierForest_actual_044303

def g32p_supplierForest_node_114020 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_114020 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114020 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_035202 := by
  decide +kernel

theorem g32p_supplierForest_actual_114020 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114020) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_114020
    g32p_supplierForest_actual_035202

def g32p_supplierForest_node_114032 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114032 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114032 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043804 := by
  decide +kernel

theorem g32p_supplierForest_actual_114032 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114032) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_114032
    g32p_supplierForest_actual_043804

def g32p_supplierForest_node_114075 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114075 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114075 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108198 := by
  decide +kernel

theorem g32p_supplierForest_actual_114075 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114075) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_114075
    g32p_supplierForest_actual_108198

def g32p_supplierForest_node_114131 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_114131 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114131 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113830 := by
  decide +kernel

theorem g32p_supplierForest_actual_114131 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114131) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_114131
    g32p_supplierForest_actual_113830

def g32p_supplierForest_node_114133 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114133 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114133 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_029268 := by
  decide +kernel

theorem g32p_supplierForest_actual_114133 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114133) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_114133
    g32p_supplierForest_actual_029268

def g32p_supplierForest_node_114143 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114143 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114143 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123333 := by
  decide +kernel

theorem g32p_supplierForest_actual_114143 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114143) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_114143
    g32p_supplierForest_actual_123333

def g32p_supplierForest_node_114146 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_114146 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114146 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_041419 := by
  decide +kernel

theorem g32p_supplierForest_actual_114146 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114146) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 3 g32p_supplierForest_edge_114146
    g32p_supplierForest_actual_041419

def g32p_supplierForest_node_114151 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114151 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114151 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113794 := by
  decide +kernel

theorem g32p_supplierForest_actual_114151 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114151) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_114151
    g32p_supplierForest_actual_113794

def g32p_supplierForest_node_114159 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114159 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114159 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_114175 := by
  decide +kernel

theorem g32p_supplierForest_actual_114159 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114159) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_114159
    g32p_supplierForest_actual_114175

def g32p_supplierForest_node_114163 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_114163 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114163 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_110768 := by
  decide +kernel

theorem g32p_supplierForest_actual_114163 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114163) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_114163
    g32p_supplierForest_actual_110768

def g32p_supplierForest_node_114205 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_114205 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114205 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_112515 := by
  decide +kernel

theorem g32p_supplierForest_actual_114205 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114205) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_114205
    g32p_supplierForest_actual_112515

def g32p_supplierForest_node_114232 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114232 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114232 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_106764 := by
  decide +kernel

theorem g32p_supplierForest_actual_114232 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114232) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_114232
    g32p_supplierForest_actual_106764

def g32p_supplierForest_node_114266 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114266 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114266 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_029366 := by
  decide +kernel

theorem g32p_supplierForest_actual_114266 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114266) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_114266
    g32p_supplierForest_actual_029366

def g32p_supplierForest_node_114270 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114270 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114270 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122728 := by
  decide +kernel

theorem g32p_supplierForest_actual_114270 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114270) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_114270
    g32p_supplierForest_actual_122728

def g32p_supplierForest_node_114274 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114274 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114274 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_102173 := by
  decide +kernel

theorem g32p_supplierForest_actual_114274 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114274) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_114274
    g32p_supplierForest_actual_102173

def g32p_supplierForest_node_114276 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114276 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114276 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_112423 := by
  decide +kernel

theorem g32p_supplierForest_actual_114276 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114276) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_114276
    g32p_supplierForest_actual_112423

def g32p_supplierForest_node_114281 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114281 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114281 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122764 := by
  decide +kernel

theorem g32p_supplierForest_actual_114281 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114281) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_114281
    g32p_supplierForest_actual_122764

def g32p_supplierForest_node_114289 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114289 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114289 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122422 := by
  decide +kernel

theorem g32p_supplierForest_actual_114289 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114289) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_114289
    g32p_supplierForest_actual_122422

def g32p_supplierForest_node_114317 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114317 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114317 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108806 := by
  decide +kernel

theorem g32p_supplierForest_actual_114317 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114317) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_114317
    g32p_supplierForest_actual_108806

def g32p_supplierForest_node_114354 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114354 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114354 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_044234 := by
  decide +kernel

theorem g32p_supplierForest_actual_114354 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114354) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_114354
    g32p_supplierForest_actual_044234

def g32p_supplierForest_node_114394 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_114394 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114394 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_040437 := by
  decide +kernel

theorem g32p_supplierForest_actual_114394 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114394) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_114394
    g32p_supplierForest_actual_040437

def g32p_supplierForest_node_114406 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_114406 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114406 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_108030 := by
  decide +kernel

theorem g32p_supplierForest_actual_114406 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114406) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_114406
    g32p_supplierForest_actual_108030

def g32p_supplierForest_node_114422 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_114422 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114422 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_123355 := by
  decide +kernel

theorem g32p_supplierForest_actual_114422 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114422) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_114422
    g32p_supplierForest_actual_123355

def g32p_supplierForest_node_114448 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_114448 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114448 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117765 := by
  decide +kernel

theorem g32p_supplierForest_actual_114448 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114448) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_114448
    g32p_supplierForest_actual_117765

def g32p_supplierForest_node_114456 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114456 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114456 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153035 := by
  decide +kernel

theorem g32p_supplierForest_actual_114456 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114456) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_114456
    g32p_supplierForest_actual_153035

def g32p_supplierForest_node_114500 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_114500 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114500 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_109196 := by
  decide +kernel

theorem g32p_supplierForest_actual_114500 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114500) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_114500
    g32p_supplierForest_actual_109196

def g32p_supplierForest_node_114544 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114544 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114544 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_110977 := by
  decide +kernel

theorem g32p_supplierForest_actual_114544 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114544) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_114544
    g32p_supplierForest_actual_110977

def g32p_supplierForest_node_114581 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114581 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114581 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_123680 := by
  decide +kernel

theorem g32p_supplierForest_actual_114581 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114581) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_114581
    g32p_supplierForest_actual_123680

def g32p_supplierForest_node_114635 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114635 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114635 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_031138 := by
  decide +kernel

theorem g32p_supplierForest_actual_114635 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114635) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_114635
    g32p_supplierForest_actual_031138

def g32p_supplierForest_node_114638 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_114638 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114638 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_126122 := by
  decide +kernel

theorem g32p_supplierForest_actual_114638 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114638) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_114638
    g32p_supplierForest_actual_126122

def g32p_supplierForest_node_114655 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_114655 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114655 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038105 := by
  decide +kernel

theorem g32p_supplierForest_actual_114655 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114655) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_114655
    g32p_supplierForest_actual_038105

def g32p_supplierForest_node_114669 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_114669 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114669 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123409 := by
  decide +kernel

theorem g32p_supplierForest_actual_114669 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114669) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_114669
    g32p_supplierForest_actual_123409

def g32p_supplierForest_node_114715 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_114715 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114715 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_111723 := by
  decide +kernel

theorem g32p_supplierForest_actual_114715 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114715) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_114715
    g32p_supplierForest_actual_111723

def g32p_supplierForest_node_114783 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114783 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114783 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_107166 := by
  decide +kernel

theorem g32p_supplierForest_actual_114783 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114783) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 1 g32p_supplierForest_edge_114783
    g32p_supplierForest_actual_107166

def g32p_supplierForest_node_114785 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_114785 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114785 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_123601 := by
  decide +kernel

theorem g32p_supplierForest_actual_114785 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114785) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 0 g32p_supplierForest_edge_114785
    g32p_supplierForest_actual_123601

def g32p_supplierForest_node_114810 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114810 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114810 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_114811 := by
  decide +kernel

theorem g32p_supplierForest_actual_114810 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114810) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_114810
    g32p_supplierForest_actual_114811

def g32p_supplierForest_node_114854 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_114854 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114854 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_111577 := by
  decide +kernel

theorem g32p_supplierForest_actual_114854 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114854) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_114854
    g32p_supplierForest_actual_111577

def g32p_supplierForest_node_114862 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_114862 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114862 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_116319 := by
  decide +kernel

theorem g32p_supplierForest_actual_114862 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114862) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_114862
    g32p_supplierForest_actual_116319

def g32p_supplierForest_node_114863 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_114863 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114863 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118412 := by
  decide +kernel

theorem g32p_supplierForest_actual_114863 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114863) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_114863
    g32p_supplierForest_actual_118412

def g32p_supplierForest_node_114869 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_114869 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114869 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_030903 := by
  decide +kernel

theorem g32p_supplierForest_actual_114869 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114869) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_114869
    g32p_supplierForest_actual_030903

def g32p_supplierForest_node_114871 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_114871 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114871 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101959 := by
  decide +kernel

theorem g32p_supplierForest_actual_114871 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114871) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_114871
    g32p_supplierForest_actual_101959

def g32p_supplierForest_node_114884 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114884 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114884 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_119404 := by
  decide +kernel

theorem g32p_supplierForest_actual_114884 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114884) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_114884
    g32p_supplierForest_actual_119404

def g32p_supplierForest_node_114898 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114898 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114898 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_116997 := by
  decide +kernel

theorem g32p_supplierForest_actual_114898 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114898) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_114898
    g32p_supplierForest_actual_116997

def g32p_supplierForest_node_114922 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114922 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114922 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_116322 := by
  decide +kernel

theorem g32p_supplierForest_actual_114922 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114922) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_114922
    g32p_supplierForest_actual_116322

def g32p_supplierForest_node_114933 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114933 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114933 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118579 := by
  decide +kernel

theorem g32p_supplierForest_actual_114933 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114933) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_114933
    g32p_supplierForest_actual_118579

def g32p_supplierForest_node_114970 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114970 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114970 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_116599 := by
  decide +kernel

theorem g32p_supplierForest_actual_114970 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114970) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_114970
    g32p_supplierForest_actual_116599

def g32p_supplierForest_node_114985 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_114985 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114985 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118702 := by
  decide +kernel

theorem g32p_supplierForest_actual_114985 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114985) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_114985
    g32p_supplierForest_actual_118702

def g32p_supplierForest_node_114986 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114986 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114986 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118548 := by
  decide +kernel

theorem g32p_supplierForest_actual_114986 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114986) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_114986
    g32p_supplierForest_actual_118548

def g32p_supplierForest_node_115019 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115019 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115019 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_112315 := by
  decide +kernel

theorem g32p_supplierForest_actual_115019 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115019) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_115019
    g32p_supplierForest_actual_112315

def g32p_supplierForest_node_115027 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_115027 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115027 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113719 := by
  decide +kernel

theorem g32p_supplierForest_actual_115027 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115027) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_115027
    g32p_supplierForest_actual_113719

def g32p_supplierForest_node_115046 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115046 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115046 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_108223 := by
  decide +kernel

theorem g32p_supplierForest_actual_115046 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115046) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_115046
    g32p_supplierForest_actual_108223

def g32p_supplierForest_node_115101 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_115101 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115101 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_110521 := by
  decide +kernel

theorem g32p_supplierForest_actual_115101 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115101) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_115101
    g32p_supplierForest_actual_110521

def g32p_supplierForest_node_115109 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_115109 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115109 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122088 := by
  decide +kernel

theorem g32p_supplierForest_actual_115109 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115109) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_115109
    g32p_supplierForest_actual_122088

def g32p_supplierForest_node_115110 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115110 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115110 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_123834 := by
  decide +kernel

theorem g32p_supplierForest_actual_115110 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115110) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_115110
    g32p_supplierForest_actual_123834

def g32p_supplierForest_node_115113 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_115113 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115113 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113860 := by
  decide +kernel

theorem g32p_supplierForest_actual_115113 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115113) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 3 g32p_supplierForest_edge_115113
    g32p_supplierForest_actual_113860

def g32p_supplierForest_node_115134 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_115134 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115134 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_121369 := by
  decide +kernel

theorem g32p_supplierForest_actual_115134 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115134) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_115134
    g32p_supplierForest_actual_121369

def g32p_supplierForest_node_115136 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_115136 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115136 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_102628 := by
  decide +kernel

theorem g32p_supplierForest_actual_115136 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115136) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_115136
    g32p_supplierForest_actual_102628

def g32p_supplierForest_node_115139 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115139 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115139 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_120354 := by
  decide +kernel

theorem g32p_supplierForest_actual_115139 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115139) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_115139
    g32p_supplierForest_actual_120354

def g32p_supplierForest_node_115175 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115175 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115175 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_103846 := by
  decide +kernel

theorem g32p_supplierForest_actual_115175 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115175) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_115175
    g32p_supplierForest_actual_103846

def g32p_supplierForest_node_115200 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_115200 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115200 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113681 := by
  decide +kernel

theorem g32p_supplierForest_actual_115200 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115200) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_115200
    g32p_supplierForest_actual_113681

def g32p_supplierForest_node_115236 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115236 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115236 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_111534 := by
  decide +kernel

theorem g32p_supplierForest_actual_115236 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115236) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_115236
    g32p_supplierForest_actual_111534

def g32p_supplierForest_node_115237 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_115237 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115237 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108677 := by
  decide +kernel

theorem g32p_supplierForest_actual_115237 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115237) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_115237
    g32p_supplierForest_actual_108677

def g32p_supplierForest_node_115272 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_115272 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115272 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_105772 := by
  decide +kernel

theorem g32p_supplierForest_actual_115272 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115272) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_115272
    g32p_supplierForest_actual_105772

def g32p_supplierForest_node_115343 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_115343 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115343 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_106229 := by
  decide +kernel

theorem g32p_supplierForest_actual_115343 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115343) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_115343
    g32p_supplierForest_actual_106229

def g32p_supplierForest_node_115349 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_115349 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115349 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_119167 := by
  decide +kernel

theorem g32p_supplierForest_actual_115349 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115349) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_115349
    g32p_supplierForest_actual_119167

def g32p_supplierForest_node_115375 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115375 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115375 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113451 := by
  decide +kernel

theorem g32p_supplierForest_actual_115375 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115375) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_115375
    g32p_supplierForest_actual_113451

def g32p_supplierForest_node_115394 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_115394 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115394 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124014 := by
  decide +kernel

theorem g32p_supplierForest_actual_115394 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115394) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_115394
    g32p_supplierForest_actual_124014

def g32p_supplierForest_node_115400 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_115400 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115400 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_114148 := by
  decide +kernel

theorem g32p_supplierForest_actual_115400 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115400) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_115400
    g32p_supplierForest_actual_114148

def g32p_supplierForest_node_115420 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_115420 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115420 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_119593 := by
  decide +kernel

theorem g32p_supplierForest_actual_115420 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115420) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_115420
    g32p_supplierForest_actual_119593

def g32p_supplierForest_node_115421 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_115421 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115421 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_041517 := by
  decide +kernel

theorem g32p_supplierForest_actual_115421 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115421) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_115421
    g32p_supplierForest_actual_041517

def g32p_supplierForest_node_115423 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_115423 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115423 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_044298 := by
  decide +kernel

theorem g32p_supplierForest_actual_115423 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115423) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_115423
    g32p_supplierForest_actual_044298

def g32p_supplierForest_node_115437 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_115437 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115437 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_120942 := by
  decide +kernel

theorem g32p_supplierForest_actual_115437 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115437) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_115437
    g32p_supplierForest_actual_120942

def g32p_supplierForest_node_115438 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115438 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115438 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_107516 := by
  decide +kernel

theorem g32p_supplierForest_actual_115438 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115438) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_115438
    g32p_supplierForest_actual_107516

def g32p_supplierForest_node_115452 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_115452 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115452 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_041859 := by
  decide +kernel

theorem g32p_supplierForest_actual_115452 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115452) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_115452
    g32p_supplierForest_actual_041859

def g32p_supplierForest_node_115460 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_115460 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115460 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_123568 := by
  decide +kernel

theorem g32p_supplierForest_actual_115460 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115460) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_115460
    g32p_supplierForest_actual_123568

def g32p_supplierForest_node_115463 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_115463 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115463 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_037654 := by
  decide +kernel

theorem g32p_supplierForest_actual_115463 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115463) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_115463
    g32p_supplierForest_actual_037654

def g32p_supplierForest_node_115465 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115465 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115465 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113186 := by
  decide +kernel

theorem g32p_supplierForest_actual_115465 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115465) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_115465
    g32p_supplierForest_actual_113186

def g32p_supplierForest_node_115486 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_115486 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115486 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118001 := by
  decide +kernel

theorem g32p_supplierForest_actual_115486 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115486) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_115486
    g32p_supplierForest_actual_118001

def g32p_supplierForest_node_115489 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_115489 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115489 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122442 := by
  decide +kernel

theorem g32p_supplierForest_actual_115489 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115489) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 1 g32p_supplierForest_edge_115489
    g32p_supplierForest_actual_122442

def g32p_supplierForest_node_115511 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_115511 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115511 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029839 := by
  decide +kernel

theorem g32p_supplierForest_actual_115511 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115511) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_115511
    g32p_supplierForest_actual_029839

def g32p_supplierForest_node_115515 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_115515 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115515 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_042185 := by
  decide +kernel

theorem g32p_supplierForest_actual_115515 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115515) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_115515
    g32p_supplierForest_actual_042185

def g32p_supplierForest_node_115526 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_115526 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115526 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122367 := by
  decide +kernel

theorem g32p_supplierForest_actual_115526 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115526) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 0 g32p_supplierForest_edge_115526
    g32p_supplierForest_actual_122367

def g32p_supplierForest_node_115535 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_115535 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115535 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_038861 := by
  decide +kernel

theorem g32p_supplierForest_actual_115535 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115535) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 3 g32p_supplierForest_edge_115535
    g32p_supplierForest_actual_038861

def g32p_supplierForest_node_115539 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_115539 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115539 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_037790 := by
  decide +kernel

theorem g32p_supplierForest_actual_115539 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115539) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_115539
    g32p_supplierForest_actual_037790

def g32p_supplierForest_node_115554 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_115554 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115554 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108764 := by
  decide +kernel

theorem g32p_supplierForest_actual_115554 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115554) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_115554
    g32p_supplierForest_actual_108764

def g32p_supplierForest_node_115566 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_115566 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115566 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_036917 := by
  decide +kernel

theorem g32p_supplierForest_actual_115566 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115566) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_115566
    g32p_supplierForest_actual_036917

def g32p_supplierForest_node_115568 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_115568 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115568 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_105067 := by
  decide +kernel

theorem g32p_supplierForest_actual_115568 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115568) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_115568
    g32p_supplierForest_actual_105067

def g32p_supplierForest_node_115570 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115570 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115570 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113873 := by
  decide +kernel

theorem g32p_supplierForest_actual_115570 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115570) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_115570
    g32p_supplierForest_actual_113873

def g32p_supplierForest_node_115578 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_115578 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115578 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_028567 := by
  decide +kernel

theorem g32p_supplierForest_actual_115578 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115578) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_115578
    g32p_supplierForest_actual_028567

def g32p_supplierForest_node_115588 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_115588 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115588 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_111731 := by
  decide +kernel

theorem g32p_supplierForest_actual_115588 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115588) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_115588
    g32p_supplierForest_actual_111731

def g32p_supplierForest_node_115592 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_115592 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115592 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_036788 := by
  decide +kernel

theorem g32p_supplierForest_actual_115592 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115592) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_115592
    g32p_supplierForest_actual_036788

def g32p_supplierForest_node_115595 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_115595 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115595 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122665 := by
  decide +kernel

theorem g32p_supplierForest_actual_115595 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115595) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_115595
    g32p_supplierForest_actual_122665

def g32p_supplierForest_node_115631 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115631 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115631 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029528 := by
  decide +kernel

theorem g32p_supplierForest_actual_115631 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115631) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_115631
    g32p_supplierForest_actual_029528

def g32p_supplierForest_node_115647 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_115647 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115647 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123403 := by
  decide +kernel

theorem g32p_supplierForest_actual_115647 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115647) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 1 g32p_supplierForest_edge_115647
    g32p_supplierForest_actual_123403

def g32p_supplierForest_node_115669 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_115669 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115669 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_031739 := by
  decide +kernel

theorem g32p_supplierForest_actual_115669 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115669) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_115669
    g32p_supplierForest_actual_031739

def g32p_supplierForest_node_115705 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115705 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115705 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115689 := by
  decide +kernel

theorem g32p_supplierForest_actual_115705 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115705) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_115705
    g32p_supplierForest_actual_115689

def g32p_supplierForest_node_115714 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_115714 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115714 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122505 := by
  decide +kernel

theorem g32p_supplierForest_actual_115714 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115714) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_115714
    g32p_supplierForest_actual_122505

def g32p_supplierForest_node_115742 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115742 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115742 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153445 := by
  decide +kernel

theorem g32p_supplierForest_actual_115742 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115742) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_115742
    g32p_supplierForest_actual_153445

def g32p_supplierForest_node_115759 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_115759 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115759 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104183 := by
  decide +kernel

theorem g32p_supplierForest_actual_115759 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115759) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_115759
    g32p_supplierForest_actual_104183

def g32p_supplierForest_node_115812 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115812 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115812 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_117140 := by
  decide +kernel

theorem g32p_supplierForest_actual_115812 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115812) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_115812
    g32p_supplierForest_actual_117140

def g32p_supplierForest_node_115815 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_115815 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115815 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_152571 := by
  decide +kernel

theorem g32p_supplierForest_actual_115815 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115815) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 1 g32p_supplierForest_edge_115815
    g32p_supplierForest_actual_152571

def g32p_supplierForest_node_115821 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_115821 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115821 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109210 := by
  decide +kernel

theorem g32p_supplierForest_actual_115821 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115821) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_115821
    g32p_supplierForest_actual_109210

def g32p_supplierForest_node_115838 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115838 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115838 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124295 := by
  decide +kernel

theorem g32p_supplierForest_actual_115838 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115838) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 0 g32p_supplierForest_edge_115838
    g32p_supplierForest_actual_124295

def g32p_supplierForest_node_115841 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115841 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115841 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_105464 := by
  decide +kernel

theorem g32p_supplierForest_actual_115841 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115841) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 1 g32p_supplierForest_edge_115841
    g32p_supplierForest_actual_105464

def g32p_supplierForest_node_115843 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_115843 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115843 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153383 := by
  decide +kernel

theorem g32p_supplierForest_actual_115843 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115843) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_115843
    g32p_supplierForest_actual_153383

def g32p_supplierForest_node_115860 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115860 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115860 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108764 := by
  decide +kernel

theorem g32p_supplierForest_actual_115860 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115860) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_115860
    g32p_supplierForest_actual_108764

def g32p_supplierForest_node_115864 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115864 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115864 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_113873 := by
  decide +kernel

theorem g32p_supplierForest_actual_115864 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115864) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_115864
    g32p_supplierForest_actual_113873

def g32p_supplierForest_node_115883 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_115883 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115883 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104277 := by
  decide +kernel

theorem g32p_supplierForest_actual_115883 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115883) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_115883
    g32p_supplierForest_actual_104277

def g32p_supplierForest_node_115887 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_115887 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115887 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_112355 := by
  decide +kernel

theorem g32p_supplierForest_actual_115887 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115887) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_115887
    g32p_supplierForest_actual_112355

def g32p_supplierForest_node_115906 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_115906 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115906 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_042451 := by
  decide +kernel

theorem g32p_supplierForest_actual_115906 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115906) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 0 g32p_supplierForest_edge_115906
    g32p_supplierForest_actual_042451

def g32p_supplierForest_node_115921 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115921 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115921 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_042005 := by
  decide +kernel

theorem g32p_supplierForest_actual_115921 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115921) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_115921
    g32p_supplierForest_actual_042005

def g32p_supplierForest_node_115954 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_115954 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115954 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_104618 := by
  decide +kernel

theorem g32p_supplierForest_actual_115954 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115954) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_115954
    g32p_supplierForest_actual_104618

def g32p_supplierForest_node_115961 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_115961 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115961 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104300 := by
  decide +kernel

theorem g32p_supplierForest_actual_115961 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115961) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_115961
    g32p_supplierForest_actual_104300

def g32p_supplierForest_node_115975 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_115975 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115975 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_037150 := by
  decide +kernel

theorem g32p_supplierForest_actual_115975 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115975) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_115975
    g32p_supplierForest_actual_037150

def g32p_supplierForest_node_115991 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_115991 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115991 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124388 := by
  decide +kernel

theorem g32p_supplierForest_actual_115991 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115991) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 0 g32p_supplierForest_edge_115991
    g32p_supplierForest_actual_124388

def g32p_supplierForest_node_115993 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_115993 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115993 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122480 := by
  decide +kernel

theorem g32p_supplierForest_actual_115993 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115993) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_115993
    g32p_supplierForest_actual_122480

def g32p_supplierForest_node_115997 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_115997 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115997 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_111184 := by
  decide +kernel

theorem g32p_supplierForest_actual_115997 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115997) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_115997
    g32p_supplierForest_actual_111184

def g32p_supplierForest_node_116052 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_116052 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116052 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124425 := by
  decide +kernel

theorem g32p_supplierForest_actual_116052 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116052) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_116052
    g32p_supplierForest_actual_124425

def g32p_supplierForest_node_116059 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_116059 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116059 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118469 := by
  decide +kernel

theorem g32p_supplierForest_actual_116059 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116059) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 3 g32p_supplierForest_edge_116059
    g32p_supplierForest_actual_118469

def g32p_supplierForest_node_116064 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_116064 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116064 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124435 := by
  decide +kernel

theorem g32p_supplierForest_actual_116064 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116064) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_116064
    g32p_supplierForest_actual_124435

def g32p_supplierForest_node_116089 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_116089 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116089 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_032209 := by
  decide +kernel

theorem g32p_supplierForest_actual_116089 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116089) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_116089
    g32p_supplierForest_actual_032209

def g32p_supplierForest_node_116095 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_116095 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116095 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122689 := by
  decide +kernel

theorem g32p_supplierForest_actual_116095 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116095) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_116095
    g32p_supplierForest_actual_122689

def g32p_supplierForest_node_116106 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_116106 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116106 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124469 := by
  decide +kernel

theorem g32p_supplierForest_actual_116106 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116106) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_116106
    g32p_supplierForest_actual_124469

def g32p_supplierForest_node_116145 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_116145 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116145 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_115648 := by
  decide +kernel

theorem g32p_supplierForest_actual_116145 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116145) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_116145
    g32p_supplierForest_actual_115648

def g32p_supplierForest_node_116156 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_116156 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116156 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_032442 := by
  decide +kernel

theorem g32p_supplierForest_actual_116156 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116156) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_116156
    g32p_supplierForest_actual_032442

def g32p_supplierForest_node_116160 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_116160 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116160 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_029072 := by
  decide +kernel

theorem g32p_supplierForest_actual_116160 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116160) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_116160
    g32p_supplierForest_actual_029072

def g32p_supplierForest_node_116175 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_116175 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116175 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108751 := by
  decide +kernel

theorem g32p_supplierForest_actual_116175 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116175) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 3 g32p_supplierForest_edge_116175
    g32p_supplierForest_actual_108751

def g32p_supplierForest_node_116176 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_116176 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116176 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_032332 := by
  decide +kernel

theorem g32p_supplierForest_actual_116176 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116176) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 3 g32p_supplierForest_edge_116176
    g32p_supplierForest_actual_032332

def g32p_supplierForest_node_116185 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_116185 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116185 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_029883 := by
  decide +kernel

theorem g32p_supplierForest_actual_116185 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116185) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_116185
    g32p_supplierForest_actual_029883

def g32p_supplierForest_node_116198 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_116198 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116198 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_113934 := by
  decide +kernel

theorem g32p_supplierForest_actual_116198 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116198) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_116198
    g32p_supplierForest_actual_113934

def g32p_supplierForest_node_116238 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_116238 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116238 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124538 := by
  decide +kernel

theorem g32p_supplierForest_actual_116238 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116238) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_116238
    g32p_supplierForest_actual_124538

def g32p_supplierForest_node_116325 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_116325 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116325 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_116180 := by
  decide +kernel

theorem g32p_supplierForest_actual_116325 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116325) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_116325
    g32p_supplierForest_actual_116180

def g32p_supplierForest_node_116368 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_116368 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116368 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_119828 := by
  decide +kernel

theorem g32p_supplierForest_actual_116368 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116368) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_116368
    g32p_supplierForest_actual_119828

def g32p_supplierForest_node_116381 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_116381 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116381 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120279 := by
  decide +kernel

theorem g32p_supplierForest_actual_116381 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116381) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_116381
    g32p_supplierForest_actual_120279

def g32p_supplierForest_node_116534 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_116534 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116534 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153449 := by
  decide +kernel

theorem g32p_supplierForest_actual_116534 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116534) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 3 g32p_supplierForest_edge_116534
    g32p_supplierForest_actual_153449

def g32p_supplierForest_node_116543 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_116543 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116543 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124114 := by
  decide +kernel

theorem g32p_supplierForest_actual_116543 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116543) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_116543
    g32p_supplierForest_actual_124114

def g32p_supplierForest_node_116575 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_116575 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116575 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120222 := by
  decide +kernel

theorem g32p_supplierForest_actual_116575 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116575) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 1 g32p_supplierForest_edge_116575
    g32p_supplierForest_actual_120222

def g32p_supplierForest_node_116604 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_116604 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116604 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154517 := by
  decide +kernel

theorem g32p_supplierForest_actual_116604 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116604) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 3 g32p_supplierForest_edge_116604
    g32p_supplierForest_actual_154517

def g32p_supplierForest_node_116627 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_116627 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116627 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_105777 := by
  decide +kernel

theorem g32p_supplierForest_actual_116627 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116627) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_116627
    g32p_supplierForest_actual_105777

def g32p_supplierForest_node_116657 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_116657 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116657 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_113609 := by
  decide +kernel

theorem g32p_supplierForest_actual_116657 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116657) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_116657
    g32p_supplierForest_actual_113609

def g32p_supplierForest_node_116715 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_116715 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116715 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_115937 := by
  decide +kernel

theorem g32p_supplierForest_actual_116715 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116715) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_116715
    g32p_supplierForest_actual_115937

def g32p_supplierForest_node_116830 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_116830 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116830 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122409 := by
  decide +kernel

theorem g32p_supplierForest_actual_116830 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116830) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_116830
    g32p_supplierForest_actual_122409

def g32p_supplierForest_node_116922 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_116922 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116922 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153035 := by
  decide +kernel

theorem g32p_supplierForest_actual_116922 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116922) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_116922
    g32p_supplierForest_actual_153035

def g32p_supplierForest_node_116924 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_116924 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116924 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_120139 := by
  decide +kernel

theorem g32p_supplierForest_actual_116924 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116924) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_116924
    g32p_supplierForest_actual_120139

def g32p_supplierForest_node_116942 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_116942 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116942 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_117729 := by
  decide +kernel

theorem g32p_supplierForest_actual_116942 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116942) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_116942
    g32p_supplierForest_actual_117729

def g32p_supplierForest_node_116969 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_116969 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116969 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126033 := by
  decide +kernel

theorem g32p_supplierForest_actual_116969 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116969) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_116969
    g32p_supplierForest_actual_126033

def g32p_supplierForest_node_116988 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_116988 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116988 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_118391 := by
  decide +kernel

theorem g32p_supplierForest_actual_116988 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116988) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 0 g32p_supplierForest_edge_116988
    g32p_supplierForest_actual_118391

def g32p_supplierForest_node_116993 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_116993 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116993 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_123449 := by
  decide +kernel

theorem g32p_supplierForest_actual_116993 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116993) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_116993
    g32p_supplierForest_actual_123449

def g32p_supplierForest_node_116998 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_116998 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116998 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037739 := by
  decide +kernel

theorem g32p_supplierForest_actual_116998 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116998) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_116998
    g32p_supplierForest_actual_037739

def g32p_supplierForest_node_117010 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117010 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117010 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124890 := by
  decide +kernel

theorem g32p_supplierForest_actual_117010 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117010) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_117010
    g32p_supplierForest_actual_124890

def g32p_supplierForest_node_117066 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117066 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117066 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_028836 := by
  decide +kernel

theorem g32p_supplierForest_actual_117066 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117066) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_117066
    g32p_supplierForest_actual_028836

def g32p_supplierForest_node_117089 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117089 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117089 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_104580 := by
  decide +kernel

theorem g32p_supplierForest_actual_117089 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117089) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_117089
    g32p_supplierForest_actual_104580

def g32p_supplierForest_node_117092 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_117092 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117092 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123598 := by
  decide +kernel

theorem g32p_supplierForest_actual_117092 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117092) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 1 g32p_supplierForest_edge_117092
    g32p_supplierForest_actual_123598

def g32p_supplierForest_node_117100 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_117100 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117100 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_044087 := by
  decide +kernel

theorem g32p_supplierForest_actual_117100 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117100) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_117100
    g32p_supplierForest_actual_044087

def g32p_supplierForest_node_117115 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_117115 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117115 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_103068 := by
  decide +kernel

theorem g32p_supplierForest_actual_117115 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117115) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 1 g32p_supplierForest_edge_117115
    g32p_supplierForest_actual_103068

def g32p_supplierForest_node_117125 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_117125 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117125 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123387 := by
  decide +kernel

theorem g32p_supplierForest_actual_117125 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117125) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 2 g32p_supplierForest_edge_117125
    g32p_supplierForest_actual_123387

def g32p_supplierForest_node_117142 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117142 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117142 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_043341 := by
  decide +kernel

theorem g32p_supplierForest_actual_117142 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117142) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_117142
    g32p_supplierForest_actual_043341

def g32p_supplierForest_node_117151 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_117151 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117151 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_124221 := by
  decide +kernel

theorem g32p_supplierForest_actual_117151 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117151) ∧
        IsConj g (g32p_literalRepresentative 87) := by
  exact g32p_archive_step_lift _ _ 87 1 g32p_supplierForest_edge_117151
    g32p_supplierForest_actual_124221

def g32p_supplierForest_node_117163 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_117163 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117163 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120465 := by
  decide +kernel

theorem g32p_supplierForest_actual_117163 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117163) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 1 g32p_supplierForest_edge_117163
    g32p_supplierForest_actual_120465

def g32p_supplierForest_node_117224 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117224 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117224 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113605 := by
  decide +kernel

theorem g32p_supplierForest_actual_117224 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117224) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_117224
    g32p_supplierForest_actual_113605

def g32p_supplierForest_node_117248 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_117248 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117248 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108843 := by
  decide +kernel

theorem g32p_supplierForest_actual_117248 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117248) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_117248
    g32p_supplierForest_actual_108843

def g32p_supplierForest_node_117264 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117264 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117264 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_036878 := by
  decide +kernel

theorem g32p_supplierForest_actual_117264 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117264) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_117264
    g32p_supplierForest_actual_036878

def g32p_supplierForest_node_117272 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_117272 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117272 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_119430 := by
  decide +kernel

theorem g32p_supplierForest_actual_117272 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117272) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_117272
    g32p_supplierForest_actual_119430

def g32p_supplierForest_node_117319 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_117319 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117319 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_107671 := by
  decide +kernel

theorem g32p_supplierForest_actual_117319 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117319) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_117319
    g32p_supplierForest_actual_107671

def g32p_supplierForest_node_117353 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117353 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117353 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122761 := by
  decide +kernel

theorem g32p_supplierForest_actual_117353 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117353) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_117353
    g32p_supplierForest_actual_122761

def g32p_supplierForest_node_117363 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_117363 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117363 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_034849 := by
  decide +kernel

theorem g32p_supplierForest_actual_117363 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117363) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_117363
    g32p_supplierForest_actual_034849

def g32p_supplierForest_node_117371 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_117371 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117371 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_110003 := by
  decide +kernel

theorem g32p_supplierForest_actual_117371 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117371) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_117371
    g32p_supplierForest_actual_110003

def g32p_supplierForest_node_117373 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117373 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117373 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_109803 := by
  decide +kernel

theorem g32p_supplierForest_actual_117373 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117373) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_117373
    g32p_supplierForest_actual_109803

def g32p_supplierForest_node_117382 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_117382 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117382 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_106963 := by
  decide +kernel

theorem g32p_supplierForest_actual_117382 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117382) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_117382
    g32p_supplierForest_actual_106963

def g32p_supplierForest_node_117383 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117383 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117383 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_105383 := by
  decide +kernel

theorem g32p_supplierForest_actual_117383 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117383) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_117383
    g32p_supplierForest_actual_105383

def g32p_supplierForest_node_117388 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_117388 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117388 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115454 := by
  decide +kernel

theorem g32p_supplierForest_actual_117388 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117388) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_117388
    g32p_supplierForest_actual_115454

def g32p_supplierForest_node_117473 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117473 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117473 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_032430 := by
  decide +kernel

theorem g32p_supplierForest_actual_117473 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117473) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 1 g32p_supplierForest_edge_117473
    g32p_supplierForest_actual_032430

def g32p_supplierForest_node_117490 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_117490 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117490 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_112525 := by
  decide +kernel

theorem g32p_supplierForest_actual_117490 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117490) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_117490
    g32p_supplierForest_actual_112525

def g32p_supplierForest_node_117534 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_117534 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117534 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_113616 := by
  decide +kernel

theorem g32p_supplierForest_actual_117534 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117534) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_117534
    g32p_supplierForest_actual_113616

def g32p_supplierForest_node_117623 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_117623 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117623 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_031371 := by
  decide +kernel

theorem g32p_supplierForest_actual_117623 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117623) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_117623
    g32p_supplierForest_actual_031371

def g32p_supplierForest_node_117639 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_117639 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117639 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120260 := by
  decide +kernel

theorem g32p_supplierForest_actual_117639 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117639) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_117639
    g32p_supplierForest_actual_120260

def g32p_supplierForest_node_117640 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_117640 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117640 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_119440 := by
  decide +kernel

theorem g32p_supplierForest_actual_117640 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117640) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_117640
    g32p_supplierForest_actual_119440

def g32p_supplierForest_node_117650 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_117650 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117650 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_154545 := by
  decide +kernel

theorem g32p_supplierForest_actual_117650 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117650) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_117650
    g32p_supplierForest_actual_154545

def g32p_supplierForest_node_117677 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117677 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117677 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_121880 := by
  decide +kernel

theorem g32p_supplierForest_actual_117677 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117677) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 3 g32p_supplierForest_edge_117677
    g32p_supplierForest_actual_121880

def g32p_supplierForest_node_117678 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_117678 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117678 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_127362 := by
  decide +kernel

theorem g32p_supplierForest_actual_117678 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117678) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_117678
    g32p_supplierForest_actual_127362

def g32p_supplierForest_node_117696 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117696 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117696 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109312 := by
  decide +kernel

theorem g32p_supplierForest_actual_117696 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117696) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_117696
    g32p_supplierForest_actual_109312

def g32p_supplierForest_node_117700 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117700 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117700 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118078 := by
  decide +kernel

theorem g32p_supplierForest_actual_117700 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117700) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 3 g32p_supplierForest_edge_117700
    g32p_supplierForest_actual_118078

def g32p_supplierForest_node_117721 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_117721 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117721 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_109996 := by
  decide +kernel

theorem g32p_supplierForest_actual_117721 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117721) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_117721
    g32p_supplierForest_actual_109996

def g32p_supplierForest_node_117727 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_117727 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117727 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117971 := by
  decide +kernel

theorem g32p_supplierForest_actual_117727 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117727) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_117727
    g32p_supplierForest_actual_117971

def g32p_supplierForest_node_117732 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_117732 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117732 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120548 := by
  decide +kernel

theorem g32p_supplierForest_actual_117732 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117732) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_117732
    g32p_supplierForest_actual_120548

def g32p_supplierForest_node_117751 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117751 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117751 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_114148 := by
  decide +kernel

theorem g32p_supplierForest_actual_117751 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117751) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_117751
    g32p_supplierForest_actual_114148

def g32p_supplierForest_node_117770 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117770 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117770 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_041046 := by
  decide +kernel

theorem g32p_supplierForest_actual_117770 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117770) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_117770
    g32p_supplierForest_actual_041046

def g32p_supplierForest_node_117809 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117809 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117809 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_125533 := by
  decide +kernel

theorem g32p_supplierForest_actual_117809 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117809) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 0 g32p_supplierForest_edge_117809
    g32p_supplierForest_actual_125533

def g32p_supplierForest_node_117841 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_117841 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117841 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_038617 := by
  decide +kernel

theorem g32p_supplierForest_actual_117841 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117841) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 3 g32p_supplierForest_edge_117841
    g32p_supplierForest_actual_038617

def g32p_supplierForest_node_117864 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_117864 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117864 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_125700 := by
  decide +kernel

theorem g32p_supplierForest_actual_117864 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117864) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 1 g32p_supplierForest_edge_117864
    g32p_supplierForest_actual_125700

def g32p_supplierForest_node_117893 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_117893 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117893 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_030547 := by
  decide +kernel

theorem g32p_supplierForest_actual_117893 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117893) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_117893
    g32p_supplierForest_actual_030547

def g32p_supplierForest_node_117917 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117917 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117917 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_039418 := by
  decide +kernel

theorem g32p_supplierForest_actual_117917 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117917) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_117917
    g32p_supplierForest_actual_039418

def g32p_supplierForest_node_117923 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117923 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117923 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_041947 := by
  decide +kernel

theorem g32p_supplierForest_actual_117923 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117923) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_117923
    g32p_supplierForest_actual_041947

def g32p_supplierForest_node_118054 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_118054 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118054 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154867 := by
  decide +kernel

theorem g32p_supplierForest_actual_118054 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118054) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_118054
    g32p_supplierForest_actual_154867

def g32p_supplierForest_node_118084 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_118084 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118084 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_120603 := by
  decide +kernel

theorem g32p_supplierForest_actual_118084 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118084) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_118084
    g32p_supplierForest_actual_120603

def g32p_supplierForest_node_118101 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_118101 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118101 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_104580 := by
  decide +kernel

theorem g32p_supplierForest_actual_118101 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118101) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_118101
    g32p_supplierForest_actual_104580

def g32p_supplierForest_node_118134 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_118134 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118134 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_123233 := by
  decide +kernel

theorem g32p_supplierForest_actual_118134 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118134) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_118134
    g32p_supplierForest_actual_123233

def g32p_supplierForest_node_118135 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118135 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118135 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_120220 := by
  decide +kernel

theorem g32p_supplierForest_actual_118135 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118135) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_118135
    g32p_supplierForest_actual_120220

def g32p_supplierForest_node_118136 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118136 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118136 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118257 := by
  decide +kernel

theorem g32p_supplierForest_actual_118136 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118136) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_118136
    g32p_supplierForest_actual_118257

def g32p_supplierForest_node_118171 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118171 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118171 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_112831 := by
  decide +kernel

theorem g32p_supplierForest_actual_118171 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118171) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_118171
    g32p_supplierForest_actual_112831

def g32p_supplierForest_node_118198 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118198 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118198 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152891 := by
  decide +kernel

theorem g32p_supplierForest_actual_118198 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118198) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_118198
    g32p_supplierForest_actual_152891

def g32p_supplierForest_node_118213 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118213 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118213 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_127527 := by
  decide +kernel

theorem g32p_supplierForest_actual_118213 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118213) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_118213
    g32p_supplierForest_actual_127527

def g32p_supplierForest_node_118223 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118223 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118223 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_117225 := by
  decide +kernel

theorem g32p_supplierForest_actual_118223 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118223) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_118223
    g32p_supplierForest_actual_117225

def g32p_supplierForest_node_118242 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118242 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118242 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_127363 := by
  decide +kernel

theorem g32p_supplierForest_actual_118242 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118242) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_118242
    g32p_supplierForest_actual_127363

def g32p_supplierForest_node_118276 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_118276 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118276 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_102251 := by
  decide +kernel

theorem g32p_supplierForest_actual_118276 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118276) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_118276
    g32p_supplierForest_actual_102251

def g32p_supplierForest_node_118279 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_118279 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118279 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_111652 := by
  decide +kernel

theorem g32p_supplierForest_actual_118279 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118279) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_118279
    g32p_supplierForest_actual_111652

def g32p_supplierForest_node_118310 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_118310 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118310 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_039453 := by
  decide +kernel

theorem g32p_supplierForest_actual_118310 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118310) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_118310
    g32p_supplierForest_actual_039453

def g32p_supplierForest_node_118337 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_118337 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118337 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_102769 := by
  decide +kernel

theorem g32p_supplierForest_actual_118337 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118337) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_118337
    g32p_supplierForest_actual_102769

def g32p_supplierForest_node_118387 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_118387 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118387 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_103150 := by
  decide +kernel

theorem g32p_supplierForest_actual_118387 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118387) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 0 g32p_supplierForest_edge_118387
    g32p_supplierForest_actual_103150

def g32p_supplierForest_node_118440 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_118440 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118440 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_036136 := by
  decide +kernel

theorem g32p_supplierForest_actual_118440 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118440) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_118440
    g32p_supplierForest_actual_036136

def g32p_supplierForest_node_118478 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_118478 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118478 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120803 := by
  decide +kernel

theorem g32p_supplierForest_actual_118478 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118478) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_118478
    g32p_supplierForest_actual_120803

def g32p_supplierForest_node_118480 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118480 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118480 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_104208 := by
  decide +kernel

theorem g32p_supplierForest_actual_118480 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118480) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 3 g32p_supplierForest_edge_118480
    g32p_supplierForest_actual_104208

def g32p_supplierForest_node_118547 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118547 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118547 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124952 := by
  decide +kernel

theorem g32p_supplierForest_actual_118547 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118547) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_118547
    g32p_supplierForest_actual_124952

def g32p_supplierForest_node_118550 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_118550 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118550 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_125944 := by
  decide +kernel

theorem g32p_supplierForest_actual_118550 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118550) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_118550
    g32p_supplierForest_actual_125944

def g32p_supplierForest_node_118558 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_118558 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118558 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_036735 := by
  decide +kernel

theorem g32p_supplierForest_actual_118558 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118558) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_118558
    g32p_supplierForest_actual_036735

def g32p_supplierForest_node_118578 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118578 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118578 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_040750 := by
  decide +kernel

theorem g32p_supplierForest_actual_118578 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118578) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_118578
    g32p_supplierForest_actual_040750

def g32p_supplierForest_node_118584 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118584 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118584 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_126551 := by
  decide +kernel

theorem g32p_supplierForest_actual_118584 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118584) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_118584
    g32p_supplierForest_actual_126551

def g32p_supplierForest_node_118595 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118595 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118595 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_028731 := by
  decide +kernel

theorem g32p_supplierForest_actual_118595 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118595) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 3 g32p_supplierForest_edge_118595
    g32p_supplierForest_actual_028731

def g32p_supplierForest_node_118610 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118610 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118610 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_126837 := by
  decide +kernel

theorem g32p_supplierForest_actual_118610 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118610) ∧
        IsConj g (g32p_literalRepresentative 93) := by
  exact g32p_archive_step_lift _ _ 93 3 g32p_supplierForest_edge_118610
    g32p_supplierForest_actual_126837

def g32p_supplierForest_node_118656 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_118656 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118656 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_040485 := by
  decide +kernel

theorem g32p_supplierForest_actual_118656 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118656) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_118656
    g32p_supplierForest_actual_040485

def g32p_supplierForest_node_118666 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_118666 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118666 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120375 := by
  decide +kernel

theorem g32p_supplierForest_actual_118666 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118666) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_118666
    g32p_supplierForest_actual_120375

def g32p_supplierForest_node_118685 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_118685 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118685 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_026334 := by
  decide +kernel

theorem g32p_supplierForest_actual_118685 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118685) ∧
        IsConj g (g32p_literalRepresentative 65) := by
  exact g32p_archive_step_lift _ _ 65 3 g32p_supplierForest_edge_118685
    g32p_supplierForest_actual_026334

def g32p_supplierForest_node_118687 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_118687 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118687 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_110756 := by
  decide +kernel

theorem g32p_supplierForest_actual_118687 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118687) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_118687
    g32p_supplierForest_actual_110756

def g32p_supplierForest_node_118724 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_118724 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118724 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_114216 := by
  decide +kernel

theorem g32p_supplierForest_actual_118724 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118724) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_118724
    g32p_supplierForest_actual_114216

def g32p_supplierForest_node_118737 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118737 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118737 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115003 := by
  decide +kernel

theorem g32p_supplierForest_actual_118737 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118737) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_118737
    g32p_supplierForest_actual_115003

end HodgeLean.Foundations.Program

end
end
