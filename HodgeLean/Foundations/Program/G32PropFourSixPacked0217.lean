import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0211
import HodgeLean.Foundations.Program.G32PropFourSixPacked0212
import HodgeLean.Foundations.Program.G32PropFourSixPacked0213
import HodgeLean.Foundations.Program.G32PropFourSixPacked0214
import HodgeLean.Foundations.Program.G32PropFourSixPacked0215
import HodgeLean.Foundations.Program.G32PropFourSixPacked0216

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_000643 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_000643 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000643 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001003 := by
  decide +kernel

theorem g32p_supplierForest_actual_000643 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000643) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 0 g32p_supplierForest_edge_000643
    g32p_supplierForest_actual_001003

def g32p_supplierForest_node_000649 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_000649 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000649 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_009389 := by
  decide +kernel

theorem g32p_supplierForest_actual_000649 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000649) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 1 g32p_supplierForest_edge_000649
    g32p_supplierForest_actual_009389

def g32p_supplierForest_node_000682 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000682 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000682 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_000044 := by
  decide +kernel

theorem g32p_supplierForest_actual_000682 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000682) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 1 g32p_supplierForest_edge_000682
    g32p_supplierForest_actual_000044

def g32p_supplierForest_node_000718 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_000718 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000718 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000691 := by
  decide +kernel

theorem g32p_supplierForest_actual_000718 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000718) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 3 g32p_supplierForest_edge_000718
    g32p_supplierForest_actual_000691

def g32p_supplierForest_node_000738 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_000738 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000738 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000035 := by
  decide +kernel

theorem g32p_supplierForest_actual_000738 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000738) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 3 g32p_supplierForest_edge_000738
    g32p_supplierForest_actual_000035

def g32p_supplierForest_node_000748 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000748 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000748 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_005940 := by
  decide +kernel

theorem g32p_supplierForest_actual_000748 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000748) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 0 g32p_supplierForest_edge_000748
    g32p_supplierForest_actual_005940

def g32p_supplierForest_node_000750 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_000750 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000750 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000691 := by
  decide +kernel

theorem g32p_supplierForest_actual_000750 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000750) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 0 g32p_supplierForest_edge_000750
    g32p_supplierForest_actual_000691

def g32p_supplierForest_node_000764 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000764 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000764 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000035 := by
  decide +kernel

theorem g32p_supplierForest_actual_000764 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000764) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 2 g32p_supplierForest_edge_000764
    g32p_supplierForest_actual_000035

def g32p_supplierForest_node_000768 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_000768 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000768 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000036 := by
  decide +kernel

theorem g32p_supplierForest_actual_000768 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000768) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 3 g32p_supplierForest_edge_000768
    g32p_supplierForest_actual_000036

def g32p_supplierForest_node_000807 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_000807 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000807 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_006068 := by
  decide +kernel

theorem g32p_supplierForest_actual_000807 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000807) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 0 g32p_supplierForest_edge_000807
    g32p_supplierForest_actual_006068

def g32p_supplierForest_node_000856 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000856 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000856 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_001003 := by
  decide +kernel

theorem g32p_supplierForest_actual_000856 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000856) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 1 g32p_supplierForest_edge_000856
    g32p_supplierForest_actual_001003

def g32p_supplierForest_node_000907 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000907 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000907 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_009389 := by
  decide +kernel

theorem g32p_supplierForest_actual_000907 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000907) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 3 g32p_supplierForest_edge_000907
    g32p_supplierForest_actual_009389

def g32p_supplierForest_node_000963 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_000963 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000963 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_009590 := by
  decide +kernel

theorem g32p_supplierForest_actual_000963 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000963) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_000963
    g32p_supplierForest_actual_009590

def g32p_supplierForest_node_000991 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000991 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000991 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000057 := by
  decide +kernel

theorem g32p_supplierForest_actual_000991 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000991) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 2 g32p_supplierForest_edge_000991
    g32p_supplierForest_actual_000057

def g32p_supplierForest_node_001042 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001042 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001042 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000044 := by
  decide +kernel

theorem g32p_supplierForest_actual_001042 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001042) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 3 g32p_supplierForest_edge_001042
    g32p_supplierForest_actual_000044

def g32p_supplierForest_node_001084 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001084 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001084 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001266 := by
  decide +kernel

theorem g32p_supplierForest_actual_001084 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001084) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001084
    g32p_supplierForest_actual_001266

def g32p_supplierForest_node_001090 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_001090 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001090 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001282 := by
  decide +kernel

theorem g32p_supplierForest_actual_001090 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001090) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_001090
    g32p_supplierForest_actual_001282

def g32p_supplierForest_node_001131 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001131 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001131 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_001335 := by
  decide +kernel

theorem g32p_supplierForest_actual_001131 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001131) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 1 g32p_supplierForest_edge_001131
    g32p_supplierForest_actual_001335

def g32p_supplierForest_node_001174 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001174 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001174 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_001148 := by
  decide +kernel

theorem g32p_supplierForest_actual_001174 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001174) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 2 g32p_supplierForest_edge_001174
    g32p_supplierForest_actual_001148

def g32p_supplierForest_node_001211 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001211 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001211 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001415 := by
  decide +kernel

theorem g32p_supplierForest_actual_001211 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001211) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001211
    g32p_supplierForest_actual_001415

def g32p_supplierForest_node_001223 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001223 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001223 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001595 := by
  decide +kernel

theorem g32p_supplierForest_actual_001223 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001223) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_001223
    g32p_supplierForest_actual_001595

def g32p_supplierForest_node_001284 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001284 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001284 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014732 := by
  decide +kernel

theorem g32p_supplierForest_actual_001284 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001284) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_001284
    g32p_supplierForest_actual_014732

def g32p_supplierForest_node_001289 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001289 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001289 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001292 := by
  decide +kernel

theorem g32p_supplierForest_actual_001289 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001289) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001289
    g32p_supplierForest_actual_001292

def g32p_supplierForest_node_001296 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001296 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001296 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014733 := by
  decide +kernel

theorem g32p_supplierForest_actual_001296 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001296) ∧
        IsConj g (g32p_literalRepresentative 28) := by
  exact g32p_archive_step_lift _ _ 28 3 g32p_supplierForest_edge_001296
    g32p_supplierForest_actual_014733

def g32p_supplierForest_node_001307 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_001307 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001307 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000109 := by
  decide +kernel

theorem g32p_supplierForest_actual_001307 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001307) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 0 g32p_supplierForest_edge_001307
    g32p_supplierForest_actual_000109

def g32p_supplierForest_node_001309 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001309 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001309 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001415 := by
  decide +kernel

theorem g32p_supplierForest_actual_001309 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001309) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_001309
    g32p_supplierForest_actual_001415

def g32p_supplierForest_node_001321 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_001321 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001321 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001262 := by
  decide +kernel

theorem g32p_supplierForest_actual_001321 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001321) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001321
    g32p_supplierForest_actual_001262

def g32p_supplierForest_node_001334 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_001334 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001334 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_014254 := by
  decide +kernel

theorem g32p_supplierForest_actual_001334 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001334) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_001334
    g32p_supplierForest_actual_014254

def g32p_supplierForest_node_001370 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_001370 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001370 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_001327 := by
  decide +kernel

theorem g32p_supplierForest_actual_001370 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001370) ∧
        IsConj g (g32p_literalRepresentative 1) := by
  exact g32p_archive_step_lift _ _ 1 2 g32p_supplierForest_edge_001370
    g32p_supplierForest_actual_001327

def g32p_supplierForest_node_001371 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001371 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001371 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000081 := by
  decide +kernel

theorem g32p_supplierForest_actual_001371 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001371) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 2 g32p_supplierForest_edge_001371
    g32p_supplierForest_actual_000081

def g32p_supplierForest_node_001380 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_001380 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001380 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015154 := by
  decide +kernel

theorem g32p_supplierForest_actual_001380 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001380) ∧
        IsConj g (g32p_literalRepresentative 28) := by
  exact g32p_archive_step_lift _ _ 28 3 g32p_supplierForest_edge_001380
    g32p_supplierForest_actual_015154

def g32p_supplierForest_node_001420 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001420 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001420 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_002019 := by
  decide +kernel

theorem g32p_supplierForest_actual_001420 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001420) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 0 g32p_supplierForest_edge_001420
    g32p_supplierForest_actual_002019

def g32p_supplierForest_node_001443 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001443 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001443 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_001266 := by
  decide +kernel

theorem g32p_supplierForest_actual_001443 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001443) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001443
    g32p_supplierForest_actual_001266

def g32p_supplierForest_node_001457 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001457 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001457 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_014733 := by
  decide +kernel

theorem g32p_supplierForest_actual_001457 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001457) ∧
        IsConj g (g32p_literalRepresentative 28) := by
  exact g32p_archive_step_lift _ _ 28 1 g32p_supplierForest_edge_001457
    g32p_supplierForest_actual_014733

def g32p_supplierForest_node_001461 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001461 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001461 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014447 := by
  decide +kernel

theorem g32p_supplierForest_actual_001461 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001461) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_001461
    g32p_supplierForest_actual_014447

def g32p_supplierForest_node_001484 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001484 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001484 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_001486 := by
  decide +kernel

theorem g32p_supplierForest_actual_001484 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001484) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001484
    g32p_supplierForest_actual_001486

def g32p_supplierForest_node_001504 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_001504 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001504 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_001475 := by
  decide +kernel

theorem g32p_supplierForest_actual_001504 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001504) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 2 g32p_supplierForest_edge_001504
    g32p_supplierForest_actual_001475

def g32p_supplierForest_node_001509 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001509 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001509 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_001486 := by
  decide +kernel

theorem g32p_supplierForest_actual_001509 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001509) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 2 g32p_supplierForest_edge_001509
    g32p_supplierForest_actual_001486

def g32p_supplierForest_node_001538 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001538 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001538 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_014732 := by
  decide +kernel

theorem g32p_supplierForest_actual_001538 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001538) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001538
    g32p_supplierForest_actual_014732

def g32p_supplierForest_node_001558 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001558 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001558 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_017227 := by
  decide +kernel

theorem g32p_supplierForest_actual_001558 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001558) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 1 g32p_supplierForest_edge_001558
    g32p_supplierForest_actual_017227

def g32p_supplierForest_node_001588 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001588 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001588 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_014447 := by
  decide +kernel

theorem g32p_supplierForest_actual_001588 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001588) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001588
    g32p_supplierForest_actual_014447

def g32p_supplierForest_node_001653 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_001653 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001653 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020169 := by
  decide +kernel

theorem g32p_supplierForest_actual_001653 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001653) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_001653
    g32p_supplierForest_actual_020169

def g32p_supplierForest_node_001668 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001668 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001668 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_012374 := by
  decide +kernel

theorem g32p_supplierForest_actual_001668 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001668) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 0 g32p_supplierForest_edge_001668
    g32p_supplierForest_actual_012374

def g32p_supplierForest_node_001692 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001692 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001692 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_012428 := by
  decide +kernel

theorem g32p_supplierForest_actual_001692 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001692) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_001692
    g32p_supplierForest_actual_012428

def g32p_supplierForest_node_001707 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_001707 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001707 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_001465 := by
  decide +kernel

theorem g32p_supplierForest_actual_001707 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001707) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_001707
    g32p_supplierForest_actual_001465

def g32p_supplierForest_node_001784 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001784 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001784 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_012622 := by
  decide +kernel

theorem g32p_supplierForest_actual_001784 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001784) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 0 g32p_supplierForest_edge_001784
    g32p_supplierForest_actual_012622

def g32p_supplierForest_node_001789 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001789 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001789 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_012636 := by
  decide +kernel

theorem g32p_supplierForest_actual_001789 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001789) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001789
    g32p_supplierForest_actual_012636

def g32p_supplierForest_node_001807 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001807 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001807 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_001254 := by
  decide +kernel

theorem g32p_supplierForest_actual_001807 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001807) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 2 g32p_supplierForest_edge_001807
    g32p_supplierForest_actual_001254

def g32p_supplierForest_node_001815 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_001815 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001815 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_017429 := by
  decide +kernel

theorem g32p_supplierForest_actual_001815 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001815) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 2 g32p_supplierForest_edge_001815
    g32p_supplierForest_actual_017429

def g32p_supplierForest_node_001850 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001850 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001850 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_012764 := by
  decide +kernel

theorem g32p_supplierForest_actual_001850 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001850) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_001850
    g32p_supplierForest_actual_012764

def g32p_supplierForest_node_001866 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001866 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001866 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000108 := by
  decide +kernel

theorem g32p_supplierForest_actual_001866 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001866) ∧
        IsConj g (g32p_literalRepresentative 1) := by
  exact g32p_archive_step_lift _ _ 1 3 g32p_supplierForest_edge_001866
    g32p_supplierForest_actual_000108

def g32p_supplierForest_node_001937 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001937 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001937 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_012755 := by
  decide +kernel

theorem g32p_supplierForest_actual_001937 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001937) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_001937
    g32p_supplierForest_actual_012755

def g32p_supplierForest_node_001940 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_001940 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001940 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_002158 := by
  decide +kernel

theorem g32p_supplierForest_actual_001940 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001940) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_001940
    g32p_supplierForest_actual_002158

def g32p_supplierForest_node_001947 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_001947 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001947 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_001958 := by
  decide +kernel

theorem g32p_supplierForest_actual_001947 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001947) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 2 g32p_supplierForest_edge_001947
    g32p_supplierForest_actual_001958

def g32p_supplierForest_node_001955 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001955 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001955 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_000134 := by
  decide +kernel

theorem g32p_supplierForest_actual_001955 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001955) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_001955
    g32p_supplierForest_actual_000134

def g32p_supplierForest_node_001959 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001959 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001959 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014360 := by
  decide +kernel

theorem g32p_supplierForest_actual_001959 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001959) ∧
        IsConj g (g32p_literalRepresentative 28) := by
  exact g32p_archive_step_lift _ _ 28 3 g32p_supplierForest_edge_001959
    g32p_supplierForest_actual_014360

def g32p_supplierForest_node_002010 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_002010 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002010 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_002314 := by
  decide +kernel

theorem g32p_supplierForest_actual_002010 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002010) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_002010
    g32p_supplierForest_actual_002314

def g32p_supplierForest_node_002018 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_002018 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002018 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002019 := by
  decide +kernel

theorem g32p_supplierForest_actual_002018 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002018) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_002018
    g32p_supplierForest_actual_002019

def g32p_supplierForest_node_002039 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_002039 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002039 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021061 := by
  decide +kernel

theorem g32p_supplierForest_actual_002039 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002039) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 2 g32p_supplierForest_edge_002039
    g32p_supplierForest_actual_021061

def g32p_supplierForest_node_002212 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_002212 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002212 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_001854 := by
  decide +kernel

theorem g32p_supplierForest_actual_002212 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002212) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_002212
    g32p_supplierForest_actual_001854

def g32p_supplierForest_node_002249 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_002249 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002249 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000134 := by
  decide +kernel

theorem g32p_supplierForest_actual_002249 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002249) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_002249
    g32p_supplierForest_actual_000134

def g32p_supplierForest_node_002262 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002262 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002262 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_019756 := by
  decide +kernel

theorem g32p_supplierForest_actual_002262 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002262) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_002262
    g32p_supplierForest_actual_019756

def g32p_supplierForest_node_002269 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_002269 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002269 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_002314 := by
  decide +kernel

theorem g32p_supplierForest_actual_002269 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002269) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_002269
    g32p_supplierForest_actual_002314

def g32p_supplierForest_node_002275 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002275 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002275 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_013675 := by
  decide +kernel

theorem g32p_supplierForest_actual_002275 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002275) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 0 g32p_supplierForest_edge_002275
    g32p_supplierForest_actual_013675

def g32p_supplierForest_node_002342 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_002342 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002342 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000134 := by
  decide +kernel

theorem g32p_supplierForest_actual_002342 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002342) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_002342
    g32p_supplierForest_actual_000134

def g32p_supplierForest_node_002348 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_002348 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002348 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_015282 := by
  decide +kernel

theorem g32p_supplierForest_actual_002348 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002348) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_002348
    g32p_supplierForest_actual_015282

def g32p_supplierForest_node_002387 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_002387 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002387 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_013908 := by
  decide +kernel

theorem g32p_supplierForest_actual_002387 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002387) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_002387
    g32p_supplierForest_actual_013908

def g32p_supplierForest_node_002422 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_002422 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002422 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012501 := by
  decide +kernel

theorem g32p_supplierForest_actual_002422 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002422) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_002422
    g32p_supplierForest_actual_012501

def g32p_supplierForest_node_002445 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002445 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002445 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000081 := by
  decide +kernel

theorem g32p_supplierForest_actual_002445 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002445) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 3 g32p_supplierForest_edge_002445
    g32p_supplierForest_actual_000081

def g32p_supplierForest_node_002476 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002476 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002476 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001932 := by
  decide +kernel

theorem g32p_supplierForest_actual_002476 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002476) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_002476
    g32p_supplierForest_actual_001932

def g32p_supplierForest_node_002498 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_002498 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002498 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_020130 := by
  decide +kernel

theorem g32p_supplierForest_actual_002498 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002498) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_002498
    g32p_supplierForest_actual_020130

def g32p_supplierForest_node_002506 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_002506 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002506 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_014156 := by
  decide +kernel

theorem g32p_supplierForest_actual_002506 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002506) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_002506
    g32p_supplierForest_actual_014156

def g32p_supplierForest_node_002519 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_002519 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002519 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015753 := by
  decide +kernel

theorem g32p_supplierForest_actual_002519 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002519) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 2 g32p_supplierForest_edge_002519
    g32p_supplierForest_actual_015753

def g32p_supplierForest_node_002549 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_002549 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002549 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_002556 := by
  decide +kernel

theorem g32p_supplierForest_actual_002549 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002549) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 1 g32p_supplierForest_edge_002549
    g32p_supplierForest_actual_002556

def g32p_supplierForest_node_002585 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_002585 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002585 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003175 := by
  decide +kernel

theorem g32p_supplierForest_actual_002585 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002585) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_002585
    g32p_supplierForest_actual_003175

def g32p_supplierForest_node_002632 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002632 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002632 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_004152 := by
  decide +kernel

theorem g32p_supplierForest_actual_002632 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002632) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_002632
    g32p_supplierForest_actual_004152

def g32p_supplierForest_node_002667 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_002667 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002667 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003103 := by
  decide +kernel

theorem g32p_supplierForest_actual_002667 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002667) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 1 g32p_supplierForest_edge_002667
    g32p_supplierForest_actual_003103

def g32p_supplierForest_node_002676 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_002676 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002676 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002672 := by
  decide +kernel

theorem g32p_supplierForest_actual_002676 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002676) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 3 g32p_supplierForest_edge_002676
    g32p_supplierForest_actual_002672

def g32p_supplierForest_node_002737 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_002737 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002737 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000313 := by
  decide +kernel

theorem g32p_supplierForest_actual_002737 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002737) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 3 g32p_supplierForest_edge_002737
    g32p_supplierForest_actual_000313

def g32p_supplierForest_node_002782 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_002782 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002782 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_002718 := by
  decide +kernel

theorem g32p_supplierForest_actual_002782 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002782) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_002782
    g32p_supplierForest_actual_002718

def g32p_supplierForest_node_002785 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_002785 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002785 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_002725 := by
  decide +kernel

theorem g32p_supplierForest_actual_002785 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002785) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_002785
    g32p_supplierForest_actual_002725

def g32p_supplierForest_node_002786 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_002786 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002786 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003260 := by
  decide +kernel

theorem g32p_supplierForest_actual_002786 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002786) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_002786
    g32p_supplierForest_actual_003260

def g32p_supplierForest_node_002876 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_002876 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002876 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003696 := by
  decide +kernel

theorem g32p_supplierForest_actual_002876 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002876) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_002876
    g32p_supplierForest_actual_003696

def g32p_supplierForest_node_002937 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_002937 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002937 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_028128 := by
  decide +kernel

theorem g32p_supplierForest_actual_002937 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002937) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_002937
    g32p_supplierForest_actual_028128

def g32p_supplierForest_node_002967 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_002967 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002967 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003894 := by
  decide +kernel

theorem g32p_supplierForest_actual_002967 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002967) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 0 g32p_supplierForest_edge_002967
    g32p_supplierForest_actual_003894

def g32p_supplierForest_node_002970 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002970 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002970 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003901 := by
  decide +kernel

theorem g32p_supplierForest_actual_002970 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002970) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_002970
    g32p_supplierForest_actual_003901

def g32p_supplierForest_node_002973 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002973 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002973 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003908 := by
  decide +kernel

theorem g32p_supplierForest_actual_002973 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002973) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_002973
    g32p_supplierForest_actual_003908

def g32p_supplierForest_node_002974 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002974 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002974 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003910 := by
  decide +kernel

theorem g32p_supplierForest_actual_002974 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002974) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_002974
    g32p_supplierForest_actual_003910

def g32p_supplierForest_node_002980 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002980 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002980 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003037 := by
  decide +kernel

theorem g32p_supplierForest_actual_002980 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002980) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_002980
    g32p_supplierForest_actual_003037

def g32p_supplierForest_node_002981 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002981 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002981 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_003495 := by
  decide +kernel

theorem g32p_supplierForest_actual_002981 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002981) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_002981
    g32p_supplierForest_actual_003495

def g32p_supplierForest_node_002991 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_002991 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002991 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003063 := by
  decide +kernel

theorem g32p_supplierForest_actual_002991 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002991) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_002991
    g32p_supplierForest_actual_003063

def g32p_supplierForest_node_003010 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_003010 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003010 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_035529 := by
  decide +kernel

theorem g32p_supplierForest_actual_003010 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003010) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 3 g32p_supplierForest_edge_003010
    g32p_supplierForest_actual_035529

def g32p_supplierForest_node_003018 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_003018 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003018 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_003004 := by
  decide +kernel

theorem g32p_supplierForest_actual_003018 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003018) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 2 g32p_supplierForest_edge_003018
    g32p_supplierForest_actual_003004

def g32p_supplierForest_node_003026 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_003026 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003026 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_030584 := by
  decide +kernel

theorem g32p_supplierForest_actual_003026 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003026) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 2 g32p_supplierForest_edge_003026
    g32p_supplierForest_actual_030584

def g32p_supplierForest_node_003035 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_003035 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003035 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_033157 := by
  decide +kernel

theorem g32p_supplierForest_actual_003035 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003035) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 3 g32p_supplierForest_edge_003035
    g32p_supplierForest_actual_033157

def g32p_supplierForest_node_003051 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_003051 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003051 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003342 := by
  decide +kernel

theorem g32p_supplierForest_actual_003051 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003051) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 1 g32p_supplierForest_edge_003051
    g32p_supplierForest_actual_003342

def g32p_supplierForest_node_003059 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_003059 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003059 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_004090 := by
  decide +kernel

theorem g32p_supplierForest_actual_003059 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003059) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 0 g32p_supplierForest_edge_003059
    g32p_supplierForest_actual_004090

def g32p_supplierForest_node_003089 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_003089 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003089 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003860 := by
  decide +kernel

theorem g32p_supplierForest_actual_003089 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003089) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_003089
    g32p_supplierForest_actual_003860

def g32p_supplierForest_node_003091 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_003091 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003091 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_005705 := by
  decide +kernel

theorem g32p_supplierForest_actual_003091 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003091) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_003091
    g32p_supplierForest_actual_005705

def g32p_supplierForest_node_003109 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_003109 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003109 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_002556 := by
  decide +kernel

theorem g32p_supplierForest_actual_003109 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003109) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 2 g32p_supplierForest_edge_003109
    g32p_supplierForest_actual_002556

def g32p_supplierForest_node_003121 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_003121 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003121 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_044160 := by
  decide +kernel

theorem g32p_supplierForest_actual_003121 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003121) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_003121
    g32p_supplierForest_actual_044160

def g32p_supplierForest_node_003156 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_003156 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003156 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_028263 := by
  decide +kernel

theorem g32p_supplierForest_actual_003156 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003156) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_003156
    g32p_supplierForest_actual_028263

def g32p_supplierForest_node_003160 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_003160 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003160 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000229 := by
  decide +kernel

theorem g32p_supplierForest_actual_003160 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003160) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 2 g32p_supplierForest_edge_003160
    g32p_supplierForest_actual_000229

def g32p_supplierForest_node_003200 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_003200 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003200 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_004403 := by
  decide +kernel

theorem g32p_supplierForest_actual_003200 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003200) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_003200
    g32p_supplierForest_actual_004403

def g32p_supplierForest_node_003231 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_003231 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003231 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_028400 := by
  decide +kernel

theorem g32p_supplierForest_actual_003231 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003231) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 1 g32p_supplierForest_edge_003231
    g32p_supplierForest_actual_028400

def g32p_supplierForest_node_003237 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_003237 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003237 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004989 := by
  decide +kernel

theorem g32p_supplierForest_actual_003237 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003237) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 3 g32p_supplierForest_edge_003237
    g32p_supplierForest_actual_004989

def g32p_supplierForest_node_003249 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_003249 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003249 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_003260 := by
  decide +kernel

theorem g32p_supplierForest_actual_003249 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003249) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_003249
    g32p_supplierForest_actual_003260

def g32p_supplierForest_node_003257 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_003257 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003257 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_004526 := by
  decide +kernel

theorem g32p_supplierForest_actual_003257 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003257) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_003257
    g32p_supplierForest_actual_004526

def g32p_supplierForest_node_003269 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_003269 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003269 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029918 := by
  decide +kernel

theorem g32p_supplierForest_actual_003269 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003269) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 3 g32p_supplierForest_edge_003269
    g32p_supplierForest_actual_029918

def g32p_supplierForest_node_003276 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_003276 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003276 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_003158 := by
  decide +kernel

theorem g32p_supplierForest_actual_003276 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003276) ∧
        IsConj g (g32p_literalRepresentative 2) := by
  exact g32p_archive_step_lift _ _ 2 2 g32p_supplierForest_edge_003276
    g32p_supplierForest_actual_003158

def g32p_supplierForest_node_003304 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_003304 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003304 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_004519 := by
  decide +kernel

theorem g32p_supplierForest_actual_003304 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003304) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_003304
    g32p_supplierForest_actual_004519

def g32p_supplierForest_node_003331 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_003331 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003331 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_028578 := by
  decide +kernel

theorem g32p_supplierForest_actual_003331 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003331) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_003331
    g32p_supplierForest_actual_028578

def g32p_supplierForest_node_003332 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_003332 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003332 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_004683 := by
  decide +kernel

theorem g32p_supplierForest_actual_003332 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003332) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_003332
    g32p_supplierForest_actual_004683

def g32p_supplierForest_node_003344 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_003344 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003344 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_004710 := by
  decide +kernel

theorem g32p_supplierForest_actual_003344 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003344) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_003344
    g32p_supplierForest_actual_004710

def g32p_supplierForest_node_003349 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_003349 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003349 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_031464 := by
  decide +kernel

theorem g32p_supplierForest_actual_003349 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003349) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 3 g32p_supplierForest_edge_003349
    g32p_supplierForest_actual_031464

def g32p_supplierForest_node_003384 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_003384 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003384 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_033660 := by
  decide +kernel

theorem g32p_supplierForest_actual_003384 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003384) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 3 g32p_supplierForest_edge_003384
    g32p_supplierForest_actual_033660

def g32p_supplierForest_node_003501 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_003501 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003501 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_005039 := by
  decide +kernel

theorem g32p_supplierForest_actual_003501 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003501) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 0 g32p_supplierForest_edge_003501
    g32p_supplierForest_actual_005039

def g32p_supplierForest_node_003543 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_003543 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003543 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_003485 := by
  decide +kernel

theorem g32p_supplierForest_actual_003543 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003543) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_003543
    g32p_supplierForest_actual_003485

def g32p_supplierForest_node_003716 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_003716 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003716 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_005493 := by
  decide +kernel

theorem g32p_supplierForest_actual_003716 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003716) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 0 g32p_supplierForest_edge_003716
    g32p_supplierForest_actual_005493

def g32p_supplierForest_node_003727 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_003727 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003727 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_031944 := by
  decide +kernel

theorem g32p_supplierForest_actual_003727 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003727) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_003727
    g32p_supplierForest_actual_031944

def g32p_supplierForest_node_003774 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_003774 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003774 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_005337 := by
  decide +kernel

theorem g32p_supplierForest_actual_003774 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003774) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_003774
    g32p_supplierForest_actual_005337

def g32p_supplierForest_node_003818 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_003818 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003818 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_005705 := by
  decide +kernel

theorem g32p_supplierForest_actual_003818 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003818) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_003818
    g32p_supplierForest_actual_005705

def g32p_supplierForest_node_003829 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_003829 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003829 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_037218 := by
  decide +kernel

theorem g32p_supplierForest_actual_003829 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003829) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 1 g32p_supplierForest_edge_003829
    g32p_supplierForest_actual_037218

def g32p_supplierForest_node_003876 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_003876 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003876 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_002726 := by
  decide +kernel

theorem g32p_supplierForest_actual_003876 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003876) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 1 g32p_supplierForest_edge_003876
    g32p_supplierForest_actual_002726

def g32p_supplierForest_node_003887 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_003887 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003887 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_005641 := by
  decide +kernel

theorem g32p_supplierForest_actual_003887 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003887) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_003887
    g32p_supplierForest_actual_005641

def g32p_supplierForest_node_003951 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_003951 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003951 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_003947 := by
  decide +kernel

theorem g32p_supplierForest_actual_003951 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003951) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 2 g32p_supplierForest_edge_003951
    g32p_supplierForest_actual_003947

def g32p_supplierForest_node_003976 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_003976 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003976 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_003362 := by
  decide +kernel

theorem g32p_supplierForest_actual_003976 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003976) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 3 g32p_supplierForest_edge_003976
    g32p_supplierForest_actual_003362

def g32p_supplierForest_node_003981 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_003981 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003981 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003447 := by
  decide +kernel

theorem g32p_supplierForest_actual_003981 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003981) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 1 g32p_supplierForest_edge_003981
    g32p_supplierForest_actual_003447

def g32p_supplierForest_node_003992 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_003992 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003992 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003474 := by
  decide +kernel

theorem g32p_supplierForest_actual_003992 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003992) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_003992
    g32p_supplierForest_actual_003474

def g32p_supplierForest_node_003993 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_003993 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003993 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003476 := by
  decide +kernel

theorem g32p_supplierForest_actual_003993 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003993) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 1 g32p_supplierForest_edge_003993
    g32p_supplierForest_actual_003476

def g32p_supplierForest_node_003999 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_003999 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003999 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003490 := by
  decide +kernel

theorem g32p_supplierForest_actual_003999 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003999) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 1 g32p_supplierForest_edge_003999
    g32p_supplierForest_actual_003490

def g32p_supplierForest_node_004045 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_004045 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004045 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003495 := by
  decide +kernel

theorem g32p_supplierForest_actual_004045 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004045) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_004045
    g32p_supplierForest_actual_003495

def g32p_supplierForest_node_004055 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_004055 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004055 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003633 := by
  decide +kernel

theorem g32p_supplierForest_actual_004055 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004055) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 1 g32p_supplierForest_edge_004055
    g32p_supplierForest_actual_003633

def g32p_supplierForest_node_004071 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004071 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004071 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038792 := by
  decide +kernel

theorem g32p_supplierForest_actual_004071 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004071) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 2 g32p_supplierForest_edge_004071
    g32p_supplierForest_actual_038792

def g32p_supplierForest_node_004154 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_004154 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004154 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_025115 := by
  decide +kernel

theorem g32p_supplierForest_actual_004154 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004154) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_004154
    g32p_supplierForest_actual_025115

def g32p_supplierForest_node_004170 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_004170 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004170 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_004173 := by
  decide +kernel

theorem g32p_supplierForest_actual_004170 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004170) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 0 g32p_supplierForest_edge_004170
    g32p_supplierForest_actual_004173

def g32p_supplierForest_node_004187 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_004187 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004187 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_000313 := by
  decide +kernel

theorem g32p_supplierForest_actual_004187 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004187) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 1 g32p_supplierForest_edge_004187
    g32p_supplierForest_actual_000313

def g32p_supplierForest_node_004200 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_004200 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004200 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_025203 := by
  decide +kernel

theorem g32p_supplierForest_actual_004200 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004200) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_004200
    g32p_supplierForest_actual_025203

def g32p_supplierForest_node_004205 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004205 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004205 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_002617 := by
  decide +kernel

theorem g32p_supplierForest_actual_004205 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004205) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 0 g32p_supplierForest_edge_004205
    g32p_supplierForest_actual_002617

def g32p_supplierForest_node_004209 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_004209 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004209 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_003063 := by
  decide +kernel

theorem g32p_supplierForest_actual_004209 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004209) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 2 g32p_supplierForest_edge_004209
    g32p_supplierForest_actual_003063

def g32p_supplierForest_node_004220 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_004220 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004220 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_025135 := by
  decide +kernel

theorem g32p_supplierForest_actual_004220 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004220) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_004220
    g32p_supplierForest_actual_025135

def g32p_supplierForest_node_004231 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004231 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004231 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_034531 := by
  decide +kernel

theorem g32p_supplierForest_actual_004231 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004231) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_004231
    g32p_supplierForest_actual_034531

def g32p_supplierForest_node_004234 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_004234 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004234 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004173 := by
  decide +kernel

theorem g32p_supplierForest_actual_004234 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004234) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 3 g32p_supplierForest_edge_004234
    g32p_supplierForest_actual_004173

def g32p_supplierForest_node_004245 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_004245 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004245 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_004092 := by
  decide +kernel

theorem g32p_supplierForest_actual_004245 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004245) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 1 g32p_supplierForest_edge_004245
    g32p_supplierForest_actual_004092

def g32p_supplierForest_node_004273 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004273 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004273 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_002630 := by
  decide +kernel

theorem g32p_supplierForest_actual_004273 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004273) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 0 g32p_supplierForest_edge_004273
    g32p_supplierForest_actual_002630

def g32p_supplierForest_node_004282 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004282 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004282 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_002767 := by
  decide +kernel

theorem g32p_supplierForest_actual_004282 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004282) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 0 g32p_supplierForest_edge_004282
    g32p_supplierForest_actual_002767

def g32p_supplierForest_node_004342 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_004342 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004342 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000299 := by
  decide +kernel

theorem g32p_supplierForest_actual_004342 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004342) ∧
        IsConj g (g32p_literalRepresentative 2) := by
  exact g32p_archive_step_lift _ _ 2 3 g32p_supplierForest_edge_004342
    g32p_supplierForest_actual_000299

def g32p_supplierForest_node_004350 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_004350 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004350 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_004526 := by
  decide +kernel

theorem g32p_supplierForest_actual_004350 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004350) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_004350
    g32p_supplierForest_actual_004526

def g32p_supplierForest_node_004352 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004352 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004352 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_025508 := by
  decide +kernel

theorem g32p_supplierForest_actual_004352 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004352) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_004352
    g32p_supplierForest_actual_025508

def g32p_supplierForest_node_004362 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_004362 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004362 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_004651 := by
  decide +kernel

theorem g32p_supplierForest_actual_004362 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004362) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 1 g32p_supplierForest_edge_004362
    g32p_supplierForest_actual_004651

def g32p_supplierForest_node_004381 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_004381 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004381 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_004708 := by
  decide +kernel

theorem g32p_supplierForest_actual_004381 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004381) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 1 g32p_supplierForest_edge_004381
    g32p_supplierForest_actual_004708

def g32p_supplierForest_node_004398 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004398 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004398 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_025604 := by
  decide +kernel

theorem g32p_supplierForest_actual_004398 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004398) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 0 g32p_supplierForest_edge_004398
    g32p_supplierForest_actual_025604

def g32p_supplierForest_node_004443 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_004443 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004443 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004236 := by
  decide +kernel

theorem g32p_supplierForest_actual_004443 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004443) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 2 g32p_supplierForest_edge_004443
    g32p_supplierForest_actual_004236

def g32p_supplierForest_node_004446 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_004446 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004446 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004411 := by
  decide +kernel

theorem g32p_supplierForest_actual_004446 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004446) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 3 g32p_supplierForest_edge_004446
    g32p_supplierForest_actual_004411

def g32p_supplierForest_node_004451 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004451 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004451 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004422 := by
  decide +kernel

theorem g32p_supplierForest_actual_004451 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004451) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 3 g32p_supplierForest_edge_004451
    g32p_supplierForest_actual_004422

def g32p_supplierForest_node_004481 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004481 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004481 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_025372 := by
  decide +kernel

theorem g32p_supplierForest_actual_004481 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004481) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_004481
    g32p_supplierForest_actual_025372

def g32p_supplierForest_node_004527 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004527 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004527 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_025858 := by
  decide +kernel

theorem g32p_supplierForest_actual_004527 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004527) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_004527
    g32p_supplierForest_actual_025858

def g32p_supplierForest_node_004532 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_004532 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004532 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_025867 := by
  decide +kernel

theorem g32p_supplierForest_actual_004532 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004532) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_004532
    g32p_supplierForest_actual_025867

def g32p_supplierForest_node_004539 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_004539 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004539 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_005039 := by
  decide +kernel

theorem g32p_supplierForest_actual_004539 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004539) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 1 g32p_supplierForest_edge_004539
    g32p_supplierForest_actual_005039

def g32p_supplierForest_node_004569 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004569 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004569 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_005120 := by
  decide +kernel

theorem g32p_supplierForest_actual_004569 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004569) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 1 g32p_supplierForest_edge_004569
    g32p_supplierForest_actual_005120

def g32p_supplierForest_node_004584 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_004584 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004584 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_005148 := by
  decide +kernel

theorem g32p_supplierForest_actual_004584 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004584) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 1 g32p_supplierForest_edge_004584
    g32p_supplierForest_actual_005148

def g32p_supplierForest_node_004589 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004589 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004589 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_005434 := by
  decide +kernel

theorem g32p_supplierForest_actual_004589 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004589) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_004589
    g32p_supplierForest_actual_005434

def g32p_supplierForest_node_004649 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_004649 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004649 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004644 := by
  decide +kernel

theorem g32p_supplierForest_actual_004649 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004649) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_004649
    g32p_supplierForest_actual_004644

def g32p_supplierForest_node_004657 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_004657 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004657 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_026118 := by
  decide +kernel

theorem g32p_supplierForest_actual_004657 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004657) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 0 g32p_supplierForest_edge_004657
    g32p_supplierForest_actual_026118

def g32p_supplierForest_node_004674 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004674 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004674 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_005526 := by
  decide +kernel

theorem g32p_supplierForest_actual_004674 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004674) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 0 g32p_supplierForest_edge_004674
    g32p_supplierForest_actual_005526

def g32p_supplierForest_node_004679 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_004679 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004679 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_005680 := by
  decide +kernel

theorem g32p_supplierForest_actual_004679 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004679) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_004679
    g32p_supplierForest_actual_005680

def g32p_supplierForest_node_004707 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_004707 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004707 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004724 := by
  decide +kernel

theorem g32p_supplierForest_actual_004707 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004707) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 2 g32p_supplierForest_edge_004707
    g32p_supplierForest_actual_004724

def g32p_supplierForest_node_004727 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_004727 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004727 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_041731 := by
  decide +kernel

theorem g32p_supplierForest_actual_004727 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004727) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_004727
    g32p_supplierForest_actual_041731

def g32p_supplierForest_node_004760 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_004760 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004760 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000198 := by
  decide +kernel

theorem g32p_supplierForest_actual_004760 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004760) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_004760
    g32p_supplierForest_actual_000198

def g32p_supplierForest_node_004763 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_004763 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004763 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002979 := by
  decide +kernel

theorem g32p_supplierForest_actual_004763 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004763) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 3 g32p_supplierForest_edge_004763
    g32p_supplierForest_actual_002979

def g32p_supplierForest_node_004811 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_004811 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004811 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004578 := by
  decide +kernel

theorem g32p_supplierForest_actual_004811 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004811) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_004811
    g32p_supplierForest_actual_004578

def g32p_supplierForest_node_004827 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_004827 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004827 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004730 := by
  decide +kernel

theorem g32p_supplierForest_actual_004827 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004827) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_004827
    g32p_supplierForest_actual_004730

def g32p_supplierForest_node_004833 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_004833 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004833 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004747 := by
  decide +kernel

theorem g32p_supplierForest_actual_004833 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004833) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 3 g32p_supplierForest_edge_004833
    g32p_supplierForest_actual_004747

def g32p_supplierForest_node_004839 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004839 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004839 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004403 := by
  decide +kernel

theorem g32p_supplierForest_actual_004839 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004839) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_004839
    g32p_supplierForest_actual_004403

def g32p_supplierForest_node_004874 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_004874 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004874 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_031944 := by
  decide +kernel

theorem g32p_supplierForest_actual_004874 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004874) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 3 g32p_supplierForest_edge_004874
    g32p_supplierForest_actual_031944

def g32p_supplierForest_node_004890 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004890 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004890 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000281 := by
  decide +kernel

theorem g32p_supplierForest_actual_004890 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004890) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 2 g32p_supplierForest_edge_004890
    g32p_supplierForest_actual_000281

def g32p_supplierForest_node_004893 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_004893 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004893 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003430 := by
  decide +kernel

theorem g32p_supplierForest_actual_004893 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004893) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 0 g32p_supplierForest_edge_004893
    g32p_supplierForest_actual_003430

def g32p_supplierForest_node_004898 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_004898 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004898 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_033660 := by
  decide +kernel

theorem g32p_supplierForest_actual_004898 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004898) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 1 g32p_supplierForest_edge_004898
    g32p_supplierForest_actual_033660

def g32p_supplierForest_node_004922 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_004922 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004922 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004152 := by
  decide +kernel

theorem g32p_supplierForest_actual_004922 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004922) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_004922
    g32p_supplierForest_actual_004152

def g32p_supplierForest_node_005020 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_005020 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005020 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004716 := by
  decide +kernel

theorem g32p_supplierForest_actual_005020 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005020) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_005020
    g32p_supplierForest_actual_004716

def g32p_supplierForest_node_005061 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_005061 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005061 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_004306 := by
  decide +kernel

theorem g32p_supplierForest_actual_005061 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005061) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_005061
    g32p_supplierForest_actual_004306

def g32p_supplierForest_node_005071 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_005071 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005071 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004834 := by
  decide +kernel

theorem g32p_supplierForest_actual_005071 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005071) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 2 g32p_supplierForest_edge_005071
    g32p_supplierForest_actual_004834

def g32p_supplierForest_node_005150 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_005150 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005150 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_027072 := by
  decide +kernel

theorem g32p_supplierForest_actual_005150 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005150) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_005150
    g32p_supplierForest_actual_027072

def g32p_supplierForest_node_005249 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_005249 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005249 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_033157 := by
  decide +kernel

theorem g32p_supplierForest_actual_005249 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005249) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_005249
    g32p_supplierForest_actual_033157

def g32p_supplierForest_node_005269 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_005269 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005269 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_005473 := by
  decide +kernel

theorem g32p_supplierForest_actual_005269 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005269) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_005269
    g32p_supplierForest_actual_005473

def g32p_supplierForest_node_005279 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_005279 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005279 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004737 := by
  decide +kernel

theorem g32p_supplierForest_actual_005279 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005279) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_005279
    g32p_supplierForest_actual_004737

def g32p_supplierForest_node_005410 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_005410 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005410 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_027568 := by
  decide +kernel

theorem g32p_supplierForest_actual_005410 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005410) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 0 g32p_supplierForest_edge_005410
    g32p_supplierForest_actual_027568

def g32p_supplierForest_node_005545 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_005545 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005545 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_003037 := by
  decide +kernel

theorem g32p_supplierForest_actual_005545 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005545) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_005545
    g32p_supplierForest_actual_003037

def g32p_supplierForest_node_005563 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_005563 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005563 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000229 := by
  decide +kernel

theorem g32p_supplierForest_actual_005563 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005563) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 3 g32p_supplierForest_edge_005563
    g32p_supplierForest_actual_000229

def g32p_supplierForest_node_005571 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_005571 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005571 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_027393 := by
  decide +kernel

theorem g32p_supplierForest_actual_005571 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005571) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 0 g32p_supplierForest_edge_005571
    g32p_supplierForest_actual_027393

def g32p_supplierForest_node_005576 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_005576 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005576 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_003430 := by
  decide +kernel

theorem g32p_supplierForest_actual_005576 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005576) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 3 g32p_supplierForest_edge_005576
    g32p_supplierForest_actual_003430

def g32p_supplierForest_node_005577 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_005577 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005577 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_028919 := by
  decide +kernel

theorem g32p_supplierForest_actual_005577 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005577) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 2 g32p_supplierForest_edge_005577
    g32p_supplierForest_actual_028919

def g32p_supplierForest_node_005584 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_005584 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005584 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000235 := by
  decide +kernel

theorem g32p_supplierForest_actual_005584 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005584) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_005584
    g32p_supplierForest_actual_000235

def g32p_supplierForest_node_005612 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_005612 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005612 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_004463 := by
  decide +kernel

theorem g32p_supplierForest_actual_005612 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005612) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 3 g32p_supplierForest_edge_005612
    g32p_supplierForest_actual_004463

def g32p_supplierForest_node_005712 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_005712 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005712 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_003353 := by
  decide +kernel

theorem g32p_supplierForest_actual_005712 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005712) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_005712
    g32p_supplierForest_actual_003353

def g32p_supplierForest_node_005717 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_005717 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005717 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_028263 := by
  decide +kernel

theorem g32p_supplierForest_actual_005717 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005717) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_005717
    g32p_supplierForest_actual_028263

def g32p_supplierForest_node_005723 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_005723 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005723 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_028077 := by
  decide +kernel

theorem g32p_supplierForest_actual_005723 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005723) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_005723
    g32p_supplierForest_actual_028077

def g32p_supplierForest_node_005728 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_005728 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005728 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_029419 := by
  decide +kernel

theorem g32p_supplierForest_actual_005728 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005728) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_005728
    g32p_supplierForest_actual_029419

def g32p_supplierForest_node_005730 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_005730 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005730 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_030019 := by
  decide +kernel

theorem g32p_supplierForest_actual_005730 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005730) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 2 g32p_supplierForest_edge_005730
    g32p_supplierForest_actual_030019

def g32p_supplierForest_node_005765 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_005765 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005765 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_005641 := by
  decide +kernel

theorem g32p_supplierForest_actual_005765 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005765) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_005765
    g32p_supplierForest_actual_005641

def g32p_supplierForest_node_005773 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_005773 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005773 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_005794 := by
  decide +kernel

theorem g32p_supplierForest_actual_005773 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005773) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 1 g32p_supplierForest_edge_005773
    g32p_supplierForest_actual_005794

def g32p_supplierForest_node_005818 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_005818 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005818 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000513 := by
  decide +kernel

theorem g32p_supplierForest_actual_005818 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005818) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 0 g32p_supplierForest_edge_005818
    g32p_supplierForest_actual_000513

def g32p_supplierForest_node_005849 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_005849 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005849 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_007151 := by
  decide +kernel

theorem g32p_supplierForest_actual_005849 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005849) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_005849
    g32p_supplierForest_actual_007151

def g32p_supplierForest_node_005855 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_005855 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005855 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_001006 := by
  decide +kernel

theorem g32p_supplierForest_actual_005855 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005855) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 2 g32p_supplierForest_edge_005855
    g32p_supplierForest_actual_001006

def g32p_supplierForest_node_005878 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_005878 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005878 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_007215 := by
  decide +kernel

theorem g32p_supplierForest_actual_005878 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005878) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 1 g32p_supplierForest_edge_005878
    g32p_supplierForest_actual_007215

def g32p_supplierForest_node_005906 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_005906 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005906 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_006969 := by
  decide +kernel

theorem g32p_supplierForest_actual_005906 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005906) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 0 g32p_supplierForest_edge_005906
    g32p_supplierForest_actual_006969

def g32p_supplierForest_node_005921 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_005921 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005921 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000531 := by
  decide +kernel

theorem g32p_supplierForest_actual_005921 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005921) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 0 g32p_supplierForest_edge_005921
    g32p_supplierForest_actual_000531

def g32p_supplierForest_node_005980 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_005980 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005980 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_005978 := by
  decide +kernel

theorem g32p_supplierForest_actual_005980 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005980) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 1 g32p_supplierForest_edge_005980
    g32p_supplierForest_actual_005978

def g32p_supplierForest_node_006028 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_006028 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006028 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_008395 := by
  decide +kernel

theorem g32p_supplierForest_actual_006028 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006028) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 1 g32p_supplierForest_edge_006028
    g32p_supplierForest_actual_008395

def g32p_supplierForest_node_006045 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_006045 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006045 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000531 := by
  decide +kernel

theorem g32p_supplierForest_actual_006045 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006045) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 2 g32p_supplierForest_edge_006045
    g32p_supplierForest_actual_000531

def g32p_supplierForest_node_006096 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_006096 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006096 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_005978 := by
  decide +kernel

theorem g32p_supplierForest_actual_006096 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006096) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 2 g32p_supplierForest_edge_006096
    g32p_supplierForest_actual_005978

def g32p_supplierForest_node_006134 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_006134 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006134 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_006068 := by
  decide +kernel

theorem g32p_supplierForest_actual_006134 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006134) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 2 g32p_supplierForest_edge_006134
    g32p_supplierForest_actual_006068

def g32p_supplierForest_node_006144 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_006144 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006144 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000799 := by
  decide +kernel

theorem g32p_supplierForest_actual_006144 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006144) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 3 g32p_supplierForest_edge_006144
    g32p_supplierForest_actual_000799

def g32p_supplierForest_node_006155 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_006155 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006155 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_006072 := by
  decide +kernel

theorem g32p_supplierForest_actual_006155 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006155) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 2 g32p_supplierForest_edge_006155
    g32p_supplierForest_actual_006072

def g32p_supplierForest_node_006181 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_006181 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006181 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_045654 := by
  decide +kernel

theorem g32p_supplierForest_actual_006181 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006181) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 1 g32p_supplierForest_edge_006181
    g32p_supplierForest_actual_045654

def g32p_supplierForest_node_006246 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_006246 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006246 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_007074 := by
  decide +kernel

theorem g32p_supplierForest_actual_006246 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006246) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_006246
    g32p_supplierForest_actual_007074

def g32p_supplierForest_node_006308 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_006308 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006308 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_007799 := by
  decide +kernel

theorem g32p_supplierForest_actual_006308 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006308) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_006308
    g32p_supplierForest_actual_007799

def g32p_supplierForest_node_006309 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_006309 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006309 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_006163 := by
  decide +kernel

theorem g32p_supplierForest_actual_006309 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006309) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_006309
    g32p_supplierForest_actual_006163

def g32p_supplierForest_node_006421 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_006421 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006421 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000489 := by
  decide +kernel

theorem g32p_supplierForest_actual_006421 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006421) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 2 g32p_supplierForest_edge_006421
    g32p_supplierForest_actual_000489

def g32p_supplierForest_node_006433 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_006433 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006433 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000491 := by
  decide +kernel

theorem g32p_supplierForest_actual_006433 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006433) ∧
        IsConj g (g32p_literalRepresentative 18) := by
  exact g32p_archive_step_lift _ _ 18 2 g32p_supplierForest_edge_006433
    g32p_supplierForest_actual_000491

def g32p_supplierForest_node_006451 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_006451 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006451 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_008138 := by
  decide +kernel

theorem g32p_supplierForest_actual_006451 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006451) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 0 g32p_supplierForest_edge_006451
    g32p_supplierForest_actual_008138

def g32p_supplierForest_node_006486 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_006486 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006486 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_050827 := by
  decide +kernel

theorem g32p_supplierForest_actual_006486 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006486) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_006486
    g32p_supplierForest_actual_050827

def g32p_supplierForest_node_006518 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_006518 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006518 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_008275 := by
  decide +kernel

theorem g32p_supplierForest_actual_006518 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006518) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_006518
    g32p_supplierForest_actual_008275

def g32p_supplierForest_node_006547 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_006547 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006547 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000686 := by
  decide +kernel

theorem g32p_supplierForest_actual_006547 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006547) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 2 g32p_supplierForest_edge_006547
    g32p_supplierForest_actual_000686

def g32p_supplierForest_node_006577 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_006577 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006577 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_008395 := by
  decide +kernel

theorem g32p_supplierForest_actual_006577 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006577) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 0 g32p_supplierForest_edge_006577
    g32p_supplierForest_actual_008395

def g32p_supplierForest_node_006686 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_006686 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006686 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_005857 := by
  decide +kernel

theorem g32p_supplierForest_actual_006686 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006686) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_006686
    g32p_supplierForest_actual_005857

def g32p_supplierForest_node_006697 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_006697 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006697 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_005883 := by
  decide +kernel

theorem g32p_supplierForest_actual_006697 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006697) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_006697
    g32p_supplierForest_actual_005883

def g32p_supplierForest_node_006715 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_006715 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006715 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000744 := by
  decide +kernel

theorem g32p_supplierForest_actual_006715 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006715) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_006715
    g32p_supplierForest_actual_000744

def g32p_supplierForest_node_006732 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_006732 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006732 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_008725 := by
  decide +kernel

theorem g32p_supplierForest_actual_006732 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006732) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_006732
    g32p_supplierForest_actual_008725

def g32p_supplierForest_node_006735 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_006735 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006735 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000686 := by
  decide +kernel

theorem g32p_supplierForest_actual_006735 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006735) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 0 g32p_supplierForest_edge_006735
    g32p_supplierForest_actual_000686

def g32p_supplierForest_node_006771 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_006771 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006771 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_006767 := by
  decide +kernel

theorem g32p_supplierForest_actual_006771 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006771) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 2 g32p_supplierForest_edge_006771
    g32p_supplierForest_actual_006767

def g32p_supplierForest_node_006772 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_006772 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006772 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_006926 := by
  decide +kernel

theorem g32p_supplierForest_actual_006772 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006772) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 1 g32p_supplierForest_edge_006772
    g32p_supplierForest_actual_006926

def g32p_supplierForest_node_006801 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_006801 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006801 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000894 := by
  decide +kernel

theorem g32p_supplierForest_actual_006801 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006801) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 2 g32p_supplierForest_edge_006801
    g32p_supplierForest_actual_000894

def g32p_supplierForest_node_006826 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_006826 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006826 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_047998 := by
  decide +kernel

theorem g32p_supplierForest_actual_006826 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006826) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 2 g32p_supplierForest_edge_006826
    g32p_supplierForest_actual_047998

def g32p_supplierForest_node_006833 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_006833 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006833 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_006267 := by
  decide +kernel

theorem g32p_supplierForest_actual_006833 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006833) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_006833
    g32p_supplierForest_actual_006267

def g32p_supplierForest_node_006836 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_006836 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006836 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_054623 := by
  decide +kernel

theorem g32p_supplierForest_actual_006836 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006836) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 2 g32p_supplierForest_edge_006836
    g32p_supplierForest_actual_054623

def g32p_supplierForest_node_006880 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_006880 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006880 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_006562 := by
  decide +kernel

theorem g32p_supplierForest_actual_006880 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006880) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 1 g32p_supplierForest_edge_006880
    g32p_supplierForest_actual_006562

def g32p_supplierForest_node_006938 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_006938 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006938 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_009015 := by
  decide +kernel

theorem g32p_supplierForest_actual_006938 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006938) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 0 g32p_supplierForest_edge_006938
    g32p_supplierForest_actual_009015

def g32p_supplierForest_node_006964 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_006964 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006964 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_050698 := by
  decide +kernel

theorem g32p_supplierForest_actual_006964 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006964) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 3 g32p_supplierForest_edge_006964
    g32p_supplierForest_actual_050698

def g32p_supplierForest_node_006974 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_006974 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006974 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_009209 := by
  decide +kernel

theorem g32p_supplierForest_actual_006974 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006974) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_006974
    g32p_supplierForest_actual_009209

def g32p_supplierForest_node_006977 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_006977 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006977 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_005794 := by
  decide +kernel

theorem g32p_supplierForest_actual_006977 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006977) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 2 g32p_supplierForest_edge_006977
    g32p_supplierForest_actual_005794

def g32p_supplierForest_node_006983 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_006983 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006983 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000737 := by
  decide +kernel

theorem g32p_supplierForest_actual_006983 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006983) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_006983
    g32p_supplierForest_actual_000737

def g32p_supplierForest_node_006985 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_006985 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006985 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_007799 := by
  decide +kernel

theorem g32p_supplierForest_actual_006985 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006985) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_006985
    g32p_supplierForest_actual_007799

def g32p_supplierForest_node_006998 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_006998 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006998 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_009260 := by
  decide +kernel

theorem g32p_supplierForest_actual_006998 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006998) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_006998
    g32p_supplierForest_actual_009260

def g32p_supplierForest_node_007012 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_007012 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_007012 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000742 := by
  decide +kernel

theorem g32p_supplierForest_actual_007012 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_007012) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 0 g32p_supplierForest_edge_007012
    g32p_supplierForest_actual_000742

def g32p_supplierForest_node_007025 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_007025 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_007025 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_005787 := by
  decide +kernel

theorem g32p_supplierForest_actual_007025 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_007025) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_007025
    g32p_supplierForest_actual_005787

def g32p_supplierForest_node_007029 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_007029 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_007029 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_005883 := by
  decide +kernel

theorem g32p_supplierForest_actual_007029 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_007029) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_007029
    g32p_supplierForest_actual_005883

def g32p_supplierForest_node_007065 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_007065 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_007065 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_009393 := by
  decide +kernel

theorem g32p_supplierForest_actual_007065 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_007065) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_007065
    g32p_supplierForest_actual_009393

def g32p_supplierForest_node_007098 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_007098 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_007098 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000537 := by
  decide +kernel

theorem g32p_supplierForest_actual_007098 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_007098) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 3 g32p_supplierForest_edge_007098
    g32p_supplierForest_actual_000537

def g32p_supplierForest_node_007100 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_007100 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_007100 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000759 := by
  decide +kernel

theorem g32p_supplierForest_actual_007100 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_007100) ∧
        IsConj g (g32p_literalRepresentative 18) := by
  exact g32p_archive_step_lift _ _ 18 0 g32p_supplierForest_edge_007100
    g32p_supplierForest_actual_000759

def g32p_supplierForest_node_007112 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_007112 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_007112 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_007807 := by
  decide +kernel

theorem g32p_supplierForest_actual_007112 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_007112) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_007112
    g32p_supplierForest_actual_007807

def g32p_supplierForest_node_007146 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_007146 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_007146 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_051027 := by
  decide +kernel

theorem g32p_supplierForest_actual_007146 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_007146) ∧
        IsConj g (g32p_literalRepresentative 23) := by
  exact g32p_archive_step_lift _ _ 23 1 g32p_supplierForest_edge_007146
    g32p_supplierForest_actual_051027

def g32p_supplierForest_node_007186 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_007186 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_007186 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_010213 := by
  decide +kernel

theorem g32p_supplierForest_actual_007186 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_007186) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 1 g32p_supplierForest_edge_007186
    g32p_supplierForest_actual_010213

def g32p_supplierForest_node_007189 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_007189 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_007189 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_051077 := by
  decide +kernel

theorem g32p_supplierForest_actual_007189 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_007189) ∧
        IsConj g (g32p_literalRepresentative 23) := by
  exact g32p_archive_step_lift _ _ 23 1 g32p_supplierForest_edge_007189
    g32p_supplierForest_actual_051077

def g32p_supplierForest_node_007202 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_007202 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_007202 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_009662 := by
  decide +kernel

theorem g32p_supplierForest_actual_007202 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_007202) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_007202
    g32p_supplierForest_actual_009662

def g32p_supplierForest_node_007241 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_007241 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_007241 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_009624 := by
  decide +kernel

theorem g32p_supplierForest_actual_007241 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_007241) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_007241
    g32p_supplierForest_actual_009624

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_008 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_019460 else g32p_supplierForest_node_019596) else (if i.val < 3 then g32p_supplierForest_node_019719 else g32p_supplierForest_node_019747)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_019756 else g32p_supplierForest_node_019886) else (if i.val < 7 then g32p_supplierForest_node_019918 else g32p_supplierForest_node_019927))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_019932 else g32p_supplierForest_node_019936) else (if i.val < 11 then g32p_supplierForest_node_019959 else g32p_supplierForest_node_019961)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_019972 else g32p_supplierForest_node_020014) else (if i.val < 15 then g32p_supplierForest_node_020050 else g32p_supplierForest_node_020093)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_020098 else g32p_supplierForest_node_020112) else (if i.val < 19 then g32p_supplierForest_node_020130 else g32p_supplierForest_node_020169)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_020235 else g32p_supplierForest_node_020272) else (if i.val < 23 then g32p_supplierForest_node_020307 else g32p_supplierForest_node_020387))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_020460 else g32p_supplierForest_node_020541) else (if i.val < 27 then g32p_supplierForest_node_020612 else g32p_supplierForest_node_020665)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_020679 else g32p_supplierForest_node_020707) else (if i.val < 31 then g32p_supplierForest_node_020862 else g32p_supplierForest_node_020863))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_020877 else g32p_supplierForest_node_020890) else (if i.val < 35 then g32p_supplierForest_node_021061 else g32p_supplierForest_node_021063)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_021074 else g32p_supplierForest_node_021079) else (if i.val < 39 then g32p_supplierForest_node_021105 else g32p_supplierForest_node_021121))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_021122 else g32p_supplierForest_node_021127) else (if i.val < 43 then g32p_supplierForest_node_021129 else g32p_supplierForest_node_021211)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_021214 else g32p_supplierForest_node_021273) else (if i.val < 47 then g32p_supplierForest_node_021281 else g32p_supplierForest_node_021304)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_021332 else g32p_supplierForest_node_021443) else (if i.val < 51 then g32p_supplierForest_node_021450 else g32p_supplierForest_node_021509)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_021539 else g32p_supplierForest_node_021557) else (if i.val < 55 then g32p_supplierForest_node_021574 else g32p_supplierForest_node_021578))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_021626 else g32p_supplierForest_node_021659) else (if i.val < 59 then g32p_supplierForest_node_021662 else g32p_supplierForest_node_021750)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_021790 else g32p_supplierForest_node_021802) else (if i.val < 63 then g32p_supplierForest_node_021809 else g32p_supplierForest_node_021861)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_021947 else g32p_supplierForest_node_022056) else (if i.val < 67 then g32p_supplierForest_node_022061 else g32p_supplierForest_node_022063)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_022095 else g32p_supplierForest_node_022101) else (if i.val < 71 then g32p_supplierForest_node_022129 else g32p_supplierForest_node_022164))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_022166 else g32p_supplierForest_node_022192) else (if i.val < 75 then g32p_supplierForest_node_022228 else g32p_supplierForest_node_022332)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_022371 else g32p_supplierForest_node_022406) else (if i.val < 79 then g32p_supplierForest_node_022562 else g32p_supplierForest_node_022620)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_022666 else g32p_supplierForest_node_022696) else (if i.val < 83 then g32p_supplierForest_node_022744 else g32p_supplierForest_node_022883)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_022897 else g32p_supplierForest_node_022951) else (if i.val < 87 then g32p_supplierForest_node_023076 else g32p_supplierForest_node_023195))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_023288 else g32p_supplierForest_node_023407) else (if i.val < 91 then g32p_supplierForest_node_023417 else g32p_supplierForest_node_023450)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_023451 else g32p_supplierForest_node_023471) else (if i.val < 95 then g32p_supplierForest_node_023537 else g32p_supplierForest_node_023568))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_023595 else g32p_supplierForest_node_023609) else (if i.val < 99 then g32p_supplierForest_node_023637 else g32p_supplierForest_node_023694)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_023747 else g32p_supplierForest_node_023759) else (if i.val < 103 then g32p_supplierForest_node_023766 else g32p_supplierForest_node_024028))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_024039 else g32p_supplierForest_node_024053) else (if i.val < 107 then g32p_supplierForest_node_024183 else g32p_supplierForest_node_024261)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_024270 else g32p_supplierForest_node_024282) else (if i.val < 111 then g32p_supplierForest_node_024292 else g32p_supplierForest_node_024295)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_024297 else g32p_supplierForest_node_024335) else (if i.val < 115 then g32p_supplierForest_node_024466 else g32p_supplierForest_node_024492)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_024498 else g32p_supplierForest_node_024505) else (if i.val < 119 then g32p_supplierForest_node_024590 else g32p_supplierForest_node_024658))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_024754 else g32p_supplierForest_node_024815) else (if i.val < 123 then g32p_supplierForest_node_024877 else g32p_supplierForest_node_024897)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_024913 else g32p_supplierForest_node_024982) else (if i.val < 127 then g32p_supplierForest_node_025091 else g32p_supplierForest_node_025108))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_025115 else g32p_supplierForest_node_025135) else (if i.val < 131 then g32p_supplierForest_node_025166 else g32p_supplierForest_node_025186)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_025203 else g32p_supplierForest_node_025217) else (if i.val < 135 then g32p_supplierForest_node_025266 else g32p_supplierForest_node_025331))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_025372 else g32p_supplierForest_node_025428) else (if i.val < 139 then g32p_supplierForest_node_025477 else g32p_supplierForest_node_025496)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_025508 else g32p_supplierForest_node_025599) else (if i.val < 143 then g32p_supplierForest_node_025604 else g32p_supplierForest_node_025610)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_025629 else g32p_supplierForest_node_025680) else (if i.val < 147 then g32p_supplierForest_node_025694 else g32p_supplierForest_node_025725)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_025765 else g32p_supplierForest_node_025789) else (if i.val < 151 then g32p_supplierForest_node_025824 else g32p_supplierForest_node_025858))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_025867 else g32p_supplierForest_node_025894) else (if i.val < 155 then g32p_supplierForest_node_025897 else g32p_supplierForest_node_026118)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_026152 else g32p_supplierForest_node_026179) else (if i.val < 159 then g32p_supplierForest_node_026331 else g32p_supplierForest_node_026377))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_026468 else g32p_supplierForest_node_026470) else (if i.val < 163 then g32p_supplierForest_node_026559 else g32p_supplierForest_node_026617)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_026716 else g32p_supplierForest_node_026801) else (if i.val < 167 then g32p_supplierForest_node_026911 else g32p_supplierForest_node_026958))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_026988 else g32p_supplierForest_node_027003) else (if i.val < 171 then g32p_supplierForest_node_027057 else g32p_supplierForest_node_027072)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_027096 else g32p_supplierForest_node_027162) else (if i.val < 175 then g32p_supplierForest_node_027393 else g32p_supplierForest_node_027426)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_027444 else g32p_supplierForest_node_027568) else (if i.val < 179 then g32p_supplierForest_node_027577 else g32p_supplierForest_node_027604)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_027737 else g32p_supplierForest_node_027790) else (if i.val < 183 then g32p_supplierForest_node_027945 else g32p_supplierForest_node_028067))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_028074 else g32p_supplierForest_node_028077) else (if i.val < 187 then g32p_supplierForest_node_028102 else g32p_supplierForest_node_028128)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_028137 else g32p_supplierForest_node_028148) else (if i.val < 191 then g32p_supplierForest_node_028153 else g32p_supplierForest_node_028155)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_028159 else g32p_supplierForest_node_028243) else (if i.val < 195 then g32p_supplierForest_node_028263 else g32p_supplierForest_node_028338)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_028400 else g32p_supplierForest_node_028404) else (if i.val < 199 then g32p_supplierForest_node_028469 else g32p_supplierForest_node_028578))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_028616 else g32p_supplierForest_node_028723) else (if i.val < 203 then g32p_supplierForest_node_028832 else g32p_supplierForest_node_028894)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_028919 else g32p_supplierForest_node_028986) else (if i.val < 207 then g32p_supplierForest_node_029045 else g32p_supplierForest_node_029090)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_029131 else g32p_supplierForest_node_029195) else (if i.val < 211 then g32p_supplierForest_node_029287 else g32p_supplierForest_node_029365)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_029389 else g32p_supplierForest_node_029393) else (if i.val < 215 then g32p_supplierForest_node_029419 else g32p_supplierForest_node_029496))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_029510 else g32p_supplierForest_node_029586) else (if i.val < 219 then g32p_supplierForest_node_029701 else g32p_supplierForest_node_029706)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_029784 else g32p_supplierForest_node_029809) else (if i.val < 223 then g32p_supplierForest_node_029811 else g32p_supplierForest_node_029816))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_029863 else g32p_supplierForest_node_029891) else (if i.val < 227 then g32p_supplierForest_node_029918 else g32p_supplierForest_node_029941)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_029954 else g32p_supplierForest_node_030003) else (if i.val < 231 then g32p_supplierForest_node_030013 else g32p_supplierForest_node_030019))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_030206 else g32p_supplierForest_node_030250) else (if i.val < 235 then g32p_supplierForest_node_030311 else g32p_supplierForest_node_030316)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_030343 else g32p_supplierForest_node_030383) else (if i.val < 239 then g32p_supplierForest_node_030392 else g32p_supplierForest_node_030522)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_030528 else g32p_supplierForest_node_030552) else (if i.val < 243 then g32p_supplierForest_node_030584 else g32p_supplierForest_node_030596)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_030606 else g32p_supplierForest_node_030611) else (if i.val < 247 then g32p_supplierForest_node_030853 else g32p_supplierForest_node_030922))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_030927 else g32p_supplierForest_node_031006) else (if i.val < 251 then g32p_supplierForest_node_031091 else g32p_supplierForest_node_031126)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_031246 else g32p_supplierForest_node_031331) else (if i.val < 255 then g32p_supplierForest_node_031385 else g32p_supplierForest_node_031399))))))))

def g32p_supplierForest_classes_008 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 13 else 45) else (if i.val < 3 then 26 else 27)) else (if i.val < 6 then (if i.val < 5 then 27 else 26) else (if i.val < 7 then 26 else 49))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9 else 26) else (if i.val < 11 then 9 else 51)) else (if i.val < 14 then (if i.val < 13 then 11 else 47) else (if i.val < 15 then 12 else 9)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 13 else 8) else (if i.val < 19 then 27 else 12)) else (if i.val < 22 then (if i.val < 21 then 51 else 52) else (if i.val < 23 then 11 else 27))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 10 else 50) else (if i.val < 27 then 26 else 50)) else (if i.val < 30 then (if i.val < 29 then 48 else 50) else (if i.val < 31 then 48 else 47))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 48 else 13) else (if i.val < 35 then 8 else 10)) else (if i.val < 38 then (if i.val < 37 then 48 else 49) else (if i.val < 39 then 9 else 27))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 11 else 25) else (if i.val < 43 then 51 else 25)) else (if i.val < 46 then (if i.val < 45 then 46 else 47) else (if i.val < 47 then 51 else 50)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 51 else 11) else (if i.val < 51 then 49 else 11)) else (if i.val < 54 then (if i.val < 53 then 12 else 50) else (if i.val < 55 then 50 else 50))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 25 else 47) else (if i.val < 59 then 47 else 51)) else (if i.val < 62 then (if i.val < 61 then 50 else 46) else (if i.val < 63 then 47 else 8)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 27 else 48) else (if i.val < 67 then 51 else 47)) else (if i.val < 70 then (if i.val < 69 then 10 else 27) else (if i.val < 71 then 46 else 51))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 26 else 56) else (if i.val < 75 then 49 else 49)) else (if i.val < 78 then (if i.val < 77 then 25 else 1) else (if i.val < 79 then 26 else 54)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 54 else 11) else (if i.val < 83 then 12 else 27)) else (if i.val < 86 then (if i.val < 85 then 12 else 9) else (if i.val < 87 then 25 else 27))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 49 else 10) else (if i.val < 91 then 8 else 10)) else (if i.val < 94 then (if i.val < 93 then 9 else 26) else (if i.val < 95 then 13 else 51))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 27 else 55) else (if i.val < 99 then 26 else 46)) else (if i.val < 102 then (if i.val < 101 then 56 else 49) else (if i.val < 103 then 13 else 8))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 51 else 27) else (if i.val < 107 then 48 else 27)) else (if i.val < 110 then (if i.val < 109 then 10 else 27) else (if i.val < 111 then 25 else 46)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 27 else 12) else (if i.val < 115 then 49 else 46)) else (if i.val < 118 then (if i.val < 117 then 31 else 16) else (if i.val < 119 then 29 else 36))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 32 else 14) else (if i.val < 123 then 33 else 36)) else (if i.val < 126 then (if i.val < 125 then 32 else 30) else (if i.val < 127 then 34 else 15))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 16 else 17) else (if i.val < 131 then 17 else 31)) else (if i.val < 134 then (if i.val < 133 then 17 else 15) else (if i.val < 135 then 34 else 59))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 29 else 58) else (if i.val < 139 then 4 else 14)) else (if i.val < 142 then (if i.val < 141 then 16 else 57) else (if i.val < 143 then 32 else 64)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 63 else 59) else (if i.val < 147 then 3 else 30)) else (if i.val < 150 then (if i.val < 149 then 29 else 61) else (if i.val < 151 then 63 else 30))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 16 else 15) else (if i.val < 155 then 17 else 4)) else (if i.val < 158 then (if i.val < 157 then 16 else 15) else (if i.val < 159 then 31 else 58))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 57 else 65) else (if i.val < 163 then 57 else 58)) else (if i.val < 166 then (if i.val < 165 then 16 else 59) else (if i.val < 167 then 57 else 57))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 60 else 59) else (if i.val < 171 then 61 else 30)) else (if i.val < 174 then (if i.val < 173 then 57 else 36) else (if i.val < 175 then 32 else 62)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 17 else 3) else (if i.val < 179 then 33 else 15)) else (if i.val < 182 then (if i.val < 181 then 34 else 36) else (if i.val < 183 then 57 else 15))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 17 else 17) else (if i.val < 187 then 57 else 16)) else (if i.val < 190 then (if i.val < 189 then 15 else 17) else (if i.val < 191 then 34 else 33)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 14 else 16) else (if i.val < 195 then 15 else 57)) else (if i.val < 198 then (if i.val < 197 then 31 else 63) else (if i.val < 199 then 30 else 15))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 32 else 58) else (if i.val < 203 then 30 else 31)) else (if i.val < 206 then (if i.val < 205 then 32 else 36) else (if i.val < 207 then 36 else 32)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 16 else 65) else (if i.val < 211 then 59 else 29)) else (if i.val < 214 then (if i.val < 213 then 15 else 16) else (if i.val < 215 then 34 else 57))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 57 else 33) else (if i.val < 219 then 57 else 32)) else (if i.val < 222 then (if i.val < 221 then 35 else 32) else (if i.val < 223 then 34 else 61))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 62 else 36) else (if i.val < 227 then 31 else 32)) else (if i.val < 230 then (if i.val < 229 then 29 else 33) else (if i.val < 231 then 33 else 14))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 17 else 30) else (if i.val < 235 then 63 else 63)) else (if i.val < 238 then (if i.val < 237 then 61 else 34) else (if i.val < 239 then 33 else 36)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 63 else 58) else (if i.val < 243 then 31 else 58)) else (if i.val < 246 then (if i.val < 245 then 59 else 58) else (if i.val < 247 then 60 else 61))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 36 else 15) else (if i.val < 251 then 17 else 36)) else (if i.val < 254 then (if i.val < 253 then 58 else 63) else (if i.val < 255 then 57 else 59))))))))

theorem g32p_supplierForest_actual_008 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_008 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_008 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_019460
  · exact g32p_supplierForest_actual_019596
  · exact g32p_supplierForest_actual_019719
  · exact g32p_supplierForest_actual_019747
  · exact g32p_supplierForest_actual_019756
  · exact g32p_supplierForest_actual_019886
  · exact g32p_supplierForest_actual_019918
  · exact g32p_supplierForest_actual_019927
  · exact g32p_supplierForest_actual_019932
  · exact g32p_supplierForest_actual_019936
  · exact g32p_supplierForest_actual_019959
  · exact g32p_supplierForest_actual_019961
  · exact g32p_supplierForest_actual_019972
  · exact g32p_supplierForest_actual_020014
  · exact g32p_supplierForest_actual_020050
  · exact g32p_supplierForest_actual_020093
  · exact g32p_supplierForest_actual_020098
  · exact g32p_supplierForest_actual_020112
  · exact g32p_supplierForest_actual_020130
  · exact g32p_supplierForest_actual_020169
  · exact g32p_supplierForest_actual_020235
  · exact g32p_supplierForest_actual_020272
  · exact g32p_supplierForest_actual_020307
  · exact g32p_supplierForest_actual_020387
  · exact g32p_supplierForest_actual_020460
  · exact g32p_supplierForest_actual_020541
  · exact g32p_supplierForest_actual_020612
  · exact g32p_supplierForest_actual_020665
  · exact g32p_supplierForest_actual_020679
  · exact g32p_supplierForest_actual_020707
  · exact g32p_supplierForest_actual_020862
  · exact g32p_supplierForest_actual_020863
  · exact g32p_supplierForest_actual_020877
  · exact g32p_supplierForest_actual_020890
  · exact g32p_supplierForest_actual_021061
  · exact g32p_supplierForest_actual_021063
  · exact g32p_supplierForest_actual_021074
  · exact g32p_supplierForest_actual_021079
  · exact g32p_supplierForest_actual_021105
  · exact g32p_supplierForest_actual_021121
  · exact g32p_supplierForest_actual_021122
  · exact g32p_supplierForest_actual_021127
  · exact g32p_supplierForest_actual_021129
  · exact g32p_supplierForest_actual_021211
  · exact g32p_supplierForest_actual_021214
  · exact g32p_supplierForest_actual_021273
  · exact g32p_supplierForest_actual_021281
  · exact g32p_supplierForest_actual_021304
  · exact g32p_supplierForest_actual_021332
  · exact g32p_supplierForest_actual_021443
  · exact g32p_supplierForest_actual_021450
  · exact g32p_supplierForest_actual_021509
  · exact g32p_supplierForest_actual_021539
  · exact g32p_supplierForest_actual_021557
  · exact g32p_supplierForest_actual_021574
  · exact g32p_supplierForest_actual_021578
  · exact g32p_supplierForest_actual_021626
  · exact g32p_supplierForest_actual_021659
  · exact g32p_supplierForest_actual_021662
  · exact g32p_supplierForest_actual_021750
  · exact g32p_supplierForest_actual_021790
  · exact g32p_supplierForest_actual_021802
  · exact g32p_supplierForest_actual_021809
  · exact g32p_supplierForest_actual_021861
  · exact g32p_supplierForest_actual_021947
  · exact g32p_supplierForest_actual_022056
  · exact g32p_supplierForest_actual_022061
  · exact g32p_supplierForest_actual_022063
  · exact g32p_supplierForest_actual_022095
  · exact g32p_supplierForest_actual_022101
  · exact g32p_supplierForest_actual_022129
  · exact g32p_supplierForest_actual_022164
  · exact g32p_supplierForest_actual_022166
  · exact g32p_supplierForest_actual_022192
  · exact g32p_supplierForest_actual_022228
  · exact g32p_supplierForest_actual_022332
  · exact g32p_supplierForest_actual_022371
  · exact g32p_supplierForest_actual_022406
  · exact g32p_supplierForest_actual_022562
  · exact g32p_supplierForest_actual_022620
  · exact g32p_supplierForest_actual_022666
  · exact g32p_supplierForest_actual_022696
  · exact g32p_supplierForest_actual_022744
  · exact g32p_supplierForest_actual_022883
  · exact g32p_supplierForest_actual_022897
  · exact g32p_supplierForest_actual_022951
  · exact g32p_supplierForest_actual_023076
  · exact g32p_supplierForest_actual_023195
  · exact g32p_supplierForest_actual_023288
  · exact g32p_supplierForest_actual_023407
  · exact g32p_supplierForest_actual_023417
  · exact g32p_supplierForest_actual_023450
  · exact g32p_supplierForest_actual_023451
  · exact g32p_supplierForest_actual_023471
  · exact g32p_supplierForest_actual_023537
  · exact g32p_supplierForest_actual_023568
  · exact g32p_supplierForest_actual_023595
  · exact g32p_supplierForest_actual_023609
  · exact g32p_supplierForest_actual_023637
  · exact g32p_supplierForest_actual_023694
  · exact g32p_supplierForest_actual_023747
  · exact g32p_supplierForest_actual_023759
  · exact g32p_supplierForest_actual_023766
  · exact g32p_supplierForest_actual_024028
  · exact g32p_supplierForest_actual_024039
  · exact g32p_supplierForest_actual_024053
  · exact g32p_supplierForest_actual_024183
  · exact g32p_supplierForest_actual_024261
  · exact g32p_supplierForest_actual_024270
  · exact g32p_supplierForest_actual_024282
  · exact g32p_supplierForest_actual_024292
  · exact g32p_supplierForest_actual_024295
  · exact g32p_supplierForest_actual_024297
  · exact g32p_supplierForest_actual_024335
  · exact g32p_supplierForest_actual_024466
  · exact g32p_supplierForest_actual_024492
  · exact g32p_supplierForest_actual_024498
  · exact g32p_supplierForest_actual_024505
  · exact g32p_supplierForest_actual_024590
  · exact g32p_supplierForest_actual_024658
  · exact g32p_supplierForest_actual_024754
  · exact g32p_supplierForest_actual_024815
  · exact g32p_supplierForest_actual_024877
  · exact g32p_supplierForest_actual_024897
  · exact g32p_supplierForest_actual_024913
  · exact g32p_supplierForest_actual_024982
  · exact g32p_supplierForest_actual_025091
  · exact g32p_supplierForest_actual_025108
  · exact g32p_supplierForest_actual_025115
  · exact g32p_supplierForest_actual_025135
  · exact g32p_supplierForest_actual_025166
  · exact g32p_supplierForest_actual_025186
  · exact g32p_supplierForest_actual_025203
  · exact g32p_supplierForest_actual_025217
  · exact g32p_supplierForest_actual_025266
  · exact g32p_supplierForest_actual_025331
  · exact g32p_supplierForest_actual_025372
  · exact g32p_supplierForest_actual_025428
  · exact g32p_supplierForest_actual_025477
  · exact g32p_supplierForest_actual_025496
  · exact g32p_supplierForest_actual_025508
  · exact g32p_supplierForest_actual_025599
  · exact g32p_supplierForest_actual_025604
  · exact g32p_supplierForest_actual_025610
  · exact g32p_supplierForest_actual_025629
  · exact g32p_supplierForest_actual_025680
  · exact g32p_supplierForest_actual_025694
  · exact g32p_supplierForest_actual_025725
  · exact g32p_supplierForest_actual_025765
  · exact g32p_supplierForest_actual_025789
  · exact g32p_supplierForest_actual_025824
  · exact g32p_supplierForest_actual_025858
  · exact g32p_supplierForest_actual_025867
  · exact g32p_supplierForest_actual_025894
  · exact g32p_supplierForest_actual_025897
  · exact g32p_supplierForest_actual_026118
  · exact g32p_supplierForest_actual_026152
  · exact g32p_supplierForest_actual_026179
  · exact g32p_supplierForest_actual_026331
  · exact g32p_supplierForest_actual_026377
  · exact g32p_supplierForest_actual_026468
  · exact g32p_supplierForest_actual_026470
  · exact g32p_supplierForest_actual_026559
  · exact g32p_supplierForest_actual_026617
  · exact g32p_supplierForest_actual_026716
  · exact g32p_supplierForest_actual_026801
  · exact g32p_supplierForest_actual_026911
  · exact g32p_supplierForest_actual_026958
  · exact g32p_supplierForest_actual_026988
  · exact g32p_supplierForest_actual_027003
  · exact g32p_supplierForest_actual_027057
  · exact g32p_supplierForest_actual_027072
  · exact g32p_supplierForest_actual_027096
  · exact g32p_supplierForest_actual_027162
  · exact g32p_supplierForest_actual_027393
  · exact g32p_supplierForest_actual_027426
  · exact g32p_supplierForest_actual_027444
  · exact g32p_supplierForest_actual_027568
  · exact g32p_supplierForest_actual_027577
  · exact g32p_supplierForest_actual_027604
  · exact g32p_supplierForest_actual_027737
  · exact g32p_supplierForest_actual_027790
  · exact g32p_supplierForest_actual_027945
  · exact g32p_supplierForest_actual_028067
  · exact g32p_supplierForest_actual_028074
  · exact g32p_supplierForest_actual_028077
  · exact g32p_supplierForest_actual_028102
  · exact g32p_supplierForest_actual_028128
  · exact g32p_supplierForest_actual_028137
  · exact g32p_supplierForest_actual_028148
  · exact g32p_supplierForest_actual_028153
  · exact g32p_supplierForest_actual_028155
  · exact g32p_supplierForest_actual_028159
  · exact g32p_supplierForest_actual_028243
  · exact g32p_supplierForest_actual_028263
  · exact g32p_supplierForest_actual_028338
  · exact g32p_supplierForest_actual_028400
  · exact g32p_supplierForest_actual_028404
  · exact g32p_supplierForest_actual_028469
  · exact g32p_supplierForest_actual_028578
  · exact g32p_supplierForest_actual_028616
  · exact g32p_supplierForest_actual_028723
  · exact g32p_supplierForest_actual_028832
  · exact g32p_supplierForest_actual_028894
  · exact g32p_supplierForest_actual_028919
  · exact g32p_supplierForest_actual_028986
  · exact g32p_supplierForest_actual_029045
  · exact g32p_supplierForest_actual_029090
  · exact g32p_supplierForest_actual_029131
  · exact g32p_supplierForest_actual_029195
  · exact g32p_supplierForest_actual_029287
  · exact g32p_supplierForest_actual_029365
  · exact g32p_supplierForest_actual_029389
  · exact g32p_supplierForest_actual_029393
  · exact g32p_supplierForest_actual_029419
  · exact g32p_supplierForest_actual_029496
  · exact g32p_supplierForest_actual_029510
  · exact g32p_supplierForest_actual_029586
  · exact g32p_supplierForest_actual_029701
  · exact g32p_supplierForest_actual_029706
  · exact g32p_supplierForest_actual_029784
  · exact g32p_supplierForest_actual_029809
  · exact g32p_supplierForest_actual_029811
  · exact g32p_supplierForest_actual_029816
  · exact g32p_supplierForest_actual_029863
  · exact g32p_supplierForest_actual_029891
  · exact g32p_supplierForest_actual_029918
  · exact g32p_supplierForest_actual_029941
  · exact g32p_supplierForest_actual_029954
  · exact g32p_supplierForest_actual_030003
  · exact g32p_supplierForest_actual_030013
  · exact g32p_supplierForest_actual_030019
  · exact g32p_supplierForest_actual_030206
  · exact g32p_supplierForest_actual_030250
  · exact g32p_supplierForest_actual_030311
  · exact g32p_supplierForest_actual_030316
  · exact g32p_supplierForest_actual_030343
  · exact g32p_supplierForest_actual_030383
  · exact g32p_supplierForest_actual_030392
  · exact g32p_supplierForest_actual_030522
  · exact g32p_supplierForest_actual_030528
  · exact g32p_supplierForest_actual_030552
  · exact g32p_supplierForest_actual_030584
  · exact g32p_supplierForest_actual_030596
  · exact g32p_supplierForest_actual_030606
  · exact g32p_supplierForest_actual_030611
  · exact g32p_supplierForest_actual_030853
  · exact g32p_supplierForest_actual_030922
  · exact g32p_supplierForest_actual_030927
  · exact g32p_supplierForest_actual_031006
  · exact g32p_supplierForest_actual_031091
  · exact g32p_supplierForest_actual_031126
  · exact g32p_supplierForest_actual_031246
  · exact g32p_supplierForest_actual_031331
  · exact g32p_supplierForest_actual_031385
  · exact g32p_supplierForest_actual_031399

def g32p_supplierForest_nodes_009 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_031422 else g32p_supplierForest_node_031425) else (if i.val < 3 then g32p_supplierForest_node_031432 else g32p_supplierForest_node_031464)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_031487 else g32p_supplierForest_node_031494) else (if i.val < 7 then g32p_supplierForest_node_031642 else g32p_supplierForest_node_031715))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_031767 else g32p_supplierForest_node_031770) else (if i.val < 11 then g32p_supplierForest_node_031775 else g32p_supplierForest_node_031874)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_031879 else g32p_supplierForest_node_031895) else (if i.val < 15 then g32p_supplierForest_node_031905 else g32p_supplierForest_node_031944)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_031969 else g32p_supplierForest_node_032008) else (if i.val < 19 then g32p_supplierForest_node_032045 else g32p_supplierForest_node_032085)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_032151 else g32p_supplierForest_node_032295) else (if i.val < 23 then g32p_supplierForest_node_032314 else g32p_supplierForest_node_032316))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_032331 else g32p_supplierForest_node_032337) else (if i.val < 27 then g32p_supplierForest_node_032347 else g32p_supplierForest_node_032433)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_032559 else g32p_supplierForest_node_032585) else (if i.val < 31 then g32p_supplierForest_node_032606 else g32p_supplierForest_node_032622))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_032781 else g32p_supplierForest_node_032807) else (if i.val < 35 then g32p_supplierForest_node_033157 else g32p_supplierForest_node_033301)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_033479 else g32p_supplierForest_node_033660) else (if i.val < 39 then g32p_supplierForest_node_033668 else g32p_supplierForest_node_033741))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_033826 else g32p_supplierForest_node_033840) else (if i.val < 43 then g32p_supplierForest_node_033872 else g32p_supplierForest_node_033930)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_033962 else g32p_supplierForest_node_033977) else (if i.val < 47 then g32p_supplierForest_node_034490 else g32p_supplierForest_node_034531)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_034562 else g32p_supplierForest_node_034569) else (if i.val < 51 then g32p_supplierForest_node_034570 else g32p_supplierForest_node_034719)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_034772 else g32p_supplierForest_node_034789) else (if i.val < 55 then g32p_supplierForest_node_034792 else g32p_supplierForest_node_034797))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_034814 else g32p_supplierForest_node_034839) else (if i.val < 59 then g32p_supplierForest_node_034869 else g32p_supplierForest_node_034881)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_034936 else g32p_supplierForest_node_034962) else (if i.val < 63 then g32p_supplierForest_node_034982 else g32p_supplierForest_node_035004)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_035126 else g32p_supplierForest_node_035142) else (if i.val < 67 then g32p_supplierForest_node_035319 else g32p_supplierForest_node_035368)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_035490 else g32p_supplierForest_node_035507) else (if i.val < 71 then g32p_supplierForest_node_035528 else g32p_supplierForest_node_035529))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_035551 else g32p_supplierForest_node_035595) else (if i.val < 75 then g32p_supplierForest_node_035643 else g32p_supplierForest_node_035850)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_035868 else g32p_supplierForest_node_035952) else (if i.val < 79 then g32p_supplierForest_node_035968 else g32p_supplierForest_node_035973)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_036162 else g32p_supplierForest_node_036459) else (if i.val < 83 then g32p_supplierForest_node_036461 else g32p_supplierForest_node_036528)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_036539 else g32p_supplierForest_node_036627) else (if i.val < 87 then g32p_supplierForest_node_036633 else g32p_supplierForest_node_036664))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_036863 else g32p_supplierForest_node_037113) else (if i.val < 91 then g32p_supplierForest_node_037209 else g32p_supplierForest_node_037210)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_037214 else g32p_supplierForest_node_037218) else (if i.val < 95 then g32p_supplierForest_node_037231 else g32p_supplierForest_node_037424))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_037503 else g32p_supplierForest_node_037535) else (if i.val < 99 then g32p_supplierForest_node_037552 else g32p_supplierForest_node_037560)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_037608 else g32p_supplierForest_node_037626) else (if i.val < 103 then g32p_supplierForest_node_037665 else g32p_supplierForest_node_037791))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_037794 else g32p_supplierForest_node_037803) else (if i.val < 107 then g32p_supplierForest_node_037817 else g32p_supplierForest_node_037824)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_037852 else g32p_supplierForest_node_037983) else (if i.val < 111 then g32p_supplierForest_node_038031 else g32p_supplierForest_node_038076)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_038150 else g32p_supplierForest_node_038189) else (if i.val < 115 then g32p_supplierForest_node_038191 else g32p_supplierForest_node_038306)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_038309 else g32p_supplierForest_node_038409) else (if i.val < 119 then g32p_supplierForest_node_038564 else g32p_supplierForest_node_038578))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_038669 else g32p_supplierForest_node_038792) else (if i.val < 123 then g32p_supplierForest_node_038983 else g32p_supplierForest_node_039105)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_039110 else g32p_supplierForest_node_039153) else (if i.val < 127 then g32p_supplierForest_node_039223 else g32p_supplierForest_node_039414))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_039504 else g32p_supplierForest_node_039519) else (if i.val < 131 then g32p_supplierForest_node_039529 else g32p_supplierForest_node_039605)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_039618 else g32p_supplierForest_node_039632) else (if i.val < 135 then g32p_supplierForest_node_039752 else g32p_supplierForest_node_039836))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_040097 else g32p_supplierForest_node_040177) else (if i.val < 139 then g32p_supplierForest_node_040368 else g32p_supplierForest_node_040399)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_040413 else g32p_supplierForest_node_040434) else (if i.val < 143 then g32p_supplierForest_node_040460 else g32p_supplierForest_node_040650)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_040720 else g32p_supplierForest_node_040823) else (if i.val < 147 then g32p_supplierForest_node_041003 else g32p_supplierForest_node_041045)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_041124 else g32p_supplierForest_node_041173) else (if i.val < 151 then g32p_supplierForest_node_041222 else g32p_supplierForest_node_041416))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_041421 else g32p_supplierForest_node_041471) else (if i.val < 155 then g32p_supplierForest_node_041490 else g32p_supplierForest_node_041521)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_041533 else g32p_supplierForest_node_041535) else (if i.val < 159 then g32p_supplierForest_node_041563 else g32p_supplierForest_node_041617))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_041716 else g32p_supplierForest_node_041718) else (if i.val < 163 then g32p_supplierForest_node_041731 else g32p_supplierForest_node_041830)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_041878 else g32p_supplierForest_node_042045) else (if i.val < 167 then g32p_supplierForest_node_042097 else g32p_supplierForest_node_042107))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_042163 else g32p_supplierForest_node_042228) else (if i.val < 171 then g32p_supplierForest_node_042242 else g32p_supplierForest_node_042245)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_042248 else g32p_supplierForest_node_042401) else (if i.val < 175 then g32p_supplierForest_node_042405 else g32p_supplierForest_node_042694)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_042731 else g32p_supplierForest_node_042759) else (if i.val < 179 then g32p_supplierForest_node_042892 else g32p_supplierForest_node_042910)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_042951 else g32p_supplierForest_node_042953) else (if i.val < 183 then g32p_supplierForest_node_042974 else g32p_supplierForest_node_042978))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_043010 else g32p_supplierForest_node_043026) else (if i.val < 187 then g32p_supplierForest_node_043136 else g32p_supplierForest_node_043155)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_043156 else g32p_supplierForest_node_043181) else (if i.val < 191 then g32p_supplierForest_node_043328 else g32p_supplierForest_node_043604)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_043617 else g32p_supplierForest_node_043667) else (if i.val < 195 then g32p_supplierForest_node_043777 else g32p_supplierForest_node_043787)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_043799 else g32p_supplierForest_node_043810) else (if i.val < 199 then g32p_supplierForest_node_043857 else g32p_supplierForest_node_043931))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_044100 else g32p_supplierForest_node_044111) else (if i.val < 203 then g32p_supplierForest_node_044118 else g32p_supplierForest_node_044152)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_044156 else g32p_supplierForest_node_044160) else (if i.val < 207 then g32p_supplierForest_node_044182 else g32p_supplierForest_node_044824)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_045022 else g32p_supplierForest_node_045025) else (if i.val < 211 then g32p_supplierForest_node_045190 else g32p_supplierForest_node_045202)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_045251 else g32p_supplierForest_node_045255) else (if i.val < 215 then g32p_supplierForest_node_045307 else g32p_supplierForest_node_045330))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_045410 else g32p_supplierForest_node_045411) else (if i.val < 219 then g32p_supplierForest_node_045452 else g32p_supplierForest_node_045558)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_045594 else g32p_supplierForest_node_045613) else (if i.val < 223 then g32p_supplierForest_node_045615 else g32p_supplierForest_node_045625))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_045653 else g32p_supplierForest_node_045654) else (if i.val < 227 then g32p_supplierForest_node_045673 else g32p_supplierForest_node_045718)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_045726 else g32p_supplierForest_node_045772) else (if i.val < 231 then g32p_supplierForest_node_045816 else g32p_supplierForest_node_045826))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_045828 else g32p_supplierForest_node_045837) else (if i.val < 235 then g32p_supplierForest_node_045873 else g32p_supplierForest_node_045948)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_045965 else g32p_supplierForest_node_045966) else (if i.val < 239 then g32p_supplierForest_node_046007 else g32p_supplierForest_node_046013)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_046108 else g32p_supplierForest_node_046176) else (if i.val < 243 then g32p_supplierForest_node_046224 else g32p_supplierForest_node_046443)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_046472 else g32p_supplierForest_node_046573) else (if i.val < 247 then g32p_supplierForest_node_046581 else g32p_supplierForest_node_046600))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_046707 else g32p_supplierForest_node_046718) else (if i.val < 251 then g32p_supplierForest_node_046792 else g32p_supplierForest_node_046815)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_046908 else g32p_supplierForest_node_046976) else (if i.val < 255 then g32p_supplierForest_node_047038 else g32p_supplierForest_node_047111))))))))

def g32p_supplierForest_classes_009 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 66 else 60) else (if i.val < 3 then 62 else 32)) else (if i.val < 6 then (if i.val < 5 then 57 else 31) else (if i.val < 7 then 62 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 57 else 60) else (if i.val < 11 then 62 else 34)) else (if i.val < 14 then (if i.val < 13 then 14 else 30) else (if i.val < 15 then 59 else 17)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 64 else 63) else (if i.val < 19 then 65 else 16)) else (if i.val < 22 then (if i.val < 21 then 63 else 64) else (if i.val < 23 then 64 else 57))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 63 else 65) else (if i.val < 27 then 63 else 35)) else (if i.val < 30 then (if i.val < 29 then 64 else 57) else (if i.val < 31 then 58 else 57))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 33 else 34) else (if i.val < 35 then 17 else 36)) else (if i.val < 38 then (if i.val < 37 then 32 else 31) else (if i.val < 39 then 14 else 36))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 14 else 16) else (if i.val < 43 then 15 else 30)) else (if i.val < 46 then (if i.val < 45 then 62 else 32) else (if i.val < 47 then 15 else 34)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 35 else 34) else (if i.val < 51 then 32 else 60)) else (if i.val < 54 then (if i.val < 53 then 57 else 16) else (if i.val < 55 then 16 else 57))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 60 else 58) else (if i.val < 59 then 14 else 59)) else (if i.val < 62 then (if i.val < 61 then 57 else 57) else (if i.val < 63 then 57 else 57)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 59 else 66) else (if i.val < 67 then 4 else 2)) else (if i.val < 70 then (if i.val < 69 then 34 else 35) else (if i.val < 71 then 17 else 31))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 16 else 16) else (if i.val < 75 then 57 else 32)) else (if i.val < 78 then (if i.val < 77 then 36 else 63) else (if i.val < 79 then 63 else 36)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 64 else 58) else (if i.val < 83 then 17 else 36)) else (if i.val < 86 then (if i.val < 85 then 62 else 63) else (if i.val < 87 then 34 else 33))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 63 else 61) else (if i.val < 91 then 35 else 59)) else (if i.val < 94 then (if i.val < 93 then 30 else 34) else (if i.val < 95 then 60 else 58))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 33 else 34) else (if i.val < 99 then 34 else 31)) else (if i.val < 102 then (if i.val < 101 then 33 else 16) else (if i.val < 103 then 36 else 14))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 33 else 59) else (if i.val < 107 then 60 else 17)) else (if i.val < 110 then (if i.val < 109 then 15 else 63) else (if i.val < 111 then 64 else 16)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 59 else 57) else (if i.val < 115 then 60 else 64)) else (if i.val < 118 then (if i.val < 117 then 34 else 61) else (if i.val < 119 then 16 else 34))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 16 else 4) else (if i.val < 123 then 58 else 64)) else (if i.val < 126 then (if i.val < 125 then 30 else 65) else (if i.val < 127 then 30 else 58))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 17 else 63) else (if i.val < 131 then 58 else 64)) else (if i.val < 134 then (if i.val < 133 then 65 else 63) else (if i.val < 135 then 29 else 65))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 58 else 57) else (if i.val < 139 then 30 else 61)) else (if i.val < 142 then (if i.val < 141 then 57 else 57) else (if i.val < 143 then 36 else 57)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 34 else 32) else (if i.val < 147 then 30 else 63)) else (if i.val < 150 then (if i.val < 149 then 58 else 63) else (if i.val < 151 then 66 else 32))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 59 else 30) else (if i.val < 155 then 35 else 34)) else (if i.val < 158 then (if i.val < 157 then 32 else 32) else (if i.val < 159 then 2 else 15))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 35 else 32) else (if i.val < 163 then 34 else 33)) else (if i.val < 166 then (if i.val < 165 then 35 else 34) else (if i.val < 167 then 33 else 33))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 33 else 30) else (if i.val < 171 then 64 else 34)) else (if i.val < 174 then (if i.val < 173 then 14 else 36) else (if i.val < 175 then 16 else 34)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 57 else 36) else (if i.val < 179 then 34 else 14)) else (if i.val < 182 then (if i.val < 181 then 17 else 36) else (if i.val < 183 then 34 else 35))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 59 else 59) else (if i.val < 187 then 66 else 30)) else (if i.val < 190 then (if i.val < 189 then 29 else 33) else (if i.val < 191 then 30 else 62)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 63 else 32) else (if i.val < 195 then 14 else 63)) else (if i.val < 198 then (if i.val < 197 then 62 else 64) else (if i.val < 199 then 36 else 57))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 29 else 34) else (if i.val < 203 then 33 else 30)) else (if i.val < 206 then (if i.val < 205 then 29 else 34) else (if i.val < 207 then 29 else 40)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 21 else 41) else (if i.val < 211 then 40 else 21)) else (if i.val < 214 then (if i.val < 213 then 21 else 19) else (if i.val < 215 then 41 else 38))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 22 else 69) else (if i.val < 219 then 20 else 39)) else (if i.val < 222 then (if i.val < 221 then 23 else 22) else (if i.val < 223 then 19 else 22))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 70 else 19) else (if i.val < 227 then 24 else 18)) else (if i.val < 230 then (if i.val < 229 then 72 else 24) else (if i.val < 231 then 38 else 22))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 24 else 22) else (if i.val < 235 then 72 else 24)) else (if i.val < 238 then (if i.val < 237 then 71 else 70) else (if i.val < 239 then 38 else 38)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 39 else 39) else (if i.val < 243 then 6 else 18)) else (if i.val < 246 then (if i.val < 245 then 41 else 20) else (if i.val < 247 then 70 else 71))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 38 else 40) else (if i.val < 251 then 74 else 68)) else (if i.val < 254 then (if i.val < 253 then 69 else 24) else (if i.val < 255 then 38 else 21))))))))

theorem g32p_supplierForest_actual_009 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_009 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_009 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_031422
  · exact g32p_supplierForest_actual_031425
  · exact g32p_supplierForest_actual_031432
  · exact g32p_supplierForest_actual_031464
  · exact g32p_supplierForest_actual_031487
  · exact g32p_supplierForest_actual_031494
  · exact g32p_supplierForest_actual_031642
  · exact g32p_supplierForest_actual_031715
  · exact g32p_supplierForest_actual_031767
  · exact g32p_supplierForest_actual_031770
  · exact g32p_supplierForest_actual_031775
  · exact g32p_supplierForest_actual_031874
  · exact g32p_supplierForest_actual_031879
  · exact g32p_supplierForest_actual_031895
  · exact g32p_supplierForest_actual_031905
  · exact g32p_supplierForest_actual_031944
  · exact g32p_supplierForest_actual_031969
  · exact g32p_supplierForest_actual_032008
  · exact g32p_supplierForest_actual_032045
  · exact g32p_supplierForest_actual_032085
  · exact g32p_supplierForest_actual_032151
  · exact g32p_supplierForest_actual_032295
  · exact g32p_supplierForest_actual_032314
  · exact g32p_supplierForest_actual_032316
  · exact g32p_supplierForest_actual_032331
  · exact g32p_supplierForest_actual_032337
  · exact g32p_supplierForest_actual_032347
  · exact g32p_supplierForest_actual_032433
  · exact g32p_supplierForest_actual_032559
  · exact g32p_supplierForest_actual_032585
  · exact g32p_supplierForest_actual_032606
  · exact g32p_supplierForest_actual_032622
  · exact g32p_supplierForest_actual_032781
  · exact g32p_supplierForest_actual_032807
  · exact g32p_supplierForest_actual_033157
  · exact g32p_supplierForest_actual_033301
  · exact g32p_supplierForest_actual_033479
  · exact g32p_supplierForest_actual_033660
  · exact g32p_supplierForest_actual_033668
  · exact g32p_supplierForest_actual_033741
  · exact g32p_supplierForest_actual_033826
  · exact g32p_supplierForest_actual_033840
  · exact g32p_supplierForest_actual_033872
  · exact g32p_supplierForest_actual_033930
  · exact g32p_supplierForest_actual_033962
  · exact g32p_supplierForest_actual_033977
  · exact g32p_supplierForest_actual_034490
  · exact g32p_supplierForest_actual_034531
  · exact g32p_supplierForest_actual_034562
  · exact g32p_supplierForest_actual_034569
  · exact g32p_supplierForest_actual_034570
  · exact g32p_supplierForest_actual_034719
  · exact g32p_supplierForest_actual_034772
  · exact g32p_supplierForest_actual_034789
  · exact g32p_supplierForest_actual_034792
  · exact g32p_supplierForest_actual_034797
  · exact g32p_supplierForest_actual_034814
  · exact g32p_supplierForest_actual_034839
  · exact g32p_supplierForest_actual_034869
  · exact g32p_supplierForest_actual_034881
  · exact g32p_supplierForest_actual_034936
  · exact g32p_supplierForest_actual_034962
  · exact g32p_supplierForest_actual_034982
  · exact g32p_supplierForest_actual_035004
  · exact g32p_supplierForest_actual_035126
  · exact g32p_supplierForest_actual_035142
  · exact g32p_supplierForest_actual_035319
  · exact g32p_supplierForest_actual_035368
  · exact g32p_supplierForest_actual_035490
  · exact g32p_supplierForest_actual_035507
  · exact g32p_supplierForest_actual_035528
  · exact g32p_supplierForest_actual_035529
  · exact g32p_supplierForest_actual_035551
  · exact g32p_supplierForest_actual_035595
  · exact g32p_supplierForest_actual_035643
  · exact g32p_supplierForest_actual_035850
  · exact g32p_supplierForest_actual_035868
  · exact g32p_supplierForest_actual_035952
  · exact g32p_supplierForest_actual_035968
  · exact g32p_supplierForest_actual_035973
  · exact g32p_supplierForest_actual_036162
  · exact g32p_supplierForest_actual_036459
  · exact g32p_supplierForest_actual_036461
  · exact g32p_supplierForest_actual_036528
  · exact g32p_supplierForest_actual_036539
  · exact g32p_supplierForest_actual_036627
  · exact g32p_supplierForest_actual_036633
  · exact g32p_supplierForest_actual_036664
  · exact g32p_supplierForest_actual_036863
  · exact g32p_supplierForest_actual_037113
  · exact g32p_supplierForest_actual_037209
  · exact g32p_supplierForest_actual_037210
  · exact g32p_supplierForest_actual_037214
  · exact g32p_supplierForest_actual_037218
  · exact g32p_supplierForest_actual_037231
  · exact g32p_supplierForest_actual_037424
  · exact g32p_supplierForest_actual_037503
  · exact g32p_supplierForest_actual_037535
  · exact g32p_supplierForest_actual_037552
  · exact g32p_supplierForest_actual_037560
  · exact g32p_supplierForest_actual_037608
  · exact g32p_supplierForest_actual_037626
  · exact g32p_supplierForest_actual_037665
  · exact g32p_supplierForest_actual_037791
  · exact g32p_supplierForest_actual_037794
  · exact g32p_supplierForest_actual_037803
  · exact g32p_supplierForest_actual_037817
  · exact g32p_supplierForest_actual_037824
  · exact g32p_supplierForest_actual_037852
  · exact g32p_supplierForest_actual_037983
  · exact g32p_supplierForest_actual_038031
  · exact g32p_supplierForest_actual_038076
  · exact g32p_supplierForest_actual_038150
  · exact g32p_supplierForest_actual_038189
  · exact g32p_supplierForest_actual_038191
  · exact g32p_supplierForest_actual_038306
  · exact g32p_supplierForest_actual_038309
  · exact g32p_supplierForest_actual_038409
  · exact g32p_supplierForest_actual_038564
  · exact g32p_supplierForest_actual_038578
  · exact g32p_supplierForest_actual_038669
  · exact g32p_supplierForest_actual_038792
  · exact g32p_supplierForest_actual_038983
  · exact g32p_supplierForest_actual_039105
  · exact g32p_supplierForest_actual_039110
  · exact g32p_supplierForest_actual_039153
  · exact g32p_supplierForest_actual_039223
  · exact g32p_supplierForest_actual_039414
  · exact g32p_supplierForest_actual_039504
  · exact g32p_supplierForest_actual_039519
  · exact g32p_supplierForest_actual_039529
  · exact g32p_supplierForest_actual_039605
  · exact g32p_supplierForest_actual_039618
  · exact g32p_supplierForest_actual_039632
  · exact g32p_supplierForest_actual_039752
  · exact g32p_supplierForest_actual_039836
  · exact g32p_supplierForest_actual_040097
  · exact g32p_supplierForest_actual_040177
  · exact g32p_supplierForest_actual_040368
  · exact g32p_supplierForest_actual_040399
  · exact g32p_supplierForest_actual_040413
  · exact g32p_supplierForest_actual_040434
  · exact g32p_supplierForest_actual_040460
  · exact g32p_supplierForest_actual_040650
  · exact g32p_supplierForest_actual_040720
  · exact g32p_supplierForest_actual_040823
  · exact g32p_supplierForest_actual_041003
  · exact g32p_supplierForest_actual_041045
  · exact g32p_supplierForest_actual_041124
  · exact g32p_supplierForest_actual_041173
  · exact g32p_supplierForest_actual_041222
  · exact g32p_supplierForest_actual_041416
  · exact g32p_supplierForest_actual_041421
  · exact g32p_supplierForest_actual_041471
  · exact g32p_supplierForest_actual_041490
  · exact g32p_supplierForest_actual_041521
  · exact g32p_supplierForest_actual_041533
  · exact g32p_supplierForest_actual_041535
  · exact g32p_supplierForest_actual_041563
  · exact g32p_supplierForest_actual_041617
  · exact g32p_supplierForest_actual_041716
  · exact g32p_supplierForest_actual_041718
  · exact g32p_supplierForest_actual_041731
  · exact g32p_supplierForest_actual_041830
  · exact g32p_supplierForest_actual_041878
  · exact g32p_supplierForest_actual_042045
  · exact g32p_supplierForest_actual_042097
  · exact g32p_supplierForest_actual_042107
  · exact g32p_supplierForest_actual_042163
  · exact g32p_supplierForest_actual_042228
  · exact g32p_supplierForest_actual_042242
  · exact g32p_supplierForest_actual_042245
  · exact g32p_supplierForest_actual_042248
  · exact g32p_supplierForest_actual_042401
  · exact g32p_supplierForest_actual_042405
  · exact g32p_supplierForest_actual_042694
  · exact g32p_supplierForest_actual_042731
  · exact g32p_supplierForest_actual_042759
  · exact g32p_supplierForest_actual_042892
  · exact g32p_supplierForest_actual_042910
  · exact g32p_supplierForest_actual_042951
  · exact g32p_supplierForest_actual_042953
  · exact g32p_supplierForest_actual_042974
  · exact g32p_supplierForest_actual_042978
  · exact g32p_supplierForest_actual_043010
  · exact g32p_supplierForest_actual_043026
  · exact g32p_supplierForest_actual_043136
  · exact g32p_supplierForest_actual_043155
  · exact g32p_supplierForest_actual_043156
  · exact g32p_supplierForest_actual_043181
  · exact g32p_supplierForest_actual_043328
  · exact g32p_supplierForest_actual_043604
  · exact g32p_supplierForest_actual_043617
  · exact g32p_supplierForest_actual_043667
  · exact g32p_supplierForest_actual_043777
  · exact g32p_supplierForest_actual_043787
  · exact g32p_supplierForest_actual_043799
  · exact g32p_supplierForest_actual_043810
  · exact g32p_supplierForest_actual_043857
  · exact g32p_supplierForest_actual_043931
  · exact g32p_supplierForest_actual_044100
  · exact g32p_supplierForest_actual_044111
  · exact g32p_supplierForest_actual_044118
  · exact g32p_supplierForest_actual_044152
  · exact g32p_supplierForest_actual_044156
  · exact g32p_supplierForest_actual_044160
  · exact g32p_supplierForest_actual_044182
  · exact g32p_supplierForest_actual_044824
  · exact g32p_supplierForest_actual_045022
  · exact g32p_supplierForest_actual_045025
  · exact g32p_supplierForest_actual_045190
  · exact g32p_supplierForest_actual_045202
  · exact g32p_supplierForest_actual_045251
  · exact g32p_supplierForest_actual_045255
  · exact g32p_supplierForest_actual_045307
  · exact g32p_supplierForest_actual_045330
  · exact g32p_supplierForest_actual_045410
  · exact g32p_supplierForest_actual_045411
  · exact g32p_supplierForest_actual_045452
  · exact g32p_supplierForest_actual_045558
  · exact g32p_supplierForest_actual_045594
  · exact g32p_supplierForest_actual_045613
  · exact g32p_supplierForest_actual_045615
  · exact g32p_supplierForest_actual_045625
  · exact g32p_supplierForest_actual_045653
  · exact g32p_supplierForest_actual_045654
  · exact g32p_supplierForest_actual_045673
  · exact g32p_supplierForest_actual_045718
  · exact g32p_supplierForest_actual_045726
  · exact g32p_supplierForest_actual_045772
  · exact g32p_supplierForest_actual_045816
  · exact g32p_supplierForest_actual_045826
  · exact g32p_supplierForest_actual_045828
  · exact g32p_supplierForest_actual_045837
  · exact g32p_supplierForest_actual_045873
  · exact g32p_supplierForest_actual_045948
  · exact g32p_supplierForest_actual_045965
  · exact g32p_supplierForest_actual_045966
  · exact g32p_supplierForest_actual_046007
  · exact g32p_supplierForest_actual_046013
  · exact g32p_supplierForest_actual_046108
  · exact g32p_supplierForest_actual_046176
  · exact g32p_supplierForest_actual_046224
  · exact g32p_supplierForest_actual_046443
  · exact g32p_supplierForest_actual_046472
  · exact g32p_supplierForest_actual_046573
  · exact g32p_supplierForest_actual_046581
  · exact g32p_supplierForest_actual_046600
  · exact g32p_supplierForest_actual_046707
  · exact g32p_supplierForest_actual_046718
  · exact g32p_supplierForest_actual_046792
  · exact g32p_supplierForest_actual_046815
  · exact g32p_supplierForest_actual_046908
  · exact g32p_supplierForest_actual_046976
  · exact g32p_supplierForest_actual_047038
  · exact g32p_supplierForest_actual_047111

def g32p_supplierForest_nodes_010 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_047205 else g32p_supplierForest_node_047211) else (if i.val < 3 then g32p_supplierForest_node_047368 else g32p_supplierForest_node_047437)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_047442 else g32p_supplierForest_node_047932) else (if i.val < 7 then g32p_supplierForest_node_047998 else g32p_supplierForest_node_048134))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_048275 else g32p_supplierForest_node_048353) else (if i.val < 11 then g32p_supplierForest_node_048416 else g32p_supplierForest_node_048447)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_048463 else g32p_supplierForest_node_048731) else (if i.val < 15 then g32p_supplierForest_node_048771 else g32p_supplierForest_node_048898)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_048919 else g32p_supplierForest_node_048922) else (if i.val < 19 then g32p_supplierForest_node_048950 else g32p_supplierForest_node_048973)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_049063 else g32p_supplierForest_node_049073) else (if i.val < 23 then g32p_supplierForest_node_049372 else g32p_supplierForest_node_049536))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_049703 else g32p_supplierForest_node_049744) else (if i.val < 27 then g32p_supplierForest_node_049755 else g32p_supplierForest_node_049766)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_049867 else g32p_supplierForest_node_049902) else (if i.val < 31 then g32p_supplierForest_node_049920 else g32p_supplierForest_node_050167))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_050180 else g32p_supplierForest_node_050412) else (if i.val < 35 then g32p_supplierForest_node_050674 else g32p_supplierForest_node_050698)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_050767 else g32p_supplierForest_node_050784) else (if i.val < 39 then g32p_supplierForest_node_050820 else g32p_supplierForest_node_050827))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_050850 else g32p_supplierForest_node_050885) else (if i.val < 43 then g32p_supplierForest_node_050947 else g32p_supplierForest_node_050950)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_050979 else g32p_supplierForest_node_051027) else (if i.val < 47 then g32p_supplierForest_node_051077 else g32p_supplierForest_node_051199)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_051213 else g32p_supplierForest_node_051229) else (if i.val < 51 then g32p_supplierForest_node_051301 else g32p_supplierForest_node_051320)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_051350 else g32p_supplierForest_node_051611) else (if i.val < 55 then g32p_supplierForest_node_051849 else g32p_supplierForest_node_051885))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_051938 else g32p_supplierForest_node_052142) else (if i.val < 59 then g32p_supplierForest_node_052202 else g32p_supplierForest_node_052243)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_052331 else g32p_supplierForest_node_052339) else (if i.val < 63 then g32p_supplierForest_node_052347 else g32p_supplierForest_node_052594)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_052633 else g32p_supplierForest_node_052652) else (if i.val < 67 then g32p_supplierForest_node_052798 else g32p_supplierForest_node_052804)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_052848 else g32p_supplierForest_node_053072) else (if i.val < 71 then g32p_supplierForest_node_053084 else g32p_supplierForest_node_053113))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_053123 else g32p_supplierForest_node_053269) else (if i.val < 75 then g32p_supplierForest_node_053272 else g32p_supplierForest_node_053315)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_053317 else g32p_supplierForest_node_053405) else (if i.val < 79 then g32p_supplierForest_node_053444 else g32p_supplierForest_node_053448)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_053460 else g32p_supplierForest_node_053549) else (if i.val < 83 then g32p_supplierForest_node_053668 else g32p_supplierForest_node_053785)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_053791 else g32p_supplierForest_node_053799) else (if i.val < 87 then g32p_supplierForest_node_053827 else g32p_supplierForest_node_054034))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_054039 else g32p_supplierForest_node_054066) else (if i.val < 91 then g32p_supplierForest_node_054113 else g32p_supplierForest_node_054180)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_054202 else g32p_supplierForest_node_054230) else (if i.val < 95 then g32p_supplierForest_node_054261 else g32p_supplierForest_node_054320))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_054342 else g32p_supplierForest_node_054564) else (if i.val < 99 then g32p_supplierForest_node_054606 else g32p_supplierForest_node_054612)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_054623 else g32p_supplierForest_node_054637) else (if i.val < 103 then g32p_supplierForest_node_054738 else g32p_supplierForest_node_054808))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_054854 else g32p_supplierForest_node_054917) else (if i.val < 107 then g32p_supplierForest_node_054966 else g32p_supplierForest_node_055036)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_055052 else g32p_supplierForest_node_055146) else (if i.val < 111 then g32p_supplierForest_node_055163 else g32p_supplierForest_node_055165)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_055166 else g32p_supplierForest_node_055270) else (if i.val < 115 then g32p_supplierForest_node_055279 else g32p_supplierForest_node_055328)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_055410 else g32p_supplierForest_node_055676) else (if i.val < 119 then g32p_supplierForest_node_055771 else g32p_supplierForest_node_055777))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_055791 else g32p_supplierForest_node_055797) else (if i.val < 123 then g32p_supplierForest_node_055811 else g32p_supplierForest_node_055859)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_055942 else g32p_supplierForest_node_056029) else (if i.val < 127 then g32p_supplierForest_node_056035 else g32p_supplierForest_node_056145))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_056308 else g32p_supplierForest_node_056386) else (if i.val < 131 then g32p_supplierForest_node_056391 else g32p_supplierForest_node_056561)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_056575 else g32p_supplierForest_node_056612) else (if i.val < 135 then g32p_supplierForest_node_056619 else g32p_supplierForest_node_056742))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_056747 else g32p_supplierForest_node_056758) else (if i.val < 139 then g32p_supplierForest_node_056893 else g32p_supplierForest_node_056934)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_057013 else g32p_supplierForest_node_057073) else (if i.val < 143 then g32p_supplierForest_node_057202 else g32p_supplierForest_node_057247)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_057333 else g32p_supplierForest_node_057368) else (if i.val < 147 then g32p_supplierForest_node_057414 else g32p_supplierForest_node_057804)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_058024 else g32p_supplierForest_node_058289) else (if i.val < 151 then g32p_supplierForest_node_058358 else g32p_supplierForest_node_058536))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_058556 else g32p_supplierForest_node_058703) else (if i.val < 155 then g32p_supplierForest_node_058807 else g32p_supplierForest_node_058884)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_059102 else g32p_supplierForest_node_059315) else (if i.val < 159 then g32p_supplierForest_node_059496 else g32p_supplierForest_node_059497))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_059546 else g32p_supplierForest_node_059564) else (if i.val < 163 then g32p_supplierForest_node_059648 else g32p_supplierForest_node_059739)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_059825 else g32p_supplierForest_node_059966) else (if i.val < 167 then g32p_supplierForest_node_060005 else g32p_supplierForest_node_060007))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_060047 else g32p_supplierForest_node_060071) else (if i.val < 171 then g32p_supplierForest_node_060375 else g32p_supplierForest_node_060376)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_060543 else g32p_supplierForest_node_060617) else (if i.val < 175 then g32p_supplierForest_node_060639 else g32p_supplierForest_node_060677)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_060712 else g32p_supplierForest_node_060722) else (if i.val < 179 then g32p_supplierForest_node_060788 else g32p_supplierForest_node_060904)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_060921 else g32p_supplierForest_node_060925) else (if i.val < 183 then g32p_supplierForest_node_060941 else g32p_supplierForest_node_061131))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_061195 else g32p_supplierForest_node_061210) else (if i.val < 187 then g32p_supplierForest_node_061290 else g32p_supplierForest_node_061338)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_061344 else g32p_supplierForest_node_061411) else (if i.val < 191 then g32p_supplierForest_node_061461 else g32p_supplierForest_node_061477)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_061859 else g32p_supplierForest_node_061868) else (if i.val < 195 then g32p_supplierForest_node_061877 else g32p_supplierForest_node_061880)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_061926 else g32p_supplierForest_node_062046) else (if i.val < 199 then g32p_supplierForest_node_062274 else g32p_supplierForest_node_062385))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_062409 else g32p_supplierForest_node_062449) else (if i.val < 203 then g32p_supplierForest_node_062458 else g32p_supplierForest_node_062479)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_062611 else g32p_supplierForest_node_062654) else (if i.val < 207 then g32p_supplierForest_node_063034 else g32p_supplierForest_node_063045)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_063061 else g32p_supplierForest_node_063099) else (if i.val < 211 then g32p_supplierForest_node_063339 else g32p_supplierForest_node_063364)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_063428 else g32p_supplierForest_node_063432) else (if i.val < 215 then g32p_supplierForest_node_063601 else g32p_supplierForest_node_063622))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_063656 else g32p_supplierForest_node_063728) else (if i.val < 219 then g32p_supplierForest_node_063810 else g32p_supplierForest_node_063872)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_063975 else g32p_supplierForest_node_064121) else (if i.val < 223 then g32p_supplierForest_node_064125 else g32p_supplierForest_node_064136))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_064139 else g32p_supplierForest_node_064147) else (if i.val < 227 then g32p_supplierForest_node_064328 else g32p_supplierForest_node_064364)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_064415 else g32p_supplierForest_node_064422) else (if i.val < 231 then g32p_supplierForest_node_064443 else g32p_supplierForest_node_064456))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_064505 else g32p_supplierForest_node_064530) else (if i.val < 235 then g32p_supplierForest_node_064586 else g32p_supplierForest_node_064657)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_064710 else g32p_supplierForest_node_064757) else (if i.val < 239 then g32p_supplierForest_node_064890 else g32p_supplierForest_node_064915)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_064927 else g32p_supplierForest_node_065055) else (if i.val < 243 then g32p_supplierForest_node_065078 else g32p_supplierForest_node_065098)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_065101 else g32p_supplierForest_node_065128) else (if i.val < 247 then g32p_supplierForest_node_065198 else g32p_supplierForest_node_065581))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_065632 else g32p_supplierForest_node_065652) else (if i.val < 251 then g32p_supplierForest_node_065842 else g32p_supplierForest_node_065972)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_066086 else g32p_supplierForest_node_066116) else (if i.val < 255 then g32p_supplierForest_node_066418 else g32p_supplierForest_node_066489))))))))

def g32p_supplierForest_classes_010 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 18 else 69) else (if i.val < 3 then 6 else 24)) else (if i.val < 6 then (if i.val < 5 then 5 else 70) else (if i.val < 7 then 39 else 19))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 24) else (if i.val < 11 then 21 else 23)) else (if i.val < 14 then (if i.val < 13 then 72 else 42) else (if i.val < 15 then 39 else 70)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 22 else 71) else (if i.val < 19 then 22 else 70)) else (if i.val < 22 then (if i.val < 21 then 73 else 74) else (if i.val < 23 then 40 else 40))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 21 else 24) else (if i.val < 27 then 7 else 42)) else (if i.val < 30 then (if i.val < 29 then 20 else 42) else (if i.val < 31 then 23 else 39))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 68 else 41) else (if i.val < 35 then 20 else 19)) else (if i.val < 38 then (if i.val < 37 then 24 else 23) else (if i.val < 39 then 20 else 21))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 24 else 23) else (if i.val < 43 then 39 else 18)) else (if i.val < 46 then (if i.val < 45 then 39 else 23) else (if i.val < 47 then 23 else 42)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 43 else 40) else (if i.val < 51 then 67 else 70)) else (if i.val < 54 then (if i.val < 53 then 69 else 41) else (if i.val < 55 then 21 else 40))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 74 else 68) else (if i.val < 59 then 40 else 69)) else (if i.val < 62 then (if i.val < 61 then 41 else 43) else (if i.val < 63 then 40 else 69)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 43 else 70) else (if i.val < 67 then 70 else 72)) else (if i.val < 70 then (if i.val < 69 then 23 else 70) else (if i.val < 71 then 38 else 72))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 40 else 43) else (if i.val < 75 then 41 else 22)) else (if i.val < 78 then (if i.val < 77 then 40 else 43) else (if i.val < 79 then 43 else 41)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 74 else 68) else (if i.val < 83 then 72 else 18)) else (if i.val < 86 then (if i.val < 85 then 69 else 20) else (if i.val < 87 then 22 else 67))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 72 else 24) else (if i.val < 91 then 38 else 40)) else (if i.val < 94 then (if i.val < 93 then 75 else 74) else (if i.val < 95 then 74 else 21))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 70 else 41) else (if i.val < 99 then 70 else 70)) else (if i.val < 102 then (if i.val < 101 then 39 else 38) else (if i.val < 103 then 40 else 42))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 44 else 70) else (if i.val < 107 then 75 else 71)) else (if i.val < 110 then (if i.val < 109 then 72 else 73) else (if i.val < 111 then 68 else 74)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 74 else 24) else (if i.val < 115 then 23 else 42)) else (if i.val < 118 then (if i.val < 117 then 70 else 21) else (if i.val < 119 then 79 else 79))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 44 else 67) else (if i.val < 123 then 70 else 71)) else (if i.val < 126 then (if i.val < 125 then 41 else 74) else (if i.val < 127 then 68 else 68))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 69 else 70) else (if i.val < 131 then 71 else 38)) else (if i.val < 134 then (if i.val < 133 then 69 else 22) else (if i.val < 135 then 71 else 74))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 69 else 69) else (if i.val < 139 then 43 else 75)) else (if i.val < 142 then (if i.val < 141 then 75 else 21) else (if i.val < 143 then 41 else 69)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 74 else 75) else (if i.val < 147 then 78 else 38)) else (if i.val < 150 then (if i.val < 149 then 39 else 20) else (if i.val < 151 then 22 else 75))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 41 else 43) else (if i.val < 155 then 75 else 20)) else (if i.val < 158 then (if i.val < 157 then 20 else 21) else (if i.val < 159 then 38 else 72))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 41 else 69) else (if i.val < 163 then 43 else 40)) else (if i.val < 166 then (if i.val < 165 then 69 else 75) else (if i.val < 167 then 69 else 43))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 38 else 73) else (if i.val < 171 then 41 else 43)) else (if i.val < 174 then (if i.val < 173 then 74 else 74) else (if i.val < 175 then 70 else 7)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 21 else 72) else (if i.val < 179 then 70 else 43)) else (if i.val < 182 then (if i.val < 181 then 20 else 71) else (if i.val < 183 then 71 else 70))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 70 else 68) else (if i.val < 187 then 78 else 69)) else (if i.val < 190 then (if i.val < 189 then 18 else 43) else (if i.val < 191 then 5 else 6)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 74 else 73) else (if i.val < 195 then 67 else 67)) else (if i.val < 198 then (if i.val < 197 then 74 else 72) else (if i.val < 199 then 75 else 79))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 69 else 41) else (if i.val < 203 then 42 else 72)) else (if i.val < 206 then (if i.val < 205 then 74 else 73) else (if i.val < 207 then 41 else 70)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 21 else 23) else (if i.val < 211 then 73 else 79)) else (if i.val < 214 then (if i.val < 213 then 69 else 18) else (if i.val < 215 then 41 else 69))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 77 else 71) else (if i.val < 219 then 68 else 38)) else (if i.val < 222 then (if i.val < 221 then 68 else 20) else (if i.val < 223 then 22 else 22))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 20 else 39) else (if i.val < 227 then 38 else 38)) else (if i.val < 230 then (if i.val < 229 then 38 else 20) else (if i.val < 231 then 71 else 42))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 73 else 75) else (if i.val < 235 then 39 else 74)) else (if i.val < 238 then (if i.val < 237 then 68 else 38) else (if i.val < 239 then 71 else 24)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 42 else 43) else (if i.val < 243 then 43 else 69)) else (if i.val < 246 then (if i.val < 245 then 38 else 21) else (if i.val < 247 then 74 else 75))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 38 else 6) else (if i.val < 251 then 43 else 42)) else (if i.val < 254 then (if i.val < 253 then 72 else 69) else (if i.val < 255 then 20 else 43))))))))

theorem g32p_supplierForest_actual_010 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_010 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_010 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_047205
  · exact g32p_supplierForest_actual_047211
  · exact g32p_supplierForest_actual_047368
  · exact g32p_supplierForest_actual_047437
  · exact g32p_supplierForest_actual_047442
  · exact g32p_supplierForest_actual_047932
  · exact g32p_supplierForest_actual_047998
  · exact g32p_supplierForest_actual_048134
  · exact g32p_supplierForest_actual_048275
  · exact g32p_supplierForest_actual_048353
  · exact g32p_supplierForest_actual_048416
  · exact g32p_supplierForest_actual_048447
  · exact g32p_supplierForest_actual_048463
  · exact g32p_supplierForest_actual_048731
  · exact g32p_supplierForest_actual_048771
  · exact g32p_supplierForest_actual_048898
  · exact g32p_supplierForest_actual_048919
  · exact g32p_supplierForest_actual_048922
  · exact g32p_supplierForest_actual_048950
  · exact g32p_supplierForest_actual_048973
  · exact g32p_supplierForest_actual_049063
  · exact g32p_supplierForest_actual_049073
  · exact g32p_supplierForest_actual_049372
  · exact g32p_supplierForest_actual_049536
  · exact g32p_supplierForest_actual_049703
  · exact g32p_supplierForest_actual_049744
  · exact g32p_supplierForest_actual_049755
  · exact g32p_supplierForest_actual_049766
  · exact g32p_supplierForest_actual_049867
  · exact g32p_supplierForest_actual_049902
  · exact g32p_supplierForest_actual_049920
  · exact g32p_supplierForest_actual_050167
  · exact g32p_supplierForest_actual_050180
  · exact g32p_supplierForest_actual_050412
  · exact g32p_supplierForest_actual_050674
  · exact g32p_supplierForest_actual_050698
  · exact g32p_supplierForest_actual_050767
  · exact g32p_supplierForest_actual_050784
  · exact g32p_supplierForest_actual_050820
  · exact g32p_supplierForest_actual_050827
  · exact g32p_supplierForest_actual_050850
  · exact g32p_supplierForest_actual_050885
  · exact g32p_supplierForest_actual_050947
  · exact g32p_supplierForest_actual_050950
  · exact g32p_supplierForest_actual_050979
  · exact g32p_supplierForest_actual_051027
  · exact g32p_supplierForest_actual_051077
  · exact g32p_supplierForest_actual_051199
  · exact g32p_supplierForest_actual_051213
  · exact g32p_supplierForest_actual_051229
  · exact g32p_supplierForest_actual_051301
  · exact g32p_supplierForest_actual_051320
  · exact g32p_supplierForest_actual_051350
  · exact g32p_supplierForest_actual_051611
  · exact g32p_supplierForest_actual_051849
  · exact g32p_supplierForest_actual_051885
  · exact g32p_supplierForest_actual_051938
  · exact g32p_supplierForest_actual_052142
  · exact g32p_supplierForest_actual_052202
  · exact g32p_supplierForest_actual_052243
  · exact g32p_supplierForest_actual_052331
  · exact g32p_supplierForest_actual_052339
  · exact g32p_supplierForest_actual_052347
  · exact g32p_supplierForest_actual_052594
  · exact g32p_supplierForest_actual_052633
  · exact g32p_supplierForest_actual_052652
  · exact g32p_supplierForest_actual_052798
  · exact g32p_supplierForest_actual_052804
  · exact g32p_supplierForest_actual_052848
  · exact g32p_supplierForest_actual_053072
  · exact g32p_supplierForest_actual_053084
  · exact g32p_supplierForest_actual_053113
  · exact g32p_supplierForest_actual_053123
  · exact g32p_supplierForest_actual_053269
  · exact g32p_supplierForest_actual_053272
  · exact g32p_supplierForest_actual_053315
  · exact g32p_supplierForest_actual_053317
  · exact g32p_supplierForest_actual_053405
  · exact g32p_supplierForest_actual_053444
  · exact g32p_supplierForest_actual_053448
  · exact g32p_supplierForest_actual_053460
  · exact g32p_supplierForest_actual_053549
  · exact g32p_supplierForest_actual_053668
  · exact g32p_supplierForest_actual_053785
  · exact g32p_supplierForest_actual_053791
  · exact g32p_supplierForest_actual_053799
  · exact g32p_supplierForest_actual_053827
  · exact g32p_supplierForest_actual_054034
  · exact g32p_supplierForest_actual_054039
  · exact g32p_supplierForest_actual_054066
  · exact g32p_supplierForest_actual_054113
  · exact g32p_supplierForest_actual_054180
  · exact g32p_supplierForest_actual_054202
  · exact g32p_supplierForest_actual_054230
  · exact g32p_supplierForest_actual_054261
  · exact g32p_supplierForest_actual_054320
  · exact g32p_supplierForest_actual_054342
  · exact g32p_supplierForest_actual_054564
  · exact g32p_supplierForest_actual_054606
  · exact g32p_supplierForest_actual_054612
  · exact g32p_supplierForest_actual_054623
  · exact g32p_supplierForest_actual_054637
  · exact g32p_supplierForest_actual_054738
  · exact g32p_supplierForest_actual_054808
  · exact g32p_supplierForest_actual_054854
  · exact g32p_supplierForest_actual_054917
  · exact g32p_supplierForest_actual_054966
  · exact g32p_supplierForest_actual_055036
  · exact g32p_supplierForest_actual_055052
  · exact g32p_supplierForest_actual_055146
  · exact g32p_supplierForest_actual_055163
  · exact g32p_supplierForest_actual_055165
  · exact g32p_supplierForest_actual_055166
  · exact g32p_supplierForest_actual_055270
  · exact g32p_supplierForest_actual_055279
  · exact g32p_supplierForest_actual_055328
  · exact g32p_supplierForest_actual_055410
  · exact g32p_supplierForest_actual_055676
  · exact g32p_supplierForest_actual_055771
  · exact g32p_supplierForest_actual_055777
  · exact g32p_supplierForest_actual_055791
  · exact g32p_supplierForest_actual_055797
  · exact g32p_supplierForest_actual_055811
  · exact g32p_supplierForest_actual_055859
  · exact g32p_supplierForest_actual_055942
  · exact g32p_supplierForest_actual_056029
  · exact g32p_supplierForest_actual_056035
  · exact g32p_supplierForest_actual_056145
  · exact g32p_supplierForest_actual_056308
  · exact g32p_supplierForest_actual_056386
  · exact g32p_supplierForest_actual_056391
  · exact g32p_supplierForest_actual_056561
  · exact g32p_supplierForest_actual_056575
  · exact g32p_supplierForest_actual_056612
  · exact g32p_supplierForest_actual_056619
  · exact g32p_supplierForest_actual_056742
  · exact g32p_supplierForest_actual_056747
  · exact g32p_supplierForest_actual_056758
  · exact g32p_supplierForest_actual_056893
  · exact g32p_supplierForest_actual_056934
  · exact g32p_supplierForest_actual_057013
  · exact g32p_supplierForest_actual_057073
  · exact g32p_supplierForest_actual_057202
  · exact g32p_supplierForest_actual_057247
  · exact g32p_supplierForest_actual_057333
  · exact g32p_supplierForest_actual_057368
  · exact g32p_supplierForest_actual_057414
  · exact g32p_supplierForest_actual_057804
  · exact g32p_supplierForest_actual_058024
  · exact g32p_supplierForest_actual_058289
  · exact g32p_supplierForest_actual_058358
  · exact g32p_supplierForest_actual_058536
  · exact g32p_supplierForest_actual_058556
  · exact g32p_supplierForest_actual_058703
  · exact g32p_supplierForest_actual_058807
  · exact g32p_supplierForest_actual_058884
  · exact g32p_supplierForest_actual_059102
  · exact g32p_supplierForest_actual_059315
  · exact g32p_supplierForest_actual_059496
  · exact g32p_supplierForest_actual_059497
  · exact g32p_supplierForest_actual_059546
  · exact g32p_supplierForest_actual_059564
  · exact g32p_supplierForest_actual_059648
  · exact g32p_supplierForest_actual_059739
  · exact g32p_supplierForest_actual_059825
  · exact g32p_supplierForest_actual_059966
  · exact g32p_supplierForest_actual_060005
  · exact g32p_supplierForest_actual_060007
  · exact g32p_supplierForest_actual_060047
  · exact g32p_supplierForest_actual_060071
  · exact g32p_supplierForest_actual_060375
  · exact g32p_supplierForest_actual_060376
  · exact g32p_supplierForest_actual_060543
  · exact g32p_supplierForest_actual_060617
  · exact g32p_supplierForest_actual_060639
  · exact g32p_supplierForest_actual_060677
  · exact g32p_supplierForest_actual_060712
  · exact g32p_supplierForest_actual_060722
  · exact g32p_supplierForest_actual_060788
  · exact g32p_supplierForest_actual_060904
  · exact g32p_supplierForest_actual_060921
  · exact g32p_supplierForest_actual_060925
  · exact g32p_supplierForest_actual_060941
  · exact g32p_supplierForest_actual_061131
  · exact g32p_supplierForest_actual_061195
  · exact g32p_supplierForest_actual_061210
  · exact g32p_supplierForest_actual_061290
  · exact g32p_supplierForest_actual_061338
  · exact g32p_supplierForest_actual_061344
  · exact g32p_supplierForest_actual_061411
  · exact g32p_supplierForest_actual_061461
  · exact g32p_supplierForest_actual_061477
  · exact g32p_supplierForest_actual_061859
  · exact g32p_supplierForest_actual_061868
  · exact g32p_supplierForest_actual_061877
  · exact g32p_supplierForest_actual_061880
  · exact g32p_supplierForest_actual_061926
  · exact g32p_supplierForest_actual_062046
  · exact g32p_supplierForest_actual_062274
  · exact g32p_supplierForest_actual_062385
  · exact g32p_supplierForest_actual_062409
  · exact g32p_supplierForest_actual_062449
  · exact g32p_supplierForest_actual_062458
  · exact g32p_supplierForest_actual_062479
  · exact g32p_supplierForest_actual_062611
  · exact g32p_supplierForest_actual_062654
  · exact g32p_supplierForest_actual_063034
  · exact g32p_supplierForest_actual_063045
  · exact g32p_supplierForest_actual_063061
  · exact g32p_supplierForest_actual_063099
  · exact g32p_supplierForest_actual_063339
  · exact g32p_supplierForest_actual_063364
  · exact g32p_supplierForest_actual_063428
  · exact g32p_supplierForest_actual_063432
  · exact g32p_supplierForest_actual_063601
  · exact g32p_supplierForest_actual_063622
  · exact g32p_supplierForest_actual_063656
  · exact g32p_supplierForest_actual_063728
  · exact g32p_supplierForest_actual_063810
  · exact g32p_supplierForest_actual_063872
  · exact g32p_supplierForest_actual_063975
  · exact g32p_supplierForest_actual_064121
  · exact g32p_supplierForest_actual_064125
  · exact g32p_supplierForest_actual_064136
  · exact g32p_supplierForest_actual_064139
  · exact g32p_supplierForest_actual_064147
  · exact g32p_supplierForest_actual_064328
  · exact g32p_supplierForest_actual_064364
  · exact g32p_supplierForest_actual_064415
  · exact g32p_supplierForest_actual_064422
  · exact g32p_supplierForest_actual_064443
  · exact g32p_supplierForest_actual_064456
  · exact g32p_supplierForest_actual_064505
  · exact g32p_supplierForest_actual_064530
  · exact g32p_supplierForest_actual_064586
  · exact g32p_supplierForest_actual_064657
  · exact g32p_supplierForest_actual_064710
  · exact g32p_supplierForest_actual_064757
  · exact g32p_supplierForest_actual_064890
  · exact g32p_supplierForest_actual_064915
  · exact g32p_supplierForest_actual_064927
  · exact g32p_supplierForest_actual_065055
  · exact g32p_supplierForest_actual_065078
  · exact g32p_supplierForest_actual_065098
  · exact g32p_supplierForest_actual_065101
  · exact g32p_supplierForest_actual_065128
  · exact g32p_supplierForest_actual_065198
  · exact g32p_supplierForest_actual_065581
  · exact g32p_supplierForest_actual_065632
  · exact g32p_supplierForest_actual_065652
  · exact g32p_supplierForest_actual_065842
  · exact g32p_supplierForest_actual_065972
  · exact g32p_supplierForest_actual_066086
  · exact g32p_supplierForest_actual_066116
  · exact g32p_supplierForest_actual_066418
  · exact g32p_supplierForest_actual_066489

def g32p_supplierForest_nodes_011 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_066558 else g32p_supplierForest_node_066595) else (if i.val < 3 then g32p_supplierForest_node_066610 else g32p_supplierForest_node_066621)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_066729 else g32p_supplierForest_node_066816) else (if i.val < 7 then g32p_supplierForest_node_066828 else g32p_supplierForest_node_066845))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_066904 else g32p_supplierForest_node_066960) else (if i.val < 11 then g32p_supplierForest_node_067001 else g32p_supplierForest_node_067125)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_067251 else g32p_supplierForest_node_067262) else (if i.val < 15 then g32p_supplierForest_node_067561 else g32p_supplierForest_node_067722)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_067836 else g32p_supplierForest_node_067860) else (if i.val < 19 then g32p_supplierForest_node_067877 else g32p_supplierForest_node_067897)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_068016 else g32p_supplierForest_node_068171) else (if i.val < 23 then g32p_supplierForest_node_068235 else g32p_supplierForest_node_068323))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_068399 else g32p_supplierForest_node_068447) else (if i.val < 27 then g32p_supplierForest_node_068488 else g32p_supplierForest_node_068506)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_068724 else g32p_supplierForest_node_068756) else (if i.val < 31 then g32p_supplierForest_node_068769 else g32p_supplierForest_node_068770))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_068820 else g32p_supplierForest_node_068868) else (if i.val < 35 then g32p_supplierForest_node_068965 else g32p_supplierForest_node_068984)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_069018 else g32p_supplierForest_node_069115) else (if i.val < 39 then g32p_supplierForest_node_069485 else g32p_supplierForest_node_069486))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_069506 else g32p_supplierForest_node_069602) else (if i.val < 43 then g32p_supplierForest_node_069607 else g32p_supplierForest_node_069781)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_069852 else g32p_supplierForest_node_070194) else (if i.val < 47 then g32p_supplierForest_node_070252 else g32p_supplierForest_node_070298)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_070334 else g32p_supplierForest_node_070407) else (if i.val < 51 then g32p_supplierForest_node_070440 else g32p_supplierForest_node_070483)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_070584 else g32p_supplierForest_node_070608) else (if i.val < 55 then g32p_supplierForest_node_070670 else g32p_supplierForest_node_070739))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_070790 else g32p_supplierForest_node_070806) else (if i.val < 59 then g32p_supplierForest_node_070884 else g32p_supplierForest_node_070974)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_071103 else g32p_supplierForest_node_071108) else (if i.val < 63 then g32p_supplierForest_node_071111 else g32p_supplierForest_node_071213)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_071271 else g32p_supplierForest_node_071440) else (if i.val < 67 then g32p_supplierForest_node_071491 else g32p_supplierForest_node_071620)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_071638 else g32p_supplierForest_node_071746) else (if i.val < 71 then g32p_supplierForest_node_071765 else g32p_supplierForest_node_071780))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_071941 else g32p_supplierForest_node_072028) else (if i.val < 75 then g32p_supplierForest_node_072107 else g32p_supplierForest_node_072178)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_072224 else g32p_supplierForest_node_072576) else (if i.val < 79 then g32p_supplierForest_node_072604 else g32p_supplierForest_node_072657)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_072693 else g32p_supplierForest_node_072722) else (if i.val < 83 then g32p_supplierForest_node_072808 else g32p_supplierForest_node_072985)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_073043 else g32p_supplierForest_node_073114) else (if i.val < 87 then g32p_supplierForest_node_073341 else g32p_supplierForest_node_073346))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_073381 else g32p_supplierForest_node_073419) else (if i.val < 91 then g32p_supplierForest_node_073595 else g32p_supplierForest_node_073629)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_073655 else g32p_supplierForest_node_073669) else (if i.val < 95 then g32p_supplierForest_node_073746 else g32p_supplierForest_node_073755))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_073837 else g32p_supplierForest_node_073875) else (if i.val < 99 then g32p_supplierForest_node_073887 else g32p_supplierForest_node_073906)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_074040 else g32p_supplierForest_node_074169) else (if i.val < 103 then g32p_supplierForest_node_074172 else g32p_supplierForest_node_074188))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_074190 else g32p_supplierForest_node_074262) else (if i.val < 107 then g32p_supplierForest_node_074264 else g32p_supplierForest_node_074285)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_074377 else g32p_supplierForest_node_074446) else (if i.val < 111 then g32p_supplierForest_node_074459 else g32p_supplierForest_node_074472)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_074506 else g32p_supplierForest_node_074529) else (if i.val < 115 then g32p_supplierForest_node_074610 else g32p_supplierForest_node_074742)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_074747 else g32p_supplierForest_node_074810) else (if i.val < 119 then g32p_supplierForest_node_074908 else g32p_supplierForest_node_074919))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_074968 else g32p_supplierForest_node_074979) else (if i.val < 123 then g32p_supplierForest_node_075139 else g32p_supplierForest_node_075185)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_075187 else g32p_supplierForest_node_075200) else (if i.val < 127 then g32p_supplierForest_node_075206 else g32p_supplierForest_node_075227))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_075370 else g32p_supplierForest_node_075377) else (if i.val < 131 then g32p_supplierForest_node_075433 else g32p_supplierForest_node_075457)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_075458 else g32p_supplierForest_node_075492) else (if i.val < 135 then g32p_supplierForest_node_075711 else g32p_supplierForest_node_075904))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_075947 else g32p_supplierForest_node_076192) else (if i.val < 139 then g32p_supplierForest_node_076320 else g32p_supplierForest_node_076330)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_076415 else g32p_supplierForest_node_076437) else (if i.val < 143 then g32p_supplierForest_node_076511 else g32p_supplierForest_node_076527)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_076546 else g32p_supplierForest_node_076729) else (if i.val < 147 then g32p_supplierForest_node_076745 else g32p_supplierForest_node_076775)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_076813 else g32p_supplierForest_node_076834) else (if i.val < 151 then g32p_supplierForest_node_076882 else g32p_supplierForest_node_076918))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_076944 else g32p_supplierForest_node_076945) else (if i.val < 155 then g32p_supplierForest_node_076972 else g32p_supplierForest_node_077076)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_077083 else g32p_supplierForest_node_077210) else (if i.val < 159 then g32p_supplierForest_node_077231 else g32p_supplierForest_node_077354))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_077391 else g32p_supplierForest_node_077816) else (if i.val < 163 then g32p_supplierForest_node_077885 else g32p_supplierForest_node_078047)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_078096 else g32p_supplierForest_node_078105) else (if i.val < 167 then g32p_supplierForest_node_078190 else g32p_supplierForest_node_078302))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_078503 else g32p_supplierForest_node_078853) else (if i.val < 171 then g32p_supplierForest_node_079094 else g32p_supplierForest_node_079686)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_079690 else g32p_supplierForest_node_079771) else (if i.val < 175 then g32p_supplierForest_node_079773 else g32p_supplierForest_node_079957)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_079979 else g32p_supplierForest_node_080073) else (if i.val < 179 then g32p_supplierForest_node_080136 else g32p_supplierForest_node_080207)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_080546 else g32p_supplierForest_node_081105) else (if i.val < 183 then g32p_supplierForest_node_081174 else g32p_supplierForest_node_081175))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_081247 else g32p_supplierForest_node_081249) else (if i.val < 187 then g32p_supplierForest_node_081294 else g32p_supplierForest_node_081441)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_081477 else g32p_supplierForest_node_081496) else (if i.val < 191 then g32p_supplierForest_node_081542 else g32p_supplierForest_node_081702)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_081994 else g32p_supplierForest_node_082013) else (if i.val < 195 then g32p_supplierForest_node_082035 else g32p_supplierForest_node_082063)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_082110 else g32p_supplierForest_node_082230) else (if i.val < 199 then g32p_supplierForest_node_082316 else g32p_supplierForest_node_082334))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_082395 else g32p_supplierForest_node_082590) else (if i.val < 203 then g32p_supplierForest_node_082662 else g32p_supplierForest_node_082666)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_082688 else g32p_supplierForest_node_082862) else (if i.val < 207 then g32p_supplierForest_node_082969 else g32p_supplierForest_node_083206)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_083212 else g32p_supplierForest_node_083215) else (if i.val < 211 then g32p_supplierForest_node_083267 else g32p_supplierForest_node_083274)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_083280 else g32p_supplierForest_node_083512) else (if i.val < 215 then g32p_supplierForest_node_083593 else g32p_supplierForest_node_083673))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_083861 else g32p_supplierForest_node_083881) else (if i.val < 219 then g32p_supplierForest_node_083894 else g32p_supplierForest_node_083907)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_083944 else g32p_supplierForest_node_084061) else (if i.val < 223 then g32p_supplierForest_node_084091 else g32p_supplierForest_node_084173))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_084355 else g32p_supplierForest_node_084393) else (if i.val < 227 then g32p_supplierForest_node_084438 else g32p_supplierForest_node_084530)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_084590 else g32p_supplierForest_node_084597) else (if i.val < 231 then g32p_supplierForest_node_084667 else g32p_supplierForest_node_084725))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_084754 else g32p_supplierForest_node_084806) else (if i.val < 235 then g32p_supplierForest_node_084922 else g32p_supplierForest_node_085018)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_085283 else g32p_supplierForest_node_085290) else (if i.val < 239 then g32p_supplierForest_node_085294 else g32p_supplierForest_node_085308)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_085385 else g32p_supplierForest_node_085473) else (if i.val < 243 then g32p_supplierForest_node_085542 else g32p_supplierForest_node_085589)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_085640 else g32p_supplierForest_node_085652) else (if i.val < 247 then g32p_supplierForest_node_085694 else g32p_supplierForest_node_085696))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_085755 else g32p_supplierForest_node_085850) else (if i.val < 251 then g32p_supplierForest_node_085867 else g32p_supplierForest_node_085962)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_086002 else g32p_supplierForest_node_086038) else (if i.val < 255 then g32p_supplierForest_node_086189 else g32p_supplierForest_node_086227))))))))

def g32p_supplierForest_classes_011 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 40 else 21) else (if i.val < 3 then 69 else 68)) else (if i.val < 6 then (if i.val < 5 then 43 else 69) else (if i.val < 7 then 69 else 74))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 75 else 72) else (if i.val < 11 then 38 else 42)) else (if i.val < 14 then (if i.val < 13 then 39 else 70) else (if i.val < 15 then 74 else 38)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 69 else 19) else (if i.val < 19 then 22 else 72)) else (if i.val < 22 then (if i.val < 21 then 43 else 69) else (if i.val < 23 then 75 else 69))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 43 else 40) else (if i.val < 27 then 43 else 67)) else (if i.val < 30 then (if i.val < 29 then 42 else 69) else (if i.val < 31 then 18 else 68))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 72 else 23) else (if i.val < 35 then 43 else 78)) else (if i.val < 38 then (if i.val < 37 then 74 else 70) else (if i.val < 39 then 69 else 43))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 43 else 69) else (if i.val < 43 then 77 else 42)) else (if i.val < 46 then (if i.val < 45 then 75 else 22) else (if i.val < 47 then 72 else 71)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 71 else 38) else (if i.val < 51 then 69 else 78)) else (if i.val < 54 then (if i.val < 53 then 75 else 73) else (if i.val < 55 then 42 else 74))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 73 else 69) else (if i.val < 59 then 79 else 68)) else (if i.val < 62 then (if i.val < 61 then 21 else 69) else (if i.val < 63 then 77 else 75)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 43 else 21) else (if i.val < 67 then 38 else 39)) else (if i.val < 70 then (if i.val < 69 then 70 else 49) else (if i.val < 71 then 50 else 56))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 47 else 47) else (if i.val < 75 then 56 else 13)) else (if i.val < 78 then (if i.val < 77 then 53 else 49) else (if i.val < 79 then 47 else 48)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 47 else 56) else (if i.val < 83 then 48 else 81)) else (if i.val < 86 then (if i.val < 85 then 54 else 47) else (if i.val < 87 then 27 else 46))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 47 else 26) else (if i.val < 91 then 49 else 25)) else (if i.val < 94 then (if i.val < 93 then 26 else 27) else (if i.val < 95 then 25 else 27))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 84 else 83) else (if i.val < 99 then 26 else 26)) else (if i.val < 102 then (if i.val < 101 then 13 else 27) else (if i.val < 103 then 27 else 83))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 84 else 50) else (if i.val < 107 then 46 else 46)) else (if i.val < 110 then (if i.val < 109 then 48 else 49) else (if i.val < 111 then 26 else 26)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 48 else 49) else (if i.val < 115 then 11 else 83)) else (if i.val < 118 then (if i.val < 117 then 83 else 46) else (if i.val < 119 then 49 else 25))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 45 else 53) else (if i.val < 123 then 83 else 83)) else (if i.val < 126 then (if i.val < 125 then 12 else 53) else (if i.val < 127 then 13 else 13))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 46 else 46) else (if i.val < 131 then 49 else 84)) else (if i.val < 134 then (if i.val < 133 then 45 else 83) else (if i.val < 135 then 48 else 80))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 80 else 53) else (if i.val < 139 then 82 else 52)) else (if i.val < 142 then (if i.val < 141 then 9 else 11) else (if i.val < 143 then 47 else 48)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 25 else 49) else (if i.val < 147 then 53 else 56)) else (if i.val < 150 then (if i.val < 149 then 56 else 48) else (if i.val < 151 then 53 else 80))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 53 else 53) else (if i.val < 155 then 49 else 82)) else (if i.val < 158 then (if i.val < 157 then 82 else 48) else (if i.val < 159 then 84 else 45))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 47 else 84) else (if i.val < 163 then 83 else 84)) else (if i.val < 166 then (if i.val < 165 then 84 else 83) else (if i.val < 167 then 81 else 52))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 47 else 84) else (if i.val < 171 then 46 else 26)) else (if i.val < 174 then (if i.val < 173 then 49 else 25) else (if i.val < 175 then 85 else 12)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 54 else 52) else (if i.val < 179 then 82 else 13)) else (if i.val < 182 then (if i.val < 181 then 56 else 26) else (if i.val < 183 then 49 else 46))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 26 else 27) else (if i.val < 187 then 49 else 47)) else (if i.val < 190 then (if i.val < 189 then 49 else 53) else (if i.val < 191 then 46 else 82)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 25 else 46) else (if i.val < 195 then 45 else 83)) else (if i.val < 198 then (if i.val < 197 then 80 else 52) else (if i.val < 199 then 47 else 47))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 47 else 50) else (if i.val < 203 then 45 else 25)) else (if i.val < 206 then (if i.val < 205 then 56 else 54) else (if i.val < 207 then 46 else 81)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 80 else 82) else (if i.val < 211 then 55 else 56)) else (if i.val < 214 then (if i.val < 213 then 47 else 46) else (if i.val < 215 then 80 else 83))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 84 else 83) else (if i.val < 219 then 46 else 83)) else (if i.val < 222 then (if i.val < 221 then 83 else 53) else (if i.val < 223 then 81 else 46))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 52 else 48) else (if i.val < 227 then 84 else 53)) else (if i.val < 230 then (if i.val < 229 then 82 else 55) else (if i.val < 231 then 47 else 85))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 56 else 46) else (if i.val < 235 then 80 else 55)) else (if i.val < 238 then (if i.val < 237 then 52 else 84) else (if i.val < 239 then 46 else 80)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 47 else 56) else (if i.val < 243 then 84 else 45)) else (if i.val < 246 then (if i.val < 245 then 84 else 26) else (if i.val < 247 then 83 else 46))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 53 else 81) else (if i.val < 251 then 82 else 85)) else (if i.val < 254 then (if i.val < 253 then 50 else 46) else (if i.val < 255 then 84 else 81))))))))

theorem g32p_supplierForest_actual_011 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_011 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_011 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_066558
  · exact g32p_supplierForest_actual_066595
  · exact g32p_supplierForest_actual_066610
  · exact g32p_supplierForest_actual_066621
  · exact g32p_supplierForest_actual_066729
  · exact g32p_supplierForest_actual_066816
  · exact g32p_supplierForest_actual_066828
  · exact g32p_supplierForest_actual_066845
  · exact g32p_supplierForest_actual_066904
  · exact g32p_supplierForest_actual_066960
  · exact g32p_supplierForest_actual_067001
  · exact g32p_supplierForest_actual_067125
  · exact g32p_supplierForest_actual_067251
  · exact g32p_supplierForest_actual_067262
  · exact g32p_supplierForest_actual_067561
  · exact g32p_supplierForest_actual_067722
  · exact g32p_supplierForest_actual_067836
  · exact g32p_supplierForest_actual_067860
  · exact g32p_supplierForest_actual_067877
  · exact g32p_supplierForest_actual_067897
  · exact g32p_supplierForest_actual_068016
  · exact g32p_supplierForest_actual_068171
  · exact g32p_supplierForest_actual_068235
  · exact g32p_supplierForest_actual_068323
  · exact g32p_supplierForest_actual_068399
  · exact g32p_supplierForest_actual_068447
  · exact g32p_supplierForest_actual_068488
  · exact g32p_supplierForest_actual_068506
  · exact g32p_supplierForest_actual_068724
  · exact g32p_supplierForest_actual_068756
  · exact g32p_supplierForest_actual_068769
  · exact g32p_supplierForest_actual_068770
  · exact g32p_supplierForest_actual_068820
  · exact g32p_supplierForest_actual_068868
  · exact g32p_supplierForest_actual_068965
  · exact g32p_supplierForest_actual_068984
  · exact g32p_supplierForest_actual_069018
  · exact g32p_supplierForest_actual_069115
  · exact g32p_supplierForest_actual_069485
  · exact g32p_supplierForest_actual_069486
  · exact g32p_supplierForest_actual_069506
  · exact g32p_supplierForest_actual_069602
  · exact g32p_supplierForest_actual_069607
  · exact g32p_supplierForest_actual_069781
  · exact g32p_supplierForest_actual_069852
  · exact g32p_supplierForest_actual_070194
  · exact g32p_supplierForest_actual_070252
  · exact g32p_supplierForest_actual_070298
  · exact g32p_supplierForest_actual_070334
  · exact g32p_supplierForest_actual_070407
  · exact g32p_supplierForest_actual_070440
  · exact g32p_supplierForest_actual_070483
  · exact g32p_supplierForest_actual_070584
  · exact g32p_supplierForest_actual_070608
  · exact g32p_supplierForest_actual_070670
  · exact g32p_supplierForest_actual_070739
  · exact g32p_supplierForest_actual_070790
  · exact g32p_supplierForest_actual_070806
  · exact g32p_supplierForest_actual_070884
  · exact g32p_supplierForest_actual_070974
  · exact g32p_supplierForest_actual_071103
  · exact g32p_supplierForest_actual_071108
  · exact g32p_supplierForest_actual_071111
  · exact g32p_supplierForest_actual_071213
  · exact g32p_supplierForest_actual_071271
  · exact g32p_supplierForest_actual_071440
  · exact g32p_supplierForest_actual_071491
  · exact g32p_supplierForest_actual_071620
  · exact g32p_supplierForest_actual_071638
  · exact g32p_supplierForest_actual_071746
  · exact g32p_supplierForest_actual_071765
  · exact g32p_supplierForest_actual_071780
  · exact g32p_supplierForest_actual_071941
  · exact g32p_supplierForest_actual_072028
  · exact g32p_supplierForest_actual_072107
  · exact g32p_supplierForest_actual_072178
  · exact g32p_supplierForest_actual_072224
  · exact g32p_supplierForest_actual_072576
  · exact g32p_supplierForest_actual_072604
  · exact g32p_supplierForest_actual_072657
  · exact g32p_supplierForest_actual_072693
  · exact g32p_supplierForest_actual_072722
  · exact g32p_supplierForest_actual_072808
  · exact g32p_supplierForest_actual_072985
  · exact g32p_supplierForest_actual_073043
  · exact g32p_supplierForest_actual_073114
  · exact g32p_supplierForest_actual_073341
  · exact g32p_supplierForest_actual_073346
  · exact g32p_supplierForest_actual_073381
  · exact g32p_supplierForest_actual_073419
  · exact g32p_supplierForest_actual_073595
  · exact g32p_supplierForest_actual_073629
  · exact g32p_supplierForest_actual_073655
  · exact g32p_supplierForest_actual_073669
  · exact g32p_supplierForest_actual_073746
  · exact g32p_supplierForest_actual_073755
  · exact g32p_supplierForest_actual_073837
  · exact g32p_supplierForest_actual_073875
  · exact g32p_supplierForest_actual_073887
  · exact g32p_supplierForest_actual_073906
  · exact g32p_supplierForest_actual_074040
  · exact g32p_supplierForest_actual_074169
  · exact g32p_supplierForest_actual_074172
  · exact g32p_supplierForest_actual_074188
  · exact g32p_supplierForest_actual_074190
  · exact g32p_supplierForest_actual_074262
  · exact g32p_supplierForest_actual_074264
  · exact g32p_supplierForest_actual_074285
  · exact g32p_supplierForest_actual_074377
  · exact g32p_supplierForest_actual_074446
  · exact g32p_supplierForest_actual_074459
  · exact g32p_supplierForest_actual_074472
  · exact g32p_supplierForest_actual_074506
  · exact g32p_supplierForest_actual_074529
  · exact g32p_supplierForest_actual_074610
  · exact g32p_supplierForest_actual_074742
  · exact g32p_supplierForest_actual_074747
  · exact g32p_supplierForest_actual_074810
  · exact g32p_supplierForest_actual_074908
  · exact g32p_supplierForest_actual_074919
  · exact g32p_supplierForest_actual_074968
  · exact g32p_supplierForest_actual_074979
  · exact g32p_supplierForest_actual_075139
  · exact g32p_supplierForest_actual_075185
  · exact g32p_supplierForest_actual_075187
  · exact g32p_supplierForest_actual_075200
  · exact g32p_supplierForest_actual_075206
  · exact g32p_supplierForest_actual_075227
  · exact g32p_supplierForest_actual_075370
  · exact g32p_supplierForest_actual_075377
  · exact g32p_supplierForest_actual_075433
  · exact g32p_supplierForest_actual_075457
  · exact g32p_supplierForest_actual_075458
  · exact g32p_supplierForest_actual_075492
  · exact g32p_supplierForest_actual_075711
  · exact g32p_supplierForest_actual_075904
  · exact g32p_supplierForest_actual_075947
  · exact g32p_supplierForest_actual_076192
  · exact g32p_supplierForest_actual_076320
  · exact g32p_supplierForest_actual_076330
  · exact g32p_supplierForest_actual_076415
  · exact g32p_supplierForest_actual_076437
  · exact g32p_supplierForest_actual_076511
  · exact g32p_supplierForest_actual_076527
  · exact g32p_supplierForest_actual_076546
  · exact g32p_supplierForest_actual_076729
  · exact g32p_supplierForest_actual_076745
  · exact g32p_supplierForest_actual_076775
  · exact g32p_supplierForest_actual_076813
  · exact g32p_supplierForest_actual_076834
  · exact g32p_supplierForest_actual_076882
  · exact g32p_supplierForest_actual_076918
  · exact g32p_supplierForest_actual_076944
  · exact g32p_supplierForest_actual_076945
  · exact g32p_supplierForest_actual_076972
  · exact g32p_supplierForest_actual_077076
  · exact g32p_supplierForest_actual_077083
  · exact g32p_supplierForest_actual_077210
  · exact g32p_supplierForest_actual_077231
  · exact g32p_supplierForest_actual_077354
  · exact g32p_supplierForest_actual_077391
  · exact g32p_supplierForest_actual_077816
  · exact g32p_supplierForest_actual_077885
  · exact g32p_supplierForest_actual_078047
  · exact g32p_supplierForest_actual_078096
  · exact g32p_supplierForest_actual_078105
  · exact g32p_supplierForest_actual_078190
  · exact g32p_supplierForest_actual_078302
  · exact g32p_supplierForest_actual_078503
  · exact g32p_supplierForest_actual_078853
  · exact g32p_supplierForest_actual_079094
  · exact g32p_supplierForest_actual_079686
  · exact g32p_supplierForest_actual_079690
  · exact g32p_supplierForest_actual_079771
  · exact g32p_supplierForest_actual_079773
  · exact g32p_supplierForest_actual_079957
  · exact g32p_supplierForest_actual_079979
  · exact g32p_supplierForest_actual_080073
  · exact g32p_supplierForest_actual_080136
  · exact g32p_supplierForest_actual_080207
  · exact g32p_supplierForest_actual_080546
  · exact g32p_supplierForest_actual_081105
  · exact g32p_supplierForest_actual_081174
  · exact g32p_supplierForest_actual_081175
  · exact g32p_supplierForest_actual_081247
  · exact g32p_supplierForest_actual_081249
  · exact g32p_supplierForest_actual_081294
  · exact g32p_supplierForest_actual_081441
  · exact g32p_supplierForest_actual_081477
  · exact g32p_supplierForest_actual_081496
  · exact g32p_supplierForest_actual_081542
  · exact g32p_supplierForest_actual_081702
  · exact g32p_supplierForest_actual_081994
  · exact g32p_supplierForest_actual_082013
  · exact g32p_supplierForest_actual_082035
  · exact g32p_supplierForest_actual_082063
  · exact g32p_supplierForest_actual_082110
  · exact g32p_supplierForest_actual_082230
  · exact g32p_supplierForest_actual_082316
  · exact g32p_supplierForest_actual_082334
  · exact g32p_supplierForest_actual_082395
  · exact g32p_supplierForest_actual_082590
  · exact g32p_supplierForest_actual_082662
  · exact g32p_supplierForest_actual_082666
  · exact g32p_supplierForest_actual_082688
  · exact g32p_supplierForest_actual_082862
  · exact g32p_supplierForest_actual_082969
  · exact g32p_supplierForest_actual_083206
  · exact g32p_supplierForest_actual_083212
  · exact g32p_supplierForest_actual_083215
  · exact g32p_supplierForest_actual_083267
  · exact g32p_supplierForest_actual_083274
  · exact g32p_supplierForest_actual_083280
  · exact g32p_supplierForest_actual_083512
  · exact g32p_supplierForest_actual_083593
  · exact g32p_supplierForest_actual_083673
  · exact g32p_supplierForest_actual_083861
  · exact g32p_supplierForest_actual_083881
  · exact g32p_supplierForest_actual_083894
  · exact g32p_supplierForest_actual_083907
  · exact g32p_supplierForest_actual_083944
  · exact g32p_supplierForest_actual_084061
  · exact g32p_supplierForest_actual_084091
  · exact g32p_supplierForest_actual_084173
  · exact g32p_supplierForest_actual_084355
  · exact g32p_supplierForest_actual_084393
  · exact g32p_supplierForest_actual_084438
  · exact g32p_supplierForest_actual_084530
  · exact g32p_supplierForest_actual_084590
  · exact g32p_supplierForest_actual_084597
  · exact g32p_supplierForest_actual_084667
  · exact g32p_supplierForest_actual_084725
  · exact g32p_supplierForest_actual_084754
  · exact g32p_supplierForest_actual_084806
  · exact g32p_supplierForest_actual_084922
  · exact g32p_supplierForest_actual_085018
  · exact g32p_supplierForest_actual_085283
  · exact g32p_supplierForest_actual_085290
  · exact g32p_supplierForest_actual_085294
  · exact g32p_supplierForest_actual_085308
  · exact g32p_supplierForest_actual_085385
  · exact g32p_supplierForest_actual_085473
  · exact g32p_supplierForest_actual_085542
  · exact g32p_supplierForest_actual_085589
  · exact g32p_supplierForest_actual_085640
  · exact g32p_supplierForest_actual_085652
  · exact g32p_supplierForest_actual_085694
  · exact g32p_supplierForest_actual_085696
  · exact g32p_supplierForest_actual_085755
  · exact g32p_supplierForest_actual_085850
  · exact g32p_supplierForest_actual_085867
  · exact g32p_supplierForest_actual_085962
  · exact g32p_supplierForest_actual_086002
  · exact g32p_supplierForest_actual_086038
  · exact g32p_supplierForest_actual_086189
  · exact g32p_supplierForest_actual_086227

def g32p_supplierForest_nodes_012 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_086237 else g32p_supplierForest_node_086327) else (if i.val < 3 then g32p_supplierForest_node_086435 else g32p_supplierForest_node_086506)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_086621 else g32p_supplierForest_node_086708) else (if i.val < 7 then g32p_supplierForest_node_087069 else g32p_supplierForest_node_087358))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_087489 else g32p_supplierForest_node_087574) else (if i.val < 11 then g32p_supplierForest_node_087653 else g32p_supplierForest_node_087745)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_087760 else g32p_supplierForest_node_087979) else (if i.val < 15 then g32p_supplierForest_node_087982 else g32p_supplierForest_node_088033)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_088037 else g32p_supplierForest_node_088102) else (if i.val < 19 then g32p_supplierForest_node_088185 else g32p_supplierForest_node_088327)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_088434 else g32p_supplierForest_node_088461) else (if i.val < 23 then g32p_supplierForest_node_088499 else g32p_supplierForest_node_088609))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_088645 else g32p_supplierForest_node_088901) else (if i.val < 27 then g32p_supplierForest_node_088929 else g32p_supplierForest_node_088949)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_088971 else g32p_supplierForest_node_089027) else (if i.val < 31 then g32p_supplierForest_node_089058 else g32p_supplierForest_node_089110))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_089361 else g32p_supplierForest_node_089453) else (if i.val < 35 then g32p_supplierForest_node_089458 else g32p_supplierForest_node_089473)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_089829 else g32p_supplierForest_node_089881) else (if i.val < 39 then g32p_supplierForest_node_090008 else g32p_supplierForest_node_090167))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_090176 else g32p_supplierForest_node_090318) else (if i.val < 43 then g32p_supplierForest_node_090340 else g32p_supplierForest_node_090371)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_090379 else g32p_supplierForest_node_090534) else (if i.val < 47 then g32p_supplierForest_node_090638 else g32p_supplierForest_node_091121)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_091162 else g32p_supplierForest_node_091558) else (if i.val < 51 then g32p_supplierForest_node_091631 else g32p_supplierForest_node_091655)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_091699 else g32p_supplierForest_node_091761) else (if i.val < 55 then g32p_supplierForest_node_091821 else g32p_supplierForest_node_091947))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_091998 else g32p_supplierForest_node_092219) else (if i.val < 59 then g32p_supplierForest_node_092319 else g32p_supplierForest_node_092543)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_092549 else g32p_supplierForest_node_092576) else (if i.val < 63 then g32p_supplierForest_node_092598 else g32p_supplierForest_node_092678)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_092683 else g32p_supplierForest_node_092695) else (if i.val < 67 then g32p_supplierForest_node_092764 else g32p_supplierForest_node_092777)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_092808 else g32p_supplierForest_node_092928) else (if i.val < 71 then g32p_supplierForest_node_092938 else g32p_supplierForest_node_093237))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_093263 else g32p_supplierForest_node_093309) else (if i.val < 75 then g32p_supplierForest_node_093315 else g32p_supplierForest_node_093485)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_093559 else g32p_supplierForest_node_093751) else (if i.val < 79 then g32p_supplierForest_node_093830 else g32p_supplierForest_node_093852)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_093891 else g32p_supplierForest_node_094271) else (if i.val < 83 then g32p_supplierForest_node_094541 else g32p_supplierForest_node_094594)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_094645 else g32p_supplierForest_node_094656) else (if i.val < 87 then g32p_supplierForest_node_094672 else g32p_supplierForest_node_094708))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_094922 else g32p_supplierForest_node_095173) else (if i.val < 91 then g32p_supplierForest_node_095269 else g32p_supplierForest_node_095270)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_095851 else g32p_supplierForest_node_095901) else (if i.val < 95 then g32p_supplierForest_node_095914 else g32p_supplierForest_node_096027))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_096068 else g32p_supplierForest_node_096088) else (if i.val < 99 then g32p_supplierForest_node_096169 else g32p_supplierForest_node_096191)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_096209 else g32p_supplierForest_node_096362) else (if i.val < 103 then g32p_supplierForest_node_096525 else g32p_supplierForest_node_096624))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_096752 else g32p_supplierForest_node_097053) else (if i.val < 107 then g32p_supplierForest_node_097056 else g32p_supplierForest_node_097180)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_097223 else g32p_supplierForest_node_097265) else (if i.val < 111 then g32p_supplierForest_node_097411 else g32p_supplierForest_node_097425)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_097542 else g32p_supplierForest_node_097878) else (if i.val < 115 then g32p_supplierForest_node_097898 else g32p_supplierForest_node_097901)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_097968 else g32p_supplierForest_node_098016) else (if i.val < 119 then g32p_supplierForest_node_098085 else g32p_supplierForest_node_098171))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_098208 else g32p_supplierForest_node_098235) else (if i.val < 123 then g32p_supplierForest_node_098241 else g32p_supplierForest_node_098563)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_098655 else g32p_supplierForest_node_098754) else (if i.val < 127 then g32p_supplierForest_node_098762 else g32p_supplierForest_node_099027))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_099251 else g32p_supplierForest_node_099336) else (if i.val < 131 then g32p_supplierForest_node_099539 else g32p_supplierForest_node_099666)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_099680 else g32p_supplierForest_node_099821) else (if i.val < 135 then g32p_supplierForest_node_099916 else g32p_supplierForest_node_100349))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_100401 else g32p_supplierForest_node_100407) else (if i.val < 139 then g32p_supplierForest_node_100548 else g32p_supplierForest_node_100562)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_100598 else g32p_supplierForest_node_100631) else (if i.val < 143 then g32p_supplierForest_node_100963 else g32p_supplierForest_node_101034)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_101035 else g32p_supplierForest_node_101389) else (if i.val < 147 then g32p_supplierForest_node_101592 else g32p_supplierForest_node_101704)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_101793 else g32p_supplierForest_node_101889) else (if i.val < 151 then g32p_supplierForest_node_101893 else g32p_supplierForest_node_101947))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_101956 else g32p_supplierForest_node_101975) else (if i.val < 155 then g32p_supplierForest_node_102006 else g32p_supplierForest_node_102240)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_102247 else g32p_supplierForest_node_102283) else (if i.val < 159 then g32p_supplierForest_node_102285 else g32p_supplierForest_node_102293))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_102456 else g32p_supplierForest_node_102483) else (if i.val < 163 then g32p_supplierForest_node_103069 else g32p_supplierForest_node_103139)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_103179 else g32p_supplierForest_node_103359) else (if i.val < 167 then g32p_supplierForest_node_103505 else g32p_supplierForest_node_103618))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_103759 else g32p_supplierForest_node_103785) else (if i.val < 171 then g32p_supplierForest_node_103954 else g32p_supplierForest_node_103991)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_104025 else g32p_supplierForest_node_104144) else (if i.val < 175 then g32p_supplierForest_node_104235 else g32p_supplierForest_node_104252)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_104376 else g32p_supplierForest_node_104387) else (if i.val < 179 then g32p_supplierForest_node_104393 else g32p_supplierForest_node_104423)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_104484 else g32p_supplierForest_node_104504) else (if i.val < 183 then g32p_supplierForest_node_104506 else g32p_supplierForest_node_104674))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_104675 else g32p_supplierForest_node_104679) else (if i.val < 187 then g32p_supplierForest_node_104787 else g32p_supplierForest_node_104809)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_104970 else g32p_supplierForest_node_104988) else (if i.val < 191 then g32p_supplierForest_node_105045 else g32p_supplierForest_node_105326)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_105332 else g32p_supplierForest_node_105389) else (if i.val < 195 then g32p_supplierForest_node_105407 else g32p_supplierForest_node_105596)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_105717 else g32p_supplierForest_node_105727) else (if i.val < 199 then g32p_supplierForest_node_105870 else g32p_supplierForest_node_105889))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_106246 else g32p_supplierForest_node_106263) else (if i.val < 203 then g32p_supplierForest_node_106272 else g32p_supplierForest_node_106338)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_106410 else g32p_supplierForest_node_106436) else (if i.val < 207 then g32p_supplierForest_node_106504 else g32p_supplierForest_node_106709)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_106809 else g32p_supplierForest_node_106924) else (if i.val < 211 then g32p_supplierForest_node_106985 else g32p_supplierForest_node_107299)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_107393 else g32p_supplierForest_node_107426) else (if i.val < 215 then g32p_supplierForest_node_107529 else g32p_supplierForest_node_107537))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_107747 else g32p_supplierForest_node_107767) else (if i.val < 219 then g32p_supplierForest_node_108015 else g32p_supplierForest_node_108024)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_108053 else g32p_supplierForest_node_108059) else (if i.val < 223 then g32p_supplierForest_node_108081 else g32p_supplierForest_node_108180))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_108334 else g32p_supplierForest_node_108338) else (if i.val < 227 then g32p_supplierForest_node_108423 else g32p_supplierForest_node_108439)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_108496 else g32p_supplierForest_node_108562) else (if i.val < 231 then g32p_supplierForest_node_108591 else g32p_supplierForest_node_108701))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_108809 else g32p_supplierForest_node_108887) else (if i.val < 235 then g32p_supplierForest_node_109186 else g32p_supplierForest_node_109301)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_109336 else g32p_supplierForest_node_109341) else (if i.val < 239 then g32p_supplierForest_node_109436 else g32p_supplierForest_node_109646)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_109896 else g32p_supplierForest_node_109915) else (if i.val < 243 then g32p_supplierForest_node_110308 else g32p_supplierForest_node_110328)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_110351 else g32p_supplierForest_node_110364) else (if i.val < 247 then g32p_supplierForest_node_110446 else g32p_supplierForest_node_110517))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_110653 else g32p_supplierForest_node_110902) else (if i.val < 251 then g32p_supplierForest_node_111025 else g32p_supplierForest_node_111330)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_111338 else g32p_supplierForest_node_111412) else (if i.val < 255 then g32p_supplierForest_node_111426 else g32p_supplierForest_node_111450))))))))

def g32p_supplierForest_classes_012 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 85 else 54) else (if i.val < 3 then 26 else 84)) else (if i.val < 6 then (if i.val < 5 then 84 else 81) else (if i.val < 7 then 47 else 52))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 52 else 47) else (if i.val < 11 then 84 else 52)) else (if i.val < 14 then (if i.val < 13 then 56 else 80) else (if i.val < 15 then 54 else 81)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 54 else 83) else (if i.val < 19 then 53 else 52)) else (if i.val < 22 then (if i.val < 21 then 48 else 52) else (if i.val < 23 then 46 else 53))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 83 else 83) else (if i.val < 27 then 84 else 52)) else (if i.val < 30 then (if i.val < 29 then 86 else 53) else (if i.val < 31 then 80 else 54))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 48 else 49) else (if i.val < 35 then 56 else 52)) else (if i.val < 38 then (if i.val < 37 then 52 else 81) else (if i.val < 39 then 46 else 49))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 26 else 82) else (if i.val < 43 then 52 else 48)) else (if i.val < 46 then (if i.val < 45 then 53 else 49) else (if i.val < 47 then 82 else 82)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 52 else 82) else (if i.val < 51 then 81 else 52)) else (if i.val < 54 then (if i.val < 53 then 86 else 80) else (if i.val < 55 then 84 else 46))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 54 else 26) else (if i.val < 59 then 55 else 55)) else (if i.val < 62 then (if i.val < 61 then 84 else 45) else (if i.val < 63 then 45 else 54)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 84 else 49) else (if i.val < 67 then 54 else 83)) else (if i.val < 70 then (if i.val < 69 then 84 else 53) else (if i.val < 71 then 49 else 46))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 83 else 80) else (if i.val < 75 then 25 else 11)) else (if i.val < 78 then (if i.val < 77 then 55 else 53) else (if i.val < 79 then 45 else 52)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 46 else 85) else (if i.val < 83 then 13 else 46)) else (if i.val < 86 then (if i.val < 85 then 82 else 81) else (if i.val < 87 then 49 else 54))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 84 else 55) else (if i.val < 91 then 26 else 80)) else (if i.val < 94 then (if i.val < 93 then 11 else 26) else (if i.val < 95 then 55 else 54))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 46 else 54) else (if i.val < 99 then 54 else 45)) else (if i.val < 102 then (if i.val < 101 then 54 else 45) else (if i.val < 103 then 53 else 45))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 55 else 54) else (if i.val < 107 then 55 else 54)) else (if i.val < 110 then (if i.val < 109 then 55 else 46) else (if i.val < 111 then 48 else 85)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 85 else 25) else (if i.val < 115 then 45 else 45)) else (if i.val < 118 then (if i.val < 117 then 53 else 26) else (if i.val < 119 then 86 else 55))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 82 else 46) else (if i.val < 123 then 80 else 83)) else (if i.val < 126 then (if i.val < 125 then 83 else 55) else (if i.val < 127 then 53 else 52))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 82 else 85) else (if i.val < 131 then 86 else 45)) else (if i.val < 134 then (if i.val < 133 then 52 else 80) else (if i.val < 135 then 86 else 55))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 25 else 46) else (if i.val < 139 then 80 else 86)) else (if i.val < 142 then (if i.val < 141 then 52 else 55) else (if i.val < 143 then 25 else 25)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 46 else 80) else (if i.val < 147 then 80 else 53)) else (if i.val < 150 then (if i.val < 149 then 80 else 55) else (if i.val < 151 then 59 else 66))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 59 else 60) else (if i.val < 155 then 64 else 60)) else (if i.val < 158 then (if i.val < 157 then 57 else 59) else (if i.val < 159 then 63 else 64))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 64 else 59) else (if i.val < 163 then 57 else 58)) else (if i.val < 166 then (if i.val < 165 then 65 else 58) else (if i.val < 167 then 66 else 60))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 62 else 64) else (if i.val < 171 then 63 else 29)) else (if i.val < 174 then (if i.val < 173 then 60 else 57) else (if i.val < 175 then 60 else 66)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 60 else 29) else (if i.val < 179 then 33 else 88)) else (if i.val < 182 then (if i.val < 181 then 30 else 88) else (if i.val < 183 then 88 else 33))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 88 else 61) else (if i.val < 187 then 33 else 30)) else (if i.val < 190 then (if i.val < 189 then 88 else 88) else (if i.val < 191 then 62 else 33)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 62 else 61) else (if i.val < 195 then 58 else 29)) else (if i.val < 198 then (if i.val < 197 then 65 else 29) else (if i.val < 199 then 60 else 63))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 60 else 62) else (if i.val < 203 then 29 else 57)) else (if i.val < 206 then (if i.val < 205 then 30 else 29) else (if i.val < 207 then 60 else 59)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 58 else 61) else (if i.val < 211 then 88 else 66)) else (if i.val < 214 then (if i.val < 213 then 59 else 89) else (if i.val < 215 then 59 else 91))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 61 else 29) else (if i.val < 219 then 59 else 60)) else (if i.val < 222 then (if i.val < 221 then 57 else 66) else (if i.val < 223 then 36 else 87))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 66 else 30) else (if i.val < 227 then 91 else 60)) else (if i.val < 230 then (if i.val < 229 then 92 else 92) else (if i.val < 231 then 59 else 60))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 63 else 35) else (if i.val < 235 then 63 else 59)) else (if i.val < 238 then (if i.val < 237 then 34 else 35) else (if i.val < 239 then 66 else 90)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 30 else 66) else (if i.val < 243 then 87 else 87)) else (if i.val < 246 then (if i.val < 245 then 60 else 90) else (if i.val < 247 then 62 else 33))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 33 else 59) else (if i.val < 251 then 30 else 60)) else (if i.val < 254 then (if i.val < 253 then 29 else 34) else (if i.val < 255 then 35 else 89))))))))

theorem g32p_supplierForest_actual_012 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_012 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_012 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_086237
  · exact g32p_supplierForest_actual_086327
  · exact g32p_supplierForest_actual_086435
  · exact g32p_supplierForest_actual_086506
  · exact g32p_supplierForest_actual_086621
  · exact g32p_supplierForest_actual_086708
  · exact g32p_supplierForest_actual_087069
  · exact g32p_supplierForest_actual_087358
  · exact g32p_supplierForest_actual_087489
  · exact g32p_supplierForest_actual_087574
  · exact g32p_supplierForest_actual_087653
  · exact g32p_supplierForest_actual_087745
  · exact g32p_supplierForest_actual_087760
  · exact g32p_supplierForest_actual_087979
  · exact g32p_supplierForest_actual_087982
  · exact g32p_supplierForest_actual_088033
  · exact g32p_supplierForest_actual_088037
  · exact g32p_supplierForest_actual_088102
  · exact g32p_supplierForest_actual_088185
  · exact g32p_supplierForest_actual_088327
  · exact g32p_supplierForest_actual_088434
  · exact g32p_supplierForest_actual_088461
  · exact g32p_supplierForest_actual_088499
  · exact g32p_supplierForest_actual_088609
  · exact g32p_supplierForest_actual_088645
  · exact g32p_supplierForest_actual_088901
  · exact g32p_supplierForest_actual_088929
  · exact g32p_supplierForest_actual_088949
  · exact g32p_supplierForest_actual_088971
  · exact g32p_supplierForest_actual_089027
  · exact g32p_supplierForest_actual_089058
  · exact g32p_supplierForest_actual_089110
  · exact g32p_supplierForest_actual_089361
  · exact g32p_supplierForest_actual_089453
  · exact g32p_supplierForest_actual_089458
  · exact g32p_supplierForest_actual_089473
  · exact g32p_supplierForest_actual_089829
  · exact g32p_supplierForest_actual_089881
  · exact g32p_supplierForest_actual_090008
  · exact g32p_supplierForest_actual_090167
  · exact g32p_supplierForest_actual_090176
  · exact g32p_supplierForest_actual_090318
  · exact g32p_supplierForest_actual_090340
  · exact g32p_supplierForest_actual_090371
  · exact g32p_supplierForest_actual_090379
  · exact g32p_supplierForest_actual_090534
  · exact g32p_supplierForest_actual_090638
  · exact g32p_supplierForest_actual_091121
  · exact g32p_supplierForest_actual_091162
  · exact g32p_supplierForest_actual_091558
  · exact g32p_supplierForest_actual_091631
  · exact g32p_supplierForest_actual_091655
  · exact g32p_supplierForest_actual_091699
  · exact g32p_supplierForest_actual_091761
  · exact g32p_supplierForest_actual_091821
  · exact g32p_supplierForest_actual_091947
  · exact g32p_supplierForest_actual_091998
  · exact g32p_supplierForest_actual_092219
  · exact g32p_supplierForest_actual_092319
  · exact g32p_supplierForest_actual_092543
  · exact g32p_supplierForest_actual_092549
  · exact g32p_supplierForest_actual_092576
  · exact g32p_supplierForest_actual_092598
  · exact g32p_supplierForest_actual_092678
  · exact g32p_supplierForest_actual_092683
  · exact g32p_supplierForest_actual_092695
  · exact g32p_supplierForest_actual_092764
  · exact g32p_supplierForest_actual_092777
  · exact g32p_supplierForest_actual_092808
  · exact g32p_supplierForest_actual_092928
  · exact g32p_supplierForest_actual_092938
  · exact g32p_supplierForest_actual_093237
  · exact g32p_supplierForest_actual_093263
  · exact g32p_supplierForest_actual_093309
  · exact g32p_supplierForest_actual_093315
  · exact g32p_supplierForest_actual_093485
  · exact g32p_supplierForest_actual_093559
  · exact g32p_supplierForest_actual_093751
  · exact g32p_supplierForest_actual_093830
  · exact g32p_supplierForest_actual_093852
  · exact g32p_supplierForest_actual_093891
  · exact g32p_supplierForest_actual_094271
  · exact g32p_supplierForest_actual_094541
  · exact g32p_supplierForest_actual_094594
  · exact g32p_supplierForest_actual_094645
  · exact g32p_supplierForest_actual_094656
  · exact g32p_supplierForest_actual_094672
  · exact g32p_supplierForest_actual_094708
  · exact g32p_supplierForest_actual_094922
  · exact g32p_supplierForest_actual_095173
  · exact g32p_supplierForest_actual_095269
  · exact g32p_supplierForest_actual_095270
  · exact g32p_supplierForest_actual_095851
  · exact g32p_supplierForest_actual_095901
  · exact g32p_supplierForest_actual_095914
  · exact g32p_supplierForest_actual_096027
  · exact g32p_supplierForest_actual_096068
  · exact g32p_supplierForest_actual_096088
  · exact g32p_supplierForest_actual_096169
  · exact g32p_supplierForest_actual_096191
  · exact g32p_supplierForest_actual_096209
  · exact g32p_supplierForest_actual_096362
  · exact g32p_supplierForest_actual_096525
  · exact g32p_supplierForest_actual_096624
  · exact g32p_supplierForest_actual_096752
  · exact g32p_supplierForest_actual_097053
  · exact g32p_supplierForest_actual_097056
  · exact g32p_supplierForest_actual_097180
  · exact g32p_supplierForest_actual_097223
  · exact g32p_supplierForest_actual_097265
  · exact g32p_supplierForest_actual_097411
  · exact g32p_supplierForest_actual_097425
  · exact g32p_supplierForest_actual_097542
  · exact g32p_supplierForest_actual_097878
  · exact g32p_supplierForest_actual_097898
  · exact g32p_supplierForest_actual_097901
  · exact g32p_supplierForest_actual_097968
  · exact g32p_supplierForest_actual_098016
  · exact g32p_supplierForest_actual_098085
  · exact g32p_supplierForest_actual_098171
  · exact g32p_supplierForest_actual_098208
  · exact g32p_supplierForest_actual_098235
  · exact g32p_supplierForest_actual_098241
  · exact g32p_supplierForest_actual_098563
  · exact g32p_supplierForest_actual_098655
  · exact g32p_supplierForest_actual_098754
  · exact g32p_supplierForest_actual_098762
  · exact g32p_supplierForest_actual_099027
  · exact g32p_supplierForest_actual_099251
  · exact g32p_supplierForest_actual_099336
  · exact g32p_supplierForest_actual_099539
  · exact g32p_supplierForest_actual_099666
  · exact g32p_supplierForest_actual_099680
  · exact g32p_supplierForest_actual_099821
  · exact g32p_supplierForest_actual_099916
  · exact g32p_supplierForest_actual_100349
  · exact g32p_supplierForest_actual_100401
  · exact g32p_supplierForest_actual_100407
  · exact g32p_supplierForest_actual_100548
  · exact g32p_supplierForest_actual_100562
  · exact g32p_supplierForest_actual_100598
  · exact g32p_supplierForest_actual_100631
  · exact g32p_supplierForest_actual_100963
  · exact g32p_supplierForest_actual_101034
  · exact g32p_supplierForest_actual_101035
  · exact g32p_supplierForest_actual_101389
  · exact g32p_supplierForest_actual_101592
  · exact g32p_supplierForest_actual_101704
  · exact g32p_supplierForest_actual_101793
  · exact g32p_supplierForest_actual_101889
  · exact g32p_supplierForest_actual_101893
  · exact g32p_supplierForest_actual_101947
  · exact g32p_supplierForest_actual_101956
  · exact g32p_supplierForest_actual_101975
  · exact g32p_supplierForest_actual_102006
  · exact g32p_supplierForest_actual_102240
  · exact g32p_supplierForest_actual_102247
  · exact g32p_supplierForest_actual_102283
  · exact g32p_supplierForest_actual_102285
  · exact g32p_supplierForest_actual_102293
  · exact g32p_supplierForest_actual_102456
  · exact g32p_supplierForest_actual_102483
  · exact g32p_supplierForest_actual_103069
  · exact g32p_supplierForest_actual_103139
  · exact g32p_supplierForest_actual_103179
  · exact g32p_supplierForest_actual_103359
  · exact g32p_supplierForest_actual_103505
  · exact g32p_supplierForest_actual_103618
  · exact g32p_supplierForest_actual_103759
  · exact g32p_supplierForest_actual_103785
  · exact g32p_supplierForest_actual_103954
  · exact g32p_supplierForest_actual_103991
  · exact g32p_supplierForest_actual_104025
  · exact g32p_supplierForest_actual_104144
  · exact g32p_supplierForest_actual_104235
  · exact g32p_supplierForest_actual_104252
  · exact g32p_supplierForest_actual_104376
  · exact g32p_supplierForest_actual_104387
  · exact g32p_supplierForest_actual_104393
  · exact g32p_supplierForest_actual_104423
  · exact g32p_supplierForest_actual_104484
  · exact g32p_supplierForest_actual_104504
  · exact g32p_supplierForest_actual_104506
  · exact g32p_supplierForest_actual_104674
  · exact g32p_supplierForest_actual_104675
  · exact g32p_supplierForest_actual_104679
  · exact g32p_supplierForest_actual_104787
  · exact g32p_supplierForest_actual_104809
  · exact g32p_supplierForest_actual_104970
  · exact g32p_supplierForest_actual_104988
  · exact g32p_supplierForest_actual_105045
  · exact g32p_supplierForest_actual_105326
  · exact g32p_supplierForest_actual_105332
  · exact g32p_supplierForest_actual_105389
  · exact g32p_supplierForest_actual_105407
  · exact g32p_supplierForest_actual_105596
  · exact g32p_supplierForest_actual_105717
  · exact g32p_supplierForest_actual_105727
  · exact g32p_supplierForest_actual_105870
  · exact g32p_supplierForest_actual_105889
  · exact g32p_supplierForest_actual_106246
  · exact g32p_supplierForest_actual_106263
  · exact g32p_supplierForest_actual_106272
  · exact g32p_supplierForest_actual_106338
  · exact g32p_supplierForest_actual_106410
  · exact g32p_supplierForest_actual_106436
  · exact g32p_supplierForest_actual_106504
  · exact g32p_supplierForest_actual_106709
  · exact g32p_supplierForest_actual_106809
  · exact g32p_supplierForest_actual_106924
  · exact g32p_supplierForest_actual_106985
  · exact g32p_supplierForest_actual_107299
  · exact g32p_supplierForest_actual_107393
  · exact g32p_supplierForest_actual_107426
  · exact g32p_supplierForest_actual_107529
  · exact g32p_supplierForest_actual_107537
  · exact g32p_supplierForest_actual_107747
  · exact g32p_supplierForest_actual_107767
  · exact g32p_supplierForest_actual_108015
  · exact g32p_supplierForest_actual_108024
  · exact g32p_supplierForest_actual_108053
  · exact g32p_supplierForest_actual_108059
  · exact g32p_supplierForest_actual_108081
  · exact g32p_supplierForest_actual_108180
  · exact g32p_supplierForest_actual_108334
  · exact g32p_supplierForest_actual_108338
  · exact g32p_supplierForest_actual_108423
  · exact g32p_supplierForest_actual_108439
  · exact g32p_supplierForest_actual_108496
  · exact g32p_supplierForest_actual_108562
  · exact g32p_supplierForest_actual_108591
  · exact g32p_supplierForest_actual_108701
  · exact g32p_supplierForest_actual_108809
  · exact g32p_supplierForest_actual_108887
  · exact g32p_supplierForest_actual_109186
  · exact g32p_supplierForest_actual_109301
  · exact g32p_supplierForest_actual_109336
  · exact g32p_supplierForest_actual_109341
  · exact g32p_supplierForest_actual_109436
  · exact g32p_supplierForest_actual_109646
  · exact g32p_supplierForest_actual_109896
  · exact g32p_supplierForest_actual_109915
  · exact g32p_supplierForest_actual_110308
  · exact g32p_supplierForest_actual_110328
  · exact g32p_supplierForest_actual_110351
  · exact g32p_supplierForest_actual_110364
  · exact g32p_supplierForest_actual_110446
  · exact g32p_supplierForest_actual_110517
  · exact g32p_supplierForest_actual_110653
  · exact g32p_supplierForest_actual_110902
  · exact g32p_supplierForest_actual_111025
  · exact g32p_supplierForest_actual_111330
  · exact g32p_supplierForest_actual_111338
  · exact g32p_supplierForest_actual_111412
  · exact g32p_supplierForest_actual_111426
  · exact g32p_supplierForest_actual_111450

def g32p_supplierForest_nodes_013 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_111474 else g32p_supplierForest_node_111518) else (if i.val < 3 then g32p_supplierForest_node_111699 else g32p_supplierForest_node_111879)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_111959 else g32p_supplierForest_node_112158) else (if i.val < 7 then g32p_supplierForest_node_112227 else g32p_supplierForest_node_112427))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_112696 else g32p_supplierForest_node_112713) else (if i.val < 11 then g32p_supplierForest_node_113017 else g32p_supplierForest_node_113057)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_113152 else g32p_supplierForest_node_113197) else (if i.val < 15 then g32p_supplierForest_node_113220 else g32p_supplierForest_node_113375)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_113442 else g32p_supplierForest_node_113491) else (if i.val < 19 then g32p_supplierForest_node_113559 else g32p_supplierForest_node_113679)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_113732 else g32p_supplierForest_node_113808) else (if i.val < 23 then g32p_supplierForest_node_113993 else g32p_supplierForest_node_114007))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_114018 else g32p_supplierForest_node_114233) else (if i.val < 27 then g32p_supplierForest_node_114255 else g32p_supplierForest_node_114273)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_114318 else g32p_supplierForest_node_114327) else (if i.val < 31 then g32p_supplierForest_node_114333 else g32p_supplierForest_node_114380))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_114784 else g32p_supplierForest_node_115212) else (if i.val < 35 then g32p_supplierForest_node_115224 else g32p_supplierForest_node_115318)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_115395 else g32p_supplierForest_node_115440) else (if i.val < 39 then g32p_supplierForest_node_115602 else g32p_supplierForest_node_115627))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_115676 else g32p_supplierForest_node_115704) else (if i.val < 43 then g32p_supplierForest_node_115799 else g32p_supplierForest_node_115828)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_115851 else g32p_supplierForest_node_116243) else (if i.val < 47 then g32p_supplierForest_node_116290 else g32p_supplierForest_node_116707)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_116776 else g32p_supplierForest_node_116915) else (if i.val < 51 then g32p_supplierForest_node_116927 else g32p_supplierForest_node_117096)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_117156 else g32p_supplierForest_node_117162) else (if i.val < 55 then g32p_supplierForest_node_117412 else g32p_supplierForest_node_117469))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_117744 else g32p_supplierForest_node_117843) else (if i.val < 59 then g32p_supplierForest_node_117916 else g32p_supplierForest_node_118024)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_118167 else g32p_supplierForest_node_118253) else (if i.val < 63 then g32p_supplierForest_node_118364 else g32p_supplierForest_node_118560)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_118982 else g32p_supplierForest_node_119068) else (if i.val < 67 then g32p_supplierForest_node_119120 else g32p_supplierForest_node_119126)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_119339 else g32p_supplierForest_node_119385) else (if i.val < 71 then g32p_supplierForest_node_119519 else g32p_supplierForest_node_119564))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_119565 else g32p_supplierForest_node_119619) else (if i.val < 75 then g32p_supplierForest_node_119698 else g32p_supplierForest_node_119760)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_119786 else g32p_supplierForest_node_119830) else (if i.val < 79 then g32p_supplierForest_node_119856 else g32p_supplierForest_node_119962)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_119976 else g32p_supplierForest_node_120276) else (if i.val < 83 then g32p_supplierForest_node_120537 else g32p_supplierForest_node_120805)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_120895 else g32p_supplierForest_node_120903) else (if i.val < 87 then g32p_supplierForest_node_121212 else g32p_supplierForest_node_121452))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_121569 else g32p_supplierForest_node_121623) else (if i.val < 91 then g32p_supplierForest_node_121862 else g32p_supplierForest_node_121877)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_121891 else g32p_supplierForest_node_121910) else (if i.val < 95 then g32p_supplierForest_node_122119 else g32p_supplierForest_node_122224))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_122439 else g32p_supplierForest_node_122451) else (if i.val < 99 then g32p_supplierForest_node_122494 else g32p_supplierForest_node_122573)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_122631 else g32p_supplierForest_node_122645) else (if i.val < 103 then g32p_supplierForest_node_122676 else g32p_supplierForest_node_122805))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_122859 else g32p_supplierForest_node_122900) else (if i.val < 107 then g32p_supplierForest_node_122905 else g32p_supplierForest_node_122921)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_122963 else g32p_supplierForest_node_123263) else (if i.val < 111 then g32p_supplierForest_node_123437 else g32p_supplierForest_node_123561)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_123647 else g32p_supplierForest_node_123800) else (if i.val < 115 then g32p_supplierForest_node_123934 else g32p_supplierForest_node_123963)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_123979 else g32p_supplierForest_node_124062) else (if i.val < 119 then g32p_supplierForest_node_124067 else g32p_supplierForest_node_124186))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_124224 else g32p_supplierForest_node_124303) else (if i.val < 123 then g32p_supplierForest_node_124477 else g32p_supplierForest_node_124637)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_124759 else g32p_supplierForest_node_124845) else (if i.val < 127 then g32p_supplierForest_node_125031 else g32p_supplierForest_node_125090))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_125375 else g32p_supplierForest_node_125456) else (if i.val < 131 then g32p_supplierForest_node_125504 else g32p_supplierForest_node_125523)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_125712 else g32p_supplierForest_node_125717) else (if i.val < 135 then g32p_supplierForest_node_125800 else g32p_supplierForest_node_125823))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_125848 else g32p_supplierForest_node_125936) else (if i.val < 139 then g32p_supplierForest_node_126026 else g32p_supplierForest_node_126083)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_126087 else g32p_supplierForest_node_126155) else (if i.val < 143 then g32p_supplierForest_node_126220 else g32p_supplierForest_node_126372)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_126445 else g32p_supplierForest_node_126527) else (if i.val < 147 then g32p_supplierForest_node_126543 else g32p_supplierForest_node_126639)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_126709 else g32p_supplierForest_node_126975) else (if i.val < 151 then g32p_supplierForest_node_126984 else g32p_supplierForest_node_127106))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_127244 else g32p_supplierForest_node_127331) else (if i.val < 155 then g32p_supplierForest_node_127338 else g32p_supplierForest_node_127366)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_127386 else g32p_supplierForest_node_127391) else (if i.val < 159 then g32p_supplierForest_node_127432 else g32p_supplierForest_node_127446))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_127505 else g32p_supplierForest_node_127541) else (if i.val < 163 then g32p_supplierForest_node_127588 else g32p_supplierForest_node_127713)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_127735 else g32p_supplierForest_node_127853) else (if i.val < 167 then g32p_supplierForest_node_127901 else g32p_supplierForest_node_128034))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_128088 else g32p_supplierForest_node_128368) else (if i.val < 171 then g32p_supplierForest_node_128378 else g32p_supplierForest_node_128892)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_129036 else g32p_supplierForest_node_129104) else (if i.val < 175 then g32p_supplierForest_node_129284 else g32p_supplierForest_node_129297)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_129356 else g32p_supplierForest_node_129384) else (if i.val < 179 then g32p_supplierForest_node_129446 else g32p_supplierForest_node_129527)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_129539 else g32p_supplierForest_node_129565) else (if i.val < 183 then g32p_supplierForest_node_129870 else g32p_supplierForest_node_129971))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_130018 else g32p_supplierForest_node_130411) else (if i.val < 187 then g32p_supplierForest_node_130437 else g32p_supplierForest_node_130493)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_130528 else g32p_supplierForest_node_130535) else (if i.val < 191 then g32p_supplierForest_node_130570 else g32p_supplierForest_node_130829)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_130842 else g32p_supplierForest_node_130857) else (if i.val < 195 then g32p_supplierForest_node_130909 else g32p_supplierForest_node_130967)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_131019 else g32p_supplierForest_node_131022) else (if i.val < 199 then g32p_supplierForest_node_131232 else g32p_supplierForest_node_131424))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_131433 else g32p_supplierForest_node_131437) else (if i.val < 203 then g32p_supplierForest_node_131834 else g32p_supplierForest_node_131859)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_131860 else g32p_supplierForest_node_131958) else (if i.val < 207 then g32p_supplierForest_node_132015 else g32p_supplierForest_node_132045)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_132093 else g32p_supplierForest_node_132095) else (if i.val < 211 then g32p_supplierForest_node_132099 else g32p_supplierForest_node_132139)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_132320 else g32p_supplierForest_node_132463) else (if i.val < 215 then g32p_supplierForest_node_132582 else g32p_supplierForest_node_132682))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_132797 else g32p_supplierForest_node_132862) else (if i.val < 219 then g32p_supplierForest_node_132865 else g32p_supplierForest_node_132872)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_132909 else g32p_supplierForest_node_132966) else (if i.val < 223 then g32p_supplierForest_node_133164 else g32p_supplierForest_node_133180))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_133181 else g32p_supplierForest_node_133265) else (if i.val < 227 then g32p_supplierForest_node_133345 else g32p_supplierForest_node_133352)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_133605 else g32p_supplierForest_node_133642) else (if i.val < 231 then g32p_supplierForest_node_133804 else g32p_supplierForest_node_133839))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_133876 else g32p_supplierForest_node_133889) else (if i.val < 235 then g32p_supplierForest_node_133919 else g32p_supplierForest_node_133974)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_133997 else g32p_supplierForest_node_134042) else (if i.val < 239 then g32p_supplierForest_node_134065 else g32p_supplierForest_node_134069)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_134142 else g32p_supplierForest_node_134476) else (if i.val < 243 then g32p_supplierForest_node_134521 else g32p_supplierForest_node_134740)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_134752 else g32p_supplierForest_node_134807) else (if i.val < 247 then g32p_supplierForest_node_134821 else g32p_supplierForest_node_135003))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_135243 else g32p_supplierForest_node_135289) else (if i.val < 251 then g32p_supplierForest_node_135666 else g32p_supplierForest_node_135691)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_135766 else g32p_supplierForest_node_135773) else (if i.val < 255 then g32p_supplierForest_node_135874 else g32p_supplierForest_node_135917))))))))

def g32p_supplierForest_classes_013 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 62 else 30) else (if i.val < 3 then 62 else 66)) else (if i.val < 6 then (if i.val < 5 then 66 else 61) else (if i.val < 7 then 61 else 62))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 29 else 59) else (if i.val < 11 then 60 else 57)) else (if i.val < 14 then (if i.val < 13 then 61 else 61) else (if i.val < 15 then 65 else 60)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 59 else 59) else (if i.val < 19 then 66 else 60)) else (if i.val < 22 then (if i.val < 21 then 61 else 61) else (if i.val < 23 then 33 else 62))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 66 else 58) else (if i.val < 27 then 60 else 60)) else (if i.val < 30 then (if i.val < 29 then 63 else 36) else (if i.val < 31 then 66 else 59))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 92 else 62) else (if i.val < 35 then 60 else 60)) else (if i.val < 38 then (if i.val < 37 then 57 else 61) else (if i.val < 39 then 59 else 59))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 89 else 89) else (if i.val < 43 then 91 else 91)) else (if i.val < 46 then (if i.val < 45 then 92 else 66) else (if i.val < 47 then 58 else 66)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 61 else 61) else (if i.val < 51 then 36 else 91)) else (if i.val < 54 then (if i.val < 53 then 30 else 92) else (if i.val < 55 then 65 else 66))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 33 else 89) else (if i.val < 59 then 58 else 30)) else (if i.val < 62 then (if i.val < 61 then 89 else 90) else (if i.val < 63 then 14 else 62)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 65 else 93) else (if i.val < 67 then 66 else 58)) else (if i.val < 70 then (if i.val < 69 then 66 else 60) else (if i.val < 71 then 62 else 35))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 60 else 35) else (if i.val < 75 then 62 else 36)) else (if i.val < 78 then (if i.val < 77 then 90 else 91) else (if i.val < 79 then 92 else 92)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 35 else 60) else (if i.val < 83 then 66 else 66)) else (if i.val < 86 then (if i.val < 85 then 91 else 35) else (if i.val < 87 then 91 else 66))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 58 else 62) else (if i.val < 91 then 92 else 91)) else (if i.val < 94 then (if i.val < 93 then 36 else 66) else (if i.val < 95 then 90 else 91))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 65 else 88) else (if i.val < 99 then 60 else 62)) else (if i.val < 102 then (if i.val < 101 then 91 else 92) else (if i.val < 103 then 60 else 93))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 63 else 91) else (if i.val < 107 then 29 else 35)) else (if i.val < 110 then (if i.val < 109 then 92 else 62) else (if i.val < 111 then 60 else 62)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 61 else 61) else (if i.val < 115 then 60 else 62)) else (if i.val < 118 then (if i.val < 117 then 61 else 91) else (if i.val < 119 then 35 else 29))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 61 else 92) else (if i.val < 123 then 61 else 58)) else (if i.val < 126 then (if i.val < 125 then 90 else 90) else (if i.val < 127 then 61 else 88))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 35 else 92) else (if i.val < 131 then 91 else 89)) else (if i.val < 134 then (if i.val < 133 then 89 else 58) else (if i.val < 135 then 90 else 29))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 91 else 92) else (if i.val < 139 then 57 else 63)) else (if i.val < 142 then (if i.val < 141 then 60 else 59) else (if i.val < 143 then 91 else 62)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 90 else 92) else (if i.val < 147 then 91 else 93)) else (if i.val < 150 then (if i.val < 149 then 92 else 87) else (if i.val < 151 then 87 else 90))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 35 else 90) else (if i.val < 155 then 90 else 91)) else (if i.val < 158 then (if i.val < 157 then 92 else 30) else (if i.val < 159 then 35 else 92))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 36 else 89) else (if i.val < 163 then 91 else 90)) else (if i.val < 166 then (if i.val < 165 then 35 else 77) else (if i.val < 167 then 71 else 70))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 77 else 42) else (if i.val < 171 then 71 else 43)) else (if i.val < 174 then (if i.val < 173 then 70 else 68) else (if i.val < 175 then 68 else 41)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 38 else 74) else (if i.val < 179 then 94 else 73)) else (if i.val < 182 then (if i.val < 181 then 68 else 71) else (if i.val < 183 then 68 else 73))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 73 else 71) else (if i.val < 187 then 77 else 78)) else (if i.val < 190 then (if i.val < 189 then 74 else 73) else (if i.val < 191 then 72 else 18)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 69 else 71) else (if i.val < 195 then 74 else 43)) else (if i.val < 198 then (if i.val < 197 then 68 else 73) else (if i.val < 199 then 42 else 38))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 42 else 42) else (if i.val < 203 then 73 else 71)) else (if i.val < 206 then (if i.val < 205 then 71 else 72) else (if i.val < 207 then 79 else 73)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 18 else 38) else (if i.val < 211 then 68 else 42)) else (if i.val < 214 then (if i.val < 213 then 94 else 71) else (if i.val < 215 then 94 else 79))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 77 else 71) else (if i.val < 219 then 77 else 71)) else (if i.val < 222 then (if i.val < 221 then 94 else 94) else (if i.val < 223 then 74 else 77))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 75 else 73) else (if i.val < 227 then 77 else 77)) else (if i.val < 230 then (if i.val < 229 then 74 else 73) else (if i.val < 231 then 72 else 95))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 70 else 74) else (if i.val < 235 then 95 else 94)) else (if i.val < 238 then (if i.val < 237 then 68 else 73) else (if i.val < 239 then 71 else 71)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 73 else 43) else (if i.val < 243 then 71 else 71)) else (if i.val < 246 then (if i.val < 245 then 95 else 73) else (if i.val < 247 then 94 else 69))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 43 else 41) else (if i.val < 251 then 18 else 71)) else (if i.val < 254 then (if i.val < 253 then 73 else 69) else (if i.val < 255 then 75 else 73))))))))

theorem g32p_supplierForest_actual_013 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_013 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_013 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_111474
  · exact g32p_supplierForest_actual_111518
  · exact g32p_supplierForest_actual_111699
  · exact g32p_supplierForest_actual_111879
  · exact g32p_supplierForest_actual_111959
  · exact g32p_supplierForest_actual_112158
  · exact g32p_supplierForest_actual_112227
  · exact g32p_supplierForest_actual_112427
  · exact g32p_supplierForest_actual_112696
  · exact g32p_supplierForest_actual_112713
  · exact g32p_supplierForest_actual_113017
  · exact g32p_supplierForest_actual_113057
  · exact g32p_supplierForest_actual_113152
  · exact g32p_supplierForest_actual_113197
  · exact g32p_supplierForest_actual_113220
  · exact g32p_supplierForest_actual_113375
  · exact g32p_supplierForest_actual_113442
  · exact g32p_supplierForest_actual_113491
  · exact g32p_supplierForest_actual_113559
  · exact g32p_supplierForest_actual_113679
  · exact g32p_supplierForest_actual_113732
  · exact g32p_supplierForest_actual_113808
  · exact g32p_supplierForest_actual_113993
  · exact g32p_supplierForest_actual_114007
  · exact g32p_supplierForest_actual_114018
  · exact g32p_supplierForest_actual_114233
  · exact g32p_supplierForest_actual_114255
  · exact g32p_supplierForest_actual_114273
  · exact g32p_supplierForest_actual_114318
  · exact g32p_supplierForest_actual_114327
  · exact g32p_supplierForest_actual_114333
  · exact g32p_supplierForest_actual_114380
  · exact g32p_supplierForest_actual_114784
  · exact g32p_supplierForest_actual_115212
  · exact g32p_supplierForest_actual_115224
  · exact g32p_supplierForest_actual_115318
  · exact g32p_supplierForest_actual_115395
  · exact g32p_supplierForest_actual_115440
  · exact g32p_supplierForest_actual_115602
  · exact g32p_supplierForest_actual_115627
  · exact g32p_supplierForest_actual_115676
  · exact g32p_supplierForest_actual_115704
  · exact g32p_supplierForest_actual_115799
  · exact g32p_supplierForest_actual_115828
  · exact g32p_supplierForest_actual_115851
  · exact g32p_supplierForest_actual_116243
  · exact g32p_supplierForest_actual_116290
  · exact g32p_supplierForest_actual_116707
  · exact g32p_supplierForest_actual_116776
  · exact g32p_supplierForest_actual_116915
  · exact g32p_supplierForest_actual_116927
  · exact g32p_supplierForest_actual_117096
  · exact g32p_supplierForest_actual_117156
  · exact g32p_supplierForest_actual_117162
  · exact g32p_supplierForest_actual_117412
  · exact g32p_supplierForest_actual_117469
  · exact g32p_supplierForest_actual_117744
  · exact g32p_supplierForest_actual_117843
  · exact g32p_supplierForest_actual_117916
  · exact g32p_supplierForest_actual_118024
  · exact g32p_supplierForest_actual_118167
  · exact g32p_supplierForest_actual_118253
  · exact g32p_supplierForest_actual_118364
  · exact g32p_supplierForest_actual_118560
  · exact g32p_supplierForest_actual_118982
  · exact g32p_supplierForest_actual_119068
  · exact g32p_supplierForest_actual_119120
  · exact g32p_supplierForest_actual_119126
  · exact g32p_supplierForest_actual_119339
  · exact g32p_supplierForest_actual_119385
  · exact g32p_supplierForest_actual_119519
  · exact g32p_supplierForest_actual_119564
  · exact g32p_supplierForest_actual_119565
  · exact g32p_supplierForest_actual_119619
  · exact g32p_supplierForest_actual_119698
  · exact g32p_supplierForest_actual_119760
  · exact g32p_supplierForest_actual_119786
  · exact g32p_supplierForest_actual_119830
  · exact g32p_supplierForest_actual_119856
  · exact g32p_supplierForest_actual_119962
  · exact g32p_supplierForest_actual_119976
  · exact g32p_supplierForest_actual_120276
  · exact g32p_supplierForest_actual_120537
  · exact g32p_supplierForest_actual_120805
  · exact g32p_supplierForest_actual_120895
  · exact g32p_supplierForest_actual_120903
  · exact g32p_supplierForest_actual_121212
  · exact g32p_supplierForest_actual_121452
  · exact g32p_supplierForest_actual_121569
  · exact g32p_supplierForest_actual_121623
  · exact g32p_supplierForest_actual_121862
  · exact g32p_supplierForest_actual_121877
  · exact g32p_supplierForest_actual_121891
  · exact g32p_supplierForest_actual_121910
  · exact g32p_supplierForest_actual_122119
  · exact g32p_supplierForest_actual_122224
  · exact g32p_supplierForest_actual_122439
  · exact g32p_supplierForest_actual_122451
  · exact g32p_supplierForest_actual_122494
  · exact g32p_supplierForest_actual_122573
  · exact g32p_supplierForest_actual_122631
  · exact g32p_supplierForest_actual_122645
  · exact g32p_supplierForest_actual_122676
  · exact g32p_supplierForest_actual_122805
  · exact g32p_supplierForest_actual_122859
  · exact g32p_supplierForest_actual_122900
  · exact g32p_supplierForest_actual_122905
  · exact g32p_supplierForest_actual_122921
  · exact g32p_supplierForest_actual_122963
  · exact g32p_supplierForest_actual_123263
  · exact g32p_supplierForest_actual_123437
  · exact g32p_supplierForest_actual_123561
  · exact g32p_supplierForest_actual_123647
  · exact g32p_supplierForest_actual_123800
  · exact g32p_supplierForest_actual_123934
  · exact g32p_supplierForest_actual_123963
  · exact g32p_supplierForest_actual_123979
  · exact g32p_supplierForest_actual_124062
  · exact g32p_supplierForest_actual_124067
  · exact g32p_supplierForest_actual_124186
  · exact g32p_supplierForest_actual_124224
  · exact g32p_supplierForest_actual_124303
  · exact g32p_supplierForest_actual_124477
  · exact g32p_supplierForest_actual_124637
  · exact g32p_supplierForest_actual_124759
  · exact g32p_supplierForest_actual_124845
  · exact g32p_supplierForest_actual_125031
  · exact g32p_supplierForest_actual_125090
  · exact g32p_supplierForest_actual_125375
  · exact g32p_supplierForest_actual_125456
  · exact g32p_supplierForest_actual_125504
  · exact g32p_supplierForest_actual_125523
  · exact g32p_supplierForest_actual_125712
  · exact g32p_supplierForest_actual_125717
  · exact g32p_supplierForest_actual_125800
  · exact g32p_supplierForest_actual_125823
  · exact g32p_supplierForest_actual_125848
  · exact g32p_supplierForest_actual_125936
  · exact g32p_supplierForest_actual_126026
  · exact g32p_supplierForest_actual_126083
  · exact g32p_supplierForest_actual_126087
  · exact g32p_supplierForest_actual_126155
  · exact g32p_supplierForest_actual_126220
  · exact g32p_supplierForest_actual_126372
  · exact g32p_supplierForest_actual_126445
  · exact g32p_supplierForest_actual_126527
  · exact g32p_supplierForest_actual_126543
  · exact g32p_supplierForest_actual_126639
  · exact g32p_supplierForest_actual_126709
  · exact g32p_supplierForest_actual_126975
  · exact g32p_supplierForest_actual_126984
  · exact g32p_supplierForest_actual_127106
  · exact g32p_supplierForest_actual_127244
  · exact g32p_supplierForest_actual_127331
  · exact g32p_supplierForest_actual_127338
  · exact g32p_supplierForest_actual_127366
  · exact g32p_supplierForest_actual_127386
  · exact g32p_supplierForest_actual_127391
  · exact g32p_supplierForest_actual_127432
  · exact g32p_supplierForest_actual_127446
  · exact g32p_supplierForest_actual_127505
  · exact g32p_supplierForest_actual_127541
  · exact g32p_supplierForest_actual_127588
  · exact g32p_supplierForest_actual_127713
  · exact g32p_supplierForest_actual_127735
  · exact g32p_supplierForest_actual_127853
  · exact g32p_supplierForest_actual_127901
  · exact g32p_supplierForest_actual_128034
  · exact g32p_supplierForest_actual_128088
  · exact g32p_supplierForest_actual_128368
  · exact g32p_supplierForest_actual_128378
  · exact g32p_supplierForest_actual_128892
  · exact g32p_supplierForest_actual_129036
  · exact g32p_supplierForest_actual_129104
  · exact g32p_supplierForest_actual_129284
  · exact g32p_supplierForest_actual_129297
  · exact g32p_supplierForest_actual_129356
  · exact g32p_supplierForest_actual_129384
  · exact g32p_supplierForest_actual_129446
  · exact g32p_supplierForest_actual_129527
  · exact g32p_supplierForest_actual_129539
  · exact g32p_supplierForest_actual_129565
  · exact g32p_supplierForest_actual_129870
  · exact g32p_supplierForest_actual_129971
  · exact g32p_supplierForest_actual_130018
  · exact g32p_supplierForest_actual_130411
  · exact g32p_supplierForest_actual_130437
  · exact g32p_supplierForest_actual_130493
  · exact g32p_supplierForest_actual_130528
  · exact g32p_supplierForest_actual_130535
  · exact g32p_supplierForest_actual_130570
  · exact g32p_supplierForest_actual_130829
  · exact g32p_supplierForest_actual_130842
  · exact g32p_supplierForest_actual_130857
  · exact g32p_supplierForest_actual_130909
  · exact g32p_supplierForest_actual_130967
  · exact g32p_supplierForest_actual_131019
  · exact g32p_supplierForest_actual_131022
  · exact g32p_supplierForest_actual_131232
  · exact g32p_supplierForest_actual_131424
  · exact g32p_supplierForest_actual_131433
  · exact g32p_supplierForest_actual_131437
  · exact g32p_supplierForest_actual_131834
  · exact g32p_supplierForest_actual_131859
  · exact g32p_supplierForest_actual_131860
  · exact g32p_supplierForest_actual_131958
  · exact g32p_supplierForest_actual_132015
  · exact g32p_supplierForest_actual_132045
  · exact g32p_supplierForest_actual_132093
  · exact g32p_supplierForest_actual_132095
  · exact g32p_supplierForest_actual_132099
  · exact g32p_supplierForest_actual_132139
  · exact g32p_supplierForest_actual_132320
  · exact g32p_supplierForest_actual_132463
  · exact g32p_supplierForest_actual_132582
  · exact g32p_supplierForest_actual_132682
  · exact g32p_supplierForest_actual_132797
  · exact g32p_supplierForest_actual_132862
  · exact g32p_supplierForest_actual_132865
  · exact g32p_supplierForest_actual_132872
  · exact g32p_supplierForest_actual_132909
  · exact g32p_supplierForest_actual_132966
  · exact g32p_supplierForest_actual_133164
  · exact g32p_supplierForest_actual_133180
  · exact g32p_supplierForest_actual_133181
  · exact g32p_supplierForest_actual_133265
  · exact g32p_supplierForest_actual_133345
  · exact g32p_supplierForest_actual_133352
  · exact g32p_supplierForest_actual_133605
  · exact g32p_supplierForest_actual_133642
  · exact g32p_supplierForest_actual_133804
  · exact g32p_supplierForest_actual_133839
  · exact g32p_supplierForest_actual_133876
  · exact g32p_supplierForest_actual_133889
  · exact g32p_supplierForest_actual_133919
  · exact g32p_supplierForest_actual_133974
  · exact g32p_supplierForest_actual_133997
  · exact g32p_supplierForest_actual_134042
  · exact g32p_supplierForest_actual_134065
  · exact g32p_supplierForest_actual_134069
  · exact g32p_supplierForest_actual_134142
  · exact g32p_supplierForest_actual_134476
  · exact g32p_supplierForest_actual_134521
  · exact g32p_supplierForest_actual_134740
  · exact g32p_supplierForest_actual_134752
  · exact g32p_supplierForest_actual_134807
  · exact g32p_supplierForest_actual_134821
  · exact g32p_supplierForest_actual_135003
  · exact g32p_supplierForest_actual_135243
  · exact g32p_supplierForest_actual_135289
  · exact g32p_supplierForest_actual_135666
  · exact g32p_supplierForest_actual_135691
  · exact g32p_supplierForest_actual_135766
  · exact g32p_supplierForest_actual_135773
  · exact g32p_supplierForest_actual_135874
  · exact g32p_supplierForest_actual_135917

def g32p_supplierForest_nodes_014 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_136144 else g32p_supplierForest_node_136413) else (if i.val < 3 then g32p_supplierForest_node_136426 else g32p_supplierForest_node_136453)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_136479 else g32p_supplierForest_node_136518) else (if i.val < 7 then g32p_supplierForest_node_136544 else g32p_supplierForest_node_136598))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_136776 else g32p_supplierForest_node_136858) else (if i.val < 11 then g32p_supplierForest_node_136988 else g32p_supplierForest_node_137065)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_137104 else g32p_supplierForest_node_137209) else (if i.val < 15 then g32p_supplierForest_node_137494 else g32p_supplierForest_node_137562)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_137589 else g32p_supplierForest_node_137668) else (if i.val < 19 then g32p_supplierForest_node_137694 else g32p_supplierForest_node_137697)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_137753 else g32p_supplierForest_node_137756) else (if i.val < 23 then g32p_supplierForest_node_137993 else g32p_supplierForest_node_138049))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_138369 else g32p_supplierForest_node_138386) else (if i.val < 27 then g32p_supplierForest_node_138482 else g32p_supplierForest_node_138538)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_138641 else g32p_supplierForest_node_138779) else (if i.val < 31 then g32p_supplierForest_node_138828 else g32p_supplierForest_node_138851))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_138863 else g32p_supplierForest_node_138940) else (if i.val < 35 then g32p_supplierForest_node_138965 else g32p_supplierForest_node_138996)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_139008 else g32p_supplierForest_node_139075) else (if i.val < 39 then g32p_supplierForest_node_139225 else g32p_supplierForest_node_139335))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_139348 else g32p_supplierForest_node_139350) else (if i.val < 43 then g32p_supplierForest_node_139445 else g32p_supplierForest_node_139573)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_139665 else g32p_supplierForest_node_139697) else (if i.val < 47 then g32p_supplierForest_node_139713 else g32p_supplierForest_node_139732)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_139807 else g32p_supplierForest_node_139809) else (if i.val < 51 then g32p_supplierForest_node_140014 else g32p_supplierForest_node_140193)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_140216 else g32p_supplierForest_node_140507) else (if i.val < 55 then g32p_supplierForest_node_140549 else g32p_supplierForest_node_140574))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_140616 else g32p_supplierForest_node_140626) else (if i.val < 59 then g32p_supplierForest_node_140696 else g32p_supplierForest_node_140760)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_140901 else g32p_supplierForest_node_140973) else (if i.val < 63 then g32p_supplierForest_node_141061 else g32p_supplierForest_node_141253)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_141392 else g32p_supplierForest_node_141423) else (if i.val < 67 then g32p_supplierForest_node_141578 else g32p_supplierForest_node_141595)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_141701 else g32p_supplierForest_node_142006) else (if i.val < 71 then g32p_supplierForest_node_142040 else g32p_supplierForest_node_142126))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_142204 else g32p_supplierForest_node_142237) else (if i.val < 75 then g32p_supplierForest_node_142430 else g32p_supplierForest_node_142441)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_142623 else g32p_supplierForest_node_142727) else (if i.val < 79 then g32p_supplierForest_node_142882 else g32p_supplierForest_node_143010)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_143104 else g32p_supplierForest_node_143188) else (if i.val < 83 then g32p_supplierForest_node_143261 else g32p_supplierForest_node_143407)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_143445 else g32p_supplierForest_node_143458) else (if i.val < 87 then g32p_supplierForest_node_143472 else g32p_supplierForest_node_143506))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_143526 else g32p_supplierForest_node_143711) else (if i.val < 91 then g32p_supplierForest_node_143769 else g32p_supplierForest_node_143801)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_144197 else g32p_supplierForest_node_144262) else (if i.val < 95 then g32p_supplierForest_node_144310 else g32p_supplierForest_node_144317))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_144351 else g32p_supplierForest_node_144359) else (if i.val < 99 then g32p_supplierForest_node_144407 else g32p_supplierForest_node_144413)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_144469 else g32p_supplierForest_node_144818) else (if i.val < 103 then g32p_supplierForest_node_144822 else g32p_supplierForest_node_145409))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_145720 else g32p_supplierForest_node_145901) else (if i.val < 107 then g32p_supplierForest_node_145916 else g32p_supplierForest_node_145951)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_146173 else g32p_supplierForest_node_146355) else (if i.val < 111 then g32p_supplierForest_node_146434 else g32p_supplierForest_node_146458)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_146487 else g32p_supplierForest_node_146518) else (if i.val < 115 then g32p_supplierForest_node_146544 else g32p_supplierForest_node_146584)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_146684 else g32p_supplierForest_node_146781) else (if i.val < 119 then g32p_supplierForest_node_146792 else g32p_supplierForest_node_146961))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_146962 else g32p_supplierForest_node_147030) else (if i.val < 123 then g32p_supplierForest_node_147121 else g32p_supplierForest_node_147333)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_147490 else g32p_supplierForest_node_147641) else (if i.val < 127 then g32p_supplierForest_node_147662 else g32p_supplierForest_node_148028))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_148049 else g32p_supplierForest_node_148064) else (if i.val < 131 then g32p_supplierForest_node_148065 else g32p_supplierForest_node_148437)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_148722 else g32p_supplierForest_node_148790) else (if i.val < 135 then g32p_supplierForest_node_148862 else g32p_supplierForest_node_148965))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_149201 else g32p_supplierForest_node_149334) else (if i.val < 139 then g32p_supplierForest_node_149348 else g32p_supplierForest_node_149509)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_149607 else g32p_supplierForest_node_149815) else (if i.val < 143 then g32p_supplierForest_node_149912 else g32p_supplierForest_node_149914)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_150176 else g32p_supplierForest_node_150228) else (if i.val < 147 then g32p_supplierForest_node_150378 else g32p_supplierForest_node_150399)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_150607 else g32p_supplierForest_node_150647) else (if i.val < 151 then g32p_supplierForest_node_150763 else g32p_supplierForest_node_150872))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_150925 else g32p_supplierForest_node_151053) else (if i.val < 155 then g32p_supplierForest_node_151054 else g32p_supplierForest_node_151084)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_151236 else g32p_supplierForest_node_151243) else (if i.val < 159 then g32p_supplierForest_node_151340 else g32p_supplierForest_node_151454))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_151492 else g32p_supplierForest_node_151529) else (if i.val < 163 then g32p_supplierForest_node_151531 else g32p_supplierForest_node_151657)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_151780 else g32p_supplierForest_node_151924) else (if i.val < 167 then g32p_supplierForest_node_152067 else g32p_supplierForest_node_152105))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_152127 else g32p_supplierForest_node_152175) else (if i.val < 171 then g32p_supplierForest_node_152210 else g32p_supplierForest_node_152225)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_152306 else g32p_supplierForest_node_152313) else (if i.val < 175 then g32p_supplierForest_node_152472 else g32p_supplierForest_node_152475)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_152498 else g32p_supplierForest_node_152591) else (if i.val < 179 then g32p_supplierForest_node_152700 else g32p_supplierForest_node_152755)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_153085 else g32p_supplierForest_node_153094) else (if i.val < 183 then g32p_supplierForest_node_153103 else g32p_supplierForest_node_153130))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_153170 else g32p_supplierForest_node_153458) else (if i.val < 187 then g32p_supplierForest_node_153560 else g32p_supplierForest_node_153727)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_153808 else g32p_supplierForest_node_153915) else (if i.val < 191 then g32p_supplierForest_node_154019 else g32p_supplierForest_node_154248)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_154311 else g32p_supplierForest_node_154335) else (if i.val < 195 then g32p_supplierForest_node_154343 else g32p_supplierForest_node_154372)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_154379 else g32p_supplierForest_node_154437) else (if i.val < 199 then g32p_supplierForest_node_154542 else g32p_supplierForest_node_154565))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_154782 else g32p_supplierForest_node_154854) else (if i.val < 203 then g32p_supplierForest_node_154933 else g32p_supplierForest_node_154939)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_154956 else g32p_supplierForest_node_155011) else (if i.val < 207 then g32p_supplierForest_node_155082 else g32p_supplierForest_node_155136)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_155169 else g32p_supplierForest_node_155177) else (if i.val < 211 then g32p_supplierForest_node_155195 else g32p_supplierForest_node_155208)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_155245 else g32p_supplierForest_node_155250) else (if i.val < 215 then g32p_supplierForest_node_155253 else g32p_supplierForest_node_155269))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_155294 else g32p_supplierForest_node_155312) else (if i.val < 219 then g32p_supplierForest_node_155317 else g32p_supplierForest_node_155325)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_155346 else g32p_supplierForest_node_155405) else (if i.val < 223 then g32p_supplierForest_node_155456 else g32p_supplierForest_node_155471))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_155472 else g32p_supplierForest_node_155474) else (if i.val < 227 then g32p_supplierForest_node_155486 else g32p_supplierForest_node_155496)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_155507 else g32p_supplierForest_node_155510) else (if i.val < 231 then g32p_supplierForest_node_000013 else g32p_supplierForest_node_000023))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_000027 else g32p_supplierForest_node_000031) else (if i.val < 235 then g32p_supplierForest_node_000045 else g32p_supplierForest_node_000115)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_000138 else g32p_supplierForest_node_000141) else (if i.val < 239 then g32p_supplierForest_node_000195 else g32p_supplierForest_node_000250)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_000297 else g32p_supplierForest_node_000319) else (if i.val < 243 then g32p_supplierForest_node_000320 else g32p_supplierForest_node_000323)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_000381 else g32p_supplierForest_node_000453) else (if i.val < 247 then g32p_supplierForest_node_000509 else g32p_supplierForest_node_000520))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_000529 else g32p_supplierForest_node_000554) else (if i.val < 251 then g32p_supplierForest_node_000577 else g32p_supplierForest_node_000592)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_000603 else g32p_supplierForest_node_000611) else (if i.val < 255 then g32p_supplierForest_node_000613 else g32p_supplierForest_node_000635))))))))

def g32p_supplierForest_classes_014 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 42 else 73) else (if i.val < 3 then 72 else 69)) else (if i.val < 6 then (if i.val < 5 then 73 else 72) else (if i.val < 7 then 73 else 79))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 77 else 79) else (if i.val < 11 then 74 else 78)) else (if i.val < 14 then (if i.val < 13 then 77 else 68) else (if i.val < 15 then 68 else 70)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 94 else 20) else (if i.val < 19 then 74 else 72)) else (if i.val < 22 then (if i.val < 21 then 74 else 73) else (if i.val < 23 then 73 else 79))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 74 else 95) else (if i.val < 27 then 78 else 74)) else (if i.val < 30 then (if i.val < 29 then 74 else 38) else (if i.val < 31 then 71 else 42))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 69 else 71) else (if i.val < 35 then 73 else 94)) else (if i.val < 38 then (if i.val < 37 then 78 else 95) else (if i.val < 39 then 78 else 94))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 73 else 38) else (if i.val < 43 then 38 else 42)) else (if i.val < 46 then (if i.val < 45 then 79 else 78) else (if i.val < 47 then 78 else 78)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 68 else 73) else (if i.val < 51 then 94 else 79)) else (if i.val < 54 then (if i.val < 53 then 43 else 94) else (if i.val < 55 then 78 else 73))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 73 else 77) else (if i.val < 59 then 42 else 78)) else (if i.val < 62 then (if i.val < 61 then 79 else 95) else (if i.val < 63 then 73 else 73)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 43 else 94) else (if i.val < 67 then 78 else 94)) else (if i.val < 70 then (if i.val < 69 then 95 else 72) else (if i.val < 71 then 78 else 72))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 79 else 42) else (if i.val < 75 then 94 else 69)) else (if i.val < 78 then (if i.val < 77 then 73 else 73) else (if i.val < 79 then 73 else 42)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 78 else 78) else (if i.val < 83 then 94 else 94)) else (if i.val < 86 then (if i.val < 85 then 79 else 78) else (if i.val < 87 then 75 else 78))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 69 else 75) else (if i.val < 91 then 73 else 78)) else (if i.val < 94 then (if i.val < 93 then 94 else 94) else (if i.val < 95 then 71 else 78))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 78 else 78) else (if i.val < 99 then 94 else 78)) else (if i.val < 102 then (if i.val < 101 then 94 else 53) else (if i.val < 103 then 55 else 55))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 81 else 55) else (if i.val < 107 then 55 else 86)) else (if i.val < 110 then (if i.val < 109 then 86 else 55) else (if i.val < 111 then 80 else 81)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 86 else 86) else (if i.val < 115 then 84 else 55)) else (if i.val < 118 then (if i.val < 117 then 80 else 86) else (if i.val < 119 then 86 else 85))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 81 else 84) else (if i.val < 123 then 45 else 84)) else (if i.val < 126 then (if i.val < 125 then 81 else 85) else (if i.val < 127 then 81 else 80))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 54 else 80) else (if i.val < 131 then 86 else 45)) else (if i.val < 134 then (if i.val < 133 then 54 else 55) else (if i.val < 135 then 54 else 86))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 84 else 80) else (if i.val < 139 then 86 else 86)) else (if i.val < 142 then (if i.val < 141 then 85 else 81) else (if i.val < 143 then 81 else 98)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 84 else 55) else (if i.val < 147 then 86 else 85)) else (if i.val < 150 then (if i.val < 149 then 86 else 81) else (if i.val < 151 then 54 else 86))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 86 else 86) else (if i.val < 155 then 86 else 85)) else (if i.val < 158 then (if i.val < 157 then 80 else 98) else (if i.val < 159 then 85 else 98))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 98 else 85) else (if i.val < 163 then 86 else 54)) else (if i.val < 166 then (if i.val < 165 then 86 else 55) else (if i.val < 167 then 98 else 80))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 86 else 86) else (if i.val < 171 then 86 else 86)) else (if i.val < 174 then (if i.val < 173 then 98 else 86) else (if i.val < 175 then 98 else 86)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 98 else 92) else (if i.val < 179 then 89 else 92)) else (if i.val < 182 then (if i.val < 181 then 90 else 93) else (if i.val < 183 then 62 else 92))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 87 else 92) else (if i.val < 187 then 90 else 93)) else (if i.val < 190 then (if i.val < 189 then 89 else 92) else (if i.val < 191 then 87 else 90)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 92 else 89) else (if i.val < 195 then 92 else 93)) else (if i.val < 198 then (if i.val < 197 then 92 else 92) else (if i.val < 199 then 66 else 89))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 90 else 61) else (if i.val < 203 then 92 else 92)) else (if i.val < 206 then (if i.val < 205 then 90 else 77) else (if i.val < 207 then 76 else 78)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 77 else 76) else (if i.val < 211 then 76 else 78)) else (if i.val < 214 then (if i.val < 213 then 76 else 78) else (if i.val < 215 then 78 else 76))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 76 else 94) else (if i.val < 219 then 77 else 78)) else (if i.val < 222 then (if i.val < 221 then 94 else 78) else (if i.val < 223 then 78 else 100))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 100 else 100) else (if i.val < 227 then 100 else 100)) else (if i.val < 230 then (if i.val < 229 then 100 else 100) else (if i.val < 231 then 3 else 5))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 6 else 5) else (if i.val < 235 then 5 else 1)) else (if i.val < 238 then (if i.val < 237 then 8 else 1) else (if i.val < 239 then 3 else 3)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 3 else 15) else (if i.val < 243 then 2 else 3)) else (if i.val < 246 then (if i.val < 245 then 2 else 5) else (if i.val < 247 then 5 else 24))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 5 else 5) else (if i.val < 251 then 19 else 19)) else (if i.val < 254 then (if i.val < 253 then 19 else 20) else (if i.val < 255 then 24 else 5))))))))

theorem g32p_supplierForest_actual_014 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_014 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_014 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_136144
  · exact g32p_supplierForest_actual_136413
  · exact g32p_supplierForest_actual_136426
  · exact g32p_supplierForest_actual_136453
  · exact g32p_supplierForest_actual_136479
  · exact g32p_supplierForest_actual_136518
  · exact g32p_supplierForest_actual_136544
  · exact g32p_supplierForest_actual_136598
  · exact g32p_supplierForest_actual_136776
  · exact g32p_supplierForest_actual_136858
  · exact g32p_supplierForest_actual_136988
  · exact g32p_supplierForest_actual_137065
  · exact g32p_supplierForest_actual_137104
  · exact g32p_supplierForest_actual_137209
  · exact g32p_supplierForest_actual_137494
  · exact g32p_supplierForest_actual_137562
  · exact g32p_supplierForest_actual_137589
  · exact g32p_supplierForest_actual_137668
  · exact g32p_supplierForest_actual_137694
  · exact g32p_supplierForest_actual_137697
  · exact g32p_supplierForest_actual_137753
  · exact g32p_supplierForest_actual_137756
  · exact g32p_supplierForest_actual_137993
  · exact g32p_supplierForest_actual_138049
  · exact g32p_supplierForest_actual_138369
  · exact g32p_supplierForest_actual_138386
  · exact g32p_supplierForest_actual_138482
  · exact g32p_supplierForest_actual_138538
  · exact g32p_supplierForest_actual_138641
  · exact g32p_supplierForest_actual_138779
  · exact g32p_supplierForest_actual_138828
  · exact g32p_supplierForest_actual_138851
  · exact g32p_supplierForest_actual_138863
  · exact g32p_supplierForest_actual_138940
  · exact g32p_supplierForest_actual_138965
  · exact g32p_supplierForest_actual_138996
  · exact g32p_supplierForest_actual_139008
  · exact g32p_supplierForest_actual_139075
  · exact g32p_supplierForest_actual_139225
  · exact g32p_supplierForest_actual_139335
  · exact g32p_supplierForest_actual_139348
  · exact g32p_supplierForest_actual_139350
  · exact g32p_supplierForest_actual_139445
  · exact g32p_supplierForest_actual_139573
  · exact g32p_supplierForest_actual_139665
  · exact g32p_supplierForest_actual_139697
  · exact g32p_supplierForest_actual_139713
  · exact g32p_supplierForest_actual_139732
  · exact g32p_supplierForest_actual_139807
  · exact g32p_supplierForest_actual_139809
  · exact g32p_supplierForest_actual_140014
  · exact g32p_supplierForest_actual_140193
  · exact g32p_supplierForest_actual_140216
  · exact g32p_supplierForest_actual_140507
  · exact g32p_supplierForest_actual_140549
  · exact g32p_supplierForest_actual_140574
  · exact g32p_supplierForest_actual_140616
  · exact g32p_supplierForest_actual_140626
  · exact g32p_supplierForest_actual_140696
  · exact g32p_supplierForest_actual_140760
  · exact g32p_supplierForest_actual_140901
  · exact g32p_supplierForest_actual_140973
  · exact g32p_supplierForest_actual_141061
  · exact g32p_supplierForest_actual_141253
  · exact g32p_supplierForest_actual_141392
  · exact g32p_supplierForest_actual_141423
  · exact g32p_supplierForest_actual_141578
  · exact g32p_supplierForest_actual_141595
  · exact g32p_supplierForest_actual_141701
  · exact g32p_supplierForest_actual_142006
  · exact g32p_supplierForest_actual_142040
  · exact g32p_supplierForest_actual_142126
  · exact g32p_supplierForest_actual_142204
  · exact g32p_supplierForest_actual_142237
  · exact g32p_supplierForest_actual_142430
  · exact g32p_supplierForest_actual_142441
  · exact g32p_supplierForest_actual_142623
  · exact g32p_supplierForest_actual_142727
  · exact g32p_supplierForest_actual_142882
  · exact g32p_supplierForest_actual_143010
  · exact g32p_supplierForest_actual_143104
  · exact g32p_supplierForest_actual_143188
  · exact g32p_supplierForest_actual_143261
  · exact g32p_supplierForest_actual_143407
  · exact g32p_supplierForest_actual_143445
  · exact g32p_supplierForest_actual_143458
  · exact g32p_supplierForest_actual_143472
  · exact g32p_supplierForest_actual_143506
  · exact g32p_supplierForest_actual_143526
  · exact g32p_supplierForest_actual_143711
  · exact g32p_supplierForest_actual_143769
  · exact g32p_supplierForest_actual_143801
  · exact g32p_supplierForest_actual_144197
  · exact g32p_supplierForest_actual_144262
  · exact g32p_supplierForest_actual_144310
  · exact g32p_supplierForest_actual_144317
  · exact g32p_supplierForest_actual_144351
  · exact g32p_supplierForest_actual_144359
  · exact g32p_supplierForest_actual_144407
  · exact g32p_supplierForest_actual_144413
  · exact g32p_supplierForest_actual_144469
  · exact g32p_supplierForest_actual_144818
  · exact g32p_supplierForest_actual_144822
  · exact g32p_supplierForest_actual_145409
  · exact g32p_supplierForest_actual_145720
  · exact g32p_supplierForest_actual_145901
  · exact g32p_supplierForest_actual_145916
  · exact g32p_supplierForest_actual_145951
  · exact g32p_supplierForest_actual_146173
  · exact g32p_supplierForest_actual_146355
  · exact g32p_supplierForest_actual_146434
  · exact g32p_supplierForest_actual_146458
  · exact g32p_supplierForest_actual_146487
  · exact g32p_supplierForest_actual_146518
  · exact g32p_supplierForest_actual_146544
  · exact g32p_supplierForest_actual_146584
  · exact g32p_supplierForest_actual_146684
  · exact g32p_supplierForest_actual_146781
  · exact g32p_supplierForest_actual_146792
  · exact g32p_supplierForest_actual_146961
  · exact g32p_supplierForest_actual_146962
  · exact g32p_supplierForest_actual_147030
  · exact g32p_supplierForest_actual_147121
  · exact g32p_supplierForest_actual_147333
  · exact g32p_supplierForest_actual_147490
  · exact g32p_supplierForest_actual_147641
  · exact g32p_supplierForest_actual_147662
  · exact g32p_supplierForest_actual_148028
  · exact g32p_supplierForest_actual_148049
  · exact g32p_supplierForest_actual_148064
  · exact g32p_supplierForest_actual_148065
  · exact g32p_supplierForest_actual_148437
  · exact g32p_supplierForest_actual_148722
  · exact g32p_supplierForest_actual_148790
  · exact g32p_supplierForest_actual_148862
  · exact g32p_supplierForest_actual_148965
  · exact g32p_supplierForest_actual_149201
  · exact g32p_supplierForest_actual_149334
  · exact g32p_supplierForest_actual_149348
  · exact g32p_supplierForest_actual_149509
  · exact g32p_supplierForest_actual_149607
  · exact g32p_supplierForest_actual_149815
  · exact g32p_supplierForest_actual_149912
  · exact g32p_supplierForest_actual_149914
  · exact g32p_supplierForest_actual_150176
  · exact g32p_supplierForest_actual_150228
  · exact g32p_supplierForest_actual_150378
  · exact g32p_supplierForest_actual_150399
  · exact g32p_supplierForest_actual_150607
  · exact g32p_supplierForest_actual_150647
  · exact g32p_supplierForest_actual_150763
  · exact g32p_supplierForest_actual_150872
  · exact g32p_supplierForest_actual_150925
  · exact g32p_supplierForest_actual_151053
  · exact g32p_supplierForest_actual_151054
  · exact g32p_supplierForest_actual_151084
  · exact g32p_supplierForest_actual_151236
  · exact g32p_supplierForest_actual_151243
  · exact g32p_supplierForest_actual_151340
  · exact g32p_supplierForest_actual_151454
  · exact g32p_supplierForest_actual_151492
  · exact g32p_supplierForest_actual_151529
  · exact g32p_supplierForest_actual_151531
  · exact g32p_supplierForest_actual_151657
  · exact g32p_supplierForest_actual_151780
  · exact g32p_supplierForest_actual_151924
  · exact g32p_supplierForest_actual_152067
  · exact g32p_supplierForest_actual_152105
  · exact g32p_supplierForest_actual_152127
  · exact g32p_supplierForest_actual_152175
  · exact g32p_supplierForest_actual_152210
  · exact g32p_supplierForest_actual_152225
  · exact g32p_supplierForest_actual_152306
  · exact g32p_supplierForest_actual_152313
  · exact g32p_supplierForest_actual_152472
  · exact g32p_supplierForest_actual_152475
  · exact g32p_supplierForest_actual_152498
  · exact g32p_supplierForest_actual_152591
  · exact g32p_supplierForest_actual_152700
  · exact g32p_supplierForest_actual_152755
  · exact g32p_supplierForest_actual_153085
  · exact g32p_supplierForest_actual_153094
  · exact g32p_supplierForest_actual_153103
  · exact g32p_supplierForest_actual_153130
  · exact g32p_supplierForest_actual_153170
  · exact g32p_supplierForest_actual_153458
  · exact g32p_supplierForest_actual_153560
  · exact g32p_supplierForest_actual_153727
  · exact g32p_supplierForest_actual_153808
  · exact g32p_supplierForest_actual_153915
  · exact g32p_supplierForest_actual_154019
  · exact g32p_supplierForest_actual_154248
  · exact g32p_supplierForest_actual_154311
  · exact g32p_supplierForest_actual_154335
  · exact g32p_supplierForest_actual_154343
  · exact g32p_supplierForest_actual_154372
  · exact g32p_supplierForest_actual_154379
  · exact g32p_supplierForest_actual_154437
  · exact g32p_supplierForest_actual_154542
  · exact g32p_supplierForest_actual_154565
  · exact g32p_supplierForest_actual_154782
  · exact g32p_supplierForest_actual_154854
  · exact g32p_supplierForest_actual_154933
  · exact g32p_supplierForest_actual_154939
  · exact g32p_supplierForest_actual_154956
  · exact g32p_supplierForest_actual_155011
  · exact g32p_supplierForest_actual_155082
  · exact g32p_supplierForest_actual_155136
  · exact g32p_supplierForest_actual_155169
  · exact g32p_supplierForest_actual_155177
  · exact g32p_supplierForest_actual_155195
  · exact g32p_supplierForest_actual_155208
  · exact g32p_supplierForest_actual_155245
  · exact g32p_supplierForest_actual_155250
  · exact g32p_supplierForest_actual_155253
  · exact g32p_supplierForest_actual_155269
  · exact g32p_supplierForest_actual_155294
  · exact g32p_supplierForest_actual_155312
  · exact g32p_supplierForest_actual_155317
  · exact g32p_supplierForest_actual_155325
  · exact g32p_supplierForest_actual_155346
  · exact g32p_supplierForest_actual_155405
  · exact g32p_supplierForest_actual_155456
  · exact g32p_supplierForest_actual_155471
  · exact g32p_supplierForest_actual_155472
  · exact g32p_supplierForest_actual_155474
  · exact g32p_supplierForest_actual_155486
  · exact g32p_supplierForest_actual_155496
  · exact g32p_supplierForest_actual_155507
  · exact g32p_supplierForest_actual_155510
  · exact g32p_supplierForest_actual_000013
  · exact g32p_supplierForest_actual_000023
  · exact g32p_supplierForest_actual_000027
  · exact g32p_supplierForest_actual_000031
  · exact g32p_supplierForest_actual_000045
  · exact g32p_supplierForest_actual_000115
  · exact g32p_supplierForest_actual_000138
  · exact g32p_supplierForest_actual_000141
  · exact g32p_supplierForest_actual_000195
  · exact g32p_supplierForest_actual_000250
  · exact g32p_supplierForest_actual_000297
  · exact g32p_supplierForest_actual_000319
  · exact g32p_supplierForest_actual_000320
  · exact g32p_supplierForest_actual_000323
  · exact g32p_supplierForest_actual_000381
  · exact g32p_supplierForest_actual_000453
  · exact g32p_supplierForest_actual_000509
  · exact g32p_supplierForest_actual_000520
  · exact g32p_supplierForest_actual_000529
  · exact g32p_supplierForest_actual_000554
  · exact g32p_supplierForest_actual_000577
  · exact g32p_supplierForest_actual_000592
  · exact g32p_supplierForest_actual_000603
  · exact g32p_supplierForest_actual_000611
  · exact g32p_supplierForest_actual_000613
  · exact g32p_supplierForest_actual_000635

def g32p_supplierForest_nodes_015 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_000643 else g32p_supplierForest_node_000649) else (if i.val < 3 then g32p_supplierForest_node_000682 else g32p_supplierForest_node_000718)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_000738 else g32p_supplierForest_node_000748) else (if i.val < 7 then g32p_supplierForest_node_000750 else g32p_supplierForest_node_000764))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_000768 else g32p_supplierForest_node_000807) else (if i.val < 11 then g32p_supplierForest_node_000856 else g32p_supplierForest_node_000907)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_000963 else g32p_supplierForest_node_000991) else (if i.val < 15 then g32p_supplierForest_node_001042 else g32p_supplierForest_node_001084)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_001090 else g32p_supplierForest_node_001131) else (if i.val < 19 then g32p_supplierForest_node_001174 else g32p_supplierForest_node_001211)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_001223 else g32p_supplierForest_node_001284) else (if i.val < 23 then g32p_supplierForest_node_001289 else g32p_supplierForest_node_001296))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_001307 else g32p_supplierForest_node_001309) else (if i.val < 27 then g32p_supplierForest_node_001321 else g32p_supplierForest_node_001334)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_001370 else g32p_supplierForest_node_001371) else (if i.val < 31 then g32p_supplierForest_node_001380 else g32p_supplierForest_node_001420))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_001443 else g32p_supplierForest_node_001457) else (if i.val < 35 then g32p_supplierForest_node_001461 else g32p_supplierForest_node_001484)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_001504 else g32p_supplierForest_node_001509) else (if i.val < 39 then g32p_supplierForest_node_001538 else g32p_supplierForest_node_001558))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_001588 else g32p_supplierForest_node_001653) else (if i.val < 43 then g32p_supplierForest_node_001668 else g32p_supplierForest_node_001692)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_001707 else g32p_supplierForest_node_001784) else (if i.val < 47 then g32p_supplierForest_node_001789 else g32p_supplierForest_node_001807)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_001815 else g32p_supplierForest_node_001850) else (if i.val < 51 then g32p_supplierForest_node_001866 else g32p_supplierForest_node_001937)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_001940 else g32p_supplierForest_node_001947) else (if i.val < 55 then g32p_supplierForest_node_001955 else g32p_supplierForest_node_001959))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_002010 else g32p_supplierForest_node_002018) else (if i.val < 59 then g32p_supplierForest_node_002039 else g32p_supplierForest_node_002212)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_002249 else g32p_supplierForest_node_002262) else (if i.val < 63 then g32p_supplierForest_node_002269 else g32p_supplierForest_node_002275)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_002342 else g32p_supplierForest_node_002348) else (if i.val < 67 then g32p_supplierForest_node_002387 else g32p_supplierForest_node_002422)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_002445 else g32p_supplierForest_node_002476) else (if i.val < 71 then g32p_supplierForest_node_002498 else g32p_supplierForest_node_002506))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_002519 else g32p_supplierForest_node_002549) else (if i.val < 75 then g32p_supplierForest_node_002585 else g32p_supplierForest_node_002632)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_002667 else g32p_supplierForest_node_002676) else (if i.val < 79 then g32p_supplierForest_node_002737 else g32p_supplierForest_node_002782)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_002785 else g32p_supplierForest_node_002786) else (if i.val < 83 then g32p_supplierForest_node_002876 else g32p_supplierForest_node_002937)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_002967 else g32p_supplierForest_node_002970) else (if i.val < 87 then g32p_supplierForest_node_002973 else g32p_supplierForest_node_002974))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_002980 else g32p_supplierForest_node_002981) else (if i.val < 91 then g32p_supplierForest_node_002991 else g32p_supplierForest_node_003010)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_003018 else g32p_supplierForest_node_003026) else (if i.val < 95 then g32p_supplierForest_node_003035 else g32p_supplierForest_node_003051))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_003059 else g32p_supplierForest_node_003089) else (if i.val < 99 then g32p_supplierForest_node_003091 else g32p_supplierForest_node_003109)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_003121 else g32p_supplierForest_node_003156) else (if i.val < 103 then g32p_supplierForest_node_003160 else g32p_supplierForest_node_003200))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_003231 else g32p_supplierForest_node_003237) else (if i.val < 107 then g32p_supplierForest_node_003249 else g32p_supplierForest_node_003257)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_003269 else g32p_supplierForest_node_003276) else (if i.val < 111 then g32p_supplierForest_node_003304 else g32p_supplierForest_node_003331)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_003332 else g32p_supplierForest_node_003344) else (if i.val < 115 then g32p_supplierForest_node_003349 else g32p_supplierForest_node_003384)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_003501 else g32p_supplierForest_node_003543) else (if i.val < 119 then g32p_supplierForest_node_003716 else g32p_supplierForest_node_003727))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_003774 else g32p_supplierForest_node_003818) else (if i.val < 123 then g32p_supplierForest_node_003829 else g32p_supplierForest_node_003876)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_003887 else g32p_supplierForest_node_003951) else (if i.val < 127 then g32p_supplierForest_node_003976 else g32p_supplierForest_node_003981))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_003992 else g32p_supplierForest_node_003993) else (if i.val < 131 then g32p_supplierForest_node_003999 else g32p_supplierForest_node_004045)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_004055 else g32p_supplierForest_node_004071) else (if i.val < 135 then g32p_supplierForest_node_004154 else g32p_supplierForest_node_004170))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_004187 else g32p_supplierForest_node_004200) else (if i.val < 139 then g32p_supplierForest_node_004205 else g32p_supplierForest_node_004209)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_004220 else g32p_supplierForest_node_004231) else (if i.val < 143 then g32p_supplierForest_node_004234 else g32p_supplierForest_node_004245)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_004273 else g32p_supplierForest_node_004282) else (if i.val < 147 then g32p_supplierForest_node_004342 else g32p_supplierForest_node_004350)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_004352 else g32p_supplierForest_node_004362) else (if i.val < 151 then g32p_supplierForest_node_004381 else g32p_supplierForest_node_004398))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_004443 else g32p_supplierForest_node_004446) else (if i.val < 155 then g32p_supplierForest_node_004451 else g32p_supplierForest_node_004481)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_004527 else g32p_supplierForest_node_004532) else (if i.val < 159 then g32p_supplierForest_node_004539 else g32p_supplierForest_node_004569))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_004584 else g32p_supplierForest_node_004589) else (if i.val < 163 then g32p_supplierForest_node_004649 else g32p_supplierForest_node_004657)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_004674 else g32p_supplierForest_node_004679) else (if i.val < 167 then g32p_supplierForest_node_004707 else g32p_supplierForest_node_004727))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_004760 else g32p_supplierForest_node_004763) else (if i.val < 171 then g32p_supplierForest_node_004811 else g32p_supplierForest_node_004827)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_004833 else g32p_supplierForest_node_004839) else (if i.val < 175 then g32p_supplierForest_node_004874 else g32p_supplierForest_node_004890)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_004893 else g32p_supplierForest_node_004898) else (if i.val < 179 then g32p_supplierForest_node_004922 else g32p_supplierForest_node_005020)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_005061 else g32p_supplierForest_node_005071) else (if i.val < 183 then g32p_supplierForest_node_005150 else g32p_supplierForest_node_005249))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_005269 else g32p_supplierForest_node_005279) else (if i.val < 187 then g32p_supplierForest_node_005410 else g32p_supplierForest_node_005545)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_005563 else g32p_supplierForest_node_005571) else (if i.val < 191 then g32p_supplierForest_node_005576 else g32p_supplierForest_node_005577)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_005584 else g32p_supplierForest_node_005612) else (if i.val < 195 then g32p_supplierForest_node_005712 else g32p_supplierForest_node_005717)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_005723 else g32p_supplierForest_node_005728) else (if i.val < 199 then g32p_supplierForest_node_005730 else g32p_supplierForest_node_005765))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_005773 else g32p_supplierForest_node_005818) else (if i.val < 203 then g32p_supplierForest_node_005849 else g32p_supplierForest_node_005855)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_005878 else g32p_supplierForest_node_005906) else (if i.val < 207 then g32p_supplierForest_node_005921 else g32p_supplierForest_node_005980)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_006028 else g32p_supplierForest_node_006045) else (if i.val < 211 then g32p_supplierForest_node_006096 else g32p_supplierForest_node_006134)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_006144 else g32p_supplierForest_node_006155) else (if i.val < 215 then g32p_supplierForest_node_006181 else g32p_supplierForest_node_006246))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_006308 else g32p_supplierForest_node_006309) else (if i.val < 219 then g32p_supplierForest_node_006421 else g32p_supplierForest_node_006433)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_006451 else g32p_supplierForest_node_006486) else (if i.val < 223 then g32p_supplierForest_node_006518 else g32p_supplierForest_node_006547))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_006577 else g32p_supplierForest_node_006686) else (if i.val < 227 then g32p_supplierForest_node_006697 else g32p_supplierForest_node_006715)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_006732 else g32p_supplierForest_node_006735) else (if i.val < 231 then g32p_supplierForest_node_006771 else g32p_supplierForest_node_006772))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_006801 else g32p_supplierForest_node_006826) else (if i.val < 235 then g32p_supplierForest_node_006833 else g32p_supplierForest_node_006836)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_006880 else g32p_supplierForest_node_006938) else (if i.val < 239 then g32p_supplierForest_node_006964 else g32p_supplierForest_node_006974)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_006977 else g32p_supplierForest_node_006983) else (if i.val < 243 then g32p_supplierForest_node_006985 else g32p_supplierForest_node_006998)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_007012 else g32p_supplierForest_node_007025) else (if i.val < 247 then g32p_supplierForest_node_007029 else g32p_supplierForest_node_007065))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_007098 else g32p_supplierForest_node_007100) else (if i.val < 251 then g32p_supplierForest_node_007112 else g32p_supplierForest_node_007146)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_007186 else g32p_supplierForest_node_007189) else (if i.val < 255 then g32p_supplierForest_node_007202 else g32p_supplierForest_node_007241))))))))

def g32p_supplierForest_classes_015 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 19 else 24) else (if i.val < 3 then 7 else 5)) else (if i.val < 6 then (if i.val < 5 then 5 else 24) else (if i.val < 7 then 5 else 5))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 5 else 7) else (if i.val < 11 then 19 else 24)) else (if i.val < 14 then (if i.val < 13 then 22 else 5) else (if i.val < 15 then 7 else 10)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 13 else 8) else (if i.val < 19 then 12 else 10)) else (if i.val < 22 then (if i.val < 21 then 13 else 10) else (if i.val < 23 then 10 else 28))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 8 else 10) else (if i.val < 27 then 10 else 9)) else (if i.val < 30 then (if i.val < 29 then 1 else 9) else (if i.val < 31 then 28 else 12))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 10 else 28) else (if i.val < 35 then 10 else 10)) else (if i.val < 38 then (if i.val < 37 then 27 else 10) else (if i.val < 39 then 10 else 8))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 10 else 12) else (if i.val < 43 then 12 else 13)) else (if i.val < 46 then (if i.val < 45 then 25 else 9) else (if i.val < 47 then 10 else 9)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 27 else 13) else (if i.val < 51 then 1 else 25)) else (if i.val < 54 then (if i.val < 53 then 13 else 12) else (if i.val < 55 then 13 else 28))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 13 else 12) else (if i.val < 59 then 8 else 9)) else (if i.val < 62 then (if i.val < 61 then 13 else 27) else (if i.val < 63 then 13 else 12)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 13 else 13) else (if i.val < 67 then 13 else 26)) else (if i.val < 70 then (if i.val < 69 then 9 else 13) else (if i.val < 71 then 27 else 10))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 9 else 14) else (if i.val < 75 then 30 else 29)) else (if i.val < 78 then (if i.val < 77 then 14 else 3) else (if i.val < 79 then 3 else 30)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 16 else 16) else (if i.val < 83 then 17 else 16)) else (if i.val < 86 then (if i.val < 85 then 14 else 30) else (if i.val < 87 then 29 else 15))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 16 else 16) else (if i.val < 91 then 17 else 31)) else (if i.val < 94 then (if i.val < 93 then 31 else 31) else (if i.val < 95 then 17 else 31))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 31 else 15) else (if i.val < 99 then 16 else 14)) else (if i.val < 102 then (if i.val < 101 then 34 else 15) else (if i.val < 103 then 14 else 16))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 31 else 3) else (if i.val < 107 then 16 else 30)) else (if i.val < 110 then (if i.val < 109 then 31 else 2) else (if i.val < 111 then 17 else 15)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 16 else 30) else (if i.val < 115 then 32 else 31)) else (if i.val < 118 then (if i.val < 117 then 31 else 34) else (if i.val < 119 then 31 else 17))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 17 else 16) else (if i.val < 123 then 34 else 31)) else (if i.val < 126 then (if i.val < 125 then 15 else 3) else (if i.val < 127 then 31 else 14))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 30 else 32) else (if i.val < 131 then 32 else 16)) else (if i.val < 134 then (if i.val < 133 then 32 else 4) else (if i.val < 135 then 16 else 3))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 3 else 17) else (if i.val < 139 then 14 else 17)) else (if i.val < 142 then (if i.val < 141 then 17 else 34) else (if i.val < 143 then 3 else 4)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 3 else 14) else (if i.val < 147 then 2 else 30)) else (if i.val < 150 then (if i.val < 149 then 16 else 4) else (if i.val < 151 then 14 else 32))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 3 else 4) else (if i.val < 155 then 3 else 29)) else (if i.val < 158 then (if i.val < 157 then 30 else 16) else (if i.val < 159 then 31 else 14))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 31 else 15) else (if i.val < 163 then 16 else 4)) else (if i.val < 166 then (if i.val < 165 then 3 else 15) else (if i.val < 167 then 14 else 34))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 15 else 17) else (if i.val < 171 then 34 else 15)) else (if i.val < 174 then (if i.val < 173 then 3 else 16) else (if i.val < 175 then 17 else 3)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 31 else 31) else (if i.val < 179 then 29 else 34)) else (if i.val < 182 then (if i.val < 181 then 15 else 31) else (if i.val < 183 then 30 else 17))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 16 else 30) else (if i.val < 187 then 3 else 16)) else (if i.val < 190 then (if i.val < 189 then 14 else 32) else (if i.val < 191 then 31 else 32)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 15 else 17) else (if i.val < 195 then 16 else 15)) else (if i.val < 198 then (if i.val < 197 then 17 else 34) else (if i.val < 199 then 14 else 15))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 20 else 5) else (if i.val < 203 then 38 else 24)) else (if i.val < 206 then (if i.val < 205 then 39 else 6) else (if i.val < 207 then 7 else 5)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 7 else 7) else (if i.val < 211 then 5 else 7)) else (if i.val < 214 then (if i.val < 213 then 5 else 5) else (if i.val < 215 then 19 else 22))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 21 else 38) else (if i.val < 219 then 19 else 18)) else (if i.val < 222 then (if i.val < 221 then 19 else 21) else (if i.val < 223 then 22 else 24))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 7 else 21) else (if i.val < 227 then 22 else 6)) else (if i.val < 230 then (if i.val < 229 then 38 else 24) else (if i.val < 231 then 19 else 24))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 7 else 39) else (if i.val < 235 then 6 else 39)) else (if i.val < 238 then (if i.val < 237 then 7 else 19) else (if i.val < 239 then 19 else 21)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 20 else 22) else (if i.val < 243 then 21 else 22)) else (if i.val < 246 then (if i.val < 245 then 7 else 6) else (if i.val < 247 then 22 else 40))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 5 else 18) else (if i.val < 251 then 38 else 23)) else (if i.val < 254 then (if i.val < 253 then 7 else 23) else (if i.val < 255 then 21 else 40))))))))

theorem g32p_supplierForest_actual_015 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_015 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_015 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_000643
  · exact g32p_supplierForest_actual_000649
  · exact g32p_supplierForest_actual_000682
  · exact g32p_supplierForest_actual_000718
  · exact g32p_supplierForest_actual_000738
  · exact g32p_supplierForest_actual_000748
  · exact g32p_supplierForest_actual_000750
  · exact g32p_supplierForest_actual_000764
  · exact g32p_supplierForest_actual_000768
  · exact g32p_supplierForest_actual_000807
  · exact g32p_supplierForest_actual_000856
  · exact g32p_supplierForest_actual_000907
  · exact g32p_supplierForest_actual_000963
  · exact g32p_supplierForest_actual_000991
  · exact g32p_supplierForest_actual_001042
  · exact g32p_supplierForest_actual_001084
  · exact g32p_supplierForest_actual_001090
  · exact g32p_supplierForest_actual_001131
  · exact g32p_supplierForest_actual_001174
  · exact g32p_supplierForest_actual_001211
  · exact g32p_supplierForest_actual_001223
  · exact g32p_supplierForest_actual_001284
  · exact g32p_supplierForest_actual_001289
  · exact g32p_supplierForest_actual_001296
  · exact g32p_supplierForest_actual_001307
  · exact g32p_supplierForest_actual_001309
  · exact g32p_supplierForest_actual_001321
  · exact g32p_supplierForest_actual_001334
  · exact g32p_supplierForest_actual_001370
  · exact g32p_supplierForest_actual_001371
  · exact g32p_supplierForest_actual_001380
  · exact g32p_supplierForest_actual_001420
  · exact g32p_supplierForest_actual_001443
  · exact g32p_supplierForest_actual_001457
  · exact g32p_supplierForest_actual_001461
  · exact g32p_supplierForest_actual_001484
  · exact g32p_supplierForest_actual_001504
  · exact g32p_supplierForest_actual_001509
  · exact g32p_supplierForest_actual_001538
  · exact g32p_supplierForest_actual_001558
  · exact g32p_supplierForest_actual_001588
  · exact g32p_supplierForest_actual_001653
  · exact g32p_supplierForest_actual_001668
  · exact g32p_supplierForest_actual_001692
  · exact g32p_supplierForest_actual_001707
  · exact g32p_supplierForest_actual_001784
  · exact g32p_supplierForest_actual_001789
  · exact g32p_supplierForest_actual_001807
  · exact g32p_supplierForest_actual_001815
  · exact g32p_supplierForest_actual_001850
  · exact g32p_supplierForest_actual_001866
  · exact g32p_supplierForest_actual_001937
  · exact g32p_supplierForest_actual_001940
  · exact g32p_supplierForest_actual_001947
  · exact g32p_supplierForest_actual_001955
  · exact g32p_supplierForest_actual_001959
  · exact g32p_supplierForest_actual_002010
  · exact g32p_supplierForest_actual_002018
  · exact g32p_supplierForest_actual_002039
  · exact g32p_supplierForest_actual_002212
  · exact g32p_supplierForest_actual_002249
  · exact g32p_supplierForest_actual_002262
  · exact g32p_supplierForest_actual_002269
  · exact g32p_supplierForest_actual_002275
  · exact g32p_supplierForest_actual_002342
  · exact g32p_supplierForest_actual_002348
  · exact g32p_supplierForest_actual_002387
  · exact g32p_supplierForest_actual_002422
  · exact g32p_supplierForest_actual_002445
  · exact g32p_supplierForest_actual_002476
  · exact g32p_supplierForest_actual_002498
  · exact g32p_supplierForest_actual_002506
  · exact g32p_supplierForest_actual_002519
  · exact g32p_supplierForest_actual_002549
  · exact g32p_supplierForest_actual_002585
  · exact g32p_supplierForest_actual_002632
  · exact g32p_supplierForest_actual_002667
  · exact g32p_supplierForest_actual_002676
  · exact g32p_supplierForest_actual_002737
  · exact g32p_supplierForest_actual_002782
  · exact g32p_supplierForest_actual_002785
  · exact g32p_supplierForest_actual_002786
  · exact g32p_supplierForest_actual_002876
  · exact g32p_supplierForest_actual_002937
  · exact g32p_supplierForest_actual_002967
  · exact g32p_supplierForest_actual_002970
  · exact g32p_supplierForest_actual_002973
  · exact g32p_supplierForest_actual_002974
  · exact g32p_supplierForest_actual_002980
  · exact g32p_supplierForest_actual_002981
  · exact g32p_supplierForest_actual_002991
  · exact g32p_supplierForest_actual_003010
  · exact g32p_supplierForest_actual_003018
  · exact g32p_supplierForest_actual_003026
  · exact g32p_supplierForest_actual_003035
  · exact g32p_supplierForest_actual_003051
  · exact g32p_supplierForest_actual_003059
  · exact g32p_supplierForest_actual_003089
  · exact g32p_supplierForest_actual_003091
  · exact g32p_supplierForest_actual_003109
  · exact g32p_supplierForest_actual_003121
  · exact g32p_supplierForest_actual_003156
  · exact g32p_supplierForest_actual_003160
  · exact g32p_supplierForest_actual_003200
  · exact g32p_supplierForest_actual_003231
  · exact g32p_supplierForest_actual_003237
  · exact g32p_supplierForest_actual_003249
  · exact g32p_supplierForest_actual_003257
  · exact g32p_supplierForest_actual_003269
  · exact g32p_supplierForest_actual_003276
  · exact g32p_supplierForest_actual_003304
  · exact g32p_supplierForest_actual_003331
  · exact g32p_supplierForest_actual_003332
  · exact g32p_supplierForest_actual_003344
  · exact g32p_supplierForest_actual_003349
  · exact g32p_supplierForest_actual_003384
  · exact g32p_supplierForest_actual_003501
  · exact g32p_supplierForest_actual_003543
  · exact g32p_supplierForest_actual_003716
  · exact g32p_supplierForest_actual_003727
  · exact g32p_supplierForest_actual_003774
  · exact g32p_supplierForest_actual_003818
  · exact g32p_supplierForest_actual_003829
  · exact g32p_supplierForest_actual_003876
  · exact g32p_supplierForest_actual_003887
  · exact g32p_supplierForest_actual_003951
  · exact g32p_supplierForest_actual_003976
  · exact g32p_supplierForest_actual_003981
  · exact g32p_supplierForest_actual_003992
  · exact g32p_supplierForest_actual_003993
  · exact g32p_supplierForest_actual_003999
  · exact g32p_supplierForest_actual_004045
  · exact g32p_supplierForest_actual_004055
  · exact g32p_supplierForest_actual_004071
  · exact g32p_supplierForest_actual_004154
  · exact g32p_supplierForest_actual_004170
  · exact g32p_supplierForest_actual_004187
  · exact g32p_supplierForest_actual_004200
  · exact g32p_supplierForest_actual_004205
  · exact g32p_supplierForest_actual_004209
  · exact g32p_supplierForest_actual_004220
  · exact g32p_supplierForest_actual_004231
  · exact g32p_supplierForest_actual_004234
  · exact g32p_supplierForest_actual_004245
  · exact g32p_supplierForest_actual_004273
  · exact g32p_supplierForest_actual_004282
  · exact g32p_supplierForest_actual_004342
  · exact g32p_supplierForest_actual_004350
  · exact g32p_supplierForest_actual_004352
  · exact g32p_supplierForest_actual_004362
  · exact g32p_supplierForest_actual_004381
  · exact g32p_supplierForest_actual_004398
  · exact g32p_supplierForest_actual_004443
  · exact g32p_supplierForest_actual_004446
  · exact g32p_supplierForest_actual_004451
  · exact g32p_supplierForest_actual_004481
  · exact g32p_supplierForest_actual_004527
  · exact g32p_supplierForest_actual_004532
  · exact g32p_supplierForest_actual_004539
  · exact g32p_supplierForest_actual_004569
  · exact g32p_supplierForest_actual_004584
  · exact g32p_supplierForest_actual_004589
  · exact g32p_supplierForest_actual_004649
  · exact g32p_supplierForest_actual_004657
  · exact g32p_supplierForest_actual_004674
  · exact g32p_supplierForest_actual_004679
  · exact g32p_supplierForest_actual_004707
  · exact g32p_supplierForest_actual_004727
  · exact g32p_supplierForest_actual_004760
  · exact g32p_supplierForest_actual_004763
  · exact g32p_supplierForest_actual_004811
  · exact g32p_supplierForest_actual_004827
  · exact g32p_supplierForest_actual_004833
  · exact g32p_supplierForest_actual_004839
  · exact g32p_supplierForest_actual_004874
  · exact g32p_supplierForest_actual_004890
  · exact g32p_supplierForest_actual_004893
  · exact g32p_supplierForest_actual_004898
  · exact g32p_supplierForest_actual_004922
  · exact g32p_supplierForest_actual_005020
  · exact g32p_supplierForest_actual_005061
  · exact g32p_supplierForest_actual_005071
  · exact g32p_supplierForest_actual_005150
  · exact g32p_supplierForest_actual_005249
  · exact g32p_supplierForest_actual_005269
  · exact g32p_supplierForest_actual_005279
  · exact g32p_supplierForest_actual_005410
  · exact g32p_supplierForest_actual_005545
  · exact g32p_supplierForest_actual_005563
  · exact g32p_supplierForest_actual_005571
  · exact g32p_supplierForest_actual_005576
  · exact g32p_supplierForest_actual_005577
  · exact g32p_supplierForest_actual_005584
  · exact g32p_supplierForest_actual_005612
  · exact g32p_supplierForest_actual_005712
  · exact g32p_supplierForest_actual_005717
  · exact g32p_supplierForest_actual_005723
  · exact g32p_supplierForest_actual_005728
  · exact g32p_supplierForest_actual_005730
  · exact g32p_supplierForest_actual_005765
  · exact g32p_supplierForest_actual_005773
  · exact g32p_supplierForest_actual_005818
  · exact g32p_supplierForest_actual_005849
  · exact g32p_supplierForest_actual_005855
  · exact g32p_supplierForest_actual_005878
  · exact g32p_supplierForest_actual_005906
  · exact g32p_supplierForest_actual_005921
  · exact g32p_supplierForest_actual_005980
  · exact g32p_supplierForest_actual_006028
  · exact g32p_supplierForest_actual_006045
  · exact g32p_supplierForest_actual_006096
  · exact g32p_supplierForest_actual_006134
  · exact g32p_supplierForest_actual_006144
  · exact g32p_supplierForest_actual_006155
  · exact g32p_supplierForest_actual_006181
  · exact g32p_supplierForest_actual_006246
  · exact g32p_supplierForest_actual_006308
  · exact g32p_supplierForest_actual_006309
  · exact g32p_supplierForest_actual_006421
  · exact g32p_supplierForest_actual_006433
  · exact g32p_supplierForest_actual_006451
  · exact g32p_supplierForest_actual_006486
  · exact g32p_supplierForest_actual_006518
  · exact g32p_supplierForest_actual_006547
  · exact g32p_supplierForest_actual_006577
  · exact g32p_supplierForest_actual_006686
  · exact g32p_supplierForest_actual_006697
  · exact g32p_supplierForest_actual_006715
  · exact g32p_supplierForest_actual_006732
  · exact g32p_supplierForest_actual_006735
  · exact g32p_supplierForest_actual_006771
  · exact g32p_supplierForest_actual_006772
  · exact g32p_supplierForest_actual_006801
  · exact g32p_supplierForest_actual_006826
  · exact g32p_supplierForest_actual_006833
  · exact g32p_supplierForest_actual_006836
  · exact g32p_supplierForest_actual_006880
  · exact g32p_supplierForest_actual_006938
  · exact g32p_supplierForest_actual_006964
  · exact g32p_supplierForest_actual_006974
  · exact g32p_supplierForest_actual_006977
  · exact g32p_supplierForest_actual_006983
  · exact g32p_supplierForest_actual_006985
  · exact g32p_supplierForest_actual_006998
  · exact g32p_supplierForest_actual_007012
  · exact g32p_supplierForest_actual_007025
  · exact g32p_supplierForest_actual_007029
  · exact g32p_supplierForest_actual_007065
  · exact g32p_supplierForest_actual_007098
  · exact g32p_supplierForest_actual_007100
  · exact g32p_supplierForest_actual_007112
  · exact g32p_supplierForest_actual_007146
  · exact g32p_supplierForest_actual_007186
  · exact g32p_supplierForest_actual_007189
  · exact g32p_supplierForest_actual_007202
  · exact g32p_supplierForest_actual_007241

end HodgeLean.Foundations.Program

end
end
