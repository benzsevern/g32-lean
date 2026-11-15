import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0247
import HodgeLean.Foundations.Program.G32PropFourSixPacked0248
import HodgeLean.Foundations.Program.G32PropFourSixPacked0249
import HodgeLean.Foundations.Program.G32PropFourSixPacked0250
import HodgeLean.Foundations.Program.G32PropFourSixPacked0251
import HodgeLean.Foundations.Program.G32PropFourSixPacked0252
import HodgeLean.Foundations.Program.G32PropFourSixPacked0253
import HodgeLean.Foundations.Program.G32PropFourSixPacked0254
import HodgeLean.Foundations.Program.G32PropFourSixPacked0255
import HodgeLean.Foundations.Program.G32PropFourSixPacked0256
import HodgeLean.Foundations.Program.G32PropFourSixPacked0257
import HodgeLean.Foundations.Program.G32PropFourSixPacked0267
import HodgeLean.Foundations.Program.G32PropFourSixPacked0268
import HodgeLean.Foundations.Program.G32PropFourSixPacked0269
import HodgeLean.Foundations.Program.G32PropFourSixPacked0270

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_149536 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_149536 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149536 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_097812 := by
  decide +kernel

theorem g32p_supplierForest_actual_149536 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149536) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_149536
    g32p_supplierForest_actual_097812

def g32p_supplierForest_node_149537 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_149537 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149537 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_071884 := by
  decide +kernel

theorem g32p_supplierForest_actual_149537 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149537) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_149537
    g32p_supplierForest_actual_071884

def g32p_supplierForest_node_149560 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_149560 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149560 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_081269 := by
  decide +kernel

theorem g32p_supplierForest_actual_149560 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149560) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_149560
    g32p_supplierForest_actual_081269

def g32p_supplierForest_node_149562 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_149562 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149562 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_151947 := by
  decide +kernel

theorem g32p_supplierForest_actual_149562 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149562) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_149562
    g32p_supplierForest_actual_151947

def g32p_supplierForest_node_149611 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_149611 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149611 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_145038 := by
  decide +kernel

theorem g32p_supplierForest_actual_149611 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149611) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_149611
    g32p_supplierForest_actual_145038

def g32p_supplierForest_node_149616 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_149616 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149616 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_097322 := by
  decide +kernel

theorem g32p_supplierForest_actual_149616 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149616) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_149616
    g32p_supplierForest_actual_097322

def g32p_supplierForest_node_149617 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_149617 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149617 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_151391 := by
  decide +kernel

theorem g32p_supplierForest_actual_149617 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149617) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_149617
    g32p_supplierForest_actual_151391

def g32p_supplierForest_node_149674 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_149674 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149674 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_148672 := by
  decide +kernel

theorem g32p_supplierForest_actual_149674 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149674) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 0 g32p_supplierForest_edge_149674
    g32p_supplierForest_actual_148672

def g32p_supplierForest_node_149689 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_149689 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149689 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086228 := by
  decide +kernel

theorem g32p_supplierForest_actual_149689 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149689) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_149689
    g32p_supplierForest_actual_086228

def g32p_supplierForest_node_149746 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_149746 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149746 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088636 := by
  decide +kernel

theorem g32p_supplierForest_actual_149746 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149746) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_149746
    g32p_supplierForest_actual_088636

def g32p_supplierForest_node_149793 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_149793 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149793 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086198 := by
  decide +kernel

theorem g32p_supplierForest_actual_149793 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149793) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_149793
    g32p_supplierForest_actual_086198

def g32p_supplierForest_node_149806 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_149806 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149806 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146145 := by
  decide +kernel

theorem g32p_supplierForest_actual_149806 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149806) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_149806
    g32p_supplierForest_actual_146145

def g32p_supplierForest_node_149859 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_149859 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149859 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_145818 := by
  decide +kernel

theorem g32p_supplierForest_actual_149859 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149859) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_149859
    g32p_supplierForest_actual_145818

def g32p_supplierForest_node_149862 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_149862 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149862 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_148755 := by
  decide +kernel

theorem g32p_supplierForest_actual_149862 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149862) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_149862
    g32p_supplierForest_actual_148755

def g32p_supplierForest_node_149924 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_149924 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149924 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_099129 := by
  decide +kernel

theorem g32p_supplierForest_actual_149924 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149924) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_149924
    g32p_supplierForest_actual_099129

def g32p_supplierForest_node_149973 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_149973 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149973 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093966 := by
  decide +kernel

theorem g32p_supplierForest_actual_149973 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149973) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_149973
    g32p_supplierForest_actual_093966

def g32p_supplierForest_node_150022 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_150022 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150022 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083839 := by
  decide +kernel

theorem g32p_supplierForest_actual_150022 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150022) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_150022
    g32p_supplierForest_actual_083839

def g32p_supplierForest_node_150030 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_150030 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150030 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_151572 := by
  decide +kernel

theorem g32p_supplierForest_actual_150030 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150030) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 0 g32p_supplierForest_edge_150030
    g32p_supplierForest_actual_151572

def g32p_supplierForest_node_150037 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_150037 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150037 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_148850 := by
  decide +kernel

theorem g32p_supplierForest_actual_150037 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150037) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_150037
    g32p_supplierForest_actual_148850

def g32p_supplierForest_node_150067 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_150067 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150067 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_146365 := by
  decide +kernel

theorem g32p_supplierForest_actual_150067 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150067) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_150067
    g32p_supplierForest_actual_146365

def g32p_supplierForest_node_150074 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_150074 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150074 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087460 := by
  decide +kernel

theorem g32p_supplierForest_actual_150074 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150074) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_150074
    g32p_supplierForest_actual_087460

def g32p_supplierForest_node_150095 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_150095 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150095 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146444 := by
  decide +kernel

theorem g32p_supplierForest_actual_150095 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150095) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_150095
    g32p_supplierForest_actual_146444

def g32p_supplierForest_node_150118 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150118 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150118 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_081859 := by
  decide +kernel

theorem g32p_supplierForest_actual_150118 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150118) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_150118
    g32p_supplierForest_actual_081859

def g32p_supplierForest_node_150119 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_150119 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150119 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_151391 := by
  decide +kernel

theorem g32p_supplierForest_actual_150119 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150119) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_150119
    g32p_supplierForest_actual_151391

def g32p_supplierForest_node_150157 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_150157 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150157 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100838 := by
  decide +kernel

theorem g32p_supplierForest_actual_150157 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150157) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_150157
    g32p_supplierForest_actual_100838

def g32p_supplierForest_node_150159 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150159 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150159 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087311 := by
  decide +kernel

theorem g32p_supplierForest_actual_150159 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150159) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_150159
    g32p_supplierForest_actual_087311

def g32p_supplierForest_node_150165 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_150165 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150165 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_151839 := by
  decide +kernel

theorem g32p_supplierForest_actual_150165 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150165) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_150165
    g32p_supplierForest_actual_151839

def g32p_supplierForest_node_150170 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_150170 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150170 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_095259 := by
  decide +kernel

theorem g32p_supplierForest_actual_150170 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150170) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_150170
    g32p_supplierForest_actual_095259

def g32p_supplierForest_node_150186 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_150186 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150186 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073421 := by
  decide +kernel

theorem g32p_supplierForest_actual_150186 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150186) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_150186
    g32p_supplierForest_actual_073421

def g32p_supplierForest_node_150192 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_150192 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150192 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_150343 := by
  decide +kernel

theorem g32p_supplierForest_actual_150192 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150192) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_150192
    g32p_supplierForest_actual_150343

def g32p_supplierForest_node_150202 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_150202 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150202 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_147009 := by
  decide +kernel

theorem g32p_supplierForest_actual_150202 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150202) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_150202
    g32p_supplierForest_actual_147009

def g32p_supplierForest_node_150217 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_150217 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150217 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093288 := by
  decide +kernel

theorem g32p_supplierForest_actual_150217 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150217) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_150217
    g32p_supplierForest_actual_093288

def g32p_supplierForest_node_150223 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150223 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150223 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152471 := by
  decide +kernel

theorem g32p_supplierForest_actual_150223 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150223) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_150223
    g32p_supplierForest_actual_152471

def g32p_supplierForest_node_150234 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_150234 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150234 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_095565 := by
  decide +kernel

theorem g32p_supplierForest_actual_150234 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150234) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_150234
    g32p_supplierForest_actual_095565

def g32p_supplierForest_node_150283 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150283 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150283 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098154 := by
  decide +kernel

theorem g32p_supplierForest_actual_150283 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150283) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_150283
    g32p_supplierForest_actual_098154

def g32p_supplierForest_node_150291 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_150291 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150291 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_090334 := by
  decide +kernel

theorem g32p_supplierForest_actual_150291 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150291) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_150291
    g32p_supplierForest_actual_090334

def g32p_supplierForest_node_150337 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_150337 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150337 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_099210 := by
  decide +kernel

theorem g32p_supplierForest_actual_150337 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150337) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_150337
    g32p_supplierForest_actual_099210

def g32p_supplierForest_node_150359 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_150359 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150359 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093025 := by
  decide +kernel

theorem g32p_supplierForest_actual_150359 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150359) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_150359
    g32p_supplierForest_actual_093025

def g32p_supplierForest_node_150364 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150364 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150364 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_099142 := by
  decide +kernel

theorem g32p_supplierForest_actual_150364 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150364) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_150364
    g32p_supplierForest_actual_099142

def g32p_supplierForest_node_150365 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150365 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150365 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_149329 := by
  decide +kernel

theorem g32p_supplierForest_actual_150365 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150365) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_150365
    g32p_supplierForest_actual_149329

def g32p_supplierForest_node_150437 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_150437 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150437 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_099849 := by
  decide +kernel

theorem g32p_supplierForest_actual_150437 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150437) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_150437
    g32p_supplierForest_actual_099849

def g32p_supplierForest_node_150452 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_150452 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150452 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_149686 := by
  decide +kernel

theorem g32p_supplierForest_actual_150452 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150452) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_150452
    g32p_supplierForest_actual_149686

def g32p_supplierForest_node_150484 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_150484 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150484 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_148682 := by
  decide +kernel

theorem g32p_supplierForest_actual_150484 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150484) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_150484
    g32p_supplierForest_actual_148682

def g32p_supplierForest_node_150485 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_150485 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150485 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100597 := by
  decide +kernel

theorem g32p_supplierForest_actual_150485 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150485) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_150485
    g32p_supplierForest_actual_100597

def g32p_supplierForest_node_150498 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150498 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150498 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_148588 := by
  decide +kernel

theorem g32p_supplierForest_actual_150498 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150498) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_150498
    g32p_supplierForest_actual_148588

def g32p_supplierForest_node_150504 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_150504 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150504 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_089888 := by
  decide +kernel

theorem g32p_supplierForest_actual_150504 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150504) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_150504
    g32p_supplierForest_actual_089888

def g32p_supplierForest_node_150526 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_150526 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150526 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_145977 := by
  decide +kernel

theorem g32p_supplierForest_actual_150526 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150526) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_150526
    g32p_supplierForest_actual_145977

def g32p_supplierForest_node_150547 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_150547 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150547 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078925 := by
  decide +kernel

theorem g32p_supplierForest_actual_150547 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150547) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_150547
    g32p_supplierForest_actual_078925

def g32p_supplierForest_node_150569 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_150569 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150569 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152252 := by
  decide +kernel

theorem g32p_supplierForest_actual_150569 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150569) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_150569
    g32p_supplierForest_actual_152252

def g32p_supplierForest_node_150579 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_150579 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150579 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_150573 := by
  decide +kernel

theorem g32p_supplierForest_actual_150579 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150579) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_150579
    g32p_supplierForest_actual_150573

def g32p_supplierForest_node_150581 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_150581 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150581 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_150478 := by
  decide +kernel

theorem g32p_supplierForest_actual_150581 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150581) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_150581
    g32p_supplierForest_actual_150478

def g32p_supplierForest_node_150599 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150599 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150599 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_149733 := by
  decide +kernel

theorem g32p_supplierForest_actual_150599 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150599) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_150599
    g32p_supplierForest_actual_149733

def g32p_supplierForest_node_150604 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150604 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150604 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097754 := by
  decide +kernel

theorem g32p_supplierForest_actual_150604 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150604) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_150604
    g32p_supplierForest_actual_097754

def g32p_supplierForest_node_150612 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150612 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150612 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_148931 := by
  decide +kernel

theorem g32p_supplierForest_actual_150612 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150612) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 0 g32p_supplierForest_edge_150612
    g32p_supplierForest_actual_148931

def g32p_supplierForest_node_150630 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150630 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150630 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076934 := by
  decide +kernel

theorem g32p_supplierForest_actual_150630 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150630) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_150630
    g32p_supplierForest_actual_076934

def g32p_supplierForest_node_150642 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150642 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150642 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098864 := by
  decide +kernel

theorem g32p_supplierForest_actual_150642 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150642) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_150642
    g32p_supplierForest_actual_098864

def g32p_supplierForest_node_150663 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_150663 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150663 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_094964 := by
  decide +kernel

theorem g32p_supplierForest_actual_150663 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150663) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_150663
    g32p_supplierForest_actual_094964

def g32p_supplierForest_node_150669 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_150669 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150669 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092834 := by
  decide +kernel

theorem g32p_supplierForest_actual_150669 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150669) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_150669
    g32p_supplierForest_actual_092834

def g32p_supplierForest_node_150709 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_150709 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150709 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_148448 := by
  decide +kernel

theorem g32p_supplierForest_actual_150709 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150709) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_150709
    g32p_supplierForest_actual_148448

def g32p_supplierForest_node_150739 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_150739 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150739 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_094703 := by
  decide +kernel

theorem g32p_supplierForest_actual_150739 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150739) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_150739
    g32p_supplierForest_actual_094703

def g32p_supplierForest_node_150751 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_150751 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150751 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_088167 := by
  decide +kernel

theorem g32p_supplierForest_actual_150751 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150751) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_150751
    g32p_supplierForest_actual_088167

def g32p_supplierForest_node_150754 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_150754 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150754 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_151864 := by
  decide +kernel

theorem g32p_supplierForest_actual_150754 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150754) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_150754
    g32p_supplierForest_actual_151864

def g32p_supplierForest_node_150815 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150815 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150815 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_149878 := by
  decide +kernel

theorem g32p_supplierForest_actual_150815 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150815) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_150815
    g32p_supplierForest_actual_149878

def g32p_supplierForest_node_150818 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_150818 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150818 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083859 := by
  decide +kernel

theorem g32p_supplierForest_actual_150818 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150818) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_150818
    g32p_supplierForest_actual_083859

def g32p_supplierForest_node_150826 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_150826 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150826 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_150341 := by
  decide +kernel

theorem g32p_supplierForest_actual_150826 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150826) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_150826
    g32p_supplierForest_actual_150341

def g32p_supplierForest_node_150894 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_150894 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150894 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152331 := by
  decide +kernel

theorem g32p_supplierForest_actual_150894 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150894) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_150894
    g32p_supplierForest_actual_152331

def g32p_supplierForest_node_150895 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_150895 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150895 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_152330 := by
  decide +kernel

theorem g32p_supplierForest_actual_150895 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150895) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_150895
    g32p_supplierForest_actual_152330

def g32p_supplierForest_node_150979 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_150979 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150979 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152339 := by
  decide +kernel

theorem g32p_supplierForest_actual_150979 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150979) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_150979
    g32p_supplierForest_actual_152339

def g32p_supplierForest_node_150994 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_150994 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150994 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_151298 := by
  decide +kernel

theorem g32p_supplierForest_actual_150994 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150994) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 2 g32p_supplierForest_edge_150994
    g32p_supplierForest_actual_151298

def g32p_supplierForest_node_150996 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_150996 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150996 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_084427 := by
  decide +kernel

theorem g32p_supplierForest_actual_150996 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150996) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_150996
    g32p_supplierForest_actual_084427

def g32p_supplierForest_node_151007 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_151007 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151007 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_148978 := by
  decide +kernel

theorem g32p_supplierForest_actual_151007 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151007) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_151007
    g32p_supplierForest_actual_148978

def g32p_supplierForest_node_151031 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151031 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151031 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_150369 := by
  decide +kernel

theorem g32p_supplierForest_actual_151031 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151031) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_151031
    g32p_supplierForest_actual_150369

def g32p_supplierForest_node_151062 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_151062 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151062 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101581 := by
  decide +kernel

theorem g32p_supplierForest_actual_151062 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151062) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_151062
    g32p_supplierForest_actual_101581

def g32p_supplierForest_node_151065 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151065 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151065 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_096659 := by
  decide +kernel

theorem g32p_supplierForest_actual_151065 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151065) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_151065
    g32p_supplierForest_actual_096659

def g32p_supplierForest_node_151072 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151072 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151072 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_149665 := by
  decide +kernel

theorem g32p_supplierForest_actual_151072 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151072) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_151072
    g32p_supplierForest_actual_149665

def g32p_supplierForest_node_151098 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_151098 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151098 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_151891 := by
  decide +kernel

theorem g32p_supplierForest_actual_151098 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151098) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_151098
    g32p_supplierForest_actual_151891

def g32p_supplierForest_node_151125 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151125 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151125 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_095014 := by
  decide +kernel

theorem g32p_supplierForest_actual_151125 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151125) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_151125
    g32p_supplierForest_actual_095014

def g32p_supplierForest_node_151143 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_151143 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151143 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_150884 := by
  decide +kernel

theorem g32p_supplierForest_actual_151143 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151143) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_151143
    g32p_supplierForest_actual_150884

def g32p_supplierForest_node_151163 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151163 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151163 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_072072 := by
  decide +kernel

theorem g32p_supplierForest_actual_151163 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151163) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_151163
    g32p_supplierForest_actual_072072

def g32p_supplierForest_node_151166 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_151166 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151166 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_151855 := by
  decide +kernel

theorem g32p_supplierForest_actual_151166 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151166) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_151166
    g32p_supplierForest_actual_151855

def g32p_supplierForest_node_151169 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151169 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151169 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_101291 := by
  decide +kernel

theorem g32p_supplierForest_actual_151169 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151169) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_151169
    g32p_supplierForest_actual_101291

def g32p_supplierForest_node_151174 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_151174 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151174 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100602 := by
  decide +kernel

theorem g32p_supplierForest_actual_151174 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151174) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_151174
    g32p_supplierForest_actual_100602

def g32p_supplierForest_node_151217 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151217 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151217 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_147338 := by
  decide +kernel

theorem g32p_supplierForest_actual_151217 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151217) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 0 g32p_supplierForest_edge_151217
    g32p_supplierForest_actual_147338

def g32p_supplierForest_node_151218 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_151218 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151218 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152390 := by
  decide +kernel

theorem g32p_supplierForest_actual_151218 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151218) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_151218
    g32p_supplierForest_actual_152390

def g32p_supplierForest_node_151326 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151326 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151326 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_149769 := by
  decide +kernel

theorem g32p_supplierForest_actual_151326 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151326) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_151326
    g32p_supplierForest_actual_149769

def g32p_supplierForest_node_151336 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_151336 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151336 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_151872 := by
  decide +kernel

theorem g32p_supplierForest_actual_151336 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151336) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_151336
    g32p_supplierForest_actual_151872

def g32p_supplierForest_node_151347 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151347 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151347 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_096339 := by
  decide +kernel

theorem g32p_supplierForest_actual_151347 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151347) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_151347
    g32p_supplierForest_actual_096339

def g32p_supplierForest_node_151354 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_151354 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151354 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_148465 := by
  decide +kernel

theorem g32p_supplierForest_actual_151354 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151354) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_151354
    g32p_supplierForest_actual_148465

def g32p_supplierForest_node_151359 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151359 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151359 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100506 := by
  decide +kernel

theorem g32p_supplierForest_actual_151359 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151359) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_151359
    g32p_supplierForest_actual_100506

def g32p_supplierForest_node_151368 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_151368 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151368 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_151109 := by
  decide +kernel

theorem g32p_supplierForest_actual_151368 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151368) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 2 g32p_supplierForest_edge_151368
    g32p_supplierForest_actual_151109

def g32p_supplierForest_node_151369 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151369 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151369 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_151251 := by
  decide +kernel

theorem g32p_supplierForest_actual_151369 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151369) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_151369
    g32p_supplierForest_actual_151251

def g32p_supplierForest_node_151432 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151432 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151432 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_100646 := by
  decide +kernel

theorem g32p_supplierForest_actual_151432 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151432) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_151432
    g32p_supplierForest_actual_100646

def g32p_supplierForest_node_151443 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151443 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151443 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_150880 := by
  decide +kernel

theorem g32p_supplierForest_actual_151443 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151443) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 3 g32p_supplierForest_edge_151443
    g32p_supplierForest_actual_150880

def g32p_supplierForest_node_151470 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151470 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151470 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_148594 := by
  decide +kernel

theorem g32p_supplierForest_actual_151470 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151470) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_151470
    g32p_supplierForest_actual_148594

def g32p_supplierForest_node_151475 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_151475 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151475 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_090874 := by
  decide +kernel

theorem g32p_supplierForest_actual_151475 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151475) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_151475
    g32p_supplierForest_actual_090874

def g32p_supplierForest_node_151511 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_151511 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151511 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_145972 := by
  decide +kernel

theorem g32p_supplierForest_actual_151511 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151511) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_151511
    g32p_supplierForest_actual_145972

def g32p_supplierForest_node_151535 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_151535 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151535 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_149186 := by
  decide +kernel

theorem g32p_supplierForest_actual_151535 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151535) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_151535
    g32p_supplierForest_actual_149186

def g32p_supplierForest_node_151548 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151548 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151548 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_099844 := by
  decide +kernel

theorem g32p_supplierForest_actual_151548 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151548) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_151548
    g32p_supplierForest_actual_099844

def g32p_supplierForest_node_151564 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151564 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151564 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_151563 := by
  decide +kernel

theorem g32p_supplierForest_actual_151564 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151564) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_151564
    g32p_supplierForest_actual_151563

def g32p_supplierForest_node_151566 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_151566 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151566 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_149242 := by
  decide +kernel

theorem g32p_supplierForest_actual_151566 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151566) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_151566
    g32p_supplierForest_actual_149242

def g32p_supplierForest_node_151567 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_151567 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151567 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_098590 := by
  decide +kernel

theorem g32p_supplierForest_actual_151567 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151567) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 3 g32p_supplierForest_edge_151567
    g32p_supplierForest_actual_098590

def g32p_supplierForest_node_151601 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151601 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151601 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_149159 := by
  decide +kernel

theorem g32p_supplierForest_actual_151601 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151601) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_151601
    g32p_supplierForest_actual_149159

def g32p_supplierForest_node_151602 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_151602 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151602 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093272 := by
  decide +kernel

theorem g32p_supplierForest_actual_151602 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151602) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_151602
    g32p_supplierForest_actual_093272

def g32p_supplierForest_node_151632 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_151632 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151632 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_098620 := by
  decide +kernel

theorem g32p_supplierForest_actual_151632 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151632) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_151632
    g32p_supplierForest_actual_098620

def g32p_supplierForest_node_151669 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_151669 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151669 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_149149 := by
  decide +kernel

theorem g32p_supplierForest_actual_151669 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151669) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 1 g32p_supplierForest_edge_151669
    g32p_supplierForest_actual_149149

def g32p_supplierForest_node_151673 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151673 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151673 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077727 := by
  decide +kernel

theorem g32p_supplierForest_actual_151673 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151673) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_151673
    g32p_supplierForest_actual_077727

def g32p_supplierForest_node_151721 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_151721 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151721 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_084679 := by
  decide +kernel

theorem g32p_supplierForest_actual_151721 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151721) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_151721
    g32p_supplierForest_actual_084679

def g32p_supplierForest_node_151782 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151782 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151782 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_146106 := by
  decide +kernel

theorem g32p_supplierForest_actual_151782 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151782) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 1 g32p_supplierForest_edge_151782
    g32p_supplierForest_actual_146106

def g32p_supplierForest_node_151792 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_151792 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151792 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_152327 := by
  decide +kernel

theorem g32p_supplierForest_actual_151792 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151792) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_151792
    g32p_supplierForest_actual_152327

def g32p_supplierForest_node_151820 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_151820 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151820 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_152029 := by
  decide +kernel

theorem g32p_supplierForest_actual_151820 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151820) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_151820
    g32p_supplierForest_actual_152029

def g32p_supplierForest_node_151837 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151837 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151837 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100795 := by
  decide +kernel

theorem g32p_supplierForest_actual_151837 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151837) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_151837
    g32p_supplierForest_actual_100795

def g32p_supplierForest_node_151848 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_151848 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151848 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_148952 := by
  decide +kernel

theorem g32p_supplierForest_actual_151848 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151848) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_151848
    g32p_supplierForest_actual_148952

def g32p_supplierForest_node_151896 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_151896 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151896 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_098532 := by
  decide +kernel

theorem g32p_supplierForest_actual_151896 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151896) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_151896
    g32p_supplierForest_actual_098532

def g32p_supplierForest_node_151905 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_151905 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151905 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_101191 := by
  decide +kernel

theorem g32p_supplierForest_actual_151905 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151905) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_151905
    g32p_supplierForest_actual_101191

def g32p_supplierForest_node_151931 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_151931 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151931 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_151077 := by
  decide +kernel

theorem g32p_supplierForest_actual_151931 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151931) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_151931
    g32p_supplierForest_actual_151077

def g32p_supplierForest_node_151955 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_151955 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151955 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_146843 := by
  decide +kernel

theorem g32p_supplierForest_actual_151955 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151955) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 3 g32p_supplierForest_edge_151955
    g32p_supplierForest_actual_146843

def g32p_supplierForest_node_151968 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_151968 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151968 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_147432 := by
  decide +kernel

theorem g32p_supplierForest_actual_151968 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151968) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 1 g32p_supplierForest_edge_151968
    g32p_supplierForest_actual_147432

def g32p_supplierForest_node_151977 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_151977 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151977 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_145080 := by
  decide +kernel

theorem g32p_supplierForest_actual_151977 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151977) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_151977
    g32p_supplierForest_actual_145080

def g32p_supplierForest_node_151981 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_151981 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151981 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097774 := by
  decide +kernel

theorem g32p_supplierForest_actual_151981 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151981) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_151981
    g32p_supplierForest_actual_097774

def g32p_supplierForest_node_151989 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_151989 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_151989 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_091627 := by
  decide +kernel

theorem g32p_supplierForest_actual_151989 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_151989) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_151989
    g32p_supplierForest_actual_091627

def g32p_supplierForest_node_152011 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_152011 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152011 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_091926 := by
  decide +kernel

theorem g32p_supplierForest_actual_152011 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152011) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_152011
    g32p_supplierForest_actual_091926

def g32p_supplierForest_node_152081 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_152081 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152081 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_144904 := by
  decide +kernel

theorem g32p_supplierForest_actual_152081 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152081) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_152081
    g32p_supplierForest_actual_144904

def g32p_supplierForest_node_152093 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_152093 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152093 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_152042 := by
  decide +kernel

theorem g32p_supplierForest_actual_152093 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152093) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_152093
    g32p_supplierForest_actual_152042

def g32p_supplierForest_node_152106 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152106 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152106 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073850 := by
  decide +kernel

theorem g32p_supplierForest_actual_152106 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152106) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_152106
    g32p_supplierForest_actual_073850

def g32p_supplierForest_node_152115 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_152115 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152115 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152464 := by
  decide +kernel

theorem g32p_supplierForest_actual_152115 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152115) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_152115
    g32p_supplierForest_actual_152464

def g32p_supplierForest_node_152144 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_152144 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152144 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_148803 := by
  decide +kernel

theorem g32p_supplierForest_actual_152144 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152144) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 3 g32p_supplierForest_edge_152144
    g32p_supplierForest_actual_148803

def g32p_supplierForest_node_152178 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_152178 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152178 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_147281 := by
  decide +kernel

theorem g32p_supplierForest_actual_152178 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152178) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_152178
    g32p_supplierForest_actual_147281

def g32p_supplierForest_node_152205 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_152205 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152205 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146704 := by
  decide +kernel

theorem g32p_supplierForest_actual_152205 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152205) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_152205
    g32p_supplierForest_actual_146704

def g32p_supplierForest_node_152238 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_152238 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152238 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_147287 := by
  decide +kernel

theorem g32p_supplierForest_actual_152238 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152238) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_152238
    g32p_supplierForest_actual_147287

def g32p_supplierForest_node_152286 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_152286 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152286 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_145428 := by
  decide +kernel

theorem g32p_supplierForest_actual_152286 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152286) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_152286
    g32p_supplierForest_actual_145428

def g32p_supplierForest_node_152292 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_152292 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152292 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100894 := by
  decide +kernel

theorem g32p_supplierForest_actual_152292 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152292) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 1 g32p_supplierForest_edge_152292
    g32p_supplierForest_actual_100894

def g32p_supplierForest_node_152299 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_152299 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152299 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_151688 := by
  decide +kernel

theorem g32p_supplierForest_actual_152299 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152299) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_152299
    g32p_supplierForest_actual_151688

def g32p_supplierForest_node_152357 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_152357 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152357 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_152050 := by
  decide +kernel

theorem g32p_supplierForest_actual_152357 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152357) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_152357
    g32p_supplierForest_actual_152050

def g32p_supplierForest_node_152382 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_152382 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152382 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_149548 := by
  decide +kernel

theorem g32p_supplierForest_actual_152382 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152382) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_152382
    g32p_supplierForest_actual_149548

def g32p_supplierForest_node_152392 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_152392 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152392 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_146821 := by
  decide +kernel

theorem g32p_supplierForest_actual_152392 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152392) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_152392
    g32p_supplierForest_actual_146821

def g32p_supplierForest_node_152405 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152405 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152405 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_149067 := by
  decide +kernel

theorem g32p_supplierForest_actual_152405 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152405) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 0 g32p_supplierForest_edge_152405
    g32p_supplierForest_actual_149067

def g32p_supplierForest_node_152515 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152515 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152515 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153995 := by
  decide +kernel

theorem g32p_supplierForest_actual_152515 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152515) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 2 g32p_supplierForest_edge_152515
    g32p_supplierForest_actual_153995

def g32p_supplierForest_node_152517 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_152517 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152517 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_114581 := by
  decide +kernel

theorem g32p_supplierForest_actual_152517 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152517) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_152517
    g32p_supplierForest_actual_114581

def g32p_supplierForest_node_152554 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_152554 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152554 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_114669 := by
  decide +kernel

theorem g32p_supplierForest_actual_152554 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152554) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_152554
    g32p_supplierForest_actual_114669

def g32p_supplierForest_node_152586 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152586 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152586 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_115669 := by
  decide +kernel

theorem g32p_supplierForest_actual_152586 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152586) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_152586
    g32p_supplierForest_actual_115669

def g32p_supplierForest_node_152589 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_152589 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152589 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120787 := by
  decide +kernel

theorem g32p_supplierForest_actual_152589 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152589) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_152589
    g32p_supplierForest_actual_120787

def g32p_supplierForest_node_152600 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152600 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152600 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_118578 := by
  decide +kernel

theorem g32p_supplierForest_actual_152600 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152600) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_152600
    g32p_supplierForest_actual_118578

def g32p_supplierForest_node_152602 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_152602 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152602 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153770 := by
  decide +kernel

theorem g32p_supplierForest_actual_152602 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152602) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_152602
    g32p_supplierForest_actual_153770

def g32p_supplierForest_node_152662 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152662 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152662 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152511 := by
  decide +kernel

theorem g32p_supplierForest_actual_152662 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152662) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 2 g32p_supplierForest_edge_152662
    g32p_supplierForest_actual_152511

def g32p_supplierForest_node_152676 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_152676 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152676 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_152961 := by
  decide +kernel

theorem g32p_supplierForest_actual_152676 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152676) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_152676
    g32p_supplierForest_actual_152961

def g32p_supplierForest_node_152718 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_152718 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152718 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115113 := by
  decide +kernel

theorem g32p_supplierForest_actual_152718 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152718) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_152718
    g32p_supplierForest_actual_115113

def g32p_supplierForest_node_152725 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_152725 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152725 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_154235 := by
  decide +kernel

theorem g32p_supplierForest_actual_152725 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152725) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_152725
    g32p_supplierForest_actual_154235

def g32p_supplierForest_node_152765 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_152765 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152765 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123890 := by
  decide +kernel

theorem g32p_supplierForest_actual_152765 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152765) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_152765
    g32p_supplierForest_actual_123890

def g32p_supplierForest_node_152767 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_152767 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152767 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153045 := by
  decide +kernel

theorem g32p_supplierForest_actual_152767 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152767) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_152767
    g32p_supplierForest_actual_153045

def g32p_supplierForest_node_152769 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152769 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152769 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104152 := by
  decide +kernel

theorem g32p_supplierForest_actual_152769 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152769) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_152769
    g32p_supplierForest_actual_104152

def g32p_supplierForest_node_152786 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_152786 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152786 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122387 := by
  decide +kernel

theorem g32p_supplierForest_actual_152786 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152786) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_152786
    g32p_supplierForest_actual_122387

def g32p_supplierForest_node_152803 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_152803 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152803 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115237 := by
  decide +kernel

theorem g32p_supplierForest_actual_152803 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152803) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_152803
    g32p_supplierForest_actual_115237

def g32p_supplierForest_node_152809 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_152809 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152809 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_123579 := by
  decide +kernel

theorem g32p_supplierForest_actual_152809 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152809) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_152809
    g32p_supplierForest_actual_123579

def g32p_supplierForest_node_152823 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_152823 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152823 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153152 := by
  decide +kernel

theorem g32p_supplierForest_actual_152823 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152823) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_152823
    g32p_supplierForest_actual_153152

def g32p_supplierForest_node_152837 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_152837 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152837 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112780 := by
  decide +kernel

theorem g32p_supplierForest_actual_152837 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152837) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_152837
    g32p_supplierForest_actual_112780

def g32p_supplierForest_node_152847 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152847 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152847 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_125644 := by
  decide +kernel

theorem g32p_supplierForest_actual_152847 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152847) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 0 g32p_supplierForest_edge_152847
    g32p_supplierForest_actual_125644

def g32p_supplierForest_node_152848 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152848 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152848 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_105192 := by
  decide +kernel

theorem g32p_supplierForest_actual_152848 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152848) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_152848
    g32p_supplierForest_actual_105192

def g32p_supplierForest_node_152850 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152850 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152850 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153921 := by
  decide +kernel

theorem g32p_supplierForest_actual_152850 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152850) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_152850
    g32p_supplierForest_actual_153921

def g32p_supplierForest_node_152905 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_152905 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152905 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122937 := by
  decide +kernel

theorem g32p_supplierForest_actual_152905 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152905) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_152905
    g32p_supplierForest_actual_122937

def g32p_supplierForest_node_152928 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_152928 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152928 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153379 := by
  decide +kernel

theorem g32p_supplierForest_actual_152928 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152928) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_152928
    g32p_supplierForest_actual_153379

def g32p_supplierForest_node_152955 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_152955 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152955 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118917 := by
  decide +kernel

theorem g32p_supplierForest_actual_152955 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152955) ∧
        IsConj g (g32p_literalRepresentative 65) := by
  exact g32p_archive_step_lift _ _ 65 3 g32p_supplierForest_edge_152955
    g32p_supplierForest_actual_118917

def g32p_supplierForest_node_152956 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152956 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152956 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_126792 := by
  decide +kernel

theorem g32p_supplierForest_actual_152956 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152956) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_152956
    g32p_supplierForest_actual_126792

def g32p_supplierForest_node_152962 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152962 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152962 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_154677 := by
  decide +kernel

theorem g32p_supplierForest_actual_152962 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152962) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_152962
    g32p_supplierForest_actual_154677

def g32p_supplierForest_node_153016 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153016 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153016 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_127404 := by
  decide +kernel

theorem g32p_supplierForest_actual_153016 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153016) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 3 g32p_supplierForest_edge_153016
    g32p_supplierForest_actual_127404

def g32p_supplierForest_node_153037 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153037 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153037 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_126335 := by
  decide +kernel

theorem g32p_supplierForest_actual_153037 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153037) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 2 g32p_supplierForest_edge_153037
    g32p_supplierForest_actual_126335

def g32p_supplierForest_node_153073 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153073 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153073 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153207 := by
  decide +kernel

theorem g32p_supplierForest_actual_153073 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153073) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 1 g32p_supplierForest_edge_153073
    g32p_supplierForest_actual_153207

def g32p_supplierForest_node_153149 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_153149 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153149 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115046 := by
  decide +kernel

theorem g32p_supplierForest_actual_153149 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153149) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_153149
    g32p_supplierForest_actual_115046

def g32p_supplierForest_node_153174 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153174 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153174 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_127224 := by
  decide +kernel

theorem g32p_supplierForest_actual_153174 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153174) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_153174
    g32p_supplierForest_actual_127224

def g32p_supplierForest_node_153180 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_153180 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153180 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152511 := by
  decide +kernel

theorem g32p_supplierForest_actual_153180 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153180) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 0 g32p_supplierForest_edge_153180
    g32p_supplierForest_actual_152511

def g32p_supplierForest_node_153220 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153220 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153220 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_105319 := by
  decide +kernel

theorem g32p_supplierForest_actual_153220 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153220) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_153220
    g32p_supplierForest_actual_105319

def g32p_supplierForest_node_153264 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153264 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153264 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_152770 := by
  decide +kernel

theorem g32p_supplierForest_actual_153264 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153264) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 1 g32p_supplierForest_edge_153264
    g32p_supplierForest_actual_152770

def g32p_supplierForest_node_153329 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153329 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153329 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_119063 := by
  decide +kernel

theorem g32p_supplierForest_actual_153329 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153329) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 0 g32p_supplierForest_edge_153329
    g32p_supplierForest_actual_119063

def g32p_supplierForest_node_153352 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153352 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153352 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_115463 := by
  decide +kernel

theorem g32p_supplierForest_actual_153352 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153352) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_153352
    g32p_supplierForest_actual_115463

def g32p_supplierForest_node_153353 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153353 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153353 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_127678 := by
  decide +kernel

theorem g32p_supplierForest_actual_153353 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153353) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_153353
    g32p_supplierForest_actual_127678

def g32p_supplierForest_node_153356 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153356 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153356 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_106247 := by
  decide +kernel

theorem g32p_supplierForest_actual_153356 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153356) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_153356
    g32p_supplierForest_actual_106247

def g32p_supplierForest_node_153390 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153390 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153390 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_114422 := by
  decide +kernel

theorem g32p_supplierForest_actual_153390 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153390) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_153390
    g32p_supplierForest_actual_114422

def g32p_supplierForest_node_153428 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153428 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153428 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153702 := by
  decide +kernel

theorem g32p_supplierForest_actual_153428 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153428) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_153428
    g32p_supplierForest_actual_153702

def g32p_supplierForest_node_153468 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153468 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153468 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_121742 := by
  decide +kernel

theorem g32p_supplierForest_actual_153468 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153468) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_153468
    g32p_supplierForest_actual_121742

def g32p_supplierForest_node_153493 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153493 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153493 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153077 := by
  decide +kernel

theorem g32p_supplierForest_actual_153493 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153493) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 3 g32p_supplierForest_edge_153493
    g32p_supplierForest_actual_153077

def g32p_supplierForest_node_153513 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153513 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153513 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153671 := by
  decide +kernel

theorem g32p_supplierForest_actual_153513 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153513) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_153513
    g32p_supplierForest_actual_153671

def g32p_supplierForest_node_153539 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153539 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153539 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_116604 := by
  decide +kernel

theorem g32p_supplierForest_actual_153539 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153539) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_153539
    g32p_supplierForest_actual_116604

def g32p_supplierForest_node_153549 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_153549 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153549 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122218 := by
  decide +kernel

theorem g32p_supplierForest_actual_153549 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153549) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_153549
    g32p_supplierForest_actual_122218

def g32p_supplierForest_node_153567 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153567 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153567 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153169 := by
  decide +kernel

theorem g32p_supplierForest_actual_153567 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153567) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_153567
    g32p_supplierForest_actual_153169

def g32p_supplierForest_node_153577 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_153577 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153577 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152666 := by
  decide +kernel

theorem g32p_supplierForest_actual_153577 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153577) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 2 g32p_supplierForest_edge_153577
    g32p_supplierForest_actual_152666

def g32p_supplierForest_node_153603 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_153603 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153603 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152900 := by
  decide +kernel

theorem g32p_supplierForest_actual_153603 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153603) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_153603
    g32p_supplierForest_actual_152900

def g32p_supplierForest_node_153620 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153620 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153620 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_119287 := by
  decide +kernel

theorem g32p_supplierForest_actual_153620 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153620) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 3 g32p_supplierForest_edge_153620
    g32p_supplierForest_actual_119287

def g32p_supplierForest_node_153659 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153659 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153659 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152575 := by
  decide +kernel

theorem g32p_supplierForest_actual_153659 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153659) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 2 g32p_supplierForest_edge_153659
    g32p_supplierForest_actual_152575

def g32p_supplierForest_node_153751 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153751 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153751 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_119445 := by
  decide +kernel

theorem g32p_supplierForest_actual_153751 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153751) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_153751
    g32p_supplierForest_actual_119445

def g32p_supplierForest_node_153845 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153845 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153845 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_127279 := by
  decide +kernel

theorem g32p_supplierForest_actual_153845 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153845) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_153845
    g32p_supplierForest_actual_127279

def g32p_supplierForest_node_153853 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153853 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153853 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_127010 := by
  decide +kernel

theorem g32p_supplierForest_actual_153853 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153853) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_153853
    g32p_supplierForest_actual_127010

def g32p_supplierForest_node_153878 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153878 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153878 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154524 := by
  decide +kernel

theorem g32p_supplierForest_actual_153878 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153878) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_153878
    g32p_supplierForest_actual_154524

def g32p_supplierForest_node_153916 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_153916 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153916 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154140 := by
  decide +kernel

theorem g32p_supplierForest_actual_153916 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153916) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_153916
    g32p_supplierForest_actual_154140

def g32p_supplierForest_node_153949 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153949 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153949 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_121674 := by
  decide +kernel

theorem g32p_supplierForest_actual_153949 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153949) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_153949
    g32p_supplierForest_actual_121674

def g32p_supplierForest_node_154002 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154002 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154002 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_152812 := by
  decide +kernel

theorem g32p_supplierForest_actual_154002 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154002) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_154002
    g32p_supplierForest_actual_152812

def g32p_supplierForest_node_154017 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154017 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154017 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_105912 := by
  decide +kernel

theorem g32p_supplierForest_actual_154017 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154017) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_154017
    g32p_supplierForest_actual_105912

def g32p_supplierForest_node_154051 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154051 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154051 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153652 := by
  decide +kernel

theorem g32p_supplierForest_actual_154051 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154051) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_154051
    g32p_supplierForest_actual_153652

def g32p_supplierForest_node_154083 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_154083 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154083 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113590 := by
  decide +kernel

theorem g32p_supplierForest_actual_154083 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154083) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_154083
    g32p_supplierForest_actual_113590

def g32p_supplierForest_node_154085 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154085 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154085 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152932 := by
  decide +kernel

theorem g32p_supplierForest_actual_154085 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154085) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_154085
    g32p_supplierForest_actual_152932

def g32p_supplierForest_node_154149 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154149 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154149 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153067 := by
  decide +kernel

theorem g32p_supplierForest_actual_154149 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154149) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_154149
    g32p_supplierForest_actual_153067

def g32p_supplierForest_node_154159 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154159 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154159 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115812 := by
  decide +kernel

theorem g32p_supplierForest_actual_154159 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154159) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_154159
    g32p_supplierForest_actual_115812

def g32p_supplierForest_node_154203 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_154203 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154203 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_123181 := by
  decide +kernel

theorem g32p_supplierForest_actual_154203 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154203) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_154203
    g32p_supplierForest_actual_123181

def g32p_supplierForest_node_154217 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_154217 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154217 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_106290 := by
  decide +kernel

theorem g32p_supplierForest_actual_154217 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154217) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_154217
    g32p_supplierForest_actual_106290

def g32p_supplierForest_node_154219 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_154219 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154219 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_152624 := by
  decide +kernel

theorem g32p_supplierForest_actual_154219 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154219) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 3 g32p_supplierForest_edge_154219
    g32p_supplierForest_actual_152624

def g32p_supplierForest_node_154281 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_154281 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154281 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_119653 := by
  decide +kernel

theorem g32p_supplierForest_actual_154281 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154281) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_154281
    g32p_supplierForest_actual_119653

def g32p_supplierForest_node_154288 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_154288 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154288 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_124006 := by
  decide +kernel

theorem g32p_supplierForest_actual_154288 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154288) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_154288
    g32p_supplierForest_actual_124006

def g32p_supplierForest_node_154318 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_154318 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154318 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_154808 := by
  decide +kernel

theorem g32p_supplierForest_actual_154318 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154318) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_154318
    g32p_supplierForest_actual_154808

def g32p_supplierForest_node_154334 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154334 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154334 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_126737 := by
  decide +kernel

theorem g32p_supplierForest_actual_154334 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154334) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_154334
    g32p_supplierForest_actual_126737

def g32p_supplierForest_node_154394 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_154394 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154394 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154465 := by
  decide +kernel

theorem g32p_supplierForest_actual_154394 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154394) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 3 g32p_supplierForest_edge_154394
    g32p_supplierForest_actual_154465

def g32p_supplierForest_node_154506 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154506 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154506 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153207 := by
  decide +kernel

theorem g32p_supplierForest_actual_154506 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154506) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_154506
    g32p_supplierForest_actual_153207

def g32p_supplierForest_node_154511 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_154511 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154511 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_154753 := by
  decide +kernel

theorem g32p_supplierForest_actual_154511 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154511) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 0 g32p_supplierForest_edge_154511
    g32p_supplierForest_actual_154753

def g32p_supplierForest_node_154543 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154543 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154543 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_120111 := by
  decide +kernel

theorem g32p_supplierForest_actual_154543 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154543) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_154543
    g32p_supplierForest_actual_120111

def g32p_supplierForest_node_154550 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154550 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154550 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_124590 := by
  decide +kernel

theorem g32p_supplierForest_actual_154550 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154550) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_154550
    g32p_supplierForest_actual_124590

def g32p_supplierForest_node_154552 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_154552 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154552 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_124971 := by
  decide +kernel

theorem g32p_supplierForest_actual_154552 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154552) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 3 g32p_supplierForest_edge_154552
    g32p_supplierForest_actual_124971

def g32p_supplierForest_node_154591 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154591 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154591 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_126331 := by
  decide +kernel

theorem g32p_supplierForest_actual_154591 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154591) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_154591
    g32p_supplierForest_actual_126331

def g32p_supplierForest_node_154614 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154614 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154614 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_125417 := by
  decide +kernel

theorem g32p_supplierForest_actual_154614 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154614) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_154614
    g32p_supplierForest_actual_125417

def g32p_supplierForest_node_154618 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154618 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154618 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154592 := by
  decide +kernel

theorem g32p_supplierForest_actual_154618 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154618) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_154618
    g32p_supplierForest_actual_154592

def g32p_supplierForest_node_154683 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_154683 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154683 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_124549 := by
  decide +kernel

theorem g32p_supplierForest_actual_154683 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154683) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_154683
    g32p_supplierForest_actual_124549

def g32p_supplierForest_node_154694 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154694 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154694 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_154783 := by
  decide +kernel

theorem g32p_supplierForest_actual_154694 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154694) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_154694
    g32p_supplierForest_actual_154783

def g32p_supplierForest_node_154725 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154725 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154725 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154731 := by
  decide +kernel

theorem g32p_supplierForest_actual_154725 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154725) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_154725
    g32p_supplierForest_actual_154731

def g32p_supplierForest_node_154764 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154764 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154764 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_152763 := by
  decide +kernel

theorem g32p_supplierForest_actual_154764 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154764) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_154764
    g32p_supplierForest_actual_152763

def g32p_supplierForest_node_154771 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154771 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154771 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_154111 := by
  decide +kernel

theorem g32p_supplierForest_actual_154771 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154771) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 1 g32p_supplierForest_edge_154771
    g32p_supplierForest_actual_154111

def g32p_supplierForest_node_154796 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_154796 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154796 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_124585 := by
  decide +kernel

theorem g32p_supplierForest_actual_154796 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154796) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_154796
    g32p_supplierForest_actual_124585

def g32p_supplierForest_node_154819 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154819 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154819 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154185 := by
  decide +kernel

theorem g32p_supplierForest_actual_154819 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154819) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_154819
    g32p_supplierForest_actual_154185

def g32p_supplierForest_node_154869 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154869 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154869 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_125464 := by
  decide +kernel

theorem g32p_supplierForest_actual_154869 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154869) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_154869
    g32p_supplierForest_actual_125464

def g32p_supplierForest_node_154897 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154897 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154897 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153043 := by
  decide +kernel

theorem g32p_supplierForest_actual_154897 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154897) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_154897
    g32p_supplierForest_actual_153043

def g32p_supplierForest_node_154905 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154905 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154905 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122154 := by
  decide +kernel

theorem g32p_supplierForest_actual_154905 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154905) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 1 g32p_supplierForest_edge_154905
    g32p_supplierForest_actual_122154

def g32p_supplierForest_node_154955 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154955 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154955 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_127444 := by
  decide +kernel

theorem g32p_supplierForest_actual_154955 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154955) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 1 g32p_supplierForest_edge_154955
    g32p_supplierForest_actual_127444

def g32p_supplierForest_node_154968 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154968 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154968 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153423 := by
  decide +kernel

theorem g32p_supplierForest_actual_154968 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154968) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_154968
    g32p_supplierForest_actual_153423

def g32p_supplierForest_node_154984 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154984 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154984 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126907 := by
  decide +kernel

theorem g32p_supplierForest_actual_154984 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154984) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 1 g32p_supplierForest_edge_154984
    g32p_supplierForest_actual_126907

def g32p_supplierForest_node_154985 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_154985 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154985 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_126430 := by
  decide +kernel

theorem g32p_supplierForest_actual_154985 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154985) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_154985
    g32p_supplierForest_actual_126430

def g32p_supplierForest_node_154987 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_154987 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154987 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126436 := by
  decide +kernel

theorem g32p_supplierForest_actual_154987 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154987) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 1 g32p_supplierForest_edge_154987
    g32p_supplierForest_actual_126436

def g32p_supplierForest_node_155009 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_155009 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155009 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_139998 := by
  decide +kernel

theorem g32p_supplierForest_actual_155009 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155009) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_155009
    g32p_supplierForest_actual_139998

def g32p_supplierForest_node_155017 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155017 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155017 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_139529 := by
  decide +kernel

theorem g32p_supplierForest_actual_155017 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155017) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 2 g32p_supplierForest_edge_155017
    g32p_supplierForest_actual_139529

def g32p_supplierForest_node_155033 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155033 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155033 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_130453 := by
  decide +kernel

theorem g32p_supplierForest_actual_155033 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155033) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 3 g32p_supplierForest_edge_155033
    g32p_supplierForest_actual_130453

def g32p_supplierForest_node_155047 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_155047 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155047 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_141145 := by
  decide +kernel

theorem g32p_supplierForest_actual_155047 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155047) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_155047
    g32p_supplierForest_actual_141145

def g32p_supplierForest_node_155125 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155125 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155125 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_130572 := by
  decide +kernel

theorem g32p_supplierForest_actual_155125 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155125) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 3 g32p_supplierForest_edge_155125
    g32p_supplierForest_actual_130572

def g32p_supplierForest_node_155157 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155157 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155157 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_141917 := by
  decide +kernel

theorem g32p_supplierForest_actual_155157 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155157) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 2 g32p_supplierForest_edge_155157
    g32p_supplierForest_actual_141917

def g32p_supplierForest_node_155165 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155165 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155165 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_144524 := by
  decide +kernel

theorem g32p_supplierForest_actual_155165 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155165) ∧
        IsConj g (g32p_literalRepresentative 94) := by
  exact g32p_archive_step_lift _ _ 94 1 g32p_supplierForest_edge_155165
    g32p_supplierForest_actual_144524

def g32p_supplierForest_node_155215 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_155215 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155215 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_142536 := by
  decide +kernel

theorem g32p_supplierForest_actual_155215 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155215) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_155215
    g32p_supplierForest_actual_142536

def g32p_supplierForest_node_155217 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_155217 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155217 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_142754 := by
  decide +kernel

theorem g32p_supplierForest_actual_155217 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155217) ∧
        IsConj g (g32p_literalRepresentative 94) := by
  exact g32p_archive_step_lift _ _ 94 3 g32p_supplierForest_edge_155217
    g32p_supplierForest_actual_142754

def g32p_supplierForest_node_155259 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155259 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155259 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_134871 := by
  decide +kernel

theorem g32p_supplierForest_actual_155259 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155259) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 3 g32p_supplierForest_edge_155259
    g32p_supplierForest_actual_134871

def g32p_supplierForest_node_155288 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_155288 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155288 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_155055 := by
  decide +kernel

theorem g32p_supplierForest_actual_155288 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155288) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 3 g32p_supplierForest_edge_155288
    g32p_supplierForest_actual_155055

def g32p_supplierForest_node_155340 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155340 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155340 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_155308 := by
  decide +kernel

theorem g32p_supplierForest_actual_155340 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155340) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 2 g32p_supplierForest_edge_155340
    g32p_supplierForest_actual_155308

def g32p_supplierForest_node_155362 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155362 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155362 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_139163 := by
  decide +kernel

theorem g32p_supplierForest_actual_155362 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155362) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 2 g32p_supplierForest_edge_155362
    g32p_supplierForest_actual_139163

def g32p_supplierForest_node_155366 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155366 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155366 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_142967 := by
  decide +kernel

theorem g32p_supplierForest_actual_155366 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155366) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 3 g32p_supplierForest_edge_155366
    g32p_supplierForest_actual_142967

def g32p_supplierForest_node_155373 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155373 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155373 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_135751 := by
  decide +kernel

theorem g32p_supplierForest_actual_155373 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155373) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 3 g32p_supplierForest_edge_155373
    g32p_supplierForest_actual_135751

def g32p_supplierForest_node_155378 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155378 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155378 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_139090 := by
  decide +kernel

theorem g32p_supplierForest_actual_155378 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155378) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 3 g32p_supplierForest_edge_155378
    g32p_supplierForest_actual_139090

def g32p_supplierForest_node_000253 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_000253 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000253 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000244 := by
  decide +kernel

theorem g32p_supplierForest_actual_000253 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000253) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 3 g32p_supplierForest_edge_000253
    g32p_supplierForest_actual_000244

def g32p_supplierForest_node_000293 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_000293 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000293 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_000282 := by
  decide +kernel

theorem g32p_supplierForest_actual_000293 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000293) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_000293
    g32p_supplierForest_actual_000282

def g32p_supplierForest_node_000385 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000385 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000385 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_005325 := by
  decide +kernel

theorem g32p_supplierForest_actual_000385 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000385) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_000385
    g32p_supplierForest_actual_005325

def g32p_supplierForest_node_000411 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000411 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000411 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_002897 := by
  decide +kernel

theorem g32p_supplierForest_actual_000411 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000411) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_000411
    g32p_supplierForest_actual_002897

def g32p_supplierForest_node_000460 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_000460 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000460 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_006976 := by
  decide +kernel

theorem g32p_supplierForest_actual_000460 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000460) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_000460
    g32p_supplierForest_actual_006976

def g32p_supplierForest_node_000562 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000562 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000562 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_007108 := by
  decide +kernel

theorem g32p_supplierForest_actual_000562 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000562) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_000562
    g32p_supplierForest_actual_007108

def g32p_supplierForest_node_000565 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_000565 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000565 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_007322 := by
  decide +kernel

theorem g32p_supplierForest_actual_000565 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000565) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_000565
    g32p_supplierForest_actual_007322

def g32p_supplierForest_node_000652 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000652 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000652 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001024 := by
  decide +kernel

theorem g32p_supplierForest_actual_000652 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000652) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 0 g32p_supplierForest_edge_000652
    g32p_supplierForest_actual_001024

def g32p_supplierForest_node_000754 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_000754 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000754 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_011107 := by
  decide +kernel

theorem g32p_supplierForest_actual_000754 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000754) ∧
        IsConj g (g32p_literalRepresentative 23) := by
  exact g32p_archive_step_lift _ _ 23 2 g32p_supplierForest_edge_000754
    g32p_supplierForest_actual_011107

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_104 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_109537 else g32p_supplierForest_node_109576) else (if i.val < 3 then g32p_supplierForest_node_109618 else g32p_supplierForest_node_109653)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_109687 else g32p_supplierForest_node_109709) else (if i.val < 7 then g32p_supplierForest_node_109715 else g32p_supplierForest_node_109719))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_109738 else g32p_supplierForest_node_109744) else (if i.val < 11 then g32p_supplierForest_node_109756 else g32p_supplierForest_node_109789)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_109793 else g32p_supplierForest_node_109832) else (if i.val < 15 then g32p_supplierForest_node_109834 else g32p_supplierForest_node_109839)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_109851 else g32p_supplierForest_node_109905) else (if i.val < 19 then g32p_supplierForest_node_109924 else g32p_supplierForest_node_109942)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_109958 else g32p_supplierForest_node_109997) else (if i.val < 23 then g32p_supplierForest_node_110006 else g32p_supplierForest_node_110010))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_110040 else g32p_supplierForest_node_110042) else (if i.val < 27 then g32p_supplierForest_node_110044 else g32p_supplierForest_node_110061)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_110063 else g32p_supplierForest_node_110070) else (if i.val < 31 then g32p_supplierForest_node_110098 else g32p_supplierForest_node_110107))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_110112 else g32p_supplierForest_node_110123) else (if i.val < 35 then g32p_supplierForest_node_110132 else g32p_supplierForest_node_110143)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_110177 else g32p_supplierForest_node_110210) else (if i.val < 39 then g32p_supplierForest_node_110216 else g32p_supplierForest_node_110237))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_110239 else g32p_supplierForest_node_110249) else (if i.val < 43 then g32p_supplierForest_node_110291 else g32p_supplierForest_node_110293)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_110302 else g32p_supplierForest_node_110336) else (if i.val < 47 then g32p_supplierForest_node_110411 else g32p_supplierForest_node_110415)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_110433 else g32p_supplierForest_node_110531) else (if i.val < 51 then g32p_supplierForest_node_110534 else g32p_supplierForest_node_110535)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_110572 else g32p_supplierForest_node_110597) else (if i.val < 55 then g32p_supplierForest_node_110606 else g32p_supplierForest_node_110626))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_110664 else g32p_supplierForest_node_110686) else (if i.val < 59 then g32p_supplierForest_node_110724 else g32p_supplierForest_node_110726)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_110821 else g32p_supplierForest_node_110832) else (if i.val < 63 then g32p_supplierForest_node_110844 else g32p_supplierForest_node_110872)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_110874 else g32p_supplierForest_node_110923) else (if i.val < 67 then g32p_supplierForest_node_110929 else g32p_supplierForest_node_110963)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_111011 else g32p_supplierForest_node_111030) else (if i.val < 71 then g32p_supplierForest_node_111037 else g32p_supplierForest_node_111057))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_111059 else g32p_supplierForest_node_111071) else (if i.val < 75 then g32p_supplierForest_node_111110 else g32p_supplierForest_node_111127)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_111130 else g32p_supplierForest_node_111172) else (if i.val < 79 then g32p_supplierForest_node_111243 else g32p_supplierForest_node_111251)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_111299 else g32p_supplierForest_node_111364) else (if i.val < 83 then g32p_supplierForest_node_111380 else g32p_supplierForest_node_111398)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_111423 else g32p_supplierForest_node_111494) else (if i.val < 87 then g32p_supplierForest_node_111515 else g32p_supplierForest_node_111522))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_111591 else g32p_supplierForest_node_111598) else (if i.val < 91 then g32p_supplierForest_node_111599 else g32p_supplierForest_node_111605)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_111626 else g32p_supplierForest_node_111637) else (if i.val < 95 then g32p_supplierForest_node_111654 else g32p_supplierForest_node_111666))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_111725 else g32p_supplierForest_node_111752) else (if i.val < 99 then g32p_supplierForest_node_111771 else g32p_supplierForest_node_111773)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_111796 else g32p_supplierForest_node_111858) else (if i.val < 103 then g32p_supplierForest_node_111873 else g32p_supplierForest_node_111895))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_111899 else g32p_supplierForest_node_111916) else (if i.val < 107 then g32p_supplierForest_node_111975 else g32p_supplierForest_node_111984)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_112062 else g32p_supplierForest_node_112151) else (if i.val < 111 then g32p_supplierForest_node_112166 else g32p_supplierForest_node_112286)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_112360 else g32p_supplierForest_node_112380) else (if i.val < 115 then g32p_supplierForest_node_112394 else g32p_supplierForest_node_112399)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_112410 else g32p_supplierForest_node_112413) else (if i.val < 119 then g32p_supplierForest_node_112466 else g32p_supplierForest_node_112482))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_112511 else g32p_supplierForest_node_112517) else (if i.val < 123 then g32p_supplierForest_node_112526 else g32p_supplierForest_node_112567)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_112585 else g32p_supplierForest_node_112629) else (if i.val < 127 then g32p_supplierForest_node_112634 else g32p_supplierForest_node_112636))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_112641 else g32p_supplierForest_node_112655) else (if i.val < 131 then g32p_supplierForest_node_112679 else g32p_supplierForest_node_112740)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_112753 else g32p_supplierForest_node_112789) else (if i.val < 135 then g32p_supplierForest_node_112830 else g32p_supplierForest_node_112856))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_112897 else g32p_supplierForest_node_112908) else (if i.val < 139 then g32p_supplierForest_node_112966 else g32p_supplierForest_node_112975)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_112984 else g32p_supplierForest_node_113015) else (if i.val < 143 then g32p_supplierForest_node_113059 else g32p_supplierForest_node_113070)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_113087 else g32p_supplierForest_node_113095) else (if i.val < 147 then g32p_supplierForest_node_113106 else g32p_supplierForest_node_113163)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_113170 else g32p_supplierForest_node_113209) else (if i.val < 151 then g32p_supplierForest_node_113232 else g32p_supplierForest_node_113239))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_113270 else g32p_supplierForest_node_113345) else (if i.val < 155 then g32p_supplierForest_node_113354 else g32p_supplierForest_node_113369)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_113380 else g32p_supplierForest_node_113396) else (if i.val < 159 then g32p_supplierForest_node_113416 else g32p_supplierForest_node_113445))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_113482 else g32p_supplierForest_node_113497) else (if i.val < 163 then g32p_supplierForest_node_113516 else g32p_supplierForest_node_113522)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_113527 else g32p_supplierForest_node_113558) else (if i.val < 167 then g32p_supplierForest_node_113562 else g32p_supplierForest_node_113598))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_113669 else g32p_supplierForest_node_113673) else (if i.val < 171 then g32p_supplierForest_node_113677 else g32p_supplierForest_node_113701)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_113712 else g32p_supplierForest_node_113723) else (if i.val < 175 then g32p_supplierForest_node_113752 else g32p_supplierForest_node_113764)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_113769 else g32p_supplierForest_node_113795) else (if i.val < 179 then g32p_supplierForest_node_113805 else g32p_supplierForest_node_113824)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_113825 else g32p_supplierForest_node_113831) else (if i.val < 183 then g32p_supplierForest_node_113839 else g32p_supplierForest_node_113840))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_113842 else g32p_supplierForest_node_113849) else (if i.val < 187 then g32p_supplierForest_node_113850 else g32p_supplierForest_node_113872)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_113882 else g32p_supplierForest_node_113892) else (if i.val < 191 then g32p_supplierForest_node_113908 else g32p_supplierForest_node_113939)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_113961 else g32p_supplierForest_node_113965) else (if i.val < 195 then g32p_supplierForest_node_114071 else g32p_supplierForest_node_114087)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_114101 else g32p_supplierForest_node_114113) else (if i.val < 199 then g32p_supplierForest_node_114129 else g32p_supplierForest_node_114132))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_114167 else g32p_supplierForest_node_114227) else (if i.val < 203 then g32p_supplierForest_node_114243 else g32p_supplierForest_node_114267)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_114291 else g32p_supplierForest_node_114314) else (if i.val < 207 then g32p_supplierForest_node_114315 else g32p_supplierForest_node_114319)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_114334 else g32p_supplierForest_node_114340) else (if i.val < 211 then g32p_supplierForest_node_114382 else g32p_supplierForest_node_114396)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_114413 else g32p_supplierForest_node_114420) else (if i.val < 215 then g32p_supplierForest_node_114445 else g32p_supplierForest_node_114468))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_114487 else g32p_supplierForest_node_114490) else (if i.val < 219 then g32p_supplierForest_node_114499 else g32p_supplierForest_node_114504)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_114547 else g32p_supplierForest_node_114587) else (if i.val < 223 then g32p_supplierForest_node_114588 else g32p_supplierForest_node_114621))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_114664 else g32p_supplierForest_node_114690) else (if i.val < 227 then g32p_supplierForest_node_114701 else g32p_supplierForest_node_114716)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_114744 else g32p_supplierForest_node_114748) else (if i.val < 231 then g32p_supplierForest_node_114755 else g32p_supplierForest_node_114761))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_114770 else g32p_supplierForest_node_114797) else (if i.val < 235 then g32p_supplierForest_node_114843 else g32p_supplierForest_node_114861)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_114864 else g32p_supplierForest_node_114866) else (if i.val < 239 then g32p_supplierForest_node_114905 else g32p_supplierForest_node_114917)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_114927 else g32p_supplierForest_node_114966) else (if i.val < 243 then g32p_supplierForest_node_114968 else g32p_supplierForest_node_115011)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_115026 else g32p_supplierForest_node_115031) else (if i.val < 247 then g32p_supplierForest_node_115032 else g32p_supplierForest_node_115054))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_115057 else g32p_supplierForest_node_115060) else (if i.val < 251 then g32p_supplierForest_node_115091 else g32p_supplierForest_node_115100)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_115102 else g32p_supplierForest_node_115187) else (if i.val < 255 then g32p_supplierForest_node_115188 else g32p_supplierForest_node_115190))))))))

def g32p_supplierForest_classes_104 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 29) else (if i.val < 3 then 60 else 63)) else (if i.val < 6 then (if i.val < 5 then 66 else 30) else (if i.val < 7 then 66 else 61))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 66 else 59) else (if i.val < 11 then 16 else 16)) else (if i.val < 14 then (if i.val < 13 then 16 else 36) else (if i.val < 15 then 30 else 66)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 59 else 33) else (if i.val < 19 then 59 else 57)) else (if i.val < 22 then (if i.val < 21 then 57 else 30) else (if i.val < 23 then 36 else 30))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 15 else 57) else (if i.val < 27 then 57 else 62)) else (if i.val < 30 then (if i.val < 29 then 30 else 34) else (if i.val < 31 then 61 else 33))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 14 else 29) else (if i.val < 35 then 16 else 58)) else (if i.val < 38 then (if i.val < 37 then 61 else 33) else (if i.val < 39 then 15 else 66))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 60 else 29) else (if i.val < 43 then 57 else 16)) else (if i.val < 46 then (if i.val < 45 then 30 else 63) else (if i.val < 47 then 29 else 15)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 66 else 29) else (if i.val < 51 then 30 else 66)) else (if i.val < 54 then (if i.val < 53 then 16 else 66) else (if i.val < 55 then 35 else 15))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 57 else 30) else (if i.val < 59 then 59 else 30)) else (if i.val < 62 then (if i.val < 61 then 15 else 57) else (if i.val < 63 then 57 else 60)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 29 else 30) else (if i.val < 67 then 34 else 60)) else (if i.val < 70 then (if i.val < 69 then 57 else 66) else (if i.val < 71 then 59 else 29))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 34 else 16) else (if i.val < 75 then 63 else 57)) else (if i.val < 78 then (if i.val < 77 then 66 else 14) else (if i.val < 79 then 57 else 29)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 59 else 15) else (if i.val < 83 then 59 else 33)) else (if i.val < 86 then (if i.val < 85 then 61 else 58) else (if i.val < 87 then 62 else 57))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 59 else 57) else (if i.val < 91 then 57 else 66)) else (if i.val < 94 then (if i.val < 93 then 58 else 16) else (if i.val < 95 then 16 else 15))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 57 else 57) else (if i.val < 99 then 59 else 66)) else (if i.val < 102 then (if i.val < 101 then 30 else 16) else (if i.val < 103 then 36 else 34))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 59 else 60) else (if i.val < 107 then 58 else 57)) else (if i.val < 110 then (if i.val < 109 then 57 else 57) else (if i.val < 111 then 66 else 30)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 36 else 30) else (if i.val < 115 then 33 else 57)) else (if i.val < 118 then (if i.val < 117 then 61 else 30) else (if i.val < 119 then 63 else 29))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 60 else 29) else (if i.val < 123 then 16 else 57)) else (if i.val < 126 then (if i.val < 125 then 57 else 57) else (if i.val < 127 then 66 else 57))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 30 else 57) else (if i.val < 131 then 15 else 30)) else (if i.val < 134 then (if i.val < 133 then 29 else 58) else (if i.val < 135 then 60 else 15))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 32 else 60) else (if i.val < 139 then 33 else 29)) else (if i.val < 142 then (if i.val < 141 then 16 else 14) else (if i.val < 143 then 59 else 30)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 16 else 36) else (if i.val < 147 then 64 else 30)) else (if i.val < 150 then (if i.val < 149 then 29 else 57) else (if i.val < 151 then 17 else 57))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 16 else 59) else (if i.val < 155 then 57 else 61)) else (if i.val < 158 then (if i.val < 157 then 57 else 30) else (if i.val < 159 then 66 else 66))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 57 else 57) else (if i.val < 163 then 29 else 60)) else (if i.val < 166 then (if i.val < 165 then 16 else 16) else (if i.val < 167 then 29 else 62))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 57 else 57) else (if i.val < 171 then 57 else 29)) else (if i.val < 174 then (if i.val < 173 then 34 else 15) else (if i.val < 175 then 57 else 34)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 60 else 30) else (if i.val < 179 then 57 else 16)) else (if i.val < 182 then (if i.val < 181 then 63 else 30) else (if i.val < 183 then 30 else 36))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 57 else 17) else (if i.val < 187 then 57 else 66)) else (if i.val < 190 then (if i.val < 189 then 57 else 63) else (if i.val < 191 then 30 else 57)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 57 else 59) else (if i.val < 195 then 4 else 30)) else (if i.val < 198 then (if i.val < 197 then 30 else 57) else (if i.val < 199 then 60 else 60))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 17 else 30) else (if i.val < 203 then 57 else 36)) else (if i.val < 206 then (if i.val < 205 then 66 else 30) else (if i.val < 207 then 30 else 36)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 36 else 29) else (if i.val < 211 then 59 else 30)) else (if i.val < 214 then (if i.val < 213 then 60 else 30) else (if i.val < 215 then 57 else 57))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 57 else 35) else (if i.val < 219 then 60 else 16)) else (if i.val < 222 then (if i.val < 221 then 57 else 62) else (if i.val < 223 then 30 else 57))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 66 else 57) else (if i.val < 227 then 30 else 36)) else (if i.val < 230 then (if i.val < 229 then 63 else 30) else (if i.val < 231 then 16 else 91))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 17 else 57) else (if i.val < 235 then 36 else 60)) else (if i.val < 238 then (if i.val < 237 then 57 else 16) else (if i.val < 239 then 66 else 59)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 57 else 57) else (if i.val < 243 then 57 else 33)) else (if i.val < 246 then (if i.val < 245 then 57 else 30) else (if i.val < 247 then 30 else 30))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 60 else 29) else (if i.val < 251 then 17 else 60)) else (if i.val < 254 then (if i.val < 253 then 63 else 30) else (if i.val < 255 then 66 else 3))))))))

theorem g32p_supplierForest_actual_104 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_104 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_104 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_109537
  · exact g32p_supplierForest_actual_109576
  · exact g32p_supplierForest_actual_109618
  · exact g32p_supplierForest_actual_109653
  · exact g32p_supplierForest_actual_109687
  · exact g32p_supplierForest_actual_109709
  · exact g32p_supplierForest_actual_109715
  · exact g32p_supplierForest_actual_109719
  · exact g32p_supplierForest_actual_109738
  · exact g32p_supplierForest_actual_109744
  · exact g32p_supplierForest_actual_109756
  · exact g32p_supplierForest_actual_109789
  · exact g32p_supplierForest_actual_109793
  · exact g32p_supplierForest_actual_109832
  · exact g32p_supplierForest_actual_109834
  · exact g32p_supplierForest_actual_109839
  · exact g32p_supplierForest_actual_109851
  · exact g32p_supplierForest_actual_109905
  · exact g32p_supplierForest_actual_109924
  · exact g32p_supplierForest_actual_109942
  · exact g32p_supplierForest_actual_109958
  · exact g32p_supplierForest_actual_109997
  · exact g32p_supplierForest_actual_110006
  · exact g32p_supplierForest_actual_110010
  · exact g32p_supplierForest_actual_110040
  · exact g32p_supplierForest_actual_110042
  · exact g32p_supplierForest_actual_110044
  · exact g32p_supplierForest_actual_110061
  · exact g32p_supplierForest_actual_110063
  · exact g32p_supplierForest_actual_110070
  · exact g32p_supplierForest_actual_110098
  · exact g32p_supplierForest_actual_110107
  · exact g32p_supplierForest_actual_110112
  · exact g32p_supplierForest_actual_110123
  · exact g32p_supplierForest_actual_110132
  · exact g32p_supplierForest_actual_110143
  · exact g32p_supplierForest_actual_110177
  · exact g32p_supplierForest_actual_110210
  · exact g32p_supplierForest_actual_110216
  · exact g32p_supplierForest_actual_110237
  · exact g32p_supplierForest_actual_110239
  · exact g32p_supplierForest_actual_110249
  · exact g32p_supplierForest_actual_110291
  · exact g32p_supplierForest_actual_110293
  · exact g32p_supplierForest_actual_110302
  · exact g32p_supplierForest_actual_110336
  · exact g32p_supplierForest_actual_110411
  · exact g32p_supplierForest_actual_110415
  · exact g32p_supplierForest_actual_110433
  · exact g32p_supplierForest_actual_110531
  · exact g32p_supplierForest_actual_110534
  · exact g32p_supplierForest_actual_110535
  · exact g32p_supplierForest_actual_110572
  · exact g32p_supplierForest_actual_110597
  · exact g32p_supplierForest_actual_110606
  · exact g32p_supplierForest_actual_110626
  · exact g32p_supplierForest_actual_110664
  · exact g32p_supplierForest_actual_110686
  · exact g32p_supplierForest_actual_110724
  · exact g32p_supplierForest_actual_110726
  · exact g32p_supplierForest_actual_110821
  · exact g32p_supplierForest_actual_110832
  · exact g32p_supplierForest_actual_110844
  · exact g32p_supplierForest_actual_110872
  · exact g32p_supplierForest_actual_110874
  · exact g32p_supplierForest_actual_110923
  · exact g32p_supplierForest_actual_110929
  · exact g32p_supplierForest_actual_110963
  · exact g32p_supplierForest_actual_111011
  · exact g32p_supplierForest_actual_111030
  · exact g32p_supplierForest_actual_111037
  · exact g32p_supplierForest_actual_111057
  · exact g32p_supplierForest_actual_111059
  · exact g32p_supplierForest_actual_111071
  · exact g32p_supplierForest_actual_111110
  · exact g32p_supplierForest_actual_111127
  · exact g32p_supplierForest_actual_111130
  · exact g32p_supplierForest_actual_111172
  · exact g32p_supplierForest_actual_111243
  · exact g32p_supplierForest_actual_111251
  · exact g32p_supplierForest_actual_111299
  · exact g32p_supplierForest_actual_111364
  · exact g32p_supplierForest_actual_111380
  · exact g32p_supplierForest_actual_111398
  · exact g32p_supplierForest_actual_111423
  · exact g32p_supplierForest_actual_111494
  · exact g32p_supplierForest_actual_111515
  · exact g32p_supplierForest_actual_111522
  · exact g32p_supplierForest_actual_111591
  · exact g32p_supplierForest_actual_111598
  · exact g32p_supplierForest_actual_111599
  · exact g32p_supplierForest_actual_111605
  · exact g32p_supplierForest_actual_111626
  · exact g32p_supplierForest_actual_111637
  · exact g32p_supplierForest_actual_111654
  · exact g32p_supplierForest_actual_111666
  · exact g32p_supplierForest_actual_111725
  · exact g32p_supplierForest_actual_111752
  · exact g32p_supplierForest_actual_111771
  · exact g32p_supplierForest_actual_111773
  · exact g32p_supplierForest_actual_111796
  · exact g32p_supplierForest_actual_111858
  · exact g32p_supplierForest_actual_111873
  · exact g32p_supplierForest_actual_111895
  · exact g32p_supplierForest_actual_111899
  · exact g32p_supplierForest_actual_111916
  · exact g32p_supplierForest_actual_111975
  · exact g32p_supplierForest_actual_111984
  · exact g32p_supplierForest_actual_112062
  · exact g32p_supplierForest_actual_112151
  · exact g32p_supplierForest_actual_112166
  · exact g32p_supplierForest_actual_112286
  · exact g32p_supplierForest_actual_112360
  · exact g32p_supplierForest_actual_112380
  · exact g32p_supplierForest_actual_112394
  · exact g32p_supplierForest_actual_112399
  · exact g32p_supplierForest_actual_112410
  · exact g32p_supplierForest_actual_112413
  · exact g32p_supplierForest_actual_112466
  · exact g32p_supplierForest_actual_112482
  · exact g32p_supplierForest_actual_112511
  · exact g32p_supplierForest_actual_112517
  · exact g32p_supplierForest_actual_112526
  · exact g32p_supplierForest_actual_112567
  · exact g32p_supplierForest_actual_112585
  · exact g32p_supplierForest_actual_112629
  · exact g32p_supplierForest_actual_112634
  · exact g32p_supplierForest_actual_112636
  · exact g32p_supplierForest_actual_112641
  · exact g32p_supplierForest_actual_112655
  · exact g32p_supplierForest_actual_112679
  · exact g32p_supplierForest_actual_112740
  · exact g32p_supplierForest_actual_112753
  · exact g32p_supplierForest_actual_112789
  · exact g32p_supplierForest_actual_112830
  · exact g32p_supplierForest_actual_112856
  · exact g32p_supplierForest_actual_112897
  · exact g32p_supplierForest_actual_112908
  · exact g32p_supplierForest_actual_112966
  · exact g32p_supplierForest_actual_112975
  · exact g32p_supplierForest_actual_112984
  · exact g32p_supplierForest_actual_113015
  · exact g32p_supplierForest_actual_113059
  · exact g32p_supplierForest_actual_113070
  · exact g32p_supplierForest_actual_113087
  · exact g32p_supplierForest_actual_113095
  · exact g32p_supplierForest_actual_113106
  · exact g32p_supplierForest_actual_113163
  · exact g32p_supplierForest_actual_113170
  · exact g32p_supplierForest_actual_113209
  · exact g32p_supplierForest_actual_113232
  · exact g32p_supplierForest_actual_113239
  · exact g32p_supplierForest_actual_113270
  · exact g32p_supplierForest_actual_113345
  · exact g32p_supplierForest_actual_113354
  · exact g32p_supplierForest_actual_113369
  · exact g32p_supplierForest_actual_113380
  · exact g32p_supplierForest_actual_113396
  · exact g32p_supplierForest_actual_113416
  · exact g32p_supplierForest_actual_113445
  · exact g32p_supplierForest_actual_113482
  · exact g32p_supplierForest_actual_113497
  · exact g32p_supplierForest_actual_113516
  · exact g32p_supplierForest_actual_113522
  · exact g32p_supplierForest_actual_113527
  · exact g32p_supplierForest_actual_113558
  · exact g32p_supplierForest_actual_113562
  · exact g32p_supplierForest_actual_113598
  · exact g32p_supplierForest_actual_113669
  · exact g32p_supplierForest_actual_113673
  · exact g32p_supplierForest_actual_113677
  · exact g32p_supplierForest_actual_113701
  · exact g32p_supplierForest_actual_113712
  · exact g32p_supplierForest_actual_113723
  · exact g32p_supplierForest_actual_113752
  · exact g32p_supplierForest_actual_113764
  · exact g32p_supplierForest_actual_113769
  · exact g32p_supplierForest_actual_113795
  · exact g32p_supplierForest_actual_113805
  · exact g32p_supplierForest_actual_113824
  · exact g32p_supplierForest_actual_113825
  · exact g32p_supplierForest_actual_113831
  · exact g32p_supplierForest_actual_113839
  · exact g32p_supplierForest_actual_113840
  · exact g32p_supplierForest_actual_113842
  · exact g32p_supplierForest_actual_113849
  · exact g32p_supplierForest_actual_113850
  · exact g32p_supplierForest_actual_113872
  · exact g32p_supplierForest_actual_113882
  · exact g32p_supplierForest_actual_113892
  · exact g32p_supplierForest_actual_113908
  · exact g32p_supplierForest_actual_113939
  · exact g32p_supplierForest_actual_113961
  · exact g32p_supplierForest_actual_113965
  · exact g32p_supplierForest_actual_114071
  · exact g32p_supplierForest_actual_114087
  · exact g32p_supplierForest_actual_114101
  · exact g32p_supplierForest_actual_114113
  · exact g32p_supplierForest_actual_114129
  · exact g32p_supplierForest_actual_114132
  · exact g32p_supplierForest_actual_114167
  · exact g32p_supplierForest_actual_114227
  · exact g32p_supplierForest_actual_114243
  · exact g32p_supplierForest_actual_114267
  · exact g32p_supplierForest_actual_114291
  · exact g32p_supplierForest_actual_114314
  · exact g32p_supplierForest_actual_114315
  · exact g32p_supplierForest_actual_114319
  · exact g32p_supplierForest_actual_114334
  · exact g32p_supplierForest_actual_114340
  · exact g32p_supplierForest_actual_114382
  · exact g32p_supplierForest_actual_114396
  · exact g32p_supplierForest_actual_114413
  · exact g32p_supplierForest_actual_114420
  · exact g32p_supplierForest_actual_114445
  · exact g32p_supplierForest_actual_114468
  · exact g32p_supplierForest_actual_114487
  · exact g32p_supplierForest_actual_114490
  · exact g32p_supplierForest_actual_114499
  · exact g32p_supplierForest_actual_114504
  · exact g32p_supplierForest_actual_114547
  · exact g32p_supplierForest_actual_114587
  · exact g32p_supplierForest_actual_114588
  · exact g32p_supplierForest_actual_114621
  · exact g32p_supplierForest_actual_114664
  · exact g32p_supplierForest_actual_114690
  · exact g32p_supplierForest_actual_114701
  · exact g32p_supplierForest_actual_114716
  · exact g32p_supplierForest_actual_114744
  · exact g32p_supplierForest_actual_114748
  · exact g32p_supplierForest_actual_114755
  · exact g32p_supplierForest_actual_114761
  · exact g32p_supplierForest_actual_114770
  · exact g32p_supplierForest_actual_114797
  · exact g32p_supplierForest_actual_114843
  · exact g32p_supplierForest_actual_114861
  · exact g32p_supplierForest_actual_114864
  · exact g32p_supplierForest_actual_114866
  · exact g32p_supplierForest_actual_114905
  · exact g32p_supplierForest_actual_114917
  · exact g32p_supplierForest_actual_114927
  · exact g32p_supplierForest_actual_114966
  · exact g32p_supplierForest_actual_114968
  · exact g32p_supplierForest_actual_115011
  · exact g32p_supplierForest_actual_115026
  · exact g32p_supplierForest_actual_115031
  · exact g32p_supplierForest_actual_115032
  · exact g32p_supplierForest_actual_115054
  · exact g32p_supplierForest_actual_115057
  · exact g32p_supplierForest_actual_115060
  · exact g32p_supplierForest_actual_115091
  · exact g32p_supplierForest_actual_115100
  · exact g32p_supplierForest_actual_115102
  · exact g32p_supplierForest_actual_115187
  · exact g32p_supplierForest_actual_115188
  · exact g32p_supplierForest_actual_115190

def g32p_supplierForest_nodes_105 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_115194 else g32p_supplierForest_node_115208) else (if i.val < 3 then g32p_supplierForest_node_115214 else g32p_supplierForest_node_115231)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_115249 else g32p_supplierForest_node_115269) else (if i.val < 7 then g32p_supplierForest_node_115279 else g32p_supplierForest_node_115307))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_115332 else g32p_supplierForest_node_115346) else (if i.val < 11 then g32p_supplierForest_node_115358 else g32p_supplierForest_node_115374)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_115379 else g32p_supplierForest_node_115411) else (if i.val < 15 then g32p_supplierForest_node_115425 else g32p_supplierForest_node_115445)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_115450 else g32p_supplierForest_node_115467) else (if i.val < 19 then g32p_supplierForest_node_115497 else g32p_supplierForest_node_115502)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_115504 else g32p_supplierForest_node_115599) else (if i.val < 23 then g32p_supplierForest_node_115621 else g32p_supplierForest_node_115653))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_115658 else g32p_supplierForest_node_115688) else (if i.val < 27 then g32p_supplierForest_node_115699 else g32p_supplierForest_node_115710)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_115713 else g32p_supplierForest_node_115717) else (if i.val < 31 then g32p_supplierForest_node_115720 else g32p_supplierForest_node_115735))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_115763 else g32p_supplierForest_node_115773) else (if i.val < 35 then g32p_supplierForest_node_115790 else g32p_supplierForest_node_115794)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_115829 else g32p_supplierForest_node_115833) else (if i.val < 39 then g32p_supplierForest_node_115855 else g32p_supplierForest_node_115862))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_115886 else g32p_supplierForest_node_115899) else (if i.val < 43 then g32p_supplierForest_node_115925 else g32p_supplierForest_node_115969)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_115990 else g32p_supplierForest_node_116026) else (if i.val < 47 then g32p_supplierForest_node_116037 else g32p_supplierForest_node_116045)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_116053 else g32p_supplierForest_node_116066) else (if i.val < 51 then g32p_supplierForest_node_116083 else g32p_supplierForest_node_116105)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_116121 else g32p_supplierForest_node_116123) else (if i.val < 55 then g32p_supplierForest_node_116150 else g32p_supplierForest_node_116184))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_116193 else g32p_supplierForest_node_116207) else (if i.val < 59 then g32p_supplierForest_node_116220 else g32p_supplierForest_node_116228)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_116276 else g32p_supplierForest_node_116303) else (if i.val < 63 then g32p_supplierForest_node_116327 else g32p_supplierForest_node_116342)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_116354 else g32p_supplierForest_node_116360) else (if i.val < 67 then g32p_supplierForest_node_116416 else g32p_supplierForest_node_116439)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_116448 else g32p_supplierForest_node_116473) else (if i.val < 71 then g32p_supplierForest_node_116481 else g32p_supplierForest_node_116488))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_116491 else g32p_supplierForest_node_116502) else (if i.val < 75 then g32p_supplierForest_node_116548 else g32p_supplierForest_node_116558)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_116565 else g32p_supplierForest_node_116576) else (if i.val < 79 then g32p_supplierForest_node_116591 else g32p_supplierForest_node_116649)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_116659 else g32p_supplierForest_node_116676) else (if i.val < 83 then g32p_supplierForest_node_116739 else g32p_supplierForest_node_116771)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_116787 else g32p_supplierForest_node_116791) else (if i.val < 87 then g32p_supplierForest_node_116805 else g32p_supplierForest_node_116826))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_116837 else g32p_supplierForest_node_116879) else (if i.val < 91 then g32p_supplierForest_node_116903 else g32p_supplierForest_node_116945)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_116974 else g32p_supplierForest_node_117014) else (if i.val < 95 then g32p_supplierForest_node_117029 else g32p_supplierForest_node_117044))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_117062 else g32p_supplierForest_node_117072) else (if i.val < 99 then g32p_supplierForest_node_117109 else g32p_supplierForest_node_117113)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_117119 else g32p_supplierForest_node_117124) else (if i.val < 103 then g32p_supplierForest_node_117167 else g32p_supplierForest_node_117192))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_117196 else g32p_supplierForest_node_117198) else (if i.val < 107 then g32p_supplierForest_node_117204 else g32p_supplierForest_node_117210)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_117222 else g32p_supplierForest_node_117234) else (if i.val < 111 then g32p_supplierForest_node_117260 else g32p_supplierForest_node_117268)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_117270 else g32p_supplierForest_node_117274) else (if i.val < 115 then g32p_supplierForest_node_117305 else g32p_supplierForest_node_117306)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_117309 else g32p_supplierForest_node_117317) else (if i.val < 119 then g32p_supplierForest_node_117370 else g32p_supplierForest_node_117399))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_117402 else g32p_supplierForest_node_117420) else (if i.val < 123 then g32p_supplierForest_node_117433 else g32p_supplierForest_node_117450)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_117452 else g32p_supplierForest_node_117464) else (if i.val < 127 then g32p_supplierForest_node_117508 else g32p_supplierForest_node_117514))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_117517 else g32p_supplierForest_node_117529) else (if i.val < 131 then g32p_supplierForest_node_117550 else g32p_supplierForest_node_117601)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_117613 else g32p_supplierForest_node_117616) else (if i.val < 135 then g32p_supplierForest_node_117674 else g32p_supplierForest_node_117707))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_117722 else g32p_supplierForest_node_117726) else (if i.val < 139 then g32p_supplierForest_node_117731 else g32p_supplierForest_node_117734)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_117737 else g32p_supplierForest_node_117754) else (if i.val < 143 then g32p_supplierForest_node_117757 else g32p_supplierForest_node_117759)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_117787 else g32p_supplierForest_node_117794) else (if i.val < 147 then g32p_supplierForest_node_117796 else g32p_supplierForest_node_117805)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_117839 else g32p_supplierForest_node_117879) else (if i.val < 151 then g32p_supplierForest_node_117881 else g32p_supplierForest_node_117908))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_117948 else g32p_supplierForest_node_117956) else (if i.val < 155 then g32p_supplierForest_node_117974 else g32p_supplierForest_node_117987)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_118004 else g32p_supplierForest_node_118015) else (if i.val < 159 then g32p_supplierForest_node_118048 else g32p_supplierForest_node_118091))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_118164 else g32p_supplierForest_node_118180) else (if i.val < 163 then g32p_supplierForest_node_118181 else g32p_supplierForest_node_118200)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_118249 else g32p_supplierForest_node_118270) else (if i.val < 167 then g32p_supplierForest_node_118282 else g32p_supplierForest_node_118291))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_118293 else g32p_supplierForest_node_118298) else (if i.val < 171 then g32p_supplierForest_node_118335 else g32p_supplierForest_node_118350)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_118351 else g32p_supplierForest_node_118374) else (if i.val < 175 then g32p_supplierForest_node_118403 else g32p_supplierForest_node_118405)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_118423 else g32p_supplierForest_node_118437) else (if i.val < 179 then g32p_supplierForest_node_118443 else g32p_supplierForest_node_118446)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_118448 else g32p_supplierForest_node_118464) else (if i.val < 183 then g32p_supplierForest_node_118479 else g32p_supplierForest_node_118485))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_118495 else g32p_supplierForest_node_118500) else (if i.val < 187 then g32p_supplierForest_node_118503 else g32p_supplierForest_node_118575)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_118612 else g32p_supplierForest_node_118614) else (if i.val < 191 then g32p_supplierForest_node_118623 else g32p_supplierForest_node_118636)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_118669 else g32p_supplierForest_node_118690) else (if i.val < 195 then g32p_supplierForest_node_118694 else g32p_supplierForest_node_118697)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_118740 else g32p_supplierForest_node_118747) else (if i.val < 199 then g32p_supplierForest_node_118769 else g32p_supplierForest_node_118790))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_118807 else g32p_supplierForest_node_118842) else (if i.val < 203 then g32p_supplierForest_node_118849 else g32p_supplierForest_node_118876)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_118894 else g32p_supplierForest_node_118916) else (if i.val < 207 then g32p_supplierForest_node_118924 else g32p_supplierForest_node_118946)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_118987 else g32p_supplierForest_node_119001) else (if i.val < 211 then g32p_supplierForest_node_119062 else g32p_supplierForest_node_119084)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_119100 else g32p_supplierForest_node_119112) else (if i.val < 215 then g32p_supplierForest_node_119136 else g32p_supplierForest_node_119138))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_119146 else g32p_supplierForest_node_119183) else (if i.val < 219 then g32p_supplierForest_node_119213 else g32p_supplierForest_node_119251)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_119259 else g32p_supplierForest_node_119263) else (if i.val < 223 then g32p_supplierForest_node_119270 else g32p_supplierForest_node_119291))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_119316 else g32p_supplierForest_node_119325) else (if i.val < 227 then g32p_supplierForest_node_119345 else g32p_supplierForest_node_119350)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_119366 else g32p_supplierForest_node_119421) else (if i.val < 231 then g32p_supplierForest_node_119467 else g32p_supplierForest_node_119516))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_119575 else g32p_supplierForest_node_119582) else (if i.val < 235 then g32p_supplierForest_node_119586 else g32p_supplierForest_node_119614)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_119658 else g32p_supplierForest_node_119660) else (if i.val < 239 then g32p_supplierForest_node_119666 else g32p_supplierForest_node_119706)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_119718 else g32p_supplierForest_node_119720) else (if i.val < 243 then g32p_supplierForest_node_119773 else g32p_supplierForest_node_119777)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_119819 else g32p_supplierForest_node_119855) else (if i.val < 247 then g32p_supplierForest_node_119859 else g32p_supplierForest_node_119867))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_119915 else g32p_supplierForest_node_119932) else (if i.val < 251 then g32p_supplierForest_node_119940 else g32p_supplierForest_node_119950)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_119966 else g32p_supplierForest_node_119967) else (if i.val < 255 then g32p_supplierForest_node_120039 else g32p_supplierForest_node_120112))))))))

def g32p_supplierForest_classes_105 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 91) else (if i.val < 3 then 57 else 60)) else (if i.val < 6 then (if i.val < 5 then 33 else 62) else (if i.val < 7 then 33 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 16 else 60) else (if i.val < 11 then 30 else 57)) else (if i.val < 14 then (if i.val < 13 then 66 else 57) else (if i.val < 15 then 66 else 17)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 30 else 60) else (if i.val < 19 then 57 else 35)) else (if i.val < 22 then (if i.val < 21 then 33 else 57) else (if i.val < 23 then 57 else 89))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 57 else 89) else (if i.val < 27 then 59 else 92)) else (if i.val < 30 then (if i.val < 29 then 59 else 57) else (if i.val < 31 then 59 else 58))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 57 else 62) else (if i.val < 35 then 15 else 57)) else (if i.val < 38 then (if i.val < 37 then 57 else 57) else (if i.val < 39 then 57 else 29))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 29 else 62) else (if i.val < 43 then 57 else 30)) else (if i.val < 46 then (if i.val < 45 then 58 else 58) else (if i.val < 47 then 60 else 89)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 91 else 30) else (if i.val < 51 then 57 else 34)) else (if i.val < 54 then (if i.val < 53 then 57 else 58) else (if i.val < 55 then 58 else 30))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 34 else 58) else (if i.val < 59 then 57 else 16)) else (if i.val < 62 then (if i.val < 61 then 36 else 16) else (if i.val < 63 then 30 else 60)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 36 else 32) else (if i.val < 67 then 59 else 29)) else (if i.val < 70 then (if i.val < 69 then 60 else 66) else (if i.val < 71 then 30 else 30))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 59 else 62) else (if i.val < 75 then 60 else 62)) else (if i.val < 78 then (if i.val < 77 then 16 else 33) else (if i.val < 79 then 60 else 30)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 60 else 30) else (if i.val < 83 then 58 else 60)) else (if i.val < 86 then (if i.val < 85 then 57 else 57) else (if i.val < 87 then 29 else 64))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 29 else 34) else (if i.val < 91 then 36 else 66)) else (if i.val < 94 then (if i.val < 93 then 57 else 57) else (if i.val < 95 then 57 else 57))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 89 else 60) else (if i.val < 99 then 36 else 29)) else (if i.val < 102 then (if i.val < 101 then 30 else 29) else (if i.val < 103 then 57 else 29))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 57 else 57) else (if i.val < 107 then 30 else 35)) else (if i.val < 110 then (if i.val < 109 then 57 else 63) else (if i.val < 111 then 16 else 29)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 29 else 16) else (if i.val < 115 then 32 else 57)) else (if i.val < 118 then (if i.val < 117 then 29 else 57) else (if i.val < 119 then 57 else 57))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 57 else 66) else (if i.val < 123 then 60 else 66)) else (if i.val < 126 then (if i.val < 125 then 36 else 34) else (if i.val < 127 then 65 else 30))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 30 else 57) else (if i.val < 131 then 33 else 66)) else (if i.val < 134 then (if i.val < 133 then 29 else 57) else (if i.val < 135 then 61 else 60))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 62 else 57) else (if i.val < 139 then 30 else 30)) else (if i.val < 142 then (if i.val < 141 then 57 else 30) else (if i.val < 143 then 30 else 29)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 57 else 62) else (if i.val < 147 then 90 else 57)) else (if i.val < 150 then (if i.val < 149 then 57 else 66) else (if i.val < 151 then 89 else 29))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 61 else 61) else (if i.val < 155 then 59 else 30)) else (if i.val < 158 then (if i.val < 157 then 57 else 30) else (if i.val < 159 then 34 else 89))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 57 else 66) else (if i.val < 163 then 66 else 61)) else (if i.val < 166 then (if i.val < 165 then 57 else 59) else (if i.val < 167 then 30 else 30))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 58 else 57) else (if i.val < 171 then 61 else 62)) else (if i.val < 174 then (if i.val < 173 then 35 else 59) else (if i.val < 175 then 57 else 30)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 61 else 30) else (if i.val < 179 then 66 else 66)) else (if i.val < 182 then (if i.val < 181 then 57 else 17) else (if i.val < 183 then 16 else 61))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 57 else 30) else (if i.val < 187 then 59 else 30)) else (if i.val < 190 then (if i.val < 189 then 57 else 58) else (if i.val < 191 then 57 else 57)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 63 else 57) else (if i.val < 195 then 57 else 66)) else (if i.val < 198 then (if i.val < 197 then 17 else 62) else (if i.val < 199 then 59 else 36))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 57 else 63) else (if i.val < 203 then 30 else 30)) else (if i.val < 206 then (if i.val < 205 then 63 else 57) else (if i.val < 207 then 57 else 57)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 36 else 57) else (if i.val < 211 then 62 else 57)) else (if i.val < 214 then (if i.val < 213 then 15 else 60) else (if i.val < 215 then 30 else 90))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 30 else 36) else (if i.val < 219 then 57 else 66)) else (if i.val < 222 then (if i.val < 221 then 30 else 30) else (if i.val < 223 then 57 else 57))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 57 else 30) else (if i.val < 227 then 30 else 58)) else (if i.val < 230 then (if i.val < 229 then 58 else 30) else (if i.val < 231 then 30 else 29))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 30 else 57) else (if i.val < 235 then 59 else 59)) else (if i.val < 238 then (if i.val < 237 then 57 else 92) else (if i.val < 239 then 30 else 36)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 89 else 59) else (if i.val < 243 then 30 else 57)) else (if i.val < 246 then (if i.val < 245 then 60 else 58) else (if i.val < 247 then 36 else 58))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 66 else 66) else (if i.val < 251 then 57 else 35)) else (if i.val < 254 then (if i.val < 253 then 57 else 60) else (if i.val < 255 then 58 else 30))))))))

theorem g32p_supplierForest_actual_105 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_105 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_105 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_115194
  · exact g32p_supplierForest_actual_115208
  · exact g32p_supplierForest_actual_115214
  · exact g32p_supplierForest_actual_115231
  · exact g32p_supplierForest_actual_115249
  · exact g32p_supplierForest_actual_115269
  · exact g32p_supplierForest_actual_115279
  · exact g32p_supplierForest_actual_115307
  · exact g32p_supplierForest_actual_115332
  · exact g32p_supplierForest_actual_115346
  · exact g32p_supplierForest_actual_115358
  · exact g32p_supplierForest_actual_115374
  · exact g32p_supplierForest_actual_115379
  · exact g32p_supplierForest_actual_115411
  · exact g32p_supplierForest_actual_115425
  · exact g32p_supplierForest_actual_115445
  · exact g32p_supplierForest_actual_115450
  · exact g32p_supplierForest_actual_115467
  · exact g32p_supplierForest_actual_115497
  · exact g32p_supplierForest_actual_115502
  · exact g32p_supplierForest_actual_115504
  · exact g32p_supplierForest_actual_115599
  · exact g32p_supplierForest_actual_115621
  · exact g32p_supplierForest_actual_115653
  · exact g32p_supplierForest_actual_115658
  · exact g32p_supplierForest_actual_115688
  · exact g32p_supplierForest_actual_115699
  · exact g32p_supplierForest_actual_115710
  · exact g32p_supplierForest_actual_115713
  · exact g32p_supplierForest_actual_115717
  · exact g32p_supplierForest_actual_115720
  · exact g32p_supplierForest_actual_115735
  · exact g32p_supplierForest_actual_115763
  · exact g32p_supplierForest_actual_115773
  · exact g32p_supplierForest_actual_115790
  · exact g32p_supplierForest_actual_115794
  · exact g32p_supplierForest_actual_115829
  · exact g32p_supplierForest_actual_115833
  · exact g32p_supplierForest_actual_115855
  · exact g32p_supplierForest_actual_115862
  · exact g32p_supplierForest_actual_115886
  · exact g32p_supplierForest_actual_115899
  · exact g32p_supplierForest_actual_115925
  · exact g32p_supplierForest_actual_115969
  · exact g32p_supplierForest_actual_115990
  · exact g32p_supplierForest_actual_116026
  · exact g32p_supplierForest_actual_116037
  · exact g32p_supplierForest_actual_116045
  · exact g32p_supplierForest_actual_116053
  · exact g32p_supplierForest_actual_116066
  · exact g32p_supplierForest_actual_116083
  · exact g32p_supplierForest_actual_116105
  · exact g32p_supplierForest_actual_116121
  · exact g32p_supplierForest_actual_116123
  · exact g32p_supplierForest_actual_116150
  · exact g32p_supplierForest_actual_116184
  · exact g32p_supplierForest_actual_116193
  · exact g32p_supplierForest_actual_116207
  · exact g32p_supplierForest_actual_116220
  · exact g32p_supplierForest_actual_116228
  · exact g32p_supplierForest_actual_116276
  · exact g32p_supplierForest_actual_116303
  · exact g32p_supplierForest_actual_116327
  · exact g32p_supplierForest_actual_116342
  · exact g32p_supplierForest_actual_116354
  · exact g32p_supplierForest_actual_116360
  · exact g32p_supplierForest_actual_116416
  · exact g32p_supplierForest_actual_116439
  · exact g32p_supplierForest_actual_116448
  · exact g32p_supplierForest_actual_116473
  · exact g32p_supplierForest_actual_116481
  · exact g32p_supplierForest_actual_116488
  · exact g32p_supplierForest_actual_116491
  · exact g32p_supplierForest_actual_116502
  · exact g32p_supplierForest_actual_116548
  · exact g32p_supplierForest_actual_116558
  · exact g32p_supplierForest_actual_116565
  · exact g32p_supplierForest_actual_116576
  · exact g32p_supplierForest_actual_116591
  · exact g32p_supplierForest_actual_116649
  · exact g32p_supplierForest_actual_116659
  · exact g32p_supplierForest_actual_116676
  · exact g32p_supplierForest_actual_116739
  · exact g32p_supplierForest_actual_116771
  · exact g32p_supplierForest_actual_116787
  · exact g32p_supplierForest_actual_116791
  · exact g32p_supplierForest_actual_116805
  · exact g32p_supplierForest_actual_116826
  · exact g32p_supplierForest_actual_116837
  · exact g32p_supplierForest_actual_116879
  · exact g32p_supplierForest_actual_116903
  · exact g32p_supplierForest_actual_116945
  · exact g32p_supplierForest_actual_116974
  · exact g32p_supplierForest_actual_117014
  · exact g32p_supplierForest_actual_117029
  · exact g32p_supplierForest_actual_117044
  · exact g32p_supplierForest_actual_117062
  · exact g32p_supplierForest_actual_117072
  · exact g32p_supplierForest_actual_117109
  · exact g32p_supplierForest_actual_117113
  · exact g32p_supplierForest_actual_117119
  · exact g32p_supplierForest_actual_117124
  · exact g32p_supplierForest_actual_117167
  · exact g32p_supplierForest_actual_117192
  · exact g32p_supplierForest_actual_117196
  · exact g32p_supplierForest_actual_117198
  · exact g32p_supplierForest_actual_117204
  · exact g32p_supplierForest_actual_117210
  · exact g32p_supplierForest_actual_117222
  · exact g32p_supplierForest_actual_117234
  · exact g32p_supplierForest_actual_117260
  · exact g32p_supplierForest_actual_117268
  · exact g32p_supplierForest_actual_117270
  · exact g32p_supplierForest_actual_117274
  · exact g32p_supplierForest_actual_117305
  · exact g32p_supplierForest_actual_117306
  · exact g32p_supplierForest_actual_117309
  · exact g32p_supplierForest_actual_117317
  · exact g32p_supplierForest_actual_117370
  · exact g32p_supplierForest_actual_117399
  · exact g32p_supplierForest_actual_117402
  · exact g32p_supplierForest_actual_117420
  · exact g32p_supplierForest_actual_117433
  · exact g32p_supplierForest_actual_117450
  · exact g32p_supplierForest_actual_117452
  · exact g32p_supplierForest_actual_117464
  · exact g32p_supplierForest_actual_117508
  · exact g32p_supplierForest_actual_117514
  · exact g32p_supplierForest_actual_117517
  · exact g32p_supplierForest_actual_117529
  · exact g32p_supplierForest_actual_117550
  · exact g32p_supplierForest_actual_117601
  · exact g32p_supplierForest_actual_117613
  · exact g32p_supplierForest_actual_117616
  · exact g32p_supplierForest_actual_117674
  · exact g32p_supplierForest_actual_117707
  · exact g32p_supplierForest_actual_117722
  · exact g32p_supplierForest_actual_117726
  · exact g32p_supplierForest_actual_117731
  · exact g32p_supplierForest_actual_117734
  · exact g32p_supplierForest_actual_117737
  · exact g32p_supplierForest_actual_117754
  · exact g32p_supplierForest_actual_117757
  · exact g32p_supplierForest_actual_117759
  · exact g32p_supplierForest_actual_117787
  · exact g32p_supplierForest_actual_117794
  · exact g32p_supplierForest_actual_117796
  · exact g32p_supplierForest_actual_117805
  · exact g32p_supplierForest_actual_117839
  · exact g32p_supplierForest_actual_117879
  · exact g32p_supplierForest_actual_117881
  · exact g32p_supplierForest_actual_117908
  · exact g32p_supplierForest_actual_117948
  · exact g32p_supplierForest_actual_117956
  · exact g32p_supplierForest_actual_117974
  · exact g32p_supplierForest_actual_117987
  · exact g32p_supplierForest_actual_118004
  · exact g32p_supplierForest_actual_118015
  · exact g32p_supplierForest_actual_118048
  · exact g32p_supplierForest_actual_118091
  · exact g32p_supplierForest_actual_118164
  · exact g32p_supplierForest_actual_118180
  · exact g32p_supplierForest_actual_118181
  · exact g32p_supplierForest_actual_118200
  · exact g32p_supplierForest_actual_118249
  · exact g32p_supplierForest_actual_118270
  · exact g32p_supplierForest_actual_118282
  · exact g32p_supplierForest_actual_118291
  · exact g32p_supplierForest_actual_118293
  · exact g32p_supplierForest_actual_118298
  · exact g32p_supplierForest_actual_118335
  · exact g32p_supplierForest_actual_118350
  · exact g32p_supplierForest_actual_118351
  · exact g32p_supplierForest_actual_118374
  · exact g32p_supplierForest_actual_118403
  · exact g32p_supplierForest_actual_118405
  · exact g32p_supplierForest_actual_118423
  · exact g32p_supplierForest_actual_118437
  · exact g32p_supplierForest_actual_118443
  · exact g32p_supplierForest_actual_118446
  · exact g32p_supplierForest_actual_118448
  · exact g32p_supplierForest_actual_118464
  · exact g32p_supplierForest_actual_118479
  · exact g32p_supplierForest_actual_118485
  · exact g32p_supplierForest_actual_118495
  · exact g32p_supplierForest_actual_118500
  · exact g32p_supplierForest_actual_118503
  · exact g32p_supplierForest_actual_118575
  · exact g32p_supplierForest_actual_118612
  · exact g32p_supplierForest_actual_118614
  · exact g32p_supplierForest_actual_118623
  · exact g32p_supplierForest_actual_118636
  · exact g32p_supplierForest_actual_118669
  · exact g32p_supplierForest_actual_118690
  · exact g32p_supplierForest_actual_118694
  · exact g32p_supplierForest_actual_118697
  · exact g32p_supplierForest_actual_118740
  · exact g32p_supplierForest_actual_118747
  · exact g32p_supplierForest_actual_118769
  · exact g32p_supplierForest_actual_118790
  · exact g32p_supplierForest_actual_118807
  · exact g32p_supplierForest_actual_118842
  · exact g32p_supplierForest_actual_118849
  · exact g32p_supplierForest_actual_118876
  · exact g32p_supplierForest_actual_118894
  · exact g32p_supplierForest_actual_118916
  · exact g32p_supplierForest_actual_118924
  · exact g32p_supplierForest_actual_118946
  · exact g32p_supplierForest_actual_118987
  · exact g32p_supplierForest_actual_119001
  · exact g32p_supplierForest_actual_119062
  · exact g32p_supplierForest_actual_119084
  · exact g32p_supplierForest_actual_119100
  · exact g32p_supplierForest_actual_119112
  · exact g32p_supplierForest_actual_119136
  · exact g32p_supplierForest_actual_119138
  · exact g32p_supplierForest_actual_119146
  · exact g32p_supplierForest_actual_119183
  · exact g32p_supplierForest_actual_119213
  · exact g32p_supplierForest_actual_119251
  · exact g32p_supplierForest_actual_119259
  · exact g32p_supplierForest_actual_119263
  · exact g32p_supplierForest_actual_119270
  · exact g32p_supplierForest_actual_119291
  · exact g32p_supplierForest_actual_119316
  · exact g32p_supplierForest_actual_119325
  · exact g32p_supplierForest_actual_119345
  · exact g32p_supplierForest_actual_119350
  · exact g32p_supplierForest_actual_119366
  · exact g32p_supplierForest_actual_119421
  · exact g32p_supplierForest_actual_119467
  · exact g32p_supplierForest_actual_119516
  · exact g32p_supplierForest_actual_119575
  · exact g32p_supplierForest_actual_119582
  · exact g32p_supplierForest_actual_119586
  · exact g32p_supplierForest_actual_119614
  · exact g32p_supplierForest_actual_119658
  · exact g32p_supplierForest_actual_119660
  · exact g32p_supplierForest_actual_119666
  · exact g32p_supplierForest_actual_119706
  · exact g32p_supplierForest_actual_119718
  · exact g32p_supplierForest_actual_119720
  · exact g32p_supplierForest_actual_119773
  · exact g32p_supplierForest_actual_119777
  · exact g32p_supplierForest_actual_119819
  · exact g32p_supplierForest_actual_119855
  · exact g32p_supplierForest_actual_119859
  · exact g32p_supplierForest_actual_119867
  · exact g32p_supplierForest_actual_119915
  · exact g32p_supplierForest_actual_119932
  · exact g32p_supplierForest_actual_119940
  · exact g32p_supplierForest_actual_119950
  · exact g32p_supplierForest_actual_119966
  · exact g32p_supplierForest_actual_119967
  · exact g32p_supplierForest_actual_120039
  · exact g32p_supplierForest_actual_120112

def g32p_supplierForest_nodes_106 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_120144 else g32p_supplierForest_node_120195) else (if i.val < 3 then g32p_supplierForest_node_120205 else g32p_supplierForest_node_120208)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_120227 else g32p_supplierForest_node_120234) else (if i.val < 7 then g32p_supplierForest_node_120258 else g32p_supplierForest_node_120289))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_120295 else g32p_supplierForest_node_120320) else (if i.val < 11 then g32p_supplierForest_node_120325 else g32p_supplierForest_node_120331)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_120345 else g32p_supplierForest_node_120367) else (if i.val < 15 then g32p_supplierForest_node_120431 else g32p_supplierForest_node_120500)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_120503 else g32p_supplierForest_node_120508) else (if i.val < 19 then g32p_supplierForest_node_120513 else g32p_supplierForest_node_120554)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_120571 else g32p_supplierForest_node_120584) else (if i.val < 23 then g32p_supplierForest_node_120629 else g32p_supplierForest_node_120654))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_120663 else g32p_supplierForest_node_120704) else (if i.val < 27 then g32p_supplierForest_node_120719 else g32p_supplierForest_node_120754)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_120758 else g32p_supplierForest_node_120761) else (if i.val < 31 then g32p_supplierForest_node_120776 else g32p_supplierForest_node_120782))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_120811 else g32p_supplierForest_node_120821) else (if i.val < 35 then g32p_supplierForest_node_120894 else g32p_supplierForest_node_120901)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_120955 else g32p_supplierForest_node_121072) else (if i.val < 39 then g32p_supplierForest_node_121078 else g32p_supplierForest_node_121092))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_121111 else g32p_supplierForest_node_121137) else (if i.val < 43 then g32p_supplierForest_node_121166 else g32p_supplierForest_node_121202)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_121204 else g32p_supplierForest_node_121210) else (if i.val < 47 then g32p_supplierForest_node_121213 else g32p_supplierForest_node_121257)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_121259 else g32p_supplierForest_node_121267) else (if i.val < 51 then g32p_supplierForest_node_121272 else g32p_supplierForest_node_121281)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_121355 else g32p_supplierForest_node_121357) else (if i.val < 55 then g32p_supplierForest_node_121358 else g32p_supplierForest_node_121362))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_121418 else g32p_supplierForest_node_121420) else (if i.val < 59 then g32p_supplierForest_node_121446 else g32p_supplierForest_node_121447)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_121454 else g32p_supplierForest_node_121487) else (if i.val < 63 then g32p_supplierForest_node_121513 else g32p_supplierForest_node_121519)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_121536 else g32p_supplierForest_node_121559) else (if i.val < 67 then g32p_supplierForest_node_121562 else g32p_supplierForest_node_121573)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_121579 else g32p_supplierForest_node_121584) else (if i.val < 71 then g32p_supplierForest_node_121601 else g32p_supplierForest_node_121603))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_121648 else g32p_supplierForest_node_121652) else (if i.val < 75 then g32p_supplierForest_node_121690 else g32p_supplierForest_node_121704)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_121722 else g32p_supplierForest_node_121723) else (if i.val < 79 then g32p_supplierForest_node_121737 else g32p_supplierForest_node_121740)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_121771 else g32p_supplierForest_node_121795) else (if i.val < 83 then g32p_supplierForest_node_121801 else g32p_supplierForest_node_121804)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_121807 else g32p_supplierForest_node_121836) else (if i.val < 87 then g32p_supplierForest_node_121906 else g32p_supplierForest_node_121932))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_121953 else g32p_supplierForest_node_121971) else (if i.val < 91 then g32p_supplierForest_node_122002 else g32p_supplierForest_node_122004)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_122017 else g32p_supplierForest_node_122052) else (if i.val < 95 then g32p_supplierForest_node_122078 else g32p_supplierForest_node_122115))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_122151 else g32p_supplierForest_node_122153) else (if i.val < 99 then g32p_supplierForest_node_122163 else g32p_supplierForest_node_122221)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_122223 else g32p_supplierForest_node_122251) else (if i.val < 103 then g32p_supplierForest_node_122305 else g32p_supplierForest_node_122384))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_122435 else g32p_supplierForest_node_122454) else (if i.val < 107 then g32p_supplierForest_node_122481 else g32p_supplierForest_node_122491)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_122539 else g32p_supplierForest_node_122604) else (if i.val < 111 then g32p_supplierForest_node_122617 else g32p_supplierForest_node_122634)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_122691 else g32p_supplierForest_node_122720) else (if i.val < 115 then g32p_supplierForest_node_122740 else g32p_supplierForest_node_122744)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_122746 else g32p_supplierForest_node_122783) else (if i.val < 119 then g32p_supplierForest_node_122809 else g32p_supplierForest_node_122841))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_122846 else g32p_supplierForest_node_122848) else (if i.val < 123 then g32p_supplierForest_node_122849 else g32p_supplierForest_node_122858)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_122863 else g32p_supplierForest_node_122866) else (if i.val < 127 then g32p_supplierForest_node_122899 else g32p_supplierForest_node_122956))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_122966 else g32p_supplierForest_node_123015) else (if i.val < 131 then g32p_supplierForest_node_123025 else g32p_supplierForest_node_123081)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_123085 else g32p_supplierForest_node_123109) else (if i.val < 135 then g32p_supplierForest_node_123187 else g32p_supplierForest_node_123188))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_123190 else g32p_supplierForest_node_123229) else (if i.val < 139 then g32p_supplierForest_node_123254 else g32p_supplierForest_node_123260)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_123272 else g32p_supplierForest_node_123277) else (if i.val < 143 then g32p_supplierForest_node_123279 else g32p_supplierForest_node_123281)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_123432 else g32p_supplierForest_node_123474) else (if i.val < 147 then g32p_supplierForest_node_123506 else g32p_supplierForest_node_123541)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_123578 else g32p_supplierForest_node_123591) else (if i.val < 151 then g32p_supplierForest_node_123703 else g32p_supplierForest_node_123711))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_123714 else g32p_supplierForest_node_123729) else (if i.val < 155 then g32p_supplierForest_node_123740 else g32p_supplierForest_node_123754)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_123764 else g32p_supplierForest_node_123770) else (if i.val < 159 then g32p_supplierForest_node_123778 else g32p_supplierForest_node_123783))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_123795 else g32p_supplierForest_node_123850) else (if i.val < 163 then g32p_supplierForest_node_123858 else g32p_supplierForest_node_123859)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_123895 else g32p_supplierForest_node_123898) else (if i.val < 167 then g32p_supplierForest_node_123939 else g32p_supplierForest_node_124024))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_124026 else g32p_supplierForest_node_124038) else (if i.val < 171 then g32p_supplierForest_node_124050 else g32p_supplierForest_node_124080)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_124081 else g32p_supplierForest_node_124092) else (if i.val < 175 then g32p_supplierForest_node_124093 else g32p_supplierForest_node_124105)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_124107 else g32p_supplierForest_node_124119) else (if i.val < 179 then g32p_supplierForest_node_124121 else g32p_supplierForest_node_124137)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_124138 else g32p_supplierForest_node_124159) else (if i.val < 183 then g32p_supplierForest_node_124180 else g32p_supplierForest_node_124189))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_124201 else g32p_supplierForest_node_124235) else (if i.val < 187 then g32p_supplierForest_node_124255 else g32p_supplierForest_node_124268)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_124276 else g32p_supplierForest_node_124282) else (if i.val < 191 then g32p_supplierForest_node_124310 else g32p_supplierForest_node_124341)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_124357 else g32p_supplierForest_node_124393) else (if i.val < 195 then g32p_supplierForest_node_124395 else g32p_supplierForest_node_124397)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_124428 else g32p_supplierForest_node_124462) else (if i.val < 199 then g32p_supplierForest_node_124488 else g32p_supplierForest_node_124518))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_124575 else g32p_supplierForest_node_124677) else (if i.val < 203 then g32p_supplierForest_node_124775 else g32p_supplierForest_node_124801)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_124846 else g32p_supplierForest_node_124860) else (if i.val < 207 then g32p_supplierForest_node_124866 else g32p_supplierForest_node_124916)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_124964 else g32p_supplierForest_node_125000) else (if i.val < 211 then g32p_supplierForest_node_125024 else g32p_supplierForest_node_125026)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_125029 else g32p_supplierForest_node_125041) else (if i.val < 215 then g32p_supplierForest_node_125056 else g32p_supplierForest_node_125105))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_125108 else g32p_supplierForest_node_125145) else (if i.val < 219 then g32p_supplierForest_node_125236 else g32p_supplierForest_node_125307)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_125308 else g32p_supplierForest_node_125309) else (if i.val < 223 then g32p_supplierForest_node_125362 else g32p_supplierForest_node_125420))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_125426 else g32p_supplierForest_node_125427) else (if i.val < 227 then g32p_supplierForest_node_125494 else g32p_supplierForest_node_125526)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_125538 else g32p_supplierForest_node_125579) else (if i.val < 231 then g32p_supplierForest_node_125609 else g32p_supplierForest_node_125651))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_125668 else g32p_supplierForest_node_125677) else (if i.val < 235 then g32p_supplierForest_node_125691 else g32p_supplierForest_node_125704)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_125725 else g32p_supplierForest_node_125781) else (if i.val < 239 then g32p_supplierForest_node_125782 else g32p_supplierForest_node_125784)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_125816 else g32p_supplierForest_node_125881) else (if i.val < 243 then g32p_supplierForest_node_125922 else g32p_supplierForest_node_125932)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_125934 else g32p_supplierForest_node_125982) else (if i.val < 247 then g32p_supplierForest_node_125997 else g32p_supplierForest_node_126031))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_126049 else g32p_supplierForest_node_126077) else (if i.val < 251 then g32p_supplierForest_node_126162 else g32p_supplierForest_node_126188)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_126198 else g32p_supplierForest_node_126211) else (if i.val < 255 then g32p_supplierForest_node_126221 else g32p_supplierForest_node_126224))))))))

def g32p_supplierForest_classes_106 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 30 else 61) else (if i.val < 3 then 59 else 66)) else (if i.val < 6 then (if i.val < 5 then 58 else 29) else (if i.val < 7 then 62 else 29))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 59 else 62) else (if i.val < 11 then 29 else 30)) else (if i.val < 14 then (if i.val < 13 then 57 else 59) else (if i.val < 15 then 15 else 57)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 59 else 57) else (if i.val < 19 then 30 else 61)) else (if i.val < 22 then (if i.val < 21 then 60 else 60) else (if i.val < 23 then 57 else 60))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 91 else 59) else (if i.val < 27 then 35 else 30)) else (if i.val < 30 then (if i.val < 29 then 60 else 30) else (if i.val < 31 then 57 else 66))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 15 else 16) else (if i.val < 35 then 33 else 29)) else (if i.val < 38 then (if i.val < 37 then 59 else 30) else (if i.val < 39 then 58 else 29))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 59 else 30) else (if i.val < 43 then 58 else 60)) else (if i.val < 46 then (if i.val < 45 then 60 else 29) else (if i.val < 47 then 15 else 57)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 57 else 33) else (if i.val < 51 then 59 else 57)) else (if i.val < 54 then (if i.val < 53 then 58 else 60) else (if i.val < 55 then 30 else 30))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 57 else 57) else (if i.val < 59 then 57 else 57)) else (if i.val < 62 then (if i.val < 61 then 61 else 61) else (if i.val < 63 then 30 else 57)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 30 else 30) else (if i.val < 67 then 59 else 29)) else (if i.val < 70 then (if i.val < 69 then 34 else 59) else (if i.val < 71 then 29 else 57))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 34 else 57) else (if i.val < 75 then 57 else 57)) else (if i.val < 78 then (if i.val < 77 then 62 else 60) else (if i.val < 79 then 60 else 60)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 60 else 57) else (if i.val < 83 then 66 else 30)) else (if i.val < 86 then (if i.val < 85 then 57 else 66) else (if i.val < 87 then 57 else 66))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 30 else 57) else (if i.val < 91 then 30 else 60)) else (if i.val < 94 then (if i.val < 93 then 57 else 66) else (if i.val < 95 then 57 else 30))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 30 else 57) else (if i.val < 99 then 59 else 33)) else (if i.val < 102 then (if i.val < 101 then 89 else 30) else (if i.val < 103 then 60 else 29))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 60 else 57) else (if i.val < 107 then 59 else 30)) else (if i.val < 110 then (if i.val < 109 then 30 else 57) else (if i.val < 111 then 60 else 91)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 60 else 60) else (if i.val < 115 then 34 else 30)) else (if i.val < 118 then (if i.val < 117 then 66 else 57) else (if i.val < 119 then 66 else 57))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 60 else 57) else (if i.val < 123 then 60 else 29)) else (if i.val < 126 then (if i.val < 125 then 33 else 36) else (if i.val < 127 then 61 else 30))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 33 else 59) else (if i.val < 131 then 66 else 57)) else (if i.val < 134 then (if i.val < 133 then 60 else 61) else (if i.val < 135 then 35 else 30))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 60 else 30) else (if i.val < 139 then 57 else 61)) else (if i.val < 142 then (if i.val < 141 then 57 else 60) else (if i.val < 143 then 66 else 57)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 66 else 57) else (if i.val < 147 then 15 else 58)) else (if i.val < 150 then (if i.val < 149 then 60 else 61) else (if i.val < 151 then 57 else 65))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 34 else 66) else (if i.val < 155 then 63 else 57)) else (if i.val < 158 then (if i.val < 157 then 61 else 60) else (if i.val < 159 then 30 else 30))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 33 else 60) else (if i.val < 163 then 57 else 66)) else (if i.val < 166 then (if i.val < 165 then 60 else 30) else (if i.val < 167 then 60 else 57))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 30 else 57) else (if i.val < 171 then 60 else 35)) else (if i.val < 174 then (if i.val < 173 then 29 else 60) else (if i.val < 175 then 30 else 29)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 35 else 57) else (if i.val < 179 then 30 else 30)) else (if i.val < 182 then (if i.val < 181 then 35 else 66) else (if i.val < 183 then 58 else 60))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 57 else 57) else (if i.val < 187 then 30 else 60)) else (if i.val < 190 then (if i.val < 189 then 57 else 66) else (if i.val < 191 then 36 else 57)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 59 else 59) else (if i.val < 195 then 29 else 62)) else (if i.val < 198 then (if i.val < 197 then 60 else 34) else (if i.val < 199 then 60 else 57))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 36 else 35) else (if i.val < 203 then 60 else 36)) else (if i.val < 206 then (if i.val < 205 then 30 else 30) else (if i.val < 207 then 60 else 57)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 36 else 60) else (if i.val < 211 then 35 else 29)) else (if i.val < 214 then (if i.val < 213 then 34 else 34) else (if i.val < 215 then 16 else 29))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 32 else 57) else (if i.val < 219 then 63 else 57)) else (if i.val < 222 then (if i.val < 221 then 62 else 30) else (if i.val < 223 then 58 else 57))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 36 else 57) else (if i.val < 227 then 30 else 30)) else (if i.val < 230 then (if i.val < 229 then 66 else 60) else (if i.val < 231 then 60 else 61))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 30 else 66) else (if i.val < 235 then 57 else 30)) else (if i.val < 238 then (if i.val < 237 then 66 else 58) else (if i.val < 239 then 57 else 60)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 60 else 61) else (if i.val < 243 then 59 else 62)) else (if i.val < 246 then (if i.val < 245 then 30 else 29) else (if i.val < 247 then 59 else 61))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 57 else 62) else (if i.val < 251 then 57 else 90)) else (if i.val < 254 then (if i.val < 253 then 15 else 60) else (if i.val < 255 then 57 else 35))))))))

theorem g32p_supplierForest_actual_106 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_106 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_106 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_120144
  · exact g32p_supplierForest_actual_120195
  · exact g32p_supplierForest_actual_120205
  · exact g32p_supplierForest_actual_120208
  · exact g32p_supplierForest_actual_120227
  · exact g32p_supplierForest_actual_120234
  · exact g32p_supplierForest_actual_120258
  · exact g32p_supplierForest_actual_120289
  · exact g32p_supplierForest_actual_120295
  · exact g32p_supplierForest_actual_120320
  · exact g32p_supplierForest_actual_120325
  · exact g32p_supplierForest_actual_120331
  · exact g32p_supplierForest_actual_120345
  · exact g32p_supplierForest_actual_120367
  · exact g32p_supplierForest_actual_120431
  · exact g32p_supplierForest_actual_120500
  · exact g32p_supplierForest_actual_120503
  · exact g32p_supplierForest_actual_120508
  · exact g32p_supplierForest_actual_120513
  · exact g32p_supplierForest_actual_120554
  · exact g32p_supplierForest_actual_120571
  · exact g32p_supplierForest_actual_120584
  · exact g32p_supplierForest_actual_120629
  · exact g32p_supplierForest_actual_120654
  · exact g32p_supplierForest_actual_120663
  · exact g32p_supplierForest_actual_120704
  · exact g32p_supplierForest_actual_120719
  · exact g32p_supplierForest_actual_120754
  · exact g32p_supplierForest_actual_120758
  · exact g32p_supplierForest_actual_120761
  · exact g32p_supplierForest_actual_120776
  · exact g32p_supplierForest_actual_120782
  · exact g32p_supplierForest_actual_120811
  · exact g32p_supplierForest_actual_120821
  · exact g32p_supplierForest_actual_120894
  · exact g32p_supplierForest_actual_120901
  · exact g32p_supplierForest_actual_120955
  · exact g32p_supplierForest_actual_121072
  · exact g32p_supplierForest_actual_121078
  · exact g32p_supplierForest_actual_121092
  · exact g32p_supplierForest_actual_121111
  · exact g32p_supplierForest_actual_121137
  · exact g32p_supplierForest_actual_121166
  · exact g32p_supplierForest_actual_121202
  · exact g32p_supplierForest_actual_121204
  · exact g32p_supplierForest_actual_121210
  · exact g32p_supplierForest_actual_121213
  · exact g32p_supplierForest_actual_121257
  · exact g32p_supplierForest_actual_121259
  · exact g32p_supplierForest_actual_121267
  · exact g32p_supplierForest_actual_121272
  · exact g32p_supplierForest_actual_121281
  · exact g32p_supplierForest_actual_121355
  · exact g32p_supplierForest_actual_121357
  · exact g32p_supplierForest_actual_121358
  · exact g32p_supplierForest_actual_121362
  · exact g32p_supplierForest_actual_121418
  · exact g32p_supplierForest_actual_121420
  · exact g32p_supplierForest_actual_121446
  · exact g32p_supplierForest_actual_121447
  · exact g32p_supplierForest_actual_121454
  · exact g32p_supplierForest_actual_121487
  · exact g32p_supplierForest_actual_121513
  · exact g32p_supplierForest_actual_121519
  · exact g32p_supplierForest_actual_121536
  · exact g32p_supplierForest_actual_121559
  · exact g32p_supplierForest_actual_121562
  · exact g32p_supplierForest_actual_121573
  · exact g32p_supplierForest_actual_121579
  · exact g32p_supplierForest_actual_121584
  · exact g32p_supplierForest_actual_121601
  · exact g32p_supplierForest_actual_121603
  · exact g32p_supplierForest_actual_121648
  · exact g32p_supplierForest_actual_121652
  · exact g32p_supplierForest_actual_121690
  · exact g32p_supplierForest_actual_121704
  · exact g32p_supplierForest_actual_121722
  · exact g32p_supplierForest_actual_121723
  · exact g32p_supplierForest_actual_121737
  · exact g32p_supplierForest_actual_121740
  · exact g32p_supplierForest_actual_121771
  · exact g32p_supplierForest_actual_121795
  · exact g32p_supplierForest_actual_121801
  · exact g32p_supplierForest_actual_121804
  · exact g32p_supplierForest_actual_121807
  · exact g32p_supplierForest_actual_121836
  · exact g32p_supplierForest_actual_121906
  · exact g32p_supplierForest_actual_121932
  · exact g32p_supplierForest_actual_121953
  · exact g32p_supplierForest_actual_121971
  · exact g32p_supplierForest_actual_122002
  · exact g32p_supplierForest_actual_122004
  · exact g32p_supplierForest_actual_122017
  · exact g32p_supplierForest_actual_122052
  · exact g32p_supplierForest_actual_122078
  · exact g32p_supplierForest_actual_122115
  · exact g32p_supplierForest_actual_122151
  · exact g32p_supplierForest_actual_122153
  · exact g32p_supplierForest_actual_122163
  · exact g32p_supplierForest_actual_122221
  · exact g32p_supplierForest_actual_122223
  · exact g32p_supplierForest_actual_122251
  · exact g32p_supplierForest_actual_122305
  · exact g32p_supplierForest_actual_122384
  · exact g32p_supplierForest_actual_122435
  · exact g32p_supplierForest_actual_122454
  · exact g32p_supplierForest_actual_122481
  · exact g32p_supplierForest_actual_122491
  · exact g32p_supplierForest_actual_122539
  · exact g32p_supplierForest_actual_122604
  · exact g32p_supplierForest_actual_122617
  · exact g32p_supplierForest_actual_122634
  · exact g32p_supplierForest_actual_122691
  · exact g32p_supplierForest_actual_122720
  · exact g32p_supplierForest_actual_122740
  · exact g32p_supplierForest_actual_122744
  · exact g32p_supplierForest_actual_122746
  · exact g32p_supplierForest_actual_122783
  · exact g32p_supplierForest_actual_122809
  · exact g32p_supplierForest_actual_122841
  · exact g32p_supplierForest_actual_122846
  · exact g32p_supplierForest_actual_122848
  · exact g32p_supplierForest_actual_122849
  · exact g32p_supplierForest_actual_122858
  · exact g32p_supplierForest_actual_122863
  · exact g32p_supplierForest_actual_122866
  · exact g32p_supplierForest_actual_122899
  · exact g32p_supplierForest_actual_122956
  · exact g32p_supplierForest_actual_122966
  · exact g32p_supplierForest_actual_123015
  · exact g32p_supplierForest_actual_123025
  · exact g32p_supplierForest_actual_123081
  · exact g32p_supplierForest_actual_123085
  · exact g32p_supplierForest_actual_123109
  · exact g32p_supplierForest_actual_123187
  · exact g32p_supplierForest_actual_123188
  · exact g32p_supplierForest_actual_123190
  · exact g32p_supplierForest_actual_123229
  · exact g32p_supplierForest_actual_123254
  · exact g32p_supplierForest_actual_123260
  · exact g32p_supplierForest_actual_123272
  · exact g32p_supplierForest_actual_123277
  · exact g32p_supplierForest_actual_123279
  · exact g32p_supplierForest_actual_123281
  · exact g32p_supplierForest_actual_123432
  · exact g32p_supplierForest_actual_123474
  · exact g32p_supplierForest_actual_123506
  · exact g32p_supplierForest_actual_123541
  · exact g32p_supplierForest_actual_123578
  · exact g32p_supplierForest_actual_123591
  · exact g32p_supplierForest_actual_123703
  · exact g32p_supplierForest_actual_123711
  · exact g32p_supplierForest_actual_123714
  · exact g32p_supplierForest_actual_123729
  · exact g32p_supplierForest_actual_123740
  · exact g32p_supplierForest_actual_123754
  · exact g32p_supplierForest_actual_123764
  · exact g32p_supplierForest_actual_123770
  · exact g32p_supplierForest_actual_123778
  · exact g32p_supplierForest_actual_123783
  · exact g32p_supplierForest_actual_123795
  · exact g32p_supplierForest_actual_123850
  · exact g32p_supplierForest_actual_123858
  · exact g32p_supplierForest_actual_123859
  · exact g32p_supplierForest_actual_123895
  · exact g32p_supplierForest_actual_123898
  · exact g32p_supplierForest_actual_123939
  · exact g32p_supplierForest_actual_124024
  · exact g32p_supplierForest_actual_124026
  · exact g32p_supplierForest_actual_124038
  · exact g32p_supplierForest_actual_124050
  · exact g32p_supplierForest_actual_124080
  · exact g32p_supplierForest_actual_124081
  · exact g32p_supplierForest_actual_124092
  · exact g32p_supplierForest_actual_124093
  · exact g32p_supplierForest_actual_124105
  · exact g32p_supplierForest_actual_124107
  · exact g32p_supplierForest_actual_124119
  · exact g32p_supplierForest_actual_124121
  · exact g32p_supplierForest_actual_124137
  · exact g32p_supplierForest_actual_124138
  · exact g32p_supplierForest_actual_124159
  · exact g32p_supplierForest_actual_124180
  · exact g32p_supplierForest_actual_124189
  · exact g32p_supplierForest_actual_124201
  · exact g32p_supplierForest_actual_124235
  · exact g32p_supplierForest_actual_124255
  · exact g32p_supplierForest_actual_124268
  · exact g32p_supplierForest_actual_124276
  · exact g32p_supplierForest_actual_124282
  · exact g32p_supplierForest_actual_124310
  · exact g32p_supplierForest_actual_124341
  · exact g32p_supplierForest_actual_124357
  · exact g32p_supplierForest_actual_124393
  · exact g32p_supplierForest_actual_124395
  · exact g32p_supplierForest_actual_124397
  · exact g32p_supplierForest_actual_124428
  · exact g32p_supplierForest_actual_124462
  · exact g32p_supplierForest_actual_124488
  · exact g32p_supplierForest_actual_124518
  · exact g32p_supplierForest_actual_124575
  · exact g32p_supplierForest_actual_124677
  · exact g32p_supplierForest_actual_124775
  · exact g32p_supplierForest_actual_124801
  · exact g32p_supplierForest_actual_124846
  · exact g32p_supplierForest_actual_124860
  · exact g32p_supplierForest_actual_124866
  · exact g32p_supplierForest_actual_124916
  · exact g32p_supplierForest_actual_124964
  · exact g32p_supplierForest_actual_125000
  · exact g32p_supplierForest_actual_125024
  · exact g32p_supplierForest_actual_125026
  · exact g32p_supplierForest_actual_125029
  · exact g32p_supplierForest_actual_125041
  · exact g32p_supplierForest_actual_125056
  · exact g32p_supplierForest_actual_125105
  · exact g32p_supplierForest_actual_125108
  · exact g32p_supplierForest_actual_125145
  · exact g32p_supplierForest_actual_125236
  · exact g32p_supplierForest_actual_125307
  · exact g32p_supplierForest_actual_125308
  · exact g32p_supplierForest_actual_125309
  · exact g32p_supplierForest_actual_125362
  · exact g32p_supplierForest_actual_125420
  · exact g32p_supplierForest_actual_125426
  · exact g32p_supplierForest_actual_125427
  · exact g32p_supplierForest_actual_125494
  · exact g32p_supplierForest_actual_125526
  · exact g32p_supplierForest_actual_125538
  · exact g32p_supplierForest_actual_125579
  · exact g32p_supplierForest_actual_125609
  · exact g32p_supplierForest_actual_125651
  · exact g32p_supplierForest_actual_125668
  · exact g32p_supplierForest_actual_125677
  · exact g32p_supplierForest_actual_125691
  · exact g32p_supplierForest_actual_125704
  · exact g32p_supplierForest_actual_125725
  · exact g32p_supplierForest_actual_125781
  · exact g32p_supplierForest_actual_125782
  · exact g32p_supplierForest_actual_125784
  · exact g32p_supplierForest_actual_125816
  · exact g32p_supplierForest_actual_125881
  · exact g32p_supplierForest_actual_125922
  · exact g32p_supplierForest_actual_125932
  · exact g32p_supplierForest_actual_125934
  · exact g32p_supplierForest_actual_125982
  · exact g32p_supplierForest_actual_125997
  · exact g32p_supplierForest_actual_126031
  · exact g32p_supplierForest_actual_126049
  · exact g32p_supplierForest_actual_126077
  · exact g32p_supplierForest_actual_126162
  · exact g32p_supplierForest_actual_126188
  · exact g32p_supplierForest_actual_126198
  · exact g32p_supplierForest_actual_126211
  · exact g32p_supplierForest_actual_126221
  · exact g32p_supplierForest_actual_126224

def g32p_supplierForest_nodes_107 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_126231 else g32p_supplierForest_node_126259) else (if i.val < 3 then g32p_supplierForest_node_126262 else g32p_supplierForest_node_126320)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_126384 else g32p_supplierForest_node_126389) else (if i.val < 7 then g32p_supplierForest_node_126479 else g32p_supplierForest_node_126492))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_126500 else g32p_supplierForest_node_126614) else (if i.val < 11 then g32p_supplierForest_node_126648 else g32p_supplierForest_node_126660)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_126666 else g32p_supplierForest_node_126685) else (if i.val < 15 then g32p_supplierForest_node_126690 else g32p_supplierForest_node_126704)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_126747 else g32p_supplierForest_node_126761) else (if i.val < 19 then g32p_supplierForest_node_126767 else g32p_supplierForest_node_126781)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_126788 else g32p_supplierForest_node_126858) else (if i.val < 23 then g32p_supplierForest_node_126868 else g32p_supplierForest_node_126869))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_126871 else g32p_supplierForest_node_126896) else (if i.val < 27 then g32p_supplierForest_node_126979 else g32p_supplierForest_node_126987)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_126999 else g32p_supplierForest_node_127025) else (if i.val < 31 then g32p_supplierForest_node_127036 else g32p_supplierForest_node_127062))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_127075 else g32p_supplierForest_node_127083) else (if i.val < 35 then g32p_supplierForest_node_127101 else g32p_supplierForest_node_127119)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_127129 else g32p_supplierForest_node_127147) else (if i.val < 39 then g32p_supplierForest_node_127150 else g32p_supplierForest_node_127153))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_127172 else g32p_supplierForest_node_127190) else (if i.val < 43 then g32p_supplierForest_node_127225 else g32p_supplierForest_node_127231)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_127250 else g32p_supplierForest_node_127254) else (if i.val < 47 then g32p_supplierForest_node_127288 else g32p_supplierForest_node_127300)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_127335 else g32p_supplierForest_node_127348) else (if i.val < 51 then g32p_supplierForest_node_127359 else g32p_supplierForest_node_127368)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_127383 else g32p_supplierForest_node_127438) else (if i.val < 55 then g32p_supplierForest_node_127476 else g32p_supplierForest_node_127481))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_127491 else g32p_supplierForest_node_127524) else (if i.val < 59 then g32p_supplierForest_node_127536 else g32p_supplierForest_node_127569)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_127587 else g32p_supplierForest_node_127598) else (if i.val < 63 then g32p_supplierForest_node_127683 else g32p_supplierForest_node_127688)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_127702 else g32p_supplierForest_node_127743) else (if i.val < 67 then g32p_supplierForest_node_127769 else g32p_supplierForest_node_127776)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_127808 else g32p_supplierForest_node_127816) else (if i.val < 71 then g32p_supplierForest_node_127843 else g32p_supplierForest_node_127876))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_127893 else g32p_supplierForest_node_127921) else (if i.val < 75 then g32p_supplierForest_node_127922 else g32p_supplierForest_node_127951)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_128005 else g32p_supplierForest_node_128025) else (if i.val < 79 then g32p_supplierForest_node_128041 else g32p_supplierForest_node_128046)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_128055 else g32p_supplierForest_node_128056) else (if i.val < 83 then g32p_supplierForest_node_128090 else g32p_supplierForest_node_128093)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_128094 else g32p_supplierForest_node_128102) else (if i.val < 87 then g32p_supplierForest_node_128105 else g32p_supplierForest_node_128131))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_128188 else g32p_supplierForest_node_128276) else (if i.val < 91 then g32p_supplierForest_node_128281 else g32p_supplierForest_node_128307)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_128312 else g32p_supplierForest_node_128318) else (if i.val < 95 then g32p_supplierForest_node_128331 else g32p_supplierForest_node_128418))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_128434 else g32p_supplierForest_node_128447) else (if i.val < 99 then g32p_supplierForest_node_128463 else g32p_supplierForest_node_128480)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_128490 else g32p_supplierForest_node_128495) else (if i.val < 103 then g32p_supplierForest_node_128496 else g32p_supplierForest_node_128514))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_128531 else g32p_supplierForest_node_128546) else (if i.val < 107 then g32p_supplierForest_node_128548 else g32p_supplierForest_node_128554)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_128599 else g32p_supplierForest_node_128621) else (if i.val < 111 then g32p_supplierForest_node_128633 else g32p_supplierForest_node_128668)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_128678 else g32p_supplierForest_node_128680) else (if i.val < 115 then g32p_supplierForest_node_128690 else g32p_supplierForest_node_128764)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_128772 else g32p_supplierForest_node_128774) else (if i.val < 119 then g32p_supplierForest_node_128800 else g32p_supplierForest_node_128805))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_128818 else g32p_supplierForest_node_128822) else (if i.val < 123 then g32p_supplierForest_node_128846 else g32p_supplierForest_node_128866)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_128873 else g32p_supplierForest_node_128878) else (if i.val < 127 then g32p_supplierForest_node_128968 else g32p_supplierForest_node_128983))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_128988 else g32p_supplierForest_node_128989) else (if i.val < 131 then g32p_supplierForest_node_129001 else g32p_supplierForest_node_129016)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_129040 else g32p_supplierForest_node_129051) else (if i.val < 135 then g32p_supplierForest_node_129068 else g32p_supplierForest_node_129097))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_129135 else g32p_supplierForest_node_129141) else (if i.val < 139 then g32p_supplierForest_node_129169 else g32p_supplierForest_node_129190)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_129203 else g32p_supplierForest_node_129204) else (if i.val < 143 then g32p_supplierForest_node_129211 else g32p_supplierForest_node_129233)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_129239 else g32p_supplierForest_node_129259) else (if i.val < 147 then g32p_supplierForest_node_129330 else g32p_supplierForest_node_129337)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_129342 else g32p_supplierForest_node_129349) else (if i.val < 151 then g32p_supplierForest_node_129355 else g32p_supplierForest_node_129373))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_129377 else g32p_supplierForest_node_129433) else (if i.val < 155 then g32p_supplierForest_node_129441 else g32p_supplierForest_node_129461)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_129462 else g32p_supplierForest_node_129489) else (if i.val < 159 then g32p_supplierForest_node_129499 else g32p_supplierForest_node_129506))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_129508 else g32p_supplierForest_node_129512) else (if i.val < 163 then g32p_supplierForest_node_129520 else g32p_supplierForest_node_129544)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_129571 else g32p_supplierForest_node_129597) else (if i.val < 167 then g32p_supplierForest_node_129607 else g32p_supplierForest_node_129626))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_129652 else g32p_supplierForest_node_129659) else (if i.val < 171 then g32p_supplierForest_node_129668 else g32p_supplierForest_node_129680)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_129682 else g32p_supplierForest_node_129706) else (if i.val < 175 then g32p_supplierForest_node_129733 else g32p_supplierForest_node_129815)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_129823 else g32p_supplierForest_node_129869) else (if i.val < 179 then g32p_supplierForest_node_129871 else g32p_supplierForest_node_129896)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_129909 else g32p_supplierForest_node_129959) else (if i.val < 183 then g32p_supplierForest_node_129968 else g32p_supplierForest_node_129989))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_129990 else g32p_supplierForest_node_130006) else (if i.val < 187 then g32p_supplierForest_node_130027 else g32p_supplierForest_node_130051)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_130063 else g32p_supplierForest_node_130073) else (if i.val < 191 then g32p_supplierForest_node_130074 else g32p_supplierForest_node_130088)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_130091 else g32p_supplierForest_node_130106) else (if i.val < 195 then g32p_supplierForest_node_130117 else g32p_supplierForest_node_130130)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_130190 else g32p_supplierForest_node_130196) else (if i.val < 199 then g32p_supplierForest_node_130202 else g32p_supplierForest_node_130264))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_130279 else g32p_supplierForest_node_130290) else (if i.val < 203 then g32p_supplierForest_node_130293 else g32p_supplierForest_node_130311)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_130314 else g32p_supplierForest_node_130316) else (if i.val < 207 then g32p_supplierForest_node_130372 else g32p_supplierForest_node_130376)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_130387 else g32p_supplierForest_node_130402) else (if i.val < 211 then g32p_supplierForest_node_130417 else g32p_supplierForest_node_130425)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_130483 else g32p_supplierForest_node_130484) else (if i.val < 215 then g32p_supplierForest_node_130508 else g32p_supplierForest_node_130569))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_130571 else g32p_supplierForest_node_130605) else (if i.val < 219 then g32p_supplierForest_node_130617 else g32p_supplierForest_node_130620)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_130662 else g32p_supplierForest_node_130718) else (if i.val < 223 then g32p_supplierForest_node_130745 else g32p_supplierForest_node_130750))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_130760 else g32p_supplierForest_node_130765) else (if i.val < 227 then g32p_supplierForest_node_130779 else g32p_supplierForest_node_130850)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_130853 else g32p_supplierForest_node_130880) else (if i.val < 231 then g32p_supplierForest_node_130898 else g32p_supplierForest_node_130941))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_130942 else g32p_supplierForest_node_130951) else (if i.val < 235 then g32p_supplierForest_node_130965 else g32p_supplierForest_node_130972)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_130979 else g32p_supplierForest_node_131004) else (if i.val < 239 then g32p_supplierForest_node_131034 else g32p_supplierForest_node_131061)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_131148 else g32p_supplierForest_node_131158) else (if i.val < 243 then g32p_supplierForest_node_131165 else g32p_supplierForest_node_131218)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_131266 else g32p_supplierForest_node_131296) else (if i.val < 247 then g32p_supplierForest_node_131360 else g32p_supplierForest_node_131374))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_131389 else g32p_supplierForest_node_131400) else (if i.val < 251 then g32p_supplierForest_node_131413 else g32p_supplierForest_node_131417)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_131421 else g32p_supplierForest_node_131438) else (if i.val < 255 then g32p_supplierForest_node_131445 else g32p_supplierForest_node_131448))))))))

def g32p_supplierForest_classes_107 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 35 else 57) else (if i.val < 3 then 57 else 35)) else (if i.val < 6 then (if i.val < 5 then 30 else 57) else (if i.val < 7 then 59 else 60))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 30 else 60) else (if i.val < 11 then 30 else 60)) else (if i.val < 14 then (if i.val < 13 then 35 else 35) else (if i.val < 15 then 66 else 35)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 60 else 60) else (if i.val < 19 then 35 else 36)) else (if i.val < 22 then (if i.val < 21 then 63 else 66) else (if i.val < 23 then 60 else 90))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 57 else 66) else (if i.val < 27 then 66 else 66)) else (if i.val < 30 then (if i.val < 29 then 60 else 30) else (if i.val < 31 then 30 else 60))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 60 else 30) else (if i.val < 35 then 30 else 30)) else (if i.val < 38 then (if i.val < 37 then 30 else 66) else (if i.val < 39 then 30 else 36))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 57 else 66) else (if i.val < 43 then 91 else 66)) else (if i.val < 46 then (if i.val < 45 then 60 else 66) else (if i.val < 47 then 16 else 60)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 90 else 59) else (if i.val < 51 then 60 else 61)) else (if i.val < 54 then (if i.val < 53 then 89 else 60) else (if i.val < 55 then 66 else 90))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 60 else 66) else (if i.val < 59 then 60 else 36)) else (if i.val < 62 then (if i.val < 61 then 60 else 61) else (if i.val < 63 then 90 else 61)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 30 else 35) else (if i.val < 67 then 61 else 66)) else (if i.val < 70 then (if i.val < 69 then 43 else 41) else (if i.val < 71 then 68 else 21))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 73 else 71) else (if i.val < 75 then 70 else 68)) else (if i.val < 78 then (if i.val < 77 then 73 else 71) else (if i.val < 79 then 70 else 38)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 21 else 38) else (if i.val < 83 then 68 else 41)) else (if i.val < 86 then (if i.val < 85 then 73 else 70) else (if i.val < 87 then 71 else 73))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 74 else 38) else (if i.val < 91 then 38 else 20)) else (if i.val < 94 then (if i.val < 93 then 38 else 73) else (if i.val < 95 then 73 else 73))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 43 else 73) else (if i.val < 99 then 21 else 71)) else (if i.val < 102 then (if i.val < 101 then 40 else 42) else (if i.val < 103 then 21 else 68))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 71 else 94) else (if i.val < 107 then 41 else 74)) else (if i.val < 110 then (if i.val < 109 then 38 else 21) else (if i.val < 111 then 38 else 21)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 39 else 40) else (if i.val < 115 then 42 else 73)) else (if i.val < 118 then (if i.val < 117 then 21 else 38) else (if i.val < 119 then 38 else 71))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 40 else 38) else (if i.val < 123 then 73 else 67)) else (if i.val < 126 then (if i.val < 125 then 21 else 72) else (if i.val < 127 then 71 else 38))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 73 else 22) else (if i.val < 131 then 71 else 73)) else (if i.val < 134 then (if i.val < 133 then 39 else 41) else (if i.val < 135 then 38 else 22))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 21 else 38) else (if i.val < 139 then 38 else 38)) else (if i.val < 142 then (if i.val < 141 then 38 else 38) else (if i.val < 143 then 22 else 38)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 38 else 40) else (if i.val < 147 then 43 else 40)) else (if i.val < 150 then (if i.val < 149 then 41 else 38) else (if i.val < 151 then 21 else 43))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 21 else 73) else (if i.val < 155 then 72 else 73)) else (if i.val < 158 then (if i.val < 157 then 73 else 41) else (if i.val < 159 then 38 else 38))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 38 else 68) else (if i.val < 163 then 73 else 75)) else (if i.val < 166 then (if i.val < 165 then 42 else 38) else (if i.val < 167 then 38 else 21))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 38 else 38) else (if i.val < 171 then 38 else 20)) else (if i.val < 174 then (if i.val < 173 then 21 else 20) else (if i.val < 175 then 74 else 43)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 38 else 74) else (if i.val < 179 then 40 else 74)) else (if i.val < 182 then (if i.val < 181 then 21 else 38) else (if i.val < 183 then 38 else 38))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 74 else 22) else (if i.val < 187 then 21 else 74)) else (if i.val < 190 then (if i.val < 189 then 38 else 38) else (if i.val < 191 then 71 else 22)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 21 else 38) else (if i.val < 195 then 40 else 20)) else (if i.val < 198 then (if i.val < 197 then 74 else 72) else (if i.val < 199 then 75 else 21))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 38 else 38) else (if i.val < 203 then 38 else 21)) else (if i.val < 206 then (if i.val < 205 then 38 else 21) else (if i.val < 207 then 21 else 22)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 74 else 20) else (if i.val < 211 then 21 else 38)) else (if i.val < 214 then (if i.val < 213 then 6 else 42) else (if i.val < 215 then 22 else 38))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 21 else 38) else (if i.val < 219 then 21 else 71)) else (if i.val < 222 then (if i.val < 221 then 38 else 38) else (if i.val < 223 then 43 else 21))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 38 else 38) else (if i.val < 227 then 38 else 21)) else (if i.val < 230 then (if i.val < 229 then 43 else 38) else (if i.val < 231 then 38 else 68))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 21 else 43) else (if i.val < 235 then 38 else 38)) else (if i.val < 238 then (if i.val < 237 then 70 else 74) else (if i.val < 239 then 73 else 38)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 77 else 74) else (if i.val < 243 then 71 else 38)) else (if i.val < 246 then (if i.val < 245 then 73 else 73) else (if i.val < 247 then 20 else 41))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 72 else 38) else (if i.val < 251 then 42 else 74)) else (if i.val < 254 then (if i.val < 253 then 73 else 21) else (if i.val < 255 then 20 else 71))))))))

theorem g32p_supplierForest_actual_107 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_107 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_107 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_126231
  · exact g32p_supplierForest_actual_126259
  · exact g32p_supplierForest_actual_126262
  · exact g32p_supplierForest_actual_126320
  · exact g32p_supplierForest_actual_126384
  · exact g32p_supplierForest_actual_126389
  · exact g32p_supplierForest_actual_126479
  · exact g32p_supplierForest_actual_126492
  · exact g32p_supplierForest_actual_126500
  · exact g32p_supplierForest_actual_126614
  · exact g32p_supplierForest_actual_126648
  · exact g32p_supplierForest_actual_126660
  · exact g32p_supplierForest_actual_126666
  · exact g32p_supplierForest_actual_126685
  · exact g32p_supplierForest_actual_126690
  · exact g32p_supplierForest_actual_126704
  · exact g32p_supplierForest_actual_126747
  · exact g32p_supplierForest_actual_126761
  · exact g32p_supplierForest_actual_126767
  · exact g32p_supplierForest_actual_126781
  · exact g32p_supplierForest_actual_126788
  · exact g32p_supplierForest_actual_126858
  · exact g32p_supplierForest_actual_126868
  · exact g32p_supplierForest_actual_126869
  · exact g32p_supplierForest_actual_126871
  · exact g32p_supplierForest_actual_126896
  · exact g32p_supplierForest_actual_126979
  · exact g32p_supplierForest_actual_126987
  · exact g32p_supplierForest_actual_126999
  · exact g32p_supplierForest_actual_127025
  · exact g32p_supplierForest_actual_127036
  · exact g32p_supplierForest_actual_127062
  · exact g32p_supplierForest_actual_127075
  · exact g32p_supplierForest_actual_127083
  · exact g32p_supplierForest_actual_127101
  · exact g32p_supplierForest_actual_127119
  · exact g32p_supplierForest_actual_127129
  · exact g32p_supplierForest_actual_127147
  · exact g32p_supplierForest_actual_127150
  · exact g32p_supplierForest_actual_127153
  · exact g32p_supplierForest_actual_127172
  · exact g32p_supplierForest_actual_127190
  · exact g32p_supplierForest_actual_127225
  · exact g32p_supplierForest_actual_127231
  · exact g32p_supplierForest_actual_127250
  · exact g32p_supplierForest_actual_127254
  · exact g32p_supplierForest_actual_127288
  · exact g32p_supplierForest_actual_127300
  · exact g32p_supplierForest_actual_127335
  · exact g32p_supplierForest_actual_127348
  · exact g32p_supplierForest_actual_127359
  · exact g32p_supplierForest_actual_127368
  · exact g32p_supplierForest_actual_127383
  · exact g32p_supplierForest_actual_127438
  · exact g32p_supplierForest_actual_127476
  · exact g32p_supplierForest_actual_127481
  · exact g32p_supplierForest_actual_127491
  · exact g32p_supplierForest_actual_127524
  · exact g32p_supplierForest_actual_127536
  · exact g32p_supplierForest_actual_127569
  · exact g32p_supplierForest_actual_127587
  · exact g32p_supplierForest_actual_127598
  · exact g32p_supplierForest_actual_127683
  · exact g32p_supplierForest_actual_127688
  · exact g32p_supplierForest_actual_127702
  · exact g32p_supplierForest_actual_127743
  · exact g32p_supplierForest_actual_127769
  · exact g32p_supplierForest_actual_127776
  · exact g32p_supplierForest_actual_127808
  · exact g32p_supplierForest_actual_127816
  · exact g32p_supplierForest_actual_127843
  · exact g32p_supplierForest_actual_127876
  · exact g32p_supplierForest_actual_127893
  · exact g32p_supplierForest_actual_127921
  · exact g32p_supplierForest_actual_127922
  · exact g32p_supplierForest_actual_127951
  · exact g32p_supplierForest_actual_128005
  · exact g32p_supplierForest_actual_128025
  · exact g32p_supplierForest_actual_128041
  · exact g32p_supplierForest_actual_128046
  · exact g32p_supplierForest_actual_128055
  · exact g32p_supplierForest_actual_128056
  · exact g32p_supplierForest_actual_128090
  · exact g32p_supplierForest_actual_128093
  · exact g32p_supplierForest_actual_128094
  · exact g32p_supplierForest_actual_128102
  · exact g32p_supplierForest_actual_128105
  · exact g32p_supplierForest_actual_128131
  · exact g32p_supplierForest_actual_128188
  · exact g32p_supplierForest_actual_128276
  · exact g32p_supplierForest_actual_128281
  · exact g32p_supplierForest_actual_128307
  · exact g32p_supplierForest_actual_128312
  · exact g32p_supplierForest_actual_128318
  · exact g32p_supplierForest_actual_128331
  · exact g32p_supplierForest_actual_128418
  · exact g32p_supplierForest_actual_128434
  · exact g32p_supplierForest_actual_128447
  · exact g32p_supplierForest_actual_128463
  · exact g32p_supplierForest_actual_128480
  · exact g32p_supplierForest_actual_128490
  · exact g32p_supplierForest_actual_128495
  · exact g32p_supplierForest_actual_128496
  · exact g32p_supplierForest_actual_128514
  · exact g32p_supplierForest_actual_128531
  · exact g32p_supplierForest_actual_128546
  · exact g32p_supplierForest_actual_128548
  · exact g32p_supplierForest_actual_128554
  · exact g32p_supplierForest_actual_128599
  · exact g32p_supplierForest_actual_128621
  · exact g32p_supplierForest_actual_128633
  · exact g32p_supplierForest_actual_128668
  · exact g32p_supplierForest_actual_128678
  · exact g32p_supplierForest_actual_128680
  · exact g32p_supplierForest_actual_128690
  · exact g32p_supplierForest_actual_128764
  · exact g32p_supplierForest_actual_128772
  · exact g32p_supplierForest_actual_128774
  · exact g32p_supplierForest_actual_128800
  · exact g32p_supplierForest_actual_128805
  · exact g32p_supplierForest_actual_128818
  · exact g32p_supplierForest_actual_128822
  · exact g32p_supplierForest_actual_128846
  · exact g32p_supplierForest_actual_128866
  · exact g32p_supplierForest_actual_128873
  · exact g32p_supplierForest_actual_128878
  · exact g32p_supplierForest_actual_128968
  · exact g32p_supplierForest_actual_128983
  · exact g32p_supplierForest_actual_128988
  · exact g32p_supplierForest_actual_128989
  · exact g32p_supplierForest_actual_129001
  · exact g32p_supplierForest_actual_129016
  · exact g32p_supplierForest_actual_129040
  · exact g32p_supplierForest_actual_129051
  · exact g32p_supplierForest_actual_129068
  · exact g32p_supplierForest_actual_129097
  · exact g32p_supplierForest_actual_129135
  · exact g32p_supplierForest_actual_129141
  · exact g32p_supplierForest_actual_129169
  · exact g32p_supplierForest_actual_129190
  · exact g32p_supplierForest_actual_129203
  · exact g32p_supplierForest_actual_129204
  · exact g32p_supplierForest_actual_129211
  · exact g32p_supplierForest_actual_129233
  · exact g32p_supplierForest_actual_129239
  · exact g32p_supplierForest_actual_129259
  · exact g32p_supplierForest_actual_129330
  · exact g32p_supplierForest_actual_129337
  · exact g32p_supplierForest_actual_129342
  · exact g32p_supplierForest_actual_129349
  · exact g32p_supplierForest_actual_129355
  · exact g32p_supplierForest_actual_129373
  · exact g32p_supplierForest_actual_129377
  · exact g32p_supplierForest_actual_129433
  · exact g32p_supplierForest_actual_129441
  · exact g32p_supplierForest_actual_129461
  · exact g32p_supplierForest_actual_129462
  · exact g32p_supplierForest_actual_129489
  · exact g32p_supplierForest_actual_129499
  · exact g32p_supplierForest_actual_129506
  · exact g32p_supplierForest_actual_129508
  · exact g32p_supplierForest_actual_129512
  · exact g32p_supplierForest_actual_129520
  · exact g32p_supplierForest_actual_129544
  · exact g32p_supplierForest_actual_129571
  · exact g32p_supplierForest_actual_129597
  · exact g32p_supplierForest_actual_129607
  · exact g32p_supplierForest_actual_129626
  · exact g32p_supplierForest_actual_129652
  · exact g32p_supplierForest_actual_129659
  · exact g32p_supplierForest_actual_129668
  · exact g32p_supplierForest_actual_129680
  · exact g32p_supplierForest_actual_129682
  · exact g32p_supplierForest_actual_129706
  · exact g32p_supplierForest_actual_129733
  · exact g32p_supplierForest_actual_129815
  · exact g32p_supplierForest_actual_129823
  · exact g32p_supplierForest_actual_129869
  · exact g32p_supplierForest_actual_129871
  · exact g32p_supplierForest_actual_129896
  · exact g32p_supplierForest_actual_129909
  · exact g32p_supplierForest_actual_129959
  · exact g32p_supplierForest_actual_129968
  · exact g32p_supplierForest_actual_129989
  · exact g32p_supplierForest_actual_129990
  · exact g32p_supplierForest_actual_130006
  · exact g32p_supplierForest_actual_130027
  · exact g32p_supplierForest_actual_130051
  · exact g32p_supplierForest_actual_130063
  · exact g32p_supplierForest_actual_130073
  · exact g32p_supplierForest_actual_130074
  · exact g32p_supplierForest_actual_130088
  · exact g32p_supplierForest_actual_130091
  · exact g32p_supplierForest_actual_130106
  · exact g32p_supplierForest_actual_130117
  · exact g32p_supplierForest_actual_130130
  · exact g32p_supplierForest_actual_130190
  · exact g32p_supplierForest_actual_130196
  · exact g32p_supplierForest_actual_130202
  · exact g32p_supplierForest_actual_130264
  · exact g32p_supplierForest_actual_130279
  · exact g32p_supplierForest_actual_130290
  · exact g32p_supplierForest_actual_130293
  · exact g32p_supplierForest_actual_130311
  · exact g32p_supplierForest_actual_130314
  · exact g32p_supplierForest_actual_130316
  · exact g32p_supplierForest_actual_130372
  · exact g32p_supplierForest_actual_130376
  · exact g32p_supplierForest_actual_130387
  · exact g32p_supplierForest_actual_130402
  · exact g32p_supplierForest_actual_130417
  · exact g32p_supplierForest_actual_130425
  · exact g32p_supplierForest_actual_130483
  · exact g32p_supplierForest_actual_130484
  · exact g32p_supplierForest_actual_130508
  · exact g32p_supplierForest_actual_130569
  · exact g32p_supplierForest_actual_130571
  · exact g32p_supplierForest_actual_130605
  · exact g32p_supplierForest_actual_130617
  · exact g32p_supplierForest_actual_130620
  · exact g32p_supplierForest_actual_130662
  · exact g32p_supplierForest_actual_130718
  · exact g32p_supplierForest_actual_130745
  · exact g32p_supplierForest_actual_130750
  · exact g32p_supplierForest_actual_130760
  · exact g32p_supplierForest_actual_130765
  · exact g32p_supplierForest_actual_130779
  · exact g32p_supplierForest_actual_130850
  · exact g32p_supplierForest_actual_130853
  · exact g32p_supplierForest_actual_130880
  · exact g32p_supplierForest_actual_130898
  · exact g32p_supplierForest_actual_130941
  · exact g32p_supplierForest_actual_130942
  · exact g32p_supplierForest_actual_130951
  · exact g32p_supplierForest_actual_130965
  · exact g32p_supplierForest_actual_130972
  · exact g32p_supplierForest_actual_130979
  · exact g32p_supplierForest_actual_131004
  · exact g32p_supplierForest_actual_131034
  · exact g32p_supplierForest_actual_131061
  · exact g32p_supplierForest_actual_131148
  · exact g32p_supplierForest_actual_131158
  · exact g32p_supplierForest_actual_131165
  · exact g32p_supplierForest_actual_131218
  · exact g32p_supplierForest_actual_131266
  · exact g32p_supplierForest_actual_131296
  · exact g32p_supplierForest_actual_131360
  · exact g32p_supplierForest_actual_131374
  · exact g32p_supplierForest_actual_131389
  · exact g32p_supplierForest_actual_131400
  · exact g32p_supplierForest_actual_131413
  · exact g32p_supplierForest_actual_131417
  · exact g32p_supplierForest_actual_131421
  · exact g32p_supplierForest_actual_131438
  · exact g32p_supplierForest_actual_131445
  · exact g32p_supplierForest_actual_131448

def g32p_supplierForest_nodes_108 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_131482 else g32p_supplierForest_node_131487) else (if i.val < 3 then g32p_supplierForest_node_131544 else g32p_supplierForest_node_131585)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_131598 else g32p_supplierForest_node_131604) else (if i.val < 7 then g32p_supplierForest_node_131674 else g32p_supplierForest_node_131682))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_131707 else g32p_supplierForest_node_131718) else (if i.val < 11 then g32p_supplierForest_node_131723 else g32p_supplierForest_node_131809)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_131840 else g32p_supplierForest_node_131863) else (if i.val < 15 then g32p_supplierForest_node_131886 else g32p_supplierForest_node_131894)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_131919 else g32p_supplierForest_node_131922) else (if i.val < 19 then g32p_supplierForest_node_131925 else g32p_supplierForest_node_131927)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_131942 else g32p_supplierForest_node_131973) else (if i.val < 23 then g32p_supplierForest_node_131979 else g32p_supplierForest_node_131982))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_131987 else g32p_supplierForest_node_132031) else (if i.val < 27 then g32p_supplierForest_node_132033 else g32p_supplierForest_node_132040)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_132042 else g32p_supplierForest_node_132134) else (if i.val < 31 then g32p_supplierForest_node_132150 else g32p_supplierForest_node_132169))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_132207 else g32p_supplierForest_node_132246) else (if i.val < 35 then g32p_supplierForest_node_132249 else g32p_supplierForest_node_132277)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_132310 else g32p_supplierForest_node_132312) else (if i.val < 39 then g32p_supplierForest_node_132323 else g32p_supplierForest_node_132336))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_132375 else g32p_supplierForest_node_132407) else (if i.val < 43 then g32p_supplierForest_node_132411 else g32p_supplierForest_node_132443)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_132466 else g32p_supplierForest_node_132468) else (if i.val < 47 then g32p_supplierForest_node_132509 else g32p_supplierForest_node_132526)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_132542 else g32p_supplierForest_node_132543) else (if i.val < 51 then g32p_supplierForest_node_132547 else g32p_supplierForest_node_132567)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_132590 else g32p_supplierForest_node_132597) else (if i.val < 55 then g32p_supplierForest_node_132607 else g32p_supplierForest_node_132613))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_132626 else g32p_supplierForest_node_132656) else (if i.val < 59 then g32p_supplierForest_node_132701 else g32p_supplierForest_node_132708)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_132710 else g32p_supplierForest_node_132720) else (if i.val < 63 then g32p_supplierForest_node_132739 else g32p_supplierForest_node_132746)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_132761 else g32p_supplierForest_node_132770) else (if i.val < 67 then g32p_supplierForest_node_132799 else g32p_supplierForest_node_132818)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_132822 else g32p_supplierForest_node_132849) else (if i.val < 71 then g32p_supplierForest_node_132851 else g32p_supplierForest_node_132854))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_132890 else g32p_supplierForest_node_132892) else (if i.val < 75 then g32p_supplierForest_node_132898 else g32p_supplierForest_node_132915)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_132917 else g32p_supplierForest_node_132954) else (if i.val < 79 then g32p_supplierForest_node_132981 else g32p_supplierForest_node_133063)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_133064 else g32p_supplierForest_node_133090) else (if i.val < 83 then g32p_supplierForest_node_133112 else g32p_supplierForest_node_133128)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_133221 else g32p_supplierForest_node_133235) else (if i.val < 87 then g32p_supplierForest_node_133248 else g32p_supplierForest_node_133261))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_133267 else g32p_supplierForest_node_133307) else (if i.val < 91 then g32p_supplierForest_node_133330 else g32p_supplierForest_node_133371)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_133384 else g32p_supplierForest_node_133402) else (if i.val < 95 then g32p_supplierForest_node_133431 else g32p_supplierForest_node_133443))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_133459 else g32p_supplierForest_node_133502) else (if i.val < 99 then g32p_supplierForest_node_133545 else g32p_supplierForest_node_133554)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_133561 else g32p_supplierForest_node_133607) else (if i.val < 103 then g32p_supplierForest_node_133635 else g32p_supplierForest_node_133637))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_133663 else g32p_supplierForest_node_133678) else (if i.val < 107 then g32p_supplierForest_node_133756 else g32p_supplierForest_node_133764)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_133800 else g32p_supplierForest_node_133805) else (if i.val < 111 then g32p_supplierForest_node_133840 else g32p_supplierForest_node_133848)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_133850 else g32p_supplierForest_node_133853) else (if i.val < 115 then g32p_supplierForest_node_133870 else g32p_supplierForest_node_133878)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_133915 else g32p_supplierForest_node_133925) else (if i.val < 119 then g32p_supplierForest_node_134026 else g32p_supplierForest_node_134030))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_134097 else g32p_supplierForest_node_134116) else (if i.val < 123 then g32p_supplierForest_node_134120 else g32p_supplierForest_node_134145)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_134147 else g32p_supplierForest_node_134156) else (if i.val < 127 then g32p_supplierForest_node_134164 else g32p_supplierForest_node_134190))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_134193 else g32p_supplierForest_node_134212) else (if i.val < 131 then g32p_supplierForest_node_134237 else g32p_supplierForest_node_134276)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_134282 else g32p_supplierForest_node_134284) else (if i.val < 135 then g32p_supplierForest_node_134328 else g32p_supplierForest_node_134344))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_134357 else g32p_supplierForest_node_134387) else (if i.val < 139 then g32p_supplierForest_node_134399 else g32p_supplierForest_node_134416)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_134445 else g32p_supplierForest_node_134554) else (if i.val < 143 then g32p_supplierForest_node_134563 else g32p_supplierForest_node_134576)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_134605 else g32p_supplierForest_node_134635) else (if i.val < 147 then g32p_supplierForest_node_134762 else g32p_supplierForest_node_134768)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_134798 else g32p_supplierForest_node_134901) else (if i.val < 151 then g32p_supplierForest_node_134950 else g32p_supplierForest_node_134986))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_134989 else g32p_supplierForest_node_135053) else (if i.val < 155 then g32p_supplierForest_node_135055 else g32p_supplierForest_node_135080)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_135087 else g32p_supplierForest_node_135093) else (if i.val < 159 then g32p_supplierForest_node_135123 else g32p_supplierForest_node_135184))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_135203 else g32p_supplierForest_node_135217) else (if i.val < 163 then g32p_supplierForest_node_135230 else g32p_supplierForest_node_135247)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_135271 else g32p_supplierForest_node_135273) else (if i.val < 167 then g32p_supplierForest_node_135283 else g32p_supplierForest_node_135290))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_135349 else g32p_supplierForest_node_135351) else (if i.val < 171 then g32p_supplierForest_node_135353 else g32p_supplierForest_node_135360)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_135363 else g32p_supplierForest_node_135411) else (if i.val < 175 then g32p_supplierForest_node_135428 else g32p_supplierForest_node_135439)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_135450 else g32p_supplierForest_node_135453) else (if i.val < 179 then g32p_supplierForest_node_135502 else g32p_supplierForest_node_135513)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_135520 else g32p_supplierForest_node_135560) else (if i.val < 183 then g32p_supplierForest_node_135565 else g32p_supplierForest_node_135583))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_135589 else g32p_supplierForest_node_135592) else (if i.val < 187 then g32p_supplierForest_node_135608 else g32p_supplierForest_node_135660)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_135668 else g32p_supplierForest_node_135700) else (if i.val < 191 then g32p_supplierForest_node_135762 else g32p_supplierForest_node_135770)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_135802 else g32p_supplierForest_node_135842) else (if i.val < 195 then g32p_supplierForest_node_135846 else g32p_supplierForest_node_135854)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_135875 else g32p_supplierForest_node_135886) else (if i.val < 199 then g32p_supplierForest_node_135904 else g32p_supplierForest_node_135910))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_135947 else g32p_supplierForest_node_135961) else (if i.val < 203 then g32p_supplierForest_node_136064 else g32p_supplierForest_node_136091)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_136118 else g32p_supplierForest_node_136125) else (if i.val < 207 then g32p_supplierForest_node_136188 else g32p_supplierForest_node_136250)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_136263 else g32p_supplierForest_node_136272) else (if i.val < 211 then g32p_supplierForest_node_136279 else g32p_supplierForest_node_136288)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_136302 else g32p_supplierForest_node_136325) else (if i.val < 215 then g32p_supplierForest_node_136342 else g32p_supplierForest_node_136346))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_136351 else g32p_supplierForest_node_136363) else (if i.val < 219 then g32p_supplierForest_node_136409 else g32p_supplierForest_node_136462)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_136607 else g32p_supplierForest_node_136615) else (if i.val < 223 then g32p_supplierForest_node_136622 else g32p_supplierForest_node_136667))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_136733 else g32p_supplierForest_node_136756) else (if i.val < 227 then g32p_supplierForest_node_136761 else g32p_supplierForest_node_136764)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_136780 else g32p_supplierForest_node_136827) else (if i.val < 231 then g32p_supplierForest_node_136834 else g32p_supplierForest_node_136860))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_136872 else g32p_supplierForest_node_136875) else (if i.val < 235 then g32p_supplierForest_node_136886 else g32p_supplierForest_node_136926)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_136958 else g32p_supplierForest_node_136961) else (if i.val < 239 then g32p_supplierForest_node_136999 else g32p_supplierForest_node_137033)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_137036 else g32p_supplierForest_node_137059) else (if i.val < 243 then g32p_supplierForest_node_137117 else g32p_supplierForest_node_137123)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_137153 else g32p_supplierForest_node_137239) else (if i.val < 247 then g32p_supplierForest_node_137240 else g32p_supplierForest_node_137243))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_137256 else g32p_supplierForest_node_137262) else (if i.val < 251 then g32p_supplierForest_node_137273 else g32p_supplierForest_node_137281)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_137317 else g32p_supplierForest_node_137327) else (if i.val < 255 then g32p_supplierForest_node_137338 else g32p_supplierForest_node_137362))))))))

def g32p_supplierForest_classes_108 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 73 else 94) else (if i.val < 3 then 38 else 41)) else (if i.val < 6 then (if i.val < 5 then 73 else 20) else (if i.val < 7 then 21 else 72))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 41 else 71) else (if i.val < 11 then 38 else 21)) else (if i.val < 14 then (if i.val < 13 then 71 else 72) else (if i.val < 15 then 71 else 43)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 73 else 71) else (if i.val < 19 then 21 else 78)) else (if i.val < 22 then (if i.val < 21 then 71 else 71) else (if i.val < 23 then 20 else 74))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 74 else 68) else (if i.val < 27 then 74 else 38)) else (if i.val < 30 then (if i.val < 29 then 21 else 71) else (if i.val < 31 then 38 else 38))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 70 else 21) else (if i.val < 35 then 38 else 38)) else (if i.val < 38 then (if i.val < 37 then 73 else 73) else (if i.val < 39 then 21 else 71))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 38 else 21) else (if i.val < 43 then 70 else 73)) else (if i.val < 46 then (if i.val < 45 then 38 else 38) else (if i.val < 47 then 38 else 71)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 71 else 38) else (if i.val < 51 then 38 else 71)) else (if i.val < 54 then (if i.val < 53 then 38 else 38) else (if i.val < 55 then 79 else 21))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 40 else 38) else (if i.val < 59 then 22 else 38)) else (if i.val < 62 then (if i.val < 61 then 38 else 21) else (if i.val < 63 then 20 else 68)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 70 else 74) else (if i.val < 67 then 21 else 74)) else (if i.val < 70 then (if i.val < 69 then 22 else 71) else (if i.val < 71 then 75 else 72))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 42 else 38) else (if i.val < 75 then 38 else 73)) else (if i.val < 78 then (if i.val < 77 then 38 else 71) else (if i.val < 79 then 21 else 72)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 21 else 71) else (if i.val < 83 then 20 else 21)) else (if i.val < 86 then (if i.val < 85 then 21 else 75) else (if i.val < 87 then 72 else 75))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 38 else 73) else (if i.val < 91 then 21 else 42)) else (if i.val < 94 then (if i.val < 93 then 73 else 77) else (if i.val < 95 then 38 else 21))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 68 else 73) else (if i.val < 99 then 73 else 68)) else (if i.val < 102 then (if i.val < 101 then 20 else 38) else (if i.val < 103 then 21 else 70))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 74 else 94) else (if i.val < 107 then 43 else 73)) else (if i.val < 110 then (if i.val < 109 then 43 else 42) else (if i.val < 111 then 38 else 38)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 21 else 21) else (if i.val < 115 then 71 else 72)) else (if i.val < 118 then (if i.val < 117 then 71 else 71) else (if i.val < 119 then 72 else 71))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 73 else 21) else (if i.val < 123 then 38 else 40)) else (if i.val < 126 then (if i.val < 125 then 21 else 73) else (if i.val < 127 then 74 else 38))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 38 else 38) else (if i.val < 131 then 68 else 38)) else (if i.val < 134 then (if i.val < 133 then 21 else 94) else (if i.val < 135 then 21 else 73))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 38 else 73) else (if i.val < 139 then 70 else 20)) else (if i.val < 142 then (if i.val < 141 then 38 else 21) else (if i.val < 143 then 71 else 73)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 20 else 21) else (if i.val < 147 then 72 else 73)) else (if i.val < 150 then (if i.val < 149 then 73 else 21) else (if i.val < 151 then 68 else 70))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 75 else 38) else (if i.val < 155 then 38 else 74)) else (if i.val < 158 then (if i.val < 157 then 73 else 42) else (if i.val < 159 then 22 else 74))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 74 else 38) else (if i.val < 163 then 71 else 21)) else (if i.val < 166 then (if i.val < 165 then 73 else 71) else (if i.val < 167 then 42 else 68))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 43 else 71) else (if i.val < 171 then 71 else 73)) else (if i.val < 174 then (if i.val < 173 then 38 else 68) else (if i.val < 175 then 40 else 38)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 21 else 73) else (if i.val < 179 then 21 else 71)) else (if i.val < 182 then (if i.val < 181 then 74 else 38) else (if i.val < 183 then 21 else 38))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 73 else 21) else (if i.val < 187 then 72 else 68)) else (if i.val < 190 then (if i.val < 189 then 38 else 38) else (if i.val < 191 then 21 else 21)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 94 else 42) else (if i.val < 195 then 43 else 40)) else (if i.val < 198 then (if i.val < 197 then 21 else 38) else (if i.val < 199 then 42 else 18))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 42 else 20) else (if i.val < 203 then 72 else 74)) else (if i.val < 206 then (if i.val < 205 then 38 else 70) else (if i.val < 207 then 68 else 21)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 21 else 73) else (if i.val < 211 then 7 else 43)) else (if i.val < 214 then (if i.val < 213 then 38 else 75) else (if i.val < 215 then 72 else 21))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 43 else 21) else (if i.val < 219 then 78 else 94)) else (if i.val < 222 then (if i.val < 221 then 38 else 38) else (if i.val < 223 then 41 else 73))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 68 else 21) else (if i.val < 227 then 79 else 73)) else (if i.val < 230 then (if i.val < 229 then 38 else 21) else (if i.val < 231 then 21 else 73))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 38 else 94) else (if i.val < 235 then 77 else 38)) else (if i.val < 238 then (if i.val < 237 then 38 else 7) else (if i.val < 239 then 73 else 38)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 42 else 42) else (if i.val < 243 then 74 else 20)) else (if i.val < 246 then (if i.val < 245 then 72 else 41) else (if i.val < 247 then 21 else 21))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 38 else 73) else (if i.val < 251 then 38 else 73)) else (if i.val < 254 then (if i.val < 253 then 73 else 72) else (if i.val < 255 then 73 else 74))))))))

theorem g32p_supplierForest_actual_108 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_108 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_108 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_131482
  · exact g32p_supplierForest_actual_131487
  · exact g32p_supplierForest_actual_131544
  · exact g32p_supplierForest_actual_131585
  · exact g32p_supplierForest_actual_131598
  · exact g32p_supplierForest_actual_131604
  · exact g32p_supplierForest_actual_131674
  · exact g32p_supplierForest_actual_131682
  · exact g32p_supplierForest_actual_131707
  · exact g32p_supplierForest_actual_131718
  · exact g32p_supplierForest_actual_131723
  · exact g32p_supplierForest_actual_131809
  · exact g32p_supplierForest_actual_131840
  · exact g32p_supplierForest_actual_131863
  · exact g32p_supplierForest_actual_131886
  · exact g32p_supplierForest_actual_131894
  · exact g32p_supplierForest_actual_131919
  · exact g32p_supplierForest_actual_131922
  · exact g32p_supplierForest_actual_131925
  · exact g32p_supplierForest_actual_131927
  · exact g32p_supplierForest_actual_131942
  · exact g32p_supplierForest_actual_131973
  · exact g32p_supplierForest_actual_131979
  · exact g32p_supplierForest_actual_131982
  · exact g32p_supplierForest_actual_131987
  · exact g32p_supplierForest_actual_132031
  · exact g32p_supplierForest_actual_132033
  · exact g32p_supplierForest_actual_132040
  · exact g32p_supplierForest_actual_132042
  · exact g32p_supplierForest_actual_132134
  · exact g32p_supplierForest_actual_132150
  · exact g32p_supplierForest_actual_132169
  · exact g32p_supplierForest_actual_132207
  · exact g32p_supplierForest_actual_132246
  · exact g32p_supplierForest_actual_132249
  · exact g32p_supplierForest_actual_132277
  · exact g32p_supplierForest_actual_132310
  · exact g32p_supplierForest_actual_132312
  · exact g32p_supplierForest_actual_132323
  · exact g32p_supplierForest_actual_132336
  · exact g32p_supplierForest_actual_132375
  · exact g32p_supplierForest_actual_132407
  · exact g32p_supplierForest_actual_132411
  · exact g32p_supplierForest_actual_132443
  · exact g32p_supplierForest_actual_132466
  · exact g32p_supplierForest_actual_132468
  · exact g32p_supplierForest_actual_132509
  · exact g32p_supplierForest_actual_132526
  · exact g32p_supplierForest_actual_132542
  · exact g32p_supplierForest_actual_132543
  · exact g32p_supplierForest_actual_132547
  · exact g32p_supplierForest_actual_132567
  · exact g32p_supplierForest_actual_132590
  · exact g32p_supplierForest_actual_132597
  · exact g32p_supplierForest_actual_132607
  · exact g32p_supplierForest_actual_132613
  · exact g32p_supplierForest_actual_132626
  · exact g32p_supplierForest_actual_132656
  · exact g32p_supplierForest_actual_132701
  · exact g32p_supplierForest_actual_132708
  · exact g32p_supplierForest_actual_132710
  · exact g32p_supplierForest_actual_132720
  · exact g32p_supplierForest_actual_132739
  · exact g32p_supplierForest_actual_132746
  · exact g32p_supplierForest_actual_132761
  · exact g32p_supplierForest_actual_132770
  · exact g32p_supplierForest_actual_132799
  · exact g32p_supplierForest_actual_132818
  · exact g32p_supplierForest_actual_132822
  · exact g32p_supplierForest_actual_132849
  · exact g32p_supplierForest_actual_132851
  · exact g32p_supplierForest_actual_132854
  · exact g32p_supplierForest_actual_132890
  · exact g32p_supplierForest_actual_132892
  · exact g32p_supplierForest_actual_132898
  · exact g32p_supplierForest_actual_132915
  · exact g32p_supplierForest_actual_132917
  · exact g32p_supplierForest_actual_132954
  · exact g32p_supplierForest_actual_132981
  · exact g32p_supplierForest_actual_133063
  · exact g32p_supplierForest_actual_133064
  · exact g32p_supplierForest_actual_133090
  · exact g32p_supplierForest_actual_133112
  · exact g32p_supplierForest_actual_133128
  · exact g32p_supplierForest_actual_133221
  · exact g32p_supplierForest_actual_133235
  · exact g32p_supplierForest_actual_133248
  · exact g32p_supplierForest_actual_133261
  · exact g32p_supplierForest_actual_133267
  · exact g32p_supplierForest_actual_133307
  · exact g32p_supplierForest_actual_133330
  · exact g32p_supplierForest_actual_133371
  · exact g32p_supplierForest_actual_133384
  · exact g32p_supplierForest_actual_133402
  · exact g32p_supplierForest_actual_133431
  · exact g32p_supplierForest_actual_133443
  · exact g32p_supplierForest_actual_133459
  · exact g32p_supplierForest_actual_133502
  · exact g32p_supplierForest_actual_133545
  · exact g32p_supplierForest_actual_133554
  · exact g32p_supplierForest_actual_133561
  · exact g32p_supplierForest_actual_133607
  · exact g32p_supplierForest_actual_133635
  · exact g32p_supplierForest_actual_133637
  · exact g32p_supplierForest_actual_133663
  · exact g32p_supplierForest_actual_133678
  · exact g32p_supplierForest_actual_133756
  · exact g32p_supplierForest_actual_133764
  · exact g32p_supplierForest_actual_133800
  · exact g32p_supplierForest_actual_133805
  · exact g32p_supplierForest_actual_133840
  · exact g32p_supplierForest_actual_133848
  · exact g32p_supplierForest_actual_133850
  · exact g32p_supplierForest_actual_133853
  · exact g32p_supplierForest_actual_133870
  · exact g32p_supplierForest_actual_133878
  · exact g32p_supplierForest_actual_133915
  · exact g32p_supplierForest_actual_133925
  · exact g32p_supplierForest_actual_134026
  · exact g32p_supplierForest_actual_134030
  · exact g32p_supplierForest_actual_134097
  · exact g32p_supplierForest_actual_134116
  · exact g32p_supplierForest_actual_134120
  · exact g32p_supplierForest_actual_134145
  · exact g32p_supplierForest_actual_134147
  · exact g32p_supplierForest_actual_134156
  · exact g32p_supplierForest_actual_134164
  · exact g32p_supplierForest_actual_134190
  · exact g32p_supplierForest_actual_134193
  · exact g32p_supplierForest_actual_134212
  · exact g32p_supplierForest_actual_134237
  · exact g32p_supplierForest_actual_134276
  · exact g32p_supplierForest_actual_134282
  · exact g32p_supplierForest_actual_134284
  · exact g32p_supplierForest_actual_134328
  · exact g32p_supplierForest_actual_134344
  · exact g32p_supplierForest_actual_134357
  · exact g32p_supplierForest_actual_134387
  · exact g32p_supplierForest_actual_134399
  · exact g32p_supplierForest_actual_134416
  · exact g32p_supplierForest_actual_134445
  · exact g32p_supplierForest_actual_134554
  · exact g32p_supplierForest_actual_134563
  · exact g32p_supplierForest_actual_134576
  · exact g32p_supplierForest_actual_134605
  · exact g32p_supplierForest_actual_134635
  · exact g32p_supplierForest_actual_134762
  · exact g32p_supplierForest_actual_134768
  · exact g32p_supplierForest_actual_134798
  · exact g32p_supplierForest_actual_134901
  · exact g32p_supplierForest_actual_134950
  · exact g32p_supplierForest_actual_134986
  · exact g32p_supplierForest_actual_134989
  · exact g32p_supplierForest_actual_135053
  · exact g32p_supplierForest_actual_135055
  · exact g32p_supplierForest_actual_135080
  · exact g32p_supplierForest_actual_135087
  · exact g32p_supplierForest_actual_135093
  · exact g32p_supplierForest_actual_135123
  · exact g32p_supplierForest_actual_135184
  · exact g32p_supplierForest_actual_135203
  · exact g32p_supplierForest_actual_135217
  · exact g32p_supplierForest_actual_135230
  · exact g32p_supplierForest_actual_135247
  · exact g32p_supplierForest_actual_135271
  · exact g32p_supplierForest_actual_135273
  · exact g32p_supplierForest_actual_135283
  · exact g32p_supplierForest_actual_135290
  · exact g32p_supplierForest_actual_135349
  · exact g32p_supplierForest_actual_135351
  · exact g32p_supplierForest_actual_135353
  · exact g32p_supplierForest_actual_135360
  · exact g32p_supplierForest_actual_135363
  · exact g32p_supplierForest_actual_135411
  · exact g32p_supplierForest_actual_135428
  · exact g32p_supplierForest_actual_135439
  · exact g32p_supplierForest_actual_135450
  · exact g32p_supplierForest_actual_135453
  · exact g32p_supplierForest_actual_135502
  · exact g32p_supplierForest_actual_135513
  · exact g32p_supplierForest_actual_135520
  · exact g32p_supplierForest_actual_135560
  · exact g32p_supplierForest_actual_135565
  · exact g32p_supplierForest_actual_135583
  · exact g32p_supplierForest_actual_135589
  · exact g32p_supplierForest_actual_135592
  · exact g32p_supplierForest_actual_135608
  · exact g32p_supplierForest_actual_135660
  · exact g32p_supplierForest_actual_135668
  · exact g32p_supplierForest_actual_135700
  · exact g32p_supplierForest_actual_135762
  · exact g32p_supplierForest_actual_135770
  · exact g32p_supplierForest_actual_135802
  · exact g32p_supplierForest_actual_135842
  · exact g32p_supplierForest_actual_135846
  · exact g32p_supplierForest_actual_135854
  · exact g32p_supplierForest_actual_135875
  · exact g32p_supplierForest_actual_135886
  · exact g32p_supplierForest_actual_135904
  · exact g32p_supplierForest_actual_135910
  · exact g32p_supplierForest_actual_135947
  · exact g32p_supplierForest_actual_135961
  · exact g32p_supplierForest_actual_136064
  · exact g32p_supplierForest_actual_136091
  · exact g32p_supplierForest_actual_136118
  · exact g32p_supplierForest_actual_136125
  · exact g32p_supplierForest_actual_136188
  · exact g32p_supplierForest_actual_136250
  · exact g32p_supplierForest_actual_136263
  · exact g32p_supplierForest_actual_136272
  · exact g32p_supplierForest_actual_136279
  · exact g32p_supplierForest_actual_136288
  · exact g32p_supplierForest_actual_136302
  · exact g32p_supplierForest_actual_136325
  · exact g32p_supplierForest_actual_136342
  · exact g32p_supplierForest_actual_136346
  · exact g32p_supplierForest_actual_136351
  · exact g32p_supplierForest_actual_136363
  · exact g32p_supplierForest_actual_136409
  · exact g32p_supplierForest_actual_136462
  · exact g32p_supplierForest_actual_136607
  · exact g32p_supplierForest_actual_136615
  · exact g32p_supplierForest_actual_136622
  · exact g32p_supplierForest_actual_136667
  · exact g32p_supplierForest_actual_136733
  · exact g32p_supplierForest_actual_136756
  · exact g32p_supplierForest_actual_136761
  · exact g32p_supplierForest_actual_136764
  · exact g32p_supplierForest_actual_136780
  · exact g32p_supplierForest_actual_136827
  · exact g32p_supplierForest_actual_136834
  · exact g32p_supplierForest_actual_136860
  · exact g32p_supplierForest_actual_136872
  · exact g32p_supplierForest_actual_136875
  · exact g32p_supplierForest_actual_136886
  · exact g32p_supplierForest_actual_136926
  · exact g32p_supplierForest_actual_136958
  · exact g32p_supplierForest_actual_136961
  · exact g32p_supplierForest_actual_136999
  · exact g32p_supplierForest_actual_137033
  · exact g32p_supplierForest_actual_137036
  · exact g32p_supplierForest_actual_137059
  · exact g32p_supplierForest_actual_137117
  · exact g32p_supplierForest_actual_137123
  · exact g32p_supplierForest_actual_137153
  · exact g32p_supplierForest_actual_137239
  · exact g32p_supplierForest_actual_137240
  · exact g32p_supplierForest_actual_137243
  · exact g32p_supplierForest_actual_137256
  · exact g32p_supplierForest_actual_137262
  · exact g32p_supplierForest_actual_137273
  · exact g32p_supplierForest_actual_137281
  · exact g32p_supplierForest_actual_137317
  · exact g32p_supplierForest_actual_137327
  · exact g32p_supplierForest_actual_137338
  · exact g32p_supplierForest_actual_137362

def g32p_supplierForest_nodes_109 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_137385 else g32p_supplierForest_node_137401) else (if i.val < 3 then g32p_supplierForest_node_137419 else g32p_supplierForest_node_137433)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_137477 else g32p_supplierForest_node_137563) else (if i.val < 7 then g32p_supplierForest_node_137623 else g32p_supplierForest_node_137639))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_137642 else g32p_supplierForest_node_137654) else (if i.val < 11 then g32p_supplierForest_node_137703 else g32p_supplierForest_node_137738)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_137743 else g32p_supplierForest_node_137792) else (if i.val < 15 then g32p_supplierForest_node_137803 else g32p_supplierForest_node_137855)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_137908 else g32p_supplierForest_node_137938) else (if i.val < 19 then g32p_supplierForest_node_137944 else g32p_supplierForest_node_137953)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_137988 else g32p_supplierForest_node_138058) else (if i.val < 23 then g32p_supplierForest_node_138090 else g32p_supplierForest_node_138093))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_138103 else g32p_supplierForest_node_138121) else (if i.val < 27 then g32p_supplierForest_node_138132 else g32p_supplierForest_node_138140)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_138150 else g32p_supplierForest_node_138165) else (if i.val < 31 then g32p_supplierForest_node_138172 else g32p_supplierForest_node_138199))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_138211 else g32p_supplierForest_node_138273) else (if i.val < 35 then g32p_supplierForest_node_138288 else g32p_supplierForest_node_138310)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_138316 else g32p_supplierForest_node_138330) else (if i.val < 39 then g32p_supplierForest_node_138339 else g32p_supplierForest_node_138370))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_138380 else g32p_supplierForest_node_138395) else (if i.val < 43 then g32p_supplierForest_node_138418 else g32p_supplierForest_node_138494)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_138512 else g32p_supplierForest_node_138602) else (if i.val < 47 then g32p_supplierForest_node_138623 else g32p_supplierForest_node_138625)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_138680 else g32p_supplierForest_node_138686) else (if i.val < 51 then g32p_supplierForest_node_138697 else g32p_supplierForest_node_138720)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_138731 else g32p_supplierForest_node_138737) else (if i.val < 55 then g32p_supplierForest_node_138740 else g32p_supplierForest_node_138759))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_138805 else g32p_supplierForest_node_138818) else (if i.val < 59 then g32p_supplierForest_node_138835 else g32p_supplierForest_node_138881)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_138919 else g32p_supplierForest_node_138956) else (if i.val < 63 then g32p_supplierForest_node_138960 else g32p_supplierForest_node_138985)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_139037 else g32p_supplierForest_node_139043) else (if i.val < 67 then g32p_supplierForest_node_139050 else g32p_supplierForest_node_139100)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_139113 else g32p_supplierForest_node_139115) else (if i.val < 71 then g32p_supplierForest_node_139131 else g32p_supplierForest_node_139154))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_139185 else g32p_supplierForest_node_139226) else (if i.val < 75 then g32p_supplierForest_node_139277 else g32p_supplierForest_node_139279)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_139306 else g32p_supplierForest_node_139314) else (if i.val < 79 then g32p_supplierForest_node_139366 else g32p_supplierForest_node_139398)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_139416 else g32p_supplierForest_node_139428) else (if i.val < 83 then g32p_supplierForest_node_139508 else g32p_supplierForest_node_139511)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_139514 else g32p_supplierForest_node_139553) else (if i.val < 87 then g32p_supplierForest_node_139565 else g32p_supplierForest_node_139572))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_139591 else g32p_supplierForest_node_139594) else (if i.val < 91 then g32p_supplierForest_node_139619 else g32p_supplierForest_node_139630)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_139657 else g32p_supplierForest_node_139674) else (if i.val < 95 then g32p_supplierForest_node_139681 else g32p_supplierForest_node_139684))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_139723 else g32p_supplierForest_node_139748) else (if i.val < 99 then g32p_supplierForest_node_139750 else g32p_supplierForest_node_139799)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_139802 else g32p_supplierForest_node_139814) else (if i.val < 103 then g32p_supplierForest_node_139852 else g32p_supplierForest_node_139922))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_139931 else g32p_supplierForest_node_140001) else (if i.val < 107 then g32p_supplierForest_node_140002 else g32p_supplierForest_node_140047)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_140091 else g32p_supplierForest_node_140098) else (if i.val < 111 then g32p_supplierForest_node_140103 else g32p_supplierForest_node_140146)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_140150 else g32p_supplierForest_node_140227) else (if i.val < 115 then g32p_supplierForest_node_140234 else g32p_supplierForest_node_140239)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_140312 else g32p_supplierForest_node_140352) else (if i.val < 119 then g32p_supplierForest_node_140361 else g32p_supplierForest_node_140372))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_140393 else g32p_supplierForest_node_140422) else (if i.val < 123 then g32p_supplierForest_node_140424 else g32p_supplierForest_node_140453)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_140500 else g32p_supplierForest_node_140513) else (if i.val < 127 then g32p_supplierForest_node_140531 else g32p_supplierForest_node_140540))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_140545 else g32p_supplierForest_node_140596) else (if i.val < 131 then g32p_supplierForest_node_140605 else g32p_supplierForest_node_140607)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_140652 else g32p_supplierForest_node_140693) else (if i.val < 135 then g32p_supplierForest_node_140698 else g32p_supplierForest_node_140713))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_140723 else g32p_supplierForest_node_140728) else (if i.val < 139 then g32p_supplierForest_node_140765 else g32p_supplierForest_node_140773)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_140813 else g32p_supplierForest_node_140827) else (if i.val < 143 then g32p_supplierForest_node_140908 else g32p_supplierForest_node_140963)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_141008 else g32p_supplierForest_node_141047) else (if i.val < 147 then g32p_supplierForest_node_141052 else g32p_supplierForest_node_141053)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_141060 else g32p_supplierForest_node_141124) else (if i.val < 151 then g32p_supplierForest_node_141134 else g32p_supplierForest_node_141169))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_141197 else g32p_supplierForest_node_141265) else (if i.val < 155 then g32p_supplierForest_node_141292 else g32p_supplierForest_node_141305)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_141321 else g32p_supplierForest_node_141333) else (if i.val < 159 then g32p_supplierForest_node_141431 else g32p_supplierForest_node_141432))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_141455 else g32p_supplierForest_node_141470) else (if i.val < 163 then g32p_supplierForest_node_141512 else g32p_supplierForest_node_141516)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_141525 else g32p_supplierForest_node_141555) else (if i.val < 167 then g32p_supplierForest_node_141573 else g32p_supplierForest_node_141577))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_141589 else g32p_supplierForest_node_141688) else (if i.val < 171 then g32p_supplierForest_node_141748 else g32p_supplierForest_node_141758)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_141796 else g32p_supplierForest_node_141813) else (if i.val < 175 then g32p_supplierForest_node_141838 else g32p_supplierForest_node_141847)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_141853 else g32p_supplierForest_node_141909) else (if i.val < 179 then g32p_supplierForest_node_141932 else g32p_supplierForest_node_141961)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_141978 else g32p_supplierForest_node_142036) else (if i.val < 183 then g32p_supplierForest_node_142062 else g32p_supplierForest_node_142070))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_142074 else g32p_supplierForest_node_142079) else (if i.val < 187 then g32p_supplierForest_node_142132 else g32p_supplierForest_node_142160)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_142213 else g32p_supplierForest_node_142226) else (if i.val < 191 then g32p_supplierForest_node_142234 else g32p_supplierForest_node_142256)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_142293 else g32p_supplierForest_node_142352) else (if i.val < 195 then g32p_supplierForest_node_142380 else g32p_supplierForest_node_142414)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_142418 else g32p_supplierForest_node_142463) else (if i.val < 199 then g32p_supplierForest_node_142464 else g32p_supplierForest_node_142466))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_142515 else g32p_supplierForest_node_142553) else (if i.val < 203 then g32p_supplierForest_node_142580 else g32p_supplierForest_node_142589)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_142594 else g32p_supplierForest_node_142634) else (if i.val < 207 then g32p_supplierForest_node_142687 else g32p_supplierForest_node_142712)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_142813 else g32p_supplierForest_node_142819) else (if i.val < 211 then g32p_supplierForest_node_142834 else g32p_supplierForest_node_142841)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_142859 else g32p_supplierForest_node_142913) else (if i.val < 215 then g32p_supplierForest_node_142942 else g32p_supplierForest_node_142976))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_142979 else g32p_supplierForest_node_143001) else (if i.val < 219 then g32p_supplierForest_node_143002 else g32p_supplierForest_node_143029)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_143051 else g32p_supplierForest_node_143060) else (if i.val < 223 then g32p_supplierForest_node_143101 else g32p_supplierForest_node_143107))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_143195 else g32p_supplierForest_node_143241) else (if i.val < 227 then g32p_supplierForest_node_143314 else g32p_supplierForest_node_143330)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_143342 else g32p_supplierForest_node_143376) else (if i.val < 231 then g32p_supplierForest_node_143418 else g32p_supplierForest_node_143444))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_143449 else g32p_supplierForest_node_143478) else (if i.val < 235 then g32p_supplierForest_node_143527 else g32p_supplierForest_node_143539)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_143546 else g32p_supplierForest_node_143597) else (if i.val < 239 then g32p_supplierForest_node_143621 else g32p_supplierForest_node_143649)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_143655 else g32p_supplierForest_node_143682) else (if i.val < 243 then g32p_supplierForest_node_143713 else g32p_supplierForest_node_143728)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_143736 else g32p_supplierForest_node_143750) else (if i.val < 247 then g32p_supplierForest_node_143798 else g32p_supplierForest_node_143860))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_143876 else g32p_supplierForest_node_143899) else (if i.val < 251 then g32p_supplierForest_node_143915 else g32p_supplierForest_node_143936)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_143952 else g32p_supplierForest_node_143963) else (if i.val < 255 then g32p_supplierForest_node_144024 else g32p_supplierForest_node_144036))))))))

def g32p_supplierForest_classes_109 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 38 else 21) else (if i.val < 3 then 73 else 42)) else (if i.val < 6 then (if i.val < 5 then 38 else 70) else (if i.val < 7 then 70 else 73))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 38 else 38) else (if i.val < 11 then 73 else 21)) else (if i.val < 14 then (if i.val < 13 then 38 else 73) else (if i.val < 15 then 72 else 74)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 7 else 38) else (if i.val < 19 then 73 else 79)) else (if i.val < 22 then (if i.val < 21 then 73 else 21) else (if i.val < 23 then 38 else 73))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 75 else 38) else (if i.val < 27 then 38 else 38)) else (if i.val < 30 then (if i.val < 29 then 38 else 79) else (if i.val < 31 then 21 else 43))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 73 else 41) else (if i.val < 35 then 72 else 38)) else (if i.val < 38 then (if i.val < 37 then 38 else 68) else (if i.val < 39 then 38 else 38))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 38 else 38) else (if i.val < 43 then 77 else 70)) else (if i.val < 46 then (if i.val < 45 then 38 else 7) else (if i.val < 47 then 74 else 38)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 38 else 71) else (if i.val < 51 then 21 else 38)) else (if i.val < 54 then (if i.val < 53 then 72 else 38) else (if i.val < 55 then 43 else 40))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 73 else 75) else (if i.val < 59 then 38 else 38)) else (if i.val < 62 then (if i.val < 61 then 21 else 38) else (if i.val < 63 then 72 else 72)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 72 else 73) else (if i.val < 67 then 74 else 71)) else (if i.val < 70 then (if i.val < 69 then 41 else 38) else (if i.val < 71 then 38 else 38))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 43 else 73) else (if i.val < 75 then 73 else 73)) else (if i.val < 78 then (if i.val < 77 then 73 else 41) else (if i.val < 79 then 73 else 73)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 73 else 72) else (if i.val < 83 then 21 else 71)) else (if i.val < 86 then (if i.val < 85 then 20 else 38) else (if i.val < 87 then 43 else 72))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 73 else 38) else (if i.val < 91 then 42 else 42)) else (if i.val < 94 then (if i.val < 93 then 68 else 94) else (if i.val < 95 then 20 else 68))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 72 else 38) else (if i.val < 99 then 73 else 74)) else (if i.val < 102 then (if i.val < 101 then 74 else 75) else (if i.val < 103 then 38 else 73))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 71 else 38) else (if i.val < 107 then 18 else 73)) else (if i.val < 110 then (if i.val < 109 then 74 else 21) else (if i.val < 111 then 73 else 22)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 38 else 21) else (if i.val < 115 then 21 else 42)) else (if i.val < 118 then (if i.val < 117 then 73 else 69) else (if i.val < 119 then 70 else 73))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 38 else 73) else (if i.val < 123 then 41 else 38)) else (if i.val < 126 then (if i.val < 125 then 38 else 40) else (if i.val < 127 then 38 else 38))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 71 else 73) else (if i.val < 131 then 77 else 38)) else (if i.val < 134 then (if i.val < 133 then 21 else 94) else (if i.val < 135 then 73 else 43))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 73 else 71) else (if i.val < 139 then 38 else 43)) else (if i.val < 142 then (if i.val < 141 then 74 else 40) else (if i.val < 143 then 73 else 21)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 43 else 43) else (if i.val < 147 then 73 else 21)) else (if i.val < 150 then (if i.val < 149 then 74 else 21) else (if i.val < 151 then 42 else 42))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 38 else 43) else (if i.val < 155 then 38 else 75)) else (if i.val < 158 then (if i.val < 157 then 38 else 38) else (if i.val < 159 then 94 else 73))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 21 else 71) else (if i.val < 163 then 73 else 75)) else (if i.val < 166 then (if i.val < 165 then 75 else 38) else (if i.val < 167 then 73 else 38))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 73 else 79) else (if i.val < 171 then 20 else 21)) else (if i.val < 174 then (if i.val < 173 then 22 else 42) else (if i.val < 175 then 71 else 68)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 38 else 21) else (if i.val < 179 then 73 else 73)) else (if i.val < 182 then (if i.val < 181 then 21 else 73) else (if i.val < 183 then 38 else 71))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 71 else 42) else (if i.val < 187 then 21 else 73)) else (if i.val < 190 then (if i.val < 189 then 74 else 75) else (if i.val < 191 then 75 else 42)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 38 else 72) else (if i.val < 195 then 70 else 38)) else (if i.val < 198 then (if i.val < 197 then 38 else 73) else (if i.val < 199 then 75 else 38))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 73 else 72) else (if i.val < 203 then 43 else 72)) else (if i.val < 206 then (if i.val < 205 then 41 else 71) else (if i.val < 207 then 73 else 71)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 73 else 43) else (if i.val < 211 then 38 else 74)) else (if i.val < 214 then (if i.val < 213 then 73 else 73) else (if i.val < 215 then 73 else 38))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 73 else 38) else (if i.val < 219 then 76 else 94)) else (if i.val < 222 then (if i.val < 221 then 73 else 43) else (if i.val < 223 then 42 else 71))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 21 else 21) else (if i.val < 227 then 75 else 71)) else (if i.val < 230 then (if i.val < 229 then 69 else 73) else (if i.val < 231 then 71 else 42))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 71 else 43) else (if i.val < 235 then 43 else 21)) else (if i.val < 238 then (if i.val < 237 then 73 else 20) else (if i.val < 239 then 71 else 42)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 42 else 38) else (if i.val < 243 then 41 else 21)) else (if i.val < 246 then (if i.val < 245 then 94 else 42) else (if i.val < 247 then 41 else 38))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 73 else 71) else (if i.val < 251 then 43 else 21)) else (if i.val < 254 then (if i.val < 253 then 74 else 94) else (if i.val < 255 then 71 else 71))))))))

theorem g32p_supplierForest_actual_109 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_109 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_109 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_137385
  · exact g32p_supplierForest_actual_137401
  · exact g32p_supplierForest_actual_137419
  · exact g32p_supplierForest_actual_137433
  · exact g32p_supplierForest_actual_137477
  · exact g32p_supplierForest_actual_137563
  · exact g32p_supplierForest_actual_137623
  · exact g32p_supplierForest_actual_137639
  · exact g32p_supplierForest_actual_137642
  · exact g32p_supplierForest_actual_137654
  · exact g32p_supplierForest_actual_137703
  · exact g32p_supplierForest_actual_137738
  · exact g32p_supplierForest_actual_137743
  · exact g32p_supplierForest_actual_137792
  · exact g32p_supplierForest_actual_137803
  · exact g32p_supplierForest_actual_137855
  · exact g32p_supplierForest_actual_137908
  · exact g32p_supplierForest_actual_137938
  · exact g32p_supplierForest_actual_137944
  · exact g32p_supplierForest_actual_137953
  · exact g32p_supplierForest_actual_137988
  · exact g32p_supplierForest_actual_138058
  · exact g32p_supplierForest_actual_138090
  · exact g32p_supplierForest_actual_138093
  · exact g32p_supplierForest_actual_138103
  · exact g32p_supplierForest_actual_138121
  · exact g32p_supplierForest_actual_138132
  · exact g32p_supplierForest_actual_138140
  · exact g32p_supplierForest_actual_138150
  · exact g32p_supplierForest_actual_138165
  · exact g32p_supplierForest_actual_138172
  · exact g32p_supplierForest_actual_138199
  · exact g32p_supplierForest_actual_138211
  · exact g32p_supplierForest_actual_138273
  · exact g32p_supplierForest_actual_138288
  · exact g32p_supplierForest_actual_138310
  · exact g32p_supplierForest_actual_138316
  · exact g32p_supplierForest_actual_138330
  · exact g32p_supplierForest_actual_138339
  · exact g32p_supplierForest_actual_138370
  · exact g32p_supplierForest_actual_138380
  · exact g32p_supplierForest_actual_138395
  · exact g32p_supplierForest_actual_138418
  · exact g32p_supplierForest_actual_138494
  · exact g32p_supplierForest_actual_138512
  · exact g32p_supplierForest_actual_138602
  · exact g32p_supplierForest_actual_138623
  · exact g32p_supplierForest_actual_138625
  · exact g32p_supplierForest_actual_138680
  · exact g32p_supplierForest_actual_138686
  · exact g32p_supplierForest_actual_138697
  · exact g32p_supplierForest_actual_138720
  · exact g32p_supplierForest_actual_138731
  · exact g32p_supplierForest_actual_138737
  · exact g32p_supplierForest_actual_138740
  · exact g32p_supplierForest_actual_138759
  · exact g32p_supplierForest_actual_138805
  · exact g32p_supplierForest_actual_138818
  · exact g32p_supplierForest_actual_138835
  · exact g32p_supplierForest_actual_138881
  · exact g32p_supplierForest_actual_138919
  · exact g32p_supplierForest_actual_138956
  · exact g32p_supplierForest_actual_138960
  · exact g32p_supplierForest_actual_138985
  · exact g32p_supplierForest_actual_139037
  · exact g32p_supplierForest_actual_139043
  · exact g32p_supplierForest_actual_139050
  · exact g32p_supplierForest_actual_139100
  · exact g32p_supplierForest_actual_139113
  · exact g32p_supplierForest_actual_139115
  · exact g32p_supplierForest_actual_139131
  · exact g32p_supplierForest_actual_139154
  · exact g32p_supplierForest_actual_139185
  · exact g32p_supplierForest_actual_139226
  · exact g32p_supplierForest_actual_139277
  · exact g32p_supplierForest_actual_139279
  · exact g32p_supplierForest_actual_139306
  · exact g32p_supplierForest_actual_139314
  · exact g32p_supplierForest_actual_139366
  · exact g32p_supplierForest_actual_139398
  · exact g32p_supplierForest_actual_139416
  · exact g32p_supplierForest_actual_139428
  · exact g32p_supplierForest_actual_139508
  · exact g32p_supplierForest_actual_139511
  · exact g32p_supplierForest_actual_139514
  · exact g32p_supplierForest_actual_139553
  · exact g32p_supplierForest_actual_139565
  · exact g32p_supplierForest_actual_139572
  · exact g32p_supplierForest_actual_139591
  · exact g32p_supplierForest_actual_139594
  · exact g32p_supplierForest_actual_139619
  · exact g32p_supplierForest_actual_139630
  · exact g32p_supplierForest_actual_139657
  · exact g32p_supplierForest_actual_139674
  · exact g32p_supplierForest_actual_139681
  · exact g32p_supplierForest_actual_139684
  · exact g32p_supplierForest_actual_139723
  · exact g32p_supplierForest_actual_139748
  · exact g32p_supplierForest_actual_139750
  · exact g32p_supplierForest_actual_139799
  · exact g32p_supplierForest_actual_139802
  · exact g32p_supplierForest_actual_139814
  · exact g32p_supplierForest_actual_139852
  · exact g32p_supplierForest_actual_139922
  · exact g32p_supplierForest_actual_139931
  · exact g32p_supplierForest_actual_140001
  · exact g32p_supplierForest_actual_140002
  · exact g32p_supplierForest_actual_140047
  · exact g32p_supplierForest_actual_140091
  · exact g32p_supplierForest_actual_140098
  · exact g32p_supplierForest_actual_140103
  · exact g32p_supplierForest_actual_140146
  · exact g32p_supplierForest_actual_140150
  · exact g32p_supplierForest_actual_140227
  · exact g32p_supplierForest_actual_140234
  · exact g32p_supplierForest_actual_140239
  · exact g32p_supplierForest_actual_140312
  · exact g32p_supplierForest_actual_140352
  · exact g32p_supplierForest_actual_140361
  · exact g32p_supplierForest_actual_140372
  · exact g32p_supplierForest_actual_140393
  · exact g32p_supplierForest_actual_140422
  · exact g32p_supplierForest_actual_140424
  · exact g32p_supplierForest_actual_140453
  · exact g32p_supplierForest_actual_140500
  · exact g32p_supplierForest_actual_140513
  · exact g32p_supplierForest_actual_140531
  · exact g32p_supplierForest_actual_140540
  · exact g32p_supplierForest_actual_140545
  · exact g32p_supplierForest_actual_140596
  · exact g32p_supplierForest_actual_140605
  · exact g32p_supplierForest_actual_140607
  · exact g32p_supplierForest_actual_140652
  · exact g32p_supplierForest_actual_140693
  · exact g32p_supplierForest_actual_140698
  · exact g32p_supplierForest_actual_140713
  · exact g32p_supplierForest_actual_140723
  · exact g32p_supplierForest_actual_140728
  · exact g32p_supplierForest_actual_140765
  · exact g32p_supplierForest_actual_140773
  · exact g32p_supplierForest_actual_140813
  · exact g32p_supplierForest_actual_140827
  · exact g32p_supplierForest_actual_140908
  · exact g32p_supplierForest_actual_140963
  · exact g32p_supplierForest_actual_141008
  · exact g32p_supplierForest_actual_141047
  · exact g32p_supplierForest_actual_141052
  · exact g32p_supplierForest_actual_141053
  · exact g32p_supplierForest_actual_141060
  · exact g32p_supplierForest_actual_141124
  · exact g32p_supplierForest_actual_141134
  · exact g32p_supplierForest_actual_141169
  · exact g32p_supplierForest_actual_141197
  · exact g32p_supplierForest_actual_141265
  · exact g32p_supplierForest_actual_141292
  · exact g32p_supplierForest_actual_141305
  · exact g32p_supplierForest_actual_141321
  · exact g32p_supplierForest_actual_141333
  · exact g32p_supplierForest_actual_141431
  · exact g32p_supplierForest_actual_141432
  · exact g32p_supplierForest_actual_141455
  · exact g32p_supplierForest_actual_141470
  · exact g32p_supplierForest_actual_141512
  · exact g32p_supplierForest_actual_141516
  · exact g32p_supplierForest_actual_141525
  · exact g32p_supplierForest_actual_141555
  · exact g32p_supplierForest_actual_141573
  · exact g32p_supplierForest_actual_141577
  · exact g32p_supplierForest_actual_141589
  · exact g32p_supplierForest_actual_141688
  · exact g32p_supplierForest_actual_141748
  · exact g32p_supplierForest_actual_141758
  · exact g32p_supplierForest_actual_141796
  · exact g32p_supplierForest_actual_141813
  · exact g32p_supplierForest_actual_141838
  · exact g32p_supplierForest_actual_141847
  · exact g32p_supplierForest_actual_141853
  · exact g32p_supplierForest_actual_141909
  · exact g32p_supplierForest_actual_141932
  · exact g32p_supplierForest_actual_141961
  · exact g32p_supplierForest_actual_141978
  · exact g32p_supplierForest_actual_142036
  · exact g32p_supplierForest_actual_142062
  · exact g32p_supplierForest_actual_142070
  · exact g32p_supplierForest_actual_142074
  · exact g32p_supplierForest_actual_142079
  · exact g32p_supplierForest_actual_142132
  · exact g32p_supplierForest_actual_142160
  · exact g32p_supplierForest_actual_142213
  · exact g32p_supplierForest_actual_142226
  · exact g32p_supplierForest_actual_142234
  · exact g32p_supplierForest_actual_142256
  · exact g32p_supplierForest_actual_142293
  · exact g32p_supplierForest_actual_142352
  · exact g32p_supplierForest_actual_142380
  · exact g32p_supplierForest_actual_142414
  · exact g32p_supplierForest_actual_142418
  · exact g32p_supplierForest_actual_142463
  · exact g32p_supplierForest_actual_142464
  · exact g32p_supplierForest_actual_142466
  · exact g32p_supplierForest_actual_142515
  · exact g32p_supplierForest_actual_142553
  · exact g32p_supplierForest_actual_142580
  · exact g32p_supplierForest_actual_142589
  · exact g32p_supplierForest_actual_142594
  · exact g32p_supplierForest_actual_142634
  · exact g32p_supplierForest_actual_142687
  · exact g32p_supplierForest_actual_142712
  · exact g32p_supplierForest_actual_142813
  · exact g32p_supplierForest_actual_142819
  · exact g32p_supplierForest_actual_142834
  · exact g32p_supplierForest_actual_142841
  · exact g32p_supplierForest_actual_142859
  · exact g32p_supplierForest_actual_142913
  · exact g32p_supplierForest_actual_142942
  · exact g32p_supplierForest_actual_142976
  · exact g32p_supplierForest_actual_142979
  · exact g32p_supplierForest_actual_143001
  · exact g32p_supplierForest_actual_143002
  · exact g32p_supplierForest_actual_143029
  · exact g32p_supplierForest_actual_143051
  · exact g32p_supplierForest_actual_143060
  · exact g32p_supplierForest_actual_143101
  · exact g32p_supplierForest_actual_143107
  · exact g32p_supplierForest_actual_143195
  · exact g32p_supplierForest_actual_143241
  · exact g32p_supplierForest_actual_143314
  · exact g32p_supplierForest_actual_143330
  · exact g32p_supplierForest_actual_143342
  · exact g32p_supplierForest_actual_143376
  · exact g32p_supplierForest_actual_143418
  · exact g32p_supplierForest_actual_143444
  · exact g32p_supplierForest_actual_143449
  · exact g32p_supplierForest_actual_143478
  · exact g32p_supplierForest_actual_143527
  · exact g32p_supplierForest_actual_143539
  · exact g32p_supplierForest_actual_143546
  · exact g32p_supplierForest_actual_143597
  · exact g32p_supplierForest_actual_143621
  · exact g32p_supplierForest_actual_143649
  · exact g32p_supplierForest_actual_143655
  · exact g32p_supplierForest_actual_143682
  · exact g32p_supplierForest_actual_143713
  · exact g32p_supplierForest_actual_143728
  · exact g32p_supplierForest_actual_143736
  · exact g32p_supplierForest_actual_143750
  · exact g32p_supplierForest_actual_143798
  · exact g32p_supplierForest_actual_143860
  · exact g32p_supplierForest_actual_143876
  · exact g32p_supplierForest_actual_143899
  · exact g32p_supplierForest_actual_143915
  · exact g32p_supplierForest_actual_143936
  · exact g32p_supplierForest_actual_143952
  · exact g32p_supplierForest_actual_143963
  · exact g32p_supplierForest_actual_144024
  · exact g32p_supplierForest_actual_144036

def g32p_supplierForest_nodes_110 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_144096 else g32p_supplierForest_node_144123) else (if i.val < 3 then g32p_supplierForest_node_144134 else g32p_supplierForest_node_144143)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_144156 else g32p_supplierForest_node_144174) else (if i.val < 7 then g32p_supplierForest_node_144183 else g32p_supplierForest_node_144189))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_144213 else g32p_supplierForest_node_144256) else (if i.val < 11 then g32p_supplierForest_node_144265 else g32p_supplierForest_node_144282)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_144291 else g32p_supplierForest_node_144292) else (if i.val < 15 then g32p_supplierForest_node_144298 else g32p_supplierForest_node_144309)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_144342 else g32p_supplierForest_node_144347) else (if i.val < 19 then g32p_supplierForest_node_144426 else g32p_supplierForest_node_144441)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_144449 else g32p_supplierForest_node_144466) else (if i.val < 23 then g32p_supplierForest_node_144473 else g32p_supplierForest_node_144478))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_144499 else g32p_supplierForest_node_144518) else (if i.val < 27 then g32p_supplierForest_node_144521 else g32p_supplierForest_node_144567)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_144610 else g32p_supplierForest_node_144656) else (if i.val < 31 then g32p_supplierForest_node_144672 else g32p_supplierForest_node_144685))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_144687 else g32p_supplierForest_node_144737) else (if i.val < 35 then g32p_supplierForest_node_144738 else g32p_supplierForest_node_144741)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_144755 else g32p_supplierForest_node_144793) else (if i.val < 39 then g32p_supplierForest_node_144802 else g32p_supplierForest_node_144810))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_144842 else g32p_supplierForest_node_144852) else (if i.val < 43 then g32p_supplierForest_node_144923 else g32p_supplierForest_node_144961)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_144977 else g32p_supplierForest_node_144982) else (if i.val < 47 then g32p_supplierForest_node_145090 else g32p_supplierForest_node_145093)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_145137 else g32p_supplierForest_node_145139) else (if i.val < 51 then g32p_supplierForest_node_145145 else g32p_supplierForest_node_145156)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_145169 else g32p_supplierForest_node_145197) else (if i.val < 55 then g32p_supplierForest_node_145202 else g32p_supplierForest_node_145204))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_145238 else g32p_supplierForest_node_145240) else (if i.val < 59 then g32p_supplierForest_node_145269 else g32p_supplierForest_node_145291)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_145298 else g32p_supplierForest_node_145299) else (if i.val < 63 then g32p_supplierForest_node_145310 else g32p_supplierForest_node_145320)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_145322 else g32p_supplierForest_node_145324) else (if i.val < 67 then g32p_supplierForest_node_145383 else g32p_supplierForest_node_145398)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_145403 else g32p_supplierForest_node_145436) else (if i.val < 71 then g32p_supplierForest_node_145470 else g32p_supplierForest_node_145475))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_145480 else g32p_supplierForest_node_145496) else (if i.val < 75 then g32p_supplierForest_node_145503 else g32p_supplierForest_node_145523)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_145599 else g32p_supplierForest_node_145602) else (if i.val < 79 then g32p_supplierForest_node_145603 else g32p_supplierForest_node_145665)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_145674 else g32p_supplierForest_node_145679) else (if i.val < 83 then g32p_supplierForest_node_145714 else g32p_supplierForest_node_145727)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_145744 else g32p_supplierForest_node_145782) else (if i.val < 87 then g32p_supplierForest_node_145793 else g32p_supplierForest_node_145845))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_145852 else g32p_supplierForest_node_145879) else (if i.val < 91 then g32p_supplierForest_node_145890 else g32p_supplierForest_node_145905)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_145959 else g32p_supplierForest_node_145975) else (if i.val < 95 then g32p_supplierForest_node_146041 else g32p_supplierForest_node_146042))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_146069 else g32p_supplierForest_node_146072) else (if i.val < 99 then g32p_supplierForest_node_146074 else g32p_supplierForest_node_146113)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_146123 else g32p_supplierForest_node_146153) else (if i.val < 103 then g32p_supplierForest_node_146157 else g32p_supplierForest_node_146187))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_146193 else g32p_supplierForest_node_146289) else (if i.val < 107 then g32p_supplierForest_node_146290 else g32p_supplierForest_node_146296)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_146304 else g32p_supplierForest_node_146316) else (if i.val < 111 then g32p_supplierForest_node_146334 else g32p_supplierForest_node_146337)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_146370 else g32p_supplierForest_node_146400) else (if i.val < 115 then g32p_supplierForest_node_146439 else g32p_supplierForest_node_146442)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_146451 else g32p_supplierForest_node_146477) else (if i.val < 119 then g32p_supplierForest_node_146484 else g32p_supplierForest_node_146502))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_146507 else g32p_supplierForest_node_146515) else (if i.val < 123 then g32p_supplierForest_node_146534 else g32p_supplierForest_node_146583)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_146591 else g32p_supplierForest_node_146619) else (if i.val < 127 then g32p_supplierForest_node_146634 else g32p_supplierForest_node_146637))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_146688 else g32p_supplierForest_node_146698) else (if i.val < 131 then g32p_supplierForest_node_146703 else g32p_supplierForest_node_146714)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_146775 else g32p_supplierForest_node_146778) else (if i.val < 135 then g32p_supplierForest_node_146789 else g32p_supplierForest_node_146798))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_146839 else g32p_supplierForest_node_146845) else (if i.val < 139 then g32p_supplierForest_node_146848 else g32p_supplierForest_node_146852)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_146855 else g32p_supplierForest_node_146894) else (if i.val < 143 then g32p_supplierForest_node_146910 else g32p_supplierForest_node_146911)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_146951 else g32p_supplierForest_node_147006) else (if i.val < 147 then g32p_supplierForest_node_147029 else g32p_supplierForest_node_147069)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_147071 else g32p_supplierForest_node_147165) else (if i.val < 151 then g32p_supplierForest_node_147172 else g32p_supplierForest_node_147193))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_147227 else g32p_supplierForest_node_147294) else (if i.val < 155 then g32p_supplierForest_node_147312 else g32p_supplierForest_node_147327)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_147393 else g32p_supplierForest_node_147433) else (if i.val < 159 then g32p_supplierForest_node_147445 else g32p_supplierForest_node_147473))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_147482 else g32p_supplierForest_node_147497) else (if i.val < 163 then g32p_supplierForest_node_147503 else g32p_supplierForest_node_147506)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_147525 else g32p_supplierForest_node_147556) else (if i.val < 167 then g32p_supplierForest_node_147566 else g32p_supplierForest_node_147592))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_147593 else g32p_supplierForest_node_147605) else (if i.val < 171 then g32p_supplierForest_node_147625 else g32p_supplierForest_node_147666)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_147668 else g32p_supplierForest_node_147669) else (if i.val < 175 then g32p_supplierForest_node_147684 else g32p_supplierForest_node_147693)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_147715 else g32p_supplierForest_node_147727) else (if i.val < 179 then g32p_supplierForest_node_147820 else g32p_supplierForest_node_147828)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_147855 else g32p_supplierForest_node_147860) else (if i.val < 183 then g32p_supplierForest_node_147910 else g32p_supplierForest_node_147932))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_147941 else g32p_supplierForest_node_147953) else (if i.val < 187 then g32p_supplierForest_node_147981 else g32p_supplierForest_node_148050)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_148054 else g32p_supplierForest_node_148072) else (if i.val < 191 then g32p_supplierForest_node_148080 else g32p_supplierForest_node_148139)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_148166 else g32p_supplierForest_node_148190) else (if i.val < 195 then g32p_supplierForest_node_148235 else g32p_supplierForest_node_148243)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_148276 else g32p_supplierForest_node_148283) else (if i.val < 199 then g32p_supplierForest_node_148285 else g32p_supplierForest_node_148291))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_148300 else g32p_supplierForest_node_148303) else (if i.val < 203 then g32p_supplierForest_node_148320 else g32p_supplierForest_node_148324)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_148339 else g32p_supplierForest_node_148341) else (if i.val < 207 then g32p_supplierForest_node_148363 else g32p_supplierForest_node_148390)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_148423 else g32p_supplierForest_node_148457) else (if i.val < 211 then g32p_supplierForest_node_148508 else g32p_supplierForest_node_148564)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_148568 else g32p_supplierForest_node_148580) else (if i.val < 215 then g32p_supplierForest_node_148591 else g32p_supplierForest_node_148596))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_148607 else g32p_supplierForest_node_148635) else (if i.val < 219 then g32p_supplierForest_node_148638 else g32p_supplierForest_node_148652)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_148670 else g32p_supplierForest_node_148675) else (if i.val < 223 then g32p_supplierForest_node_148717 else g32p_supplierForest_node_148724))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_148726 else g32p_supplierForest_node_148732) else (if i.val < 227 then g32p_supplierForest_node_148749 else g32p_supplierForest_node_148757)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_148769 else g32p_supplierForest_node_148771) else (if i.val < 231 then g32p_supplierForest_node_148814 else g32p_supplierForest_node_148860))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_149031 else g32p_supplierForest_node_149036) else (if i.val < 235 then g32p_supplierForest_node_149050 else g32p_supplierForest_node_149068)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_149096 else g32p_supplierForest_node_149100) else (if i.val < 239 then g32p_supplierForest_node_149101 else g32p_supplierForest_node_149105)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_149169 else g32p_supplierForest_node_149192) else (if i.val < 243 then g32p_supplierForest_node_149225 else g32p_supplierForest_node_149227)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_149229 else g32p_supplierForest_node_149256) else (if i.val < 247 then g32p_supplierForest_node_149326 else g32p_supplierForest_node_149327))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_149331 else g32p_supplierForest_node_149338) else (if i.val < 251 then g32p_supplierForest_node_149382 else g32p_supplierForest_node_149511)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_149515 else g32p_supplierForest_node_149519) else (if i.val < 255 then g32p_supplierForest_node_149523 else g32p_supplierForest_node_149528))))))))

def g32p_supplierForest_classes_110 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 42 else 74) else (if i.val < 3 then 21 else 73)) else (if i.val < 6 then (if i.val < 5 then 77 else 42) else (if i.val < 7 then 74 else 75))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 42 else 94) else (if i.val < 11 then 71 else 94)) else (if i.val < 14 then (if i.val < 13 then 38 else 71) else (if i.val < 15 then 42 else 73)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 72 else 71) else (if i.val < 19 then 42 else 73)) else (if i.val < 22 then (if i.val < 21 then 42 else 94) else (if i.val < 23 then 75 else 72))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 72 else 71) else (if i.val < 27 then 71 else 94)) else (if i.val < 30 then (if i.val < 29 then 94 else 53) else (if i.val < 31 then 86 else 53))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 46 else 80) else (if i.val < 35 then 25 else 55)) else (if i.val < 38 then (if i.val < 37 then 86 else 86) else (if i.val < 39 then 26 else 9))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 47 else 46) else (if i.val < 43 then 47 else 46)) else (if i.val < 46 then (if i.val < 45 then 46 else 46) else (if i.val < 47 then 55 else 47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 49 else 49) else (if i.val < 51 then 46 else 46)) else (if i.val < 54 then (if i.val < 53 then 49 else 46) else (if i.val < 55 then 50 else 49))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 47 else 46) else (if i.val < 59 then 53 else 49)) else (if i.val < 62 then (if i.val < 61 then 80 else 86) else (if i.val < 63 then 26 else 54)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 54) else (if i.val < 67 then 46 else 86)) else (if i.val < 70 then (if i.val < 69 then 47 else 83) else (if i.val < 71 then 53 else 86))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 51 else 49) else (if i.val < 75 then 49 else 47)) else (if i.val < 78 then (if i.val < 77 then 13 else 86) else (if i.val < 79 then 55 else 46)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 26 else 49) else (if i.val < 83 then 26 else 49)) else (if i.val < 86 then (if i.val < 85 then 47 else 54) else (if i.val < 87 then 80 else 46))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 80 else 86) else (if i.val < 91 then 86 else 50)) else (if i.val < 94 then (if i.val < 93 then 86 else 49) else (if i.val < 95 then 55 else 46))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 53 else 12) else (if i.val < 99 then 47 else 47)) else (if i.val < 102 then (if i.val < 101 then 49 else 49) else (if i.val < 103 then 26 else 49))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 54 else 49) else (if i.val < 107 then 86 else 55)) else (if i.val < 110 then (if i.val < 109 then 46 else 49) else (if i.val < 111 then 84 else 49)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 26 else 84) else (if i.val < 115 then 46 else 86)) else (if i.val < 118 then (if i.val < 117 then 49 else 86) else (if i.val < 119 then 49 else 25))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 49 else 55) else (if i.val < 123 then 54 else 47)) else (if i.val < 126 then (if i.val < 125 then 50 else 46) else (if i.val < 127 then 53 else 53))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 54 else 49) else (if i.val < 131 then 50 else 84)) else (if i.val < 134 then (if i.val < 133 then 86 else 46) else (if i.val < 135 then 47 else 46))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 83 else 46) else (if i.val < 139 then 26 else 86)) else (if i.val < 142 then (if i.val < 141 then 46 else 46) else (if i.val < 143 then 11 else 54)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 49 else 54) else (if i.val < 147 then 54 else 47)) else (if i.val < 150 then (if i.val < 149 then 46 else 53) else (if i.val < 151 then 49 else 86))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 47 else 46) else (if i.val < 155 then 84 else 83)) else (if i.val < 158 then (if i.val < 157 then 53 else 47) else (if i.val < 159 then 50 else 47))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 49 else 46) else (if i.val < 163 then 49 else 54)) else (if i.val < 166 then (if i.val < 165 then 54 else 11) else (if i.val < 167 then 83 else 46))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 53 else 84) else (if i.val < 171 then 86 else 53)) else (if i.val < 174 then (if i.val < 173 then 86 else 46) else (if i.val < 175 then 47 else 86)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 54 else 55) else (if i.val < 179 then 26 else 54)) else (if i.val < 182 then (if i.val < 181 then 26 else 86) else (if i.val < 183 then 50 else 46))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 49 else 86) else (if i.val < 187 then 46 else 46)) else (if i.val < 190 then (if i.val < 189 then 47 else 86) else (if i.val < 191 then 49 else 47)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 49 else 55) else (if i.val < 195 then 46 else 86)) else (if i.val < 198 then (if i.val < 197 then 46 else 45) else (if i.val < 199 then 49 else 81))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 46 else 50) else (if i.val < 203 then 53 else 55)) else (if i.val < 206 then (if i.val < 205 then 81 else 49) else (if i.val < 207 then 86 else 49)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 53 else 26) else (if i.val < 211 then 49 else 54)) else (if i.val < 214 then (if i.val < 213 then 86 else 80) else (if i.val < 215 then 47 else 53))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 46 else 86) else (if i.val < 219 then 86 else 47)) else (if i.val < 222 then (if i.val < 221 then 55 else 47) else (if i.val < 223 then 86 else 45))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 54 else 49) else (if i.val < 227 then 49 else 49)) else (if i.val < 230 then (if i.val < 229 then 25 else 54) else (if i.val < 231 then 55 else 86))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 86 else 86) else (if i.val < 235 then 53 else 86)) else (if i.val < 238 then (if i.val < 237 then 13 else 86) else (if i.val < 239 then 86 else 46)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 11 else 26) else (if i.val < 243 then 53 else 47)) else (if i.val < 246 then (if i.val < 245 then 49 else 25) else (if i.val < 247 then 27 else 86))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 53 else 13) else (if i.val < 251 then 54 else 46)) else (if i.val < 254 then (if i.val < 253 then 26 else 26) else (if i.val < 255 then 84 else 54))))))))

theorem g32p_supplierForest_actual_110 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_110 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_110 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_144096
  · exact g32p_supplierForest_actual_144123
  · exact g32p_supplierForest_actual_144134
  · exact g32p_supplierForest_actual_144143
  · exact g32p_supplierForest_actual_144156
  · exact g32p_supplierForest_actual_144174
  · exact g32p_supplierForest_actual_144183
  · exact g32p_supplierForest_actual_144189
  · exact g32p_supplierForest_actual_144213
  · exact g32p_supplierForest_actual_144256
  · exact g32p_supplierForest_actual_144265
  · exact g32p_supplierForest_actual_144282
  · exact g32p_supplierForest_actual_144291
  · exact g32p_supplierForest_actual_144292
  · exact g32p_supplierForest_actual_144298
  · exact g32p_supplierForest_actual_144309
  · exact g32p_supplierForest_actual_144342
  · exact g32p_supplierForest_actual_144347
  · exact g32p_supplierForest_actual_144426
  · exact g32p_supplierForest_actual_144441
  · exact g32p_supplierForest_actual_144449
  · exact g32p_supplierForest_actual_144466
  · exact g32p_supplierForest_actual_144473
  · exact g32p_supplierForest_actual_144478
  · exact g32p_supplierForest_actual_144499
  · exact g32p_supplierForest_actual_144518
  · exact g32p_supplierForest_actual_144521
  · exact g32p_supplierForest_actual_144567
  · exact g32p_supplierForest_actual_144610
  · exact g32p_supplierForest_actual_144656
  · exact g32p_supplierForest_actual_144672
  · exact g32p_supplierForest_actual_144685
  · exact g32p_supplierForest_actual_144687
  · exact g32p_supplierForest_actual_144737
  · exact g32p_supplierForest_actual_144738
  · exact g32p_supplierForest_actual_144741
  · exact g32p_supplierForest_actual_144755
  · exact g32p_supplierForest_actual_144793
  · exact g32p_supplierForest_actual_144802
  · exact g32p_supplierForest_actual_144810
  · exact g32p_supplierForest_actual_144842
  · exact g32p_supplierForest_actual_144852
  · exact g32p_supplierForest_actual_144923
  · exact g32p_supplierForest_actual_144961
  · exact g32p_supplierForest_actual_144977
  · exact g32p_supplierForest_actual_144982
  · exact g32p_supplierForest_actual_145090
  · exact g32p_supplierForest_actual_145093
  · exact g32p_supplierForest_actual_145137
  · exact g32p_supplierForest_actual_145139
  · exact g32p_supplierForest_actual_145145
  · exact g32p_supplierForest_actual_145156
  · exact g32p_supplierForest_actual_145169
  · exact g32p_supplierForest_actual_145197
  · exact g32p_supplierForest_actual_145202
  · exact g32p_supplierForest_actual_145204
  · exact g32p_supplierForest_actual_145238
  · exact g32p_supplierForest_actual_145240
  · exact g32p_supplierForest_actual_145269
  · exact g32p_supplierForest_actual_145291
  · exact g32p_supplierForest_actual_145298
  · exact g32p_supplierForest_actual_145299
  · exact g32p_supplierForest_actual_145310
  · exact g32p_supplierForest_actual_145320
  · exact g32p_supplierForest_actual_145322
  · exact g32p_supplierForest_actual_145324
  · exact g32p_supplierForest_actual_145383
  · exact g32p_supplierForest_actual_145398
  · exact g32p_supplierForest_actual_145403
  · exact g32p_supplierForest_actual_145436
  · exact g32p_supplierForest_actual_145470
  · exact g32p_supplierForest_actual_145475
  · exact g32p_supplierForest_actual_145480
  · exact g32p_supplierForest_actual_145496
  · exact g32p_supplierForest_actual_145503
  · exact g32p_supplierForest_actual_145523
  · exact g32p_supplierForest_actual_145599
  · exact g32p_supplierForest_actual_145602
  · exact g32p_supplierForest_actual_145603
  · exact g32p_supplierForest_actual_145665
  · exact g32p_supplierForest_actual_145674
  · exact g32p_supplierForest_actual_145679
  · exact g32p_supplierForest_actual_145714
  · exact g32p_supplierForest_actual_145727
  · exact g32p_supplierForest_actual_145744
  · exact g32p_supplierForest_actual_145782
  · exact g32p_supplierForest_actual_145793
  · exact g32p_supplierForest_actual_145845
  · exact g32p_supplierForest_actual_145852
  · exact g32p_supplierForest_actual_145879
  · exact g32p_supplierForest_actual_145890
  · exact g32p_supplierForest_actual_145905
  · exact g32p_supplierForest_actual_145959
  · exact g32p_supplierForest_actual_145975
  · exact g32p_supplierForest_actual_146041
  · exact g32p_supplierForest_actual_146042
  · exact g32p_supplierForest_actual_146069
  · exact g32p_supplierForest_actual_146072
  · exact g32p_supplierForest_actual_146074
  · exact g32p_supplierForest_actual_146113
  · exact g32p_supplierForest_actual_146123
  · exact g32p_supplierForest_actual_146153
  · exact g32p_supplierForest_actual_146157
  · exact g32p_supplierForest_actual_146187
  · exact g32p_supplierForest_actual_146193
  · exact g32p_supplierForest_actual_146289
  · exact g32p_supplierForest_actual_146290
  · exact g32p_supplierForest_actual_146296
  · exact g32p_supplierForest_actual_146304
  · exact g32p_supplierForest_actual_146316
  · exact g32p_supplierForest_actual_146334
  · exact g32p_supplierForest_actual_146337
  · exact g32p_supplierForest_actual_146370
  · exact g32p_supplierForest_actual_146400
  · exact g32p_supplierForest_actual_146439
  · exact g32p_supplierForest_actual_146442
  · exact g32p_supplierForest_actual_146451
  · exact g32p_supplierForest_actual_146477
  · exact g32p_supplierForest_actual_146484
  · exact g32p_supplierForest_actual_146502
  · exact g32p_supplierForest_actual_146507
  · exact g32p_supplierForest_actual_146515
  · exact g32p_supplierForest_actual_146534
  · exact g32p_supplierForest_actual_146583
  · exact g32p_supplierForest_actual_146591
  · exact g32p_supplierForest_actual_146619
  · exact g32p_supplierForest_actual_146634
  · exact g32p_supplierForest_actual_146637
  · exact g32p_supplierForest_actual_146688
  · exact g32p_supplierForest_actual_146698
  · exact g32p_supplierForest_actual_146703
  · exact g32p_supplierForest_actual_146714
  · exact g32p_supplierForest_actual_146775
  · exact g32p_supplierForest_actual_146778
  · exact g32p_supplierForest_actual_146789
  · exact g32p_supplierForest_actual_146798
  · exact g32p_supplierForest_actual_146839
  · exact g32p_supplierForest_actual_146845
  · exact g32p_supplierForest_actual_146848
  · exact g32p_supplierForest_actual_146852
  · exact g32p_supplierForest_actual_146855
  · exact g32p_supplierForest_actual_146894
  · exact g32p_supplierForest_actual_146910
  · exact g32p_supplierForest_actual_146911
  · exact g32p_supplierForest_actual_146951
  · exact g32p_supplierForest_actual_147006
  · exact g32p_supplierForest_actual_147029
  · exact g32p_supplierForest_actual_147069
  · exact g32p_supplierForest_actual_147071
  · exact g32p_supplierForest_actual_147165
  · exact g32p_supplierForest_actual_147172
  · exact g32p_supplierForest_actual_147193
  · exact g32p_supplierForest_actual_147227
  · exact g32p_supplierForest_actual_147294
  · exact g32p_supplierForest_actual_147312
  · exact g32p_supplierForest_actual_147327
  · exact g32p_supplierForest_actual_147393
  · exact g32p_supplierForest_actual_147433
  · exact g32p_supplierForest_actual_147445
  · exact g32p_supplierForest_actual_147473
  · exact g32p_supplierForest_actual_147482
  · exact g32p_supplierForest_actual_147497
  · exact g32p_supplierForest_actual_147503
  · exact g32p_supplierForest_actual_147506
  · exact g32p_supplierForest_actual_147525
  · exact g32p_supplierForest_actual_147556
  · exact g32p_supplierForest_actual_147566
  · exact g32p_supplierForest_actual_147592
  · exact g32p_supplierForest_actual_147593
  · exact g32p_supplierForest_actual_147605
  · exact g32p_supplierForest_actual_147625
  · exact g32p_supplierForest_actual_147666
  · exact g32p_supplierForest_actual_147668
  · exact g32p_supplierForest_actual_147669
  · exact g32p_supplierForest_actual_147684
  · exact g32p_supplierForest_actual_147693
  · exact g32p_supplierForest_actual_147715
  · exact g32p_supplierForest_actual_147727
  · exact g32p_supplierForest_actual_147820
  · exact g32p_supplierForest_actual_147828
  · exact g32p_supplierForest_actual_147855
  · exact g32p_supplierForest_actual_147860
  · exact g32p_supplierForest_actual_147910
  · exact g32p_supplierForest_actual_147932
  · exact g32p_supplierForest_actual_147941
  · exact g32p_supplierForest_actual_147953
  · exact g32p_supplierForest_actual_147981
  · exact g32p_supplierForest_actual_148050
  · exact g32p_supplierForest_actual_148054
  · exact g32p_supplierForest_actual_148072
  · exact g32p_supplierForest_actual_148080
  · exact g32p_supplierForest_actual_148139
  · exact g32p_supplierForest_actual_148166
  · exact g32p_supplierForest_actual_148190
  · exact g32p_supplierForest_actual_148235
  · exact g32p_supplierForest_actual_148243
  · exact g32p_supplierForest_actual_148276
  · exact g32p_supplierForest_actual_148283
  · exact g32p_supplierForest_actual_148285
  · exact g32p_supplierForest_actual_148291
  · exact g32p_supplierForest_actual_148300
  · exact g32p_supplierForest_actual_148303
  · exact g32p_supplierForest_actual_148320
  · exact g32p_supplierForest_actual_148324
  · exact g32p_supplierForest_actual_148339
  · exact g32p_supplierForest_actual_148341
  · exact g32p_supplierForest_actual_148363
  · exact g32p_supplierForest_actual_148390
  · exact g32p_supplierForest_actual_148423
  · exact g32p_supplierForest_actual_148457
  · exact g32p_supplierForest_actual_148508
  · exact g32p_supplierForest_actual_148564
  · exact g32p_supplierForest_actual_148568
  · exact g32p_supplierForest_actual_148580
  · exact g32p_supplierForest_actual_148591
  · exact g32p_supplierForest_actual_148596
  · exact g32p_supplierForest_actual_148607
  · exact g32p_supplierForest_actual_148635
  · exact g32p_supplierForest_actual_148638
  · exact g32p_supplierForest_actual_148652
  · exact g32p_supplierForest_actual_148670
  · exact g32p_supplierForest_actual_148675
  · exact g32p_supplierForest_actual_148717
  · exact g32p_supplierForest_actual_148724
  · exact g32p_supplierForest_actual_148726
  · exact g32p_supplierForest_actual_148732
  · exact g32p_supplierForest_actual_148749
  · exact g32p_supplierForest_actual_148757
  · exact g32p_supplierForest_actual_148769
  · exact g32p_supplierForest_actual_148771
  · exact g32p_supplierForest_actual_148814
  · exact g32p_supplierForest_actual_148860
  · exact g32p_supplierForest_actual_149031
  · exact g32p_supplierForest_actual_149036
  · exact g32p_supplierForest_actual_149050
  · exact g32p_supplierForest_actual_149068
  · exact g32p_supplierForest_actual_149096
  · exact g32p_supplierForest_actual_149100
  · exact g32p_supplierForest_actual_149101
  · exact g32p_supplierForest_actual_149105
  · exact g32p_supplierForest_actual_149169
  · exact g32p_supplierForest_actual_149192
  · exact g32p_supplierForest_actual_149225
  · exact g32p_supplierForest_actual_149227
  · exact g32p_supplierForest_actual_149229
  · exact g32p_supplierForest_actual_149256
  · exact g32p_supplierForest_actual_149326
  · exact g32p_supplierForest_actual_149327
  · exact g32p_supplierForest_actual_149331
  · exact g32p_supplierForest_actual_149338
  · exact g32p_supplierForest_actual_149382
  · exact g32p_supplierForest_actual_149511
  · exact g32p_supplierForest_actual_149515
  · exact g32p_supplierForest_actual_149519
  · exact g32p_supplierForest_actual_149523
  · exact g32p_supplierForest_actual_149528

def g32p_supplierForest_nodes_111 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_149536 else g32p_supplierForest_node_149537) else (if i.val < 3 then g32p_supplierForest_node_149560 else g32p_supplierForest_node_149562)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_149611 else g32p_supplierForest_node_149616) else (if i.val < 7 then g32p_supplierForest_node_149617 else g32p_supplierForest_node_149674))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_149689 else g32p_supplierForest_node_149746) else (if i.val < 11 then g32p_supplierForest_node_149793 else g32p_supplierForest_node_149806)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_149859 else g32p_supplierForest_node_149862) else (if i.val < 15 then g32p_supplierForest_node_149924 else g32p_supplierForest_node_149973)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_150022 else g32p_supplierForest_node_150030) else (if i.val < 19 then g32p_supplierForest_node_150037 else g32p_supplierForest_node_150067)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_150074 else g32p_supplierForest_node_150095) else (if i.val < 23 then g32p_supplierForest_node_150118 else g32p_supplierForest_node_150119))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_150157 else g32p_supplierForest_node_150159) else (if i.val < 27 then g32p_supplierForest_node_150165 else g32p_supplierForest_node_150170)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_150186 else g32p_supplierForest_node_150192) else (if i.val < 31 then g32p_supplierForest_node_150202 else g32p_supplierForest_node_150217))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_150223 else g32p_supplierForest_node_150234) else (if i.val < 35 then g32p_supplierForest_node_150283 else g32p_supplierForest_node_150291)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_150337 else g32p_supplierForest_node_150359) else (if i.val < 39 then g32p_supplierForest_node_150364 else g32p_supplierForest_node_150365))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_150437 else g32p_supplierForest_node_150452) else (if i.val < 43 then g32p_supplierForest_node_150484 else g32p_supplierForest_node_150485)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_150498 else g32p_supplierForest_node_150504) else (if i.val < 47 then g32p_supplierForest_node_150526 else g32p_supplierForest_node_150547)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_150569 else g32p_supplierForest_node_150579) else (if i.val < 51 then g32p_supplierForest_node_150581 else g32p_supplierForest_node_150599)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_150604 else g32p_supplierForest_node_150612) else (if i.val < 55 then g32p_supplierForest_node_150630 else g32p_supplierForest_node_150642))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_150663 else g32p_supplierForest_node_150669) else (if i.val < 59 then g32p_supplierForest_node_150709 else g32p_supplierForest_node_150739)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_150751 else g32p_supplierForest_node_150754) else (if i.val < 63 then g32p_supplierForest_node_150815 else g32p_supplierForest_node_150818)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_150826 else g32p_supplierForest_node_150894) else (if i.val < 67 then g32p_supplierForest_node_150895 else g32p_supplierForest_node_150979)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_150994 else g32p_supplierForest_node_150996) else (if i.val < 71 then g32p_supplierForest_node_151007 else g32p_supplierForest_node_151031))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_151062 else g32p_supplierForest_node_151065) else (if i.val < 75 then g32p_supplierForest_node_151072 else g32p_supplierForest_node_151098)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_151125 else g32p_supplierForest_node_151143) else (if i.val < 79 then g32p_supplierForest_node_151163 else g32p_supplierForest_node_151166)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_151169 else g32p_supplierForest_node_151174) else (if i.val < 83 then g32p_supplierForest_node_151217 else g32p_supplierForest_node_151218)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_151326 else g32p_supplierForest_node_151336) else (if i.val < 87 then g32p_supplierForest_node_151347 else g32p_supplierForest_node_151354))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_151359 else g32p_supplierForest_node_151368) else (if i.val < 91 then g32p_supplierForest_node_151369 else g32p_supplierForest_node_151432)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_151443 else g32p_supplierForest_node_151470) else (if i.val < 95 then g32p_supplierForest_node_151475 else g32p_supplierForest_node_151511))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_151535 else g32p_supplierForest_node_151548) else (if i.val < 99 then g32p_supplierForest_node_151564 else g32p_supplierForest_node_151566)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_151567 else g32p_supplierForest_node_151601) else (if i.val < 103 then g32p_supplierForest_node_151602 else g32p_supplierForest_node_151632))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_151669 else g32p_supplierForest_node_151673) else (if i.val < 107 then g32p_supplierForest_node_151721 else g32p_supplierForest_node_151782)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_151792 else g32p_supplierForest_node_151820) else (if i.val < 111 then g32p_supplierForest_node_151837 else g32p_supplierForest_node_151848)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_151896 else g32p_supplierForest_node_151905) else (if i.val < 115 then g32p_supplierForest_node_151931 else g32p_supplierForest_node_151955)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_151968 else g32p_supplierForest_node_151977) else (if i.val < 119 then g32p_supplierForest_node_151981 else g32p_supplierForest_node_151989))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_152011 else g32p_supplierForest_node_152081) else (if i.val < 123 then g32p_supplierForest_node_152093 else g32p_supplierForest_node_152106)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_152115 else g32p_supplierForest_node_152144) else (if i.val < 127 then g32p_supplierForest_node_152178 else g32p_supplierForest_node_152205))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_152238 else g32p_supplierForest_node_152286) else (if i.val < 131 then g32p_supplierForest_node_152292 else g32p_supplierForest_node_152299)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_152357 else g32p_supplierForest_node_152382) else (if i.val < 135 then g32p_supplierForest_node_152392 else g32p_supplierForest_node_152405))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_152515 else g32p_supplierForest_node_152517) else (if i.val < 139 then g32p_supplierForest_node_152554 else g32p_supplierForest_node_152586)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_152589 else g32p_supplierForest_node_152600) else (if i.val < 143 then g32p_supplierForest_node_152602 else g32p_supplierForest_node_152662)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_152676 else g32p_supplierForest_node_152718) else (if i.val < 147 then g32p_supplierForest_node_152725 else g32p_supplierForest_node_152765)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_152767 else g32p_supplierForest_node_152769) else (if i.val < 151 then g32p_supplierForest_node_152786 else g32p_supplierForest_node_152803))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_152809 else g32p_supplierForest_node_152823) else (if i.val < 155 then g32p_supplierForest_node_152837 else g32p_supplierForest_node_152847)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_152848 else g32p_supplierForest_node_152850) else (if i.val < 159 then g32p_supplierForest_node_152905 else g32p_supplierForest_node_152928))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_152955 else g32p_supplierForest_node_152956) else (if i.val < 163 then g32p_supplierForest_node_152962 else g32p_supplierForest_node_153016)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_153037 else g32p_supplierForest_node_153073) else (if i.val < 167 then g32p_supplierForest_node_153149 else g32p_supplierForest_node_153174))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_153180 else g32p_supplierForest_node_153220) else (if i.val < 171 then g32p_supplierForest_node_153264 else g32p_supplierForest_node_153329)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_153352 else g32p_supplierForest_node_153353) else (if i.val < 175 then g32p_supplierForest_node_153356 else g32p_supplierForest_node_153390)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_153428 else g32p_supplierForest_node_153468) else (if i.val < 179 then g32p_supplierForest_node_153493 else g32p_supplierForest_node_153513)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_153539 else g32p_supplierForest_node_153549) else (if i.val < 183 then g32p_supplierForest_node_153567 else g32p_supplierForest_node_153577))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_153603 else g32p_supplierForest_node_153620) else (if i.val < 187 then g32p_supplierForest_node_153659 else g32p_supplierForest_node_153751)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_153845 else g32p_supplierForest_node_153853) else (if i.val < 191 then g32p_supplierForest_node_153878 else g32p_supplierForest_node_153916)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_153949 else g32p_supplierForest_node_154002) else (if i.val < 195 then g32p_supplierForest_node_154017 else g32p_supplierForest_node_154051)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_154083 else g32p_supplierForest_node_154085) else (if i.val < 199 then g32p_supplierForest_node_154149 else g32p_supplierForest_node_154159))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_154203 else g32p_supplierForest_node_154217) else (if i.val < 203 then g32p_supplierForest_node_154219 else g32p_supplierForest_node_154281)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_154288 else g32p_supplierForest_node_154318) else (if i.val < 207 then g32p_supplierForest_node_154334 else g32p_supplierForest_node_154394)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_154506 else g32p_supplierForest_node_154511) else (if i.val < 211 then g32p_supplierForest_node_154543 else g32p_supplierForest_node_154550)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_154552 else g32p_supplierForest_node_154591) else (if i.val < 215 then g32p_supplierForest_node_154614 else g32p_supplierForest_node_154618))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_154683 else g32p_supplierForest_node_154694) else (if i.val < 219 then g32p_supplierForest_node_154725 else g32p_supplierForest_node_154764)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_154771 else g32p_supplierForest_node_154796) else (if i.val < 223 then g32p_supplierForest_node_154819 else g32p_supplierForest_node_154869))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_154897 else g32p_supplierForest_node_154905) else (if i.val < 227 then g32p_supplierForest_node_154955 else g32p_supplierForest_node_154968)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_154984 else g32p_supplierForest_node_154985) else (if i.val < 231 then g32p_supplierForest_node_154987 else g32p_supplierForest_node_155009))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_155017 else g32p_supplierForest_node_155033) else (if i.val < 235 then g32p_supplierForest_node_155047 else g32p_supplierForest_node_155125)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_155157 else g32p_supplierForest_node_155165) else (if i.val < 239 then g32p_supplierForest_node_155215 else g32p_supplierForest_node_155217)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_155259 else g32p_supplierForest_node_155288) else (if i.val < 243 then g32p_supplierForest_node_155340 else g32p_supplierForest_node_155362)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_155366 else g32p_supplierForest_node_155373) else (if i.val < 247 then g32p_supplierForest_node_155378 else g32p_supplierForest_node_000253))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_000293 else g32p_supplierForest_node_000385) else (if i.val < 251 then g32p_supplierForest_node_000411 else g32p_supplierForest_node_000460)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_000562 else g32p_supplierForest_node_000565) else (if i.val < 255 then g32p_supplierForest_node_000652 else g32p_supplierForest_node_000754))))))))

def g32p_supplierForest_classes_111 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 26 else 49) else (if i.val < 3 then 50 else 13)) else (if i.val < 6 then (if i.val < 5 then 86 else 26) else (if i.val < 7 then 86 else 55))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 49 else 49) else (if i.val < 11 then 49 else 46)) else (if i.val < 14 then (if i.val < 13 then 46 else 45) else (if i.val < 15 then 46 else 49)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 13 else 52) else (if i.val < 19 then 86 else 47)) else (if i.val < 22 then (if i.val < 21 then 86 else 54) else (if i.val < 23 then 13 else 86))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 86 else 53) else (if i.val < 27 then 86 else 46)) else (if i.val < 30 then (if i.val < 29 then 49 else 50) else (if i.val < 31 then 86 else 13))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 86 else 50) else (if i.val < 35 then 55 else 13)) else (if i.val < 38 then (if i.val < 37 then 55 else 47) else (if i.val < 39 then 25 else 49))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 45 else 49) else (if i.val < 43 then 47 else 47)) else (if i.val < 46 then (if i.val < 45 then 86 else 86) else (if i.val < 47 then 55 else 47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 49 else 86) else (if i.val < 51 then 86 else 46)) else (if i.val < 54 then (if i.val < 53 then 47 else 80) else (if i.val < 55 then 49 else 47))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 55 else 47) else (if i.val < 59 then 86 else 86)) else (if i.val < 62 then (if i.val < 61 then 49 else 86) else (if i.val < 63 then 55 else 13)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 86) else (if i.val < 67 then 26 else 86)) else (if i.val < 70 then (if i.val < 69 then 85 else 49) else (if i.val < 71 then 86 else 49))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 26 else 26) else (if i.val < 75 then 46 else 86)) else (if i.val < 78 then (if i.val < 77 then 84 else 86) else (if i.val < 79 then 47 else 55)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 47 else 55) else (if i.val < 83 then 80 else 86)) else (if i.val < 86 then (if i.val < 85 then 45 else 86) else (if i.val < 87 then 45 else 86))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 13 else 54) else (if i.val < 91 then 13 else 86)) else (if i.val < 94 then (if i.val < 93 then 53 else 86) else (if i.val < 95 then 26 else 86))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 46 else 50) else (if i.val < 99 then 86 else 49)) else (if i.val < 102 then (if i.val < 101 then 53 else 46) else (if i.val < 103 then 49 else 26))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 53 else 47) else (if i.val < 107 then 49 else 81)) else (if i.val < 110 then (if i.val < 109 then 86 else 86) else (if i.val < 111 then 50 else 50)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 86 else 49) else (if i.val < 115 then 86 else 54)) else (if i.val < 118 then (if i.val < 117 then 83 else 46) else (if i.val < 119 then 86 else 86))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 13 else 49) else (if i.val < 123 then 86 else 49)) else (if i.val < 126 then (if i.val < 125 then 86 else 54) else (if i.val < 127 then 55 else 54))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 46 else 86) else (if i.val < 131 then 85 else 26)) else (if i.val < 134 then (if i.val < 133 then 86 else 86) else (if i.val < 135 then 26 else 85))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 89 else 66) else (if i.val < 139 then 60 else 59)) else (if i.val < 142 then (if i.val < 141 then 30 else 60) else (if i.val < 143 then 60 else 89)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 29 else 62) else (if i.val < 147 then 66 else 35)) else (if i.val < 150 then (if i.val < 149 then 60 else 15) else (if i.val < 151 then 29 else 60))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 60 else 61) else (if i.val < 155 then 30 else 62)) else (if i.val < 158 then (if i.val < 157 then 60 else 35) else (if i.val < 159 then 29 else 62))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 65 else 61) else (if i.val < 163 then 62 else 62)) else (if i.val < 166 then (if i.val < 165 then 89 else 90) else (if i.val < 167 then 66 else 58))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 89 else 30) else (if i.val < 171 then 35 else 62)) else (if i.val < 174 then (if i.val < 173 then 35 else 90) else (if i.val < 175 then 35 else 35)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 60 else 35) else (if i.val < 179 then 62 else 90)) else (if i.val < 182 then (if i.val < 181 then 61 else 90) else (if i.val < 183 then 66 else 89))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 90 else 89) else (if i.val < 187 then 92 else 29)) else (if i.val < 190 then (if i.val < 189 then 57 else 57) else (if i.val < 191 then 30 else 30)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 66 else 62) else (if i.val < 195 then 29 else 66)) else (if i.val < 198 then (if i.val < 197 then 60 else 66) else (if i.val < 199 then 90 else 66))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 29 else 35) else (if i.val < 203 then 92 else 57)) else (if i.val < 206 then (if i.val < 205 then 90 else 30) else (if i.val < 207 then 66 else 61)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 90 else 89) else (if i.val < 211 then 62 else 35)) else (if i.val < 214 then (if i.val < 213 then 63 else 61) else (if i.val < 215 then 66 else 90))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 66 else 90) else (if i.val < 219 then 35 else 90)) else (if i.val < 222 then (if i.val < 221 then 89 else 30) else (if i.val < 223 then 66 else 61))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 90 else 90) else (if i.val < 227 then 35 else 62)) else (if i.val < 230 then (if i.val < 229 then 35 else 35) else (if i.val < 231 then 35 else 38))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 42 else 71) else (if i.val < 235 then 21 else 71)) else (if i.val < 238 then (if i.val < 237 then 78 else 94) else (if i.val < 239 then 71 else 94)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 71 else 77) else (if i.val < 243 then 77 else 71)) else (if i.val < 246 then (if i.val < 245 then 78 else 77) else (if i.val < 247 then 71 else 17))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 15 else 16) else (if i.val < 251 then 17 else 21)) else (if i.val < 254 then (if i.val < 253 then 22 else 21) else (if i.val < 255 then 7 else 23))))))))

theorem g32p_supplierForest_actual_111 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_111 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_111 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_149536
  · exact g32p_supplierForest_actual_149537
  · exact g32p_supplierForest_actual_149560
  · exact g32p_supplierForest_actual_149562
  · exact g32p_supplierForest_actual_149611
  · exact g32p_supplierForest_actual_149616
  · exact g32p_supplierForest_actual_149617
  · exact g32p_supplierForest_actual_149674
  · exact g32p_supplierForest_actual_149689
  · exact g32p_supplierForest_actual_149746
  · exact g32p_supplierForest_actual_149793
  · exact g32p_supplierForest_actual_149806
  · exact g32p_supplierForest_actual_149859
  · exact g32p_supplierForest_actual_149862
  · exact g32p_supplierForest_actual_149924
  · exact g32p_supplierForest_actual_149973
  · exact g32p_supplierForest_actual_150022
  · exact g32p_supplierForest_actual_150030
  · exact g32p_supplierForest_actual_150037
  · exact g32p_supplierForest_actual_150067
  · exact g32p_supplierForest_actual_150074
  · exact g32p_supplierForest_actual_150095
  · exact g32p_supplierForest_actual_150118
  · exact g32p_supplierForest_actual_150119
  · exact g32p_supplierForest_actual_150157
  · exact g32p_supplierForest_actual_150159
  · exact g32p_supplierForest_actual_150165
  · exact g32p_supplierForest_actual_150170
  · exact g32p_supplierForest_actual_150186
  · exact g32p_supplierForest_actual_150192
  · exact g32p_supplierForest_actual_150202
  · exact g32p_supplierForest_actual_150217
  · exact g32p_supplierForest_actual_150223
  · exact g32p_supplierForest_actual_150234
  · exact g32p_supplierForest_actual_150283
  · exact g32p_supplierForest_actual_150291
  · exact g32p_supplierForest_actual_150337
  · exact g32p_supplierForest_actual_150359
  · exact g32p_supplierForest_actual_150364
  · exact g32p_supplierForest_actual_150365
  · exact g32p_supplierForest_actual_150437
  · exact g32p_supplierForest_actual_150452
  · exact g32p_supplierForest_actual_150484
  · exact g32p_supplierForest_actual_150485
  · exact g32p_supplierForest_actual_150498
  · exact g32p_supplierForest_actual_150504
  · exact g32p_supplierForest_actual_150526
  · exact g32p_supplierForest_actual_150547
  · exact g32p_supplierForest_actual_150569
  · exact g32p_supplierForest_actual_150579
  · exact g32p_supplierForest_actual_150581
  · exact g32p_supplierForest_actual_150599
  · exact g32p_supplierForest_actual_150604
  · exact g32p_supplierForest_actual_150612
  · exact g32p_supplierForest_actual_150630
  · exact g32p_supplierForest_actual_150642
  · exact g32p_supplierForest_actual_150663
  · exact g32p_supplierForest_actual_150669
  · exact g32p_supplierForest_actual_150709
  · exact g32p_supplierForest_actual_150739
  · exact g32p_supplierForest_actual_150751
  · exact g32p_supplierForest_actual_150754
  · exact g32p_supplierForest_actual_150815
  · exact g32p_supplierForest_actual_150818
  · exact g32p_supplierForest_actual_150826
  · exact g32p_supplierForest_actual_150894
  · exact g32p_supplierForest_actual_150895
  · exact g32p_supplierForest_actual_150979
  · exact g32p_supplierForest_actual_150994
  · exact g32p_supplierForest_actual_150996
  · exact g32p_supplierForest_actual_151007
  · exact g32p_supplierForest_actual_151031
  · exact g32p_supplierForest_actual_151062
  · exact g32p_supplierForest_actual_151065
  · exact g32p_supplierForest_actual_151072
  · exact g32p_supplierForest_actual_151098
  · exact g32p_supplierForest_actual_151125
  · exact g32p_supplierForest_actual_151143
  · exact g32p_supplierForest_actual_151163
  · exact g32p_supplierForest_actual_151166
  · exact g32p_supplierForest_actual_151169
  · exact g32p_supplierForest_actual_151174
  · exact g32p_supplierForest_actual_151217
  · exact g32p_supplierForest_actual_151218
  · exact g32p_supplierForest_actual_151326
  · exact g32p_supplierForest_actual_151336
  · exact g32p_supplierForest_actual_151347
  · exact g32p_supplierForest_actual_151354
  · exact g32p_supplierForest_actual_151359
  · exact g32p_supplierForest_actual_151368
  · exact g32p_supplierForest_actual_151369
  · exact g32p_supplierForest_actual_151432
  · exact g32p_supplierForest_actual_151443
  · exact g32p_supplierForest_actual_151470
  · exact g32p_supplierForest_actual_151475
  · exact g32p_supplierForest_actual_151511
  · exact g32p_supplierForest_actual_151535
  · exact g32p_supplierForest_actual_151548
  · exact g32p_supplierForest_actual_151564
  · exact g32p_supplierForest_actual_151566
  · exact g32p_supplierForest_actual_151567
  · exact g32p_supplierForest_actual_151601
  · exact g32p_supplierForest_actual_151602
  · exact g32p_supplierForest_actual_151632
  · exact g32p_supplierForest_actual_151669
  · exact g32p_supplierForest_actual_151673
  · exact g32p_supplierForest_actual_151721
  · exact g32p_supplierForest_actual_151782
  · exact g32p_supplierForest_actual_151792
  · exact g32p_supplierForest_actual_151820
  · exact g32p_supplierForest_actual_151837
  · exact g32p_supplierForest_actual_151848
  · exact g32p_supplierForest_actual_151896
  · exact g32p_supplierForest_actual_151905
  · exact g32p_supplierForest_actual_151931
  · exact g32p_supplierForest_actual_151955
  · exact g32p_supplierForest_actual_151968
  · exact g32p_supplierForest_actual_151977
  · exact g32p_supplierForest_actual_151981
  · exact g32p_supplierForest_actual_151989
  · exact g32p_supplierForest_actual_152011
  · exact g32p_supplierForest_actual_152081
  · exact g32p_supplierForest_actual_152093
  · exact g32p_supplierForest_actual_152106
  · exact g32p_supplierForest_actual_152115
  · exact g32p_supplierForest_actual_152144
  · exact g32p_supplierForest_actual_152178
  · exact g32p_supplierForest_actual_152205
  · exact g32p_supplierForest_actual_152238
  · exact g32p_supplierForest_actual_152286
  · exact g32p_supplierForest_actual_152292
  · exact g32p_supplierForest_actual_152299
  · exact g32p_supplierForest_actual_152357
  · exact g32p_supplierForest_actual_152382
  · exact g32p_supplierForest_actual_152392
  · exact g32p_supplierForest_actual_152405
  · exact g32p_supplierForest_actual_152515
  · exact g32p_supplierForest_actual_152517
  · exact g32p_supplierForest_actual_152554
  · exact g32p_supplierForest_actual_152586
  · exact g32p_supplierForest_actual_152589
  · exact g32p_supplierForest_actual_152600
  · exact g32p_supplierForest_actual_152602
  · exact g32p_supplierForest_actual_152662
  · exact g32p_supplierForest_actual_152676
  · exact g32p_supplierForest_actual_152718
  · exact g32p_supplierForest_actual_152725
  · exact g32p_supplierForest_actual_152765
  · exact g32p_supplierForest_actual_152767
  · exact g32p_supplierForest_actual_152769
  · exact g32p_supplierForest_actual_152786
  · exact g32p_supplierForest_actual_152803
  · exact g32p_supplierForest_actual_152809
  · exact g32p_supplierForest_actual_152823
  · exact g32p_supplierForest_actual_152837
  · exact g32p_supplierForest_actual_152847
  · exact g32p_supplierForest_actual_152848
  · exact g32p_supplierForest_actual_152850
  · exact g32p_supplierForest_actual_152905
  · exact g32p_supplierForest_actual_152928
  · exact g32p_supplierForest_actual_152955
  · exact g32p_supplierForest_actual_152956
  · exact g32p_supplierForest_actual_152962
  · exact g32p_supplierForest_actual_153016
  · exact g32p_supplierForest_actual_153037
  · exact g32p_supplierForest_actual_153073
  · exact g32p_supplierForest_actual_153149
  · exact g32p_supplierForest_actual_153174
  · exact g32p_supplierForest_actual_153180
  · exact g32p_supplierForest_actual_153220
  · exact g32p_supplierForest_actual_153264
  · exact g32p_supplierForest_actual_153329
  · exact g32p_supplierForest_actual_153352
  · exact g32p_supplierForest_actual_153353
  · exact g32p_supplierForest_actual_153356
  · exact g32p_supplierForest_actual_153390
  · exact g32p_supplierForest_actual_153428
  · exact g32p_supplierForest_actual_153468
  · exact g32p_supplierForest_actual_153493
  · exact g32p_supplierForest_actual_153513
  · exact g32p_supplierForest_actual_153539
  · exact g32p_supplierForest_actual_153549
  · exact g32p_supplierForest_actual_153567
  · exact g32p_supplierForest_actual_153577
  · exact g32p_supplierForest_actual_153603
  · exact g32p_supplierForest_actual_153620
  · exact g32p_supplierForest_actual_153659
  · exact g32p_supplierForest_actual_153751
  · exact g32p_supplierForest_actual_153845
  · exact g32p_supplierForest_actual_153853
  · exact g32p_supplierForest_actual_153878
  · exact g32p_supplierForest_actual_153916
  · exact g32p_supplierForest_actual_153949
  · exact g32p_supplierForest_actual_154002
  · exact g32p_supplierForest_actual_154017
  · exact g32p_supplierForest_actual_154051
  · exact g32p_supplierForest_actual_154083
  · exact g32p_supplierForest_actual_154085
  · exact g32p_supplierForest_actual_154149
  · exact g32p_supplierForest_actual_154159
  · exact g32p_supplierForest_actual_154203
  · exact g32p_supplierForest_actual_154217
  · exact g32p_supplierForest_actual_154219
  · exact g32p_supplierForest_actual_154281
  · exact g32p_supplierForest_actual_154288
  · exact g32p_supplierForest_actual_154318
  · exact g32p_supplierForest_actual_154334
  · exact g32p_supplierForest_actual_154394
  · exact g32p_supplierForest_actual_154506
  · exact g32p_supplierForest_actual_154511
  · exact g32p_supplierForest_actual_154543
  · exact g32p_supplierForest_actual_154550
  · exact g32p_supplierForest_actual_154552
  · exact g32p_supplierForest_actual_154591
  · exact g32p_supplierForest_actual_154614
  · exact g32p_supplierForest_actual_154618
  · exact g32p_supplierForest_actual_154683
  · exact g32p_supplierForest_actual_154694
  · exact g32p_supplierForest_actual_154725
  · exact g32p_supplierForest_actual_154764
  · exact g32p_supplierForest_actual_154771
  · exact g32p_supplierForest_actual_154796
  · exact g32p_supplierForest_actual_154819
  · exact g32p_supplierForest_actual_154869
  · exact g32p_supplierForest_actual_154897
  · exact g32p_supplierForest_actual_154905
  · exact g32p_supplierForest_actual_154955
  · exact g32p_supplierForest_actual_154968
  · exact g32p_supplierForest_actual_154984
  · exact g32p_supplierForest_actual_154985
  · exact g32p_supplierForest_actual_154987
  · exact g32p_supplierForest_actual_155009
  · exact g32p_supplierForest_actual_155017
  · exact g32p_supplierForest_actual_155033
  · exact g32p_supplierForest_actual_155047
  · exact g32p_supplierForest_actual_155125
  · exact g32p_supplierForest_actual_155157
  · exact g32p_supplierForest_actual_155165
  · exact g32p_supplierForest_actual_155215
  · exact g32p_supplierForest_actual_155217
  · exact g32p_supplierForest_actual_155259
  · exact g32p_supplierForest_actual_155288
  · exact g32p_supplierForest_actual_155340
  · exact g32p_supplierForest_actual_155362
  · exact g32p_supplierForest_actual_155366
  · exact g32p_supplierForest_actual_155373
  · exact g32p_supplierForest_actual_155378
  · exact g32p_supplierForest_actual_000253
  · exact g32p_supplierForest_actual_000293
  · exact g32p_supplierForest_actual_000385
  · exact g32p_supplierForest_actual_000411
  · exact g32p_supplierForest_actual_000460
  · exact g32p_supplierForest_actual_000562
  · exact g32p_supplierForest_actual_000565
  · exact g32p_supplierForest_actual_000652
  · exact g32p_supplierForest_actual_000754

end HodgeLean.Foundations.Program

end
end
