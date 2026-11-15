import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0258
import HodgeLean.Foundations.Program.G32PropFourSixPacked0259
import HodgeLean.Foundations.Program.G32PropFourSixPacked0260
import HodgeLean.Foundations.Program.G32PropFourSixPacked0266
import HodgeLean.Foundations.Program.G32PropFourSixPacked0267
import HodgeLean.Foundations.Program.G32PropFourSixPacked0268
import HodgeLean.Foundations.Program.G32PropFourSixPacked0269
import HodgeLean.Foundations.Program.G32PropFourSixPacked0271
import HodgeLean.Foundations.Program.G32PropFourSixPacked0276
import HodgeLean.Foundations.Program.G32PropFourSixPacked0277
import HodgeLean.Foundations.Program.G32PropFourSixPacked0278
import HodgeLean.Foundations.Program.G32PropFourSixPacked0279

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_118384 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118384 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118384 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154543 := by
  decide +kernel

theorem g32p_supplierForest_actual_118384 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118384) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_118384
    g32p_supplierForest_actual_154543

def g32p_supplierForest_node_118392 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_118392 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118392 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_041283 := by
  decide +kernel

theorem g32p_supplierForest_actual_118392 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118392) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_118392
    g32p_supplierForest_actual_041283

def g32p_supplierForest_node_118521 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_118521 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118521 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_125309 := by
  decide +kernel

theorem g32p_supplierForest_actual_118521 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118521) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_118521
    g32p_supplierForest_actual_125309

def g32p_supplierForest_node_118530 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118530 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118530 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_117731 := by
  decide +kernel

theorem g32p_supplierForest_actual_118530 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118530) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_118530
    g32p_supplierForest_actual_117731

def g32p_supplierForest_node_118542 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_118542 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118542 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_125934 := by
  decide +kernel

theorem g32p_supplierForest_actual_118542 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118542) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_118542
    g32p_supplierForest_actual_125934

def g32p_supplierForest_node_118569 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_118569 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118569 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_125932 := by
  decide +kernel

theorem g32p_supplierForest_actual_118569 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118569) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 0 g32p_supplierForest_edge_118569
    g32p_supplierForest_actual_125932

def g32p_supplierForest_node_118592 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118592 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118592 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_123109 := by
  decide +kernel

theorem g32p_supplierForest_actual_118592 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118592) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_118592
    g32p_supplierForest_actual_123109

def g32p_supplierForest_node_118601 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118601 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118601 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120901 := by
  decide +kernel

theorem g32p_supplierForest_actual_118601 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118601) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_118601
    g32p_supplierForest_actual_120901

def g32p_supplierForest_node_118604 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_118604 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118604 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_115425 := by
  decide +kernel

theorem g32p_supplierForest_actual_118604 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118604) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_118604
    g32p_supplierForest_actual_115425

def g32p_supplierForest_node_118639 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_118639 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118639 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_111599 := by
  decide +kernel

theorem g32p_supplierForest_actual_118639 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118639) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_118639
    g32p_supplierForest_actual_111599

def g32p_supplierForest_node_118640 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118640 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118640 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_115688 := by
  decide +kernel

theorem g32p_supplierForest_actual_118640 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118640) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 1 g32p_supplierForest_edge_118640
    g32p_supplierForest_actual_115688

def g32p_supplierForest_node_118646 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_118646 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118646 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_102386 := by
  decide +kernel

theorem g32p_supplierForest_actual_118646 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118646) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 0 g32p_supplierForest_edge_118646
    g32p_supplierForest_actual_102386

def g32p_supplierForest_node_118718 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118718 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118718 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118849 := by
  decide +kernel

theorem g32p_supplierForest_actual_118718 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118718) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_118718
    g32p_supplierForest_actual_118849

def g32p_supplierForest_node_118753 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_118753 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118753 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118790 := by
  decide +kernel

theorem g32p_supplierForest_actual_118753 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118753) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_118753
    g32p_supplierForest_actual_118790

def g32p_supplierForest_node_118763 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118763 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118763 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108092 := by
  decide +kernel

theorem g32p_supplierForest_actual_118763 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118763) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_118763
    g32p_supplierForest_actual_108092

def g32p_supplierForest_node_118782 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118782 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118782 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_108647 := by
  decide +kernel

theorem g32p_supplierForest_actual_118782 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118782) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_118782
    g32p_supplierForest_actual_108647

def g32p_supplierForest_node_118844 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_118844 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118844 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_103439 := by
  decide +kernel

theorem g32p_supplierForest_actual_118844 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118844) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_118844
    g32p_supplierForest_actual_103439

def g32p_supplierForest_node_118846 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_118846 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118846 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_117601 := by
  decide +kernel

theorem g32p_supplierForest_actual_118846 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118846) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_118846
    g32p_supplierForest_actual_117601

def g32p_supplierForest_node_118908 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_118908 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118908 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121932 := by
  decide +kernel

theorem g32p_supplierForest_actual_118908 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118908) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_118908
    g32p_supplierForest_actual_121932

def g32p_supplierForest_node_118912 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_118912 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118912 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112567 := by
  decide +kernel

theorem g32p_supplierForest_actual_118912 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118912) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_118912
    g32p_supplierForest_actual_112567

def g32p_supplierForest_node_118914 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_118914 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118914 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_041022 := by
  decide +kernel

theorem g32p_supplierForest_actual_118914 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118914) ∧
        IsConj g (g32p_literalRepresentative 64) := by
  exact g32p_archive_step_lift _ _ 64 2 g32p_supplierForest_edge_118914
    g32p_supplierForest_actual_041022

def g32p_supplierForest_node_118930 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_118930 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118930 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038311 := by
  decide +kernel

theorem g32p_supplierForest_actual_118930 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118930) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_118930
    g32p_supplierForest_actual_038311

def g32p_supplierForest_node_118967 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_118967 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118967 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_117514 := by
  decide +kernel

theorem g32p_supplierForest_actual_118967 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118967) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_118967
    g32p_supplierForest_actual_117514

def g32p_supplierForest_node_118972 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_118972 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118972 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_040018 := by
  decide +kernel

theorem g32p_supplierForest_actual_118972 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118972) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_118972
    g32p_supplierForest_actual_040018

def g32p_supplierForest_node_118979 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_118979 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118979 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_041053 := by
  decide +kernel

theorem g32p_supplierForest_actual_118979 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118979) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_118979
    g32p_supplierForest_actual_041053

def g32p_supplierForest_node_119028 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119028 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119028 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_154591 := by
  decide +kernel

theorem g32p_supplierForest_actual_119028 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119028) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_119028
    g32p_supplierForest_actual_154591

def g32p_supplierForest_node_119056 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_119056 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119056 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_038998 := by
  decide +kernel

theorem g32p_supplierForest_actual_119056 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119056) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_119056
    g32p_supplierForest_actual_038998

def g32p_supplierForest_node_119099 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_119099 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119099 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_121971 := by
  decide +kernel

theorem g32p_supplierForest_actual_119099 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119099) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_119099
    g32p_supplierForest_actual_121971

def g32p_supplierForest_node_119232 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_119232 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119232 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_104038 := by
  decide +kernel

theorem g32p_supplierForest_actual_119232 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119232) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_119232
    g32p_supplierForest_actual_104038

def g32p_supplierForest_node_119276 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_119276 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119276 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_119575 := by
  decide +kernel

theorem g32p_supplierForest_actual_119276 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119276) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_119276
    g32p_supplierForest_actual_119575

def g32p_supplierForest_node_119283 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119283 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119283 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_032619 := by
  decide +kernel

theorem g32p_supplierForest_actual_119283 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119283) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_119283
    g32p_supplierForest_actual_032619

def g32p_supplierForest_node_119288 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_119288 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119288 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126211 := by
  decide +kernel

theorem g32p_supplierForest_actual_119288 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119288) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_119288
    g32p_supplierForest_actual_126211

def g32p_supplierForest_node_119298 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119298 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119298 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118987 := by
  decide +kernel

theorem g32p_supplierForest_actual_119298 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119298) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 3 g32p_supplierForest_edge_119298
    g32p_supplierForest_actual_118987

def g32p_supplierForest_node_119302 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_119302 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119302 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_104344 := by
  decide +kernel

theorem g32p_supplierForest_actual_119302 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119302) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_119302
    g32p_supplierForest_actual_104344

def g32p_supplierForest_node_119357 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_119357 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119357 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118614 := by
  decide +kernel

theorem g32p_supplierForest_actual_119357 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119357) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 1 g32p_supplierForest_edge_119357
    g32p_supplierForest_actual_118614

def g32p_supplierForest_node_119360 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119360 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119360 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104619 := by
  decide +kernel

theorem g32p_supplierForest_actual_119360 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119360) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_119360
    g32p_supplierForest_actual_104619

def g32p_supplierForest_node_119377 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_119377 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119377 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_116974 := by
  decide +kernel

theorem g32p_supplierForest_actual_119377 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119377) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_119377
    g32p_supplierForest_actual_116974

def g32p_supplierForest_node_119382 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_119382 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119382 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113396 := by
  decide +kernel

theorem g32p_supplierForest_actual_119382 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119382) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_119382
    g32p_supplierForest_actual_113396

def g32p_supplierForest_node_119396 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_119396 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119396 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_116903 := by
  decide +kernel

theorem g32p_supplierForest_actual_119396 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119396) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 3 g32p_supplierForest_edge_119396
    g32p_supplierForest_actual_116903

def g32p_supplierForest_node_119428 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_119428 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119428 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_103723 := by
  decide +kernel

theorem g32p_supplierForest_actual_119428 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119428) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_119428
    g32p_supplierForest_actual_103723

def g32p_supplierForest_node_119450 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_119450 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119450 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_109576 := by
  decide +kernel

theorem g32p_supplierForest_actual_119450 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119450) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_119450
    g32p_supplierForest_actual_109576

def g32p_supplierForest_node_119455 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_119455 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119455 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113961 := by
  decide +kernel

theorem g32p_supplierForest_actual_119455 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119455) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_119455
    g32p_supplierForest_actual_113961

def g32p_supplierForest_node_119461 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119461 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119461 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_152676 := by
  decide +kernel

theorem g32p_supplierForest_actual_119461 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119461) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_119461
    g32p_supplierForest_actual_152676

def g32p_supplierForest_node_119511 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_119511 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119511 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_043362 := by
  decide +kernel

theorem g32p_supplierForest_actual_119511 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119511) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_119511
    g32p_supplierForest_actual_043362

def g32p_supplierForest_node_119544 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_119544 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119544 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_107131 := by
  decide +kernel

theorem g32p_supplierForest_actual_119544 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119544) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_119544
    g32p_supplierForest_actual_107131

def g32p_supplierForest_node_119594 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_119594 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119594 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123432 := by
  decide +kernel

theorem g32p_supplierForest_actual_119594 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119594) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_119594
    g32p_supplierForest_actual_123432

def g32p_supplierForest_node_119641 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_119641 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119641 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_110239 := by
  decide +kernel

theorem g32p_supplierForest_actual_119641 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119641) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_119641
    g32p_supplierForest_actual_110239

def g32p_supplierForest_node_119643 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119643 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119643 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121204 := by
  decide +kernel

theorem g32p_supplierForest_actual_119643 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119643) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_119643
    g32p_supplierForest_actual_121204

def g32p_supplierForest_node_119688 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_119688 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119688 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_031368 := by
  decide +kernel

theorem g32p_supplierForest_actual_119688 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119688) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_119688
    g32p_supplierForest_actual_031368

def g32p_supplierForest_node_119711 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119711 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119711 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_119932 := by
  decide +kernel

theorem g32p_supplierForest_actual_119711 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119711) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_119711
    g32p_supplierForest_actual_119932

def g32p_supplierForest_node_119756 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119756 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119756 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043322 := by
  decide +kernel

theorem g32p_supplierForest_actual_119756 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119756) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_119756
    g32p_supplierForest_actual_043322

def g32p_supplierForest_node_119768 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_119768 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119768 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113939 := by
  decide +kernel

theorem g32p_supplierForest_actual_119768 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119768) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_119768
    g32p_supplierForest_actual_113939

def g32p_supplierForest_node_119776 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_119776 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119776 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_033223 := by
  decide +kernel

theorem g32p_supplierForest_actual_119776 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119776) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_119776
    g32p_supplierForest_actual_033223

def g32p_supplierForest_node_119817 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_119817 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119817 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_114770 := by
  decide +kernel

theorem g32p_supplierForest_actual_119817 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119817) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_119817
    g32p_supplierForest_actual_114770

def g32p_supplierForest_node_119821 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119821 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119821 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_116659 := by
  decide +kernel

theorem g32p_supplierForest_actual_119821 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119821) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_119821
    g32p_supplierForest_actual_116659

def g32p_supplierForest_node_119837 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_119837 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119837 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_106404 := by
  decide +kernel

theorem g32p_supplierForest_actual_119837 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119837) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_119837
    g32p_supplierForest_actual_106404

def g32p_supplierForest_node_119854 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119854 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119854 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_127702 := by
  decide +kernel

theorem g32p_supplierForest_actual_119854 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119854) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_119854
    g32p_supplierForest_actual_127702

def g32p_supplierForest_node_119923 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_119923 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119923 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_025823 := by
  decide +kernel

theorem g32p_supplierForest_actual_119923 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119923) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_119923
    g32p_supplierForest_actual_025823

def g32p_supplierForest_node_119954 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_119954 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119954 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_033284 := by
  decide +kernel

theorem g32p_supplierForest_actual_119954 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119954) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_119954
    g32p_supplierForest_actual_033284

def g32p_supplierForest_node_119974 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_119974 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119974 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121202 := by
  decide +kernel

theorem g32p_supplierForest_actual_119974 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119974) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_119974
    g32p_supplierForest_actual_121202

def g32p_supplierForest_node_120019 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_120019 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120019 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_106299 := by
  decide +kernel

theorem g32p_supplierForest_actual_120019 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120019) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_120019
    g32p_supplierForest_actual_106299

def g32p_supplierForest_node_120138 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_120138 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120138 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118697 := by
  decide +kernel

theorem g32p_supplierForest_actual_120138 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120138) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_120138
    g32p_supplierForest_actual_118697

def g32p_supplierForest_node_120146 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_120146 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120146 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038630 := by
  decide +kernel

theorem g32p_supplierForest_actual_120146 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120146) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_120146
    g32p_supplierForest_actual_038630

def g32p_supplierForest_node_120156 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120156 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120156 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_126788 := by
  decide +kernel

theorem g32p_supplierForest_actual_120156 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120156) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 0 g32p_supplierForest_edge_120156
    g32p_supplierForest_actual_126788

def g32p_supplierForest_node_120164 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_120164 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120164 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_127231 := by
  decide +kernel

theorem g32p_supplierForest_actual_120164 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120164) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_120164
    g32p_supplierForest_actual_127231

def g32p_supplierForest_node_120171 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120171 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120171 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029370 := by
  decide +kernel

theorem g32p_supplierForest_actual_120171 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120171) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_120171
    g32p_supplierForest_actual_029370

def g32p_supplierForest_node_120180 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120180 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120180 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_117234 := by
  decide +kernel

theorem g32p_supplierForest_actual_120180 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120180) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 3 g32p_supplierForest_edge_120180
    g32p_supplierForest_actual_117234

def g32p_supplierForest_node_120200 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_120200 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120200 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_034353 := by
  decide +kernel

theorem g32p_supplierForest_actual_120200 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120200) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_120200
    g32p_supplierForest_actual_034353

def g32p_supplierForest_node_120206 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_120206 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120206 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122153 := by
  decide +kernel

theorem g32p_supplierForest_actual_120206 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120206) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_120206
    g32p_supplierForest_actual_122153

def g32p_supplierForest_node_120230 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_120230 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120230 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_031792 := by
  decide +kernel

theorem g32p_supplierForest_actual_120230 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120230) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_120230
    g32p_supplierForest_actual_031792

def g32p_supplierForest_node_120277 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120277 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120277 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_124341 := by
  decide +kernel

theorem g32p_supplierForest_actual_120277 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120277) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_120277
    g32p_supplierForest_actual_124341

def g32p_supplierForest_node_120284 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_120284 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120284 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_038554 := by
  decide +kernel

theorem g32p_supplierForest_actual_120284 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120284) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_120284
    g32p_supplierForest_actual_038554

def g32p_supplierForest_node_120393 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_120393 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120393 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124119 := by
  decide +kernel

theorem g32p_supplierForest_actual_120393 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120393) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_120393
    g32p_supplierForest_actual_124119

def g32p_supplierForest_node_120443 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120443 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120443 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_154694 := by
  decide +kernel

theorem g32p_supplierForest_actual_120443 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120443) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 1 g32p_supplierForest_edge_120443
    g32p_supplierForest_actual_154694

def g32p_supplierForest_node_120451 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120451 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120451 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_126479 := by
  decide +kernel

theorem g32p_supplierForest_actual_120451 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120451) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_120451
    g32p_supplierForest_actual_126479

def g32p_supplierForest_node_120457 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_120457 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120457 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_119586 := by
  decide +kernel

theorem g32p_supplierForest_actual_120457 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120457) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_120457
    g32p_supplierForest_actual_119586

def g32p_supplierForest_node_120653 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_120653 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120653 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_103882 := by
  decide +kernel

theorem g32p_supplierForest_actual_120653 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120653) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_120653
    g32p_supplierForest_actual_103882

def g32p_supplierForest_node_120658 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120658 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120658 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_035900 := by
  decide +kernel

theorem g32p_supplierForest_actual_120658 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120658) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_120658
    g32p_supplierForest_actual_035900

def g32p_supplierForest_node_120688 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_120688 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120688 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102873 := by
  decide +kernel

theorem g32p_supplierForest_actual_120688 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120688) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_120688
    g32p_supplierForest_actual_102873

def g32p_supplierForest_node_120742 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120742 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120742 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_111243 := by
  decide +kernel

theorem g32p_supplierForest_actual_120742 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120742) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_120742
    g32p_supplierForest_actual_111243

def g32p_supplierForest_node_120762 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_120762 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120762 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_121259 := by
  decide +kernel

theorem g32p_supplierForest_actual_120762 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120762) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_120762
    g32p_supplierForest_actual_121259

def g32p_supplierForest_node_120763 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_120763 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120763 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_103385 := by
  decide +kernel

theorem g32p_supplierForest_actual_120763 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120763) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 3 g32p_supplierForest_edge_120763
    g32p_supplierForest_actual_103385

def g32p_supplierForest_node_120813 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_120813 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120813 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_109002 := by
  decide +kernel

theorem g32p_supplierForest_actual_120813 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120813) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_120813
    g32p_supplierForest_actual_109002

def g32p_supplierForest_node_120817 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_120817 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120817 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_104160 := by
  decide +kernel

theorem g32p_supplierForest_actual_120817 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120817) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_120817
    g32p_supplierForest_actual_104160

def g32p_supplierForest_node_120822 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_120822 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120822 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_111299 := by
  decide +kernel

theorem g32p_supplierForest_actual_120822 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120822) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_120822
    g32p_supplierForest_actual_111299

def g32p_supplierForest_node_120892 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_120892 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120892 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_111899 := by
  decide +kernel

theorem g32p_supplierForest_actual_120892 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120892) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_120892
    g32p_supplierForest_actual_111899

def g32p_supplierForest_node_120938 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_120938 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120938 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_108625 := by
  decide +kernel

theorem g32p_supplierForest_actual_120938 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120938) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_120938
    g32p_supplierForest_actual_108625

def g32p_supplierForest_node_121006 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_121006 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121006 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_043425 := by
  decide +kernel

theorem g32p_supplierForest_actual_121006 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121006) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_121006
    g32p_supplierForest_actual_043425

def g32p_supplierForest_node_121015 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_121015 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121015 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126690 := by
  decide +kernel

theorem g32p_supplierForest_actual_121015 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121015) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_121015
    g32p_supplierForest_actual_126690

def g32p_supplierForest_node_121103 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_121103 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121103 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_036367 := by
  decide +kernel

theorem g32p_supplierForest_actual_121103 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121103) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_121103
    g32p_supplierForest_actual_036367

def g32p_supplierForest_node_121165 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_121165 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121165 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_104770 := by
  decide +kernel

theorem g32p_supplierForest_actual_121165 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121165) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_121165
    g32p_supplierForest_actual_104770

def g32p_supplierForest_node_121199 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121199 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121199 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_106480 := by
  decide +kernel

theorem g32p_supplierForest_actual_121199 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121199) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_121199
    g32p_supplierForest_actual_106480

def g32p_supplierForest_node_121219 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121219 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121219 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_109167 := by
  decide +kernel

theorem g32p_supplierForest_actual_121219 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121219) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_121219
    g32p_supplierForest_actual_109167

def g32p_supplierForest_node_121235 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_121235 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121235 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_106477 := by
  decide +kernel

theorem g32p_supplierForest_actual_121235 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121235) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_121235
    g32p_supplierForest_actual_106477

def g32p_supplierForest_node_121254 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_121254 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121254 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_110210 := by
  decide +kernel

theorem g32p_supplierForest_actual_121254 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121254) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_121254
    g32p_supplierForest_actual_110210

def g32p_supplierForest_node_121269 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_121269 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121269 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108811 := by
  decide +kernel

theorem g32p_supplierForest_actual_121269 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121269) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_121269
    g32p_supplierForest_actual_108811

def g32p_supplierForest_node_121282 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_121282 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121282 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121281 := by
  decide +kernel

theorem g32p_supplierForest_actual_121282 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121282) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_121282
    g32p_supplierForest_actual_121281

def g32p_supplierForest_node_121310 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_121310 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121310 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_124038 := by
  decide +kernel

theorem g32p_supplierForest_actual_121310 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121310) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_121310
    g32p_supplierForest_actual_124038

def g32p_supplierForest_node_121349 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_121349 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121349 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102148 := by
  decide +kernel

theorem g32p_supplierForest_actual_121349 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121349) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_121349
    g32p_supplierForest_actual_102148

def g32p_supplierForest_node_121393 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_121393 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121393 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_111916 := by
  decide +kernel

theorem g32p_supplierForest_actual_121393 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121393) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_121393
    g32p_supplierForest_actual_111916

def g32p_supplierForest_node_121406 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_121406 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121406 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_102250 := by
  decide +kernel

theorem g32p_supplierForest_actual_121406 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121406) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 3 g32p_supplierForest_edge_121406
    g32p_supplierForest_actual_102250

def g32p_supplierForest_node_121408 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_121408 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121408 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121447 := by
  decide +kernel

theorem g32p_supplierForest_actual_121408 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121408) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_121408
    g32p_supplierForest_actual_121447

def g32p_supplierForest_node_121436 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_121436 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121436 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_106288 := by
  decide +kernel

theorem g32p_supplierForest_actual_121436 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121436) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_121436
    g32p_supplierForest_actual_106288

def g32p_supplierForest_node_121485 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_121485 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121485 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123703 := by
  decide +kernel

theorem g32p_supplierForest_actual_121485 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121485) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_121485
    g32p_supplierForest_actual_123703

def g32p_supplierForest_node_121497 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_121497 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121497 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_106390 := by
  decide +kernel

theorem g32p_supplierForest_actual_121497 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121497) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_121497
    g32p_supplierForest_actual_106390

def g32p_supplierForest_node_121515 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_121515 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121515 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121603 := by
  decide +kernel

theorem g32p_supplierForest_actual_121515 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121515) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_121515
    g32p_supplierForest_actual_121603

def g32p_supplierForest_node_121538 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_121538 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121538 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_043189 := by
  decide +kernel

theorem g32p_supplierForest_actual_121538 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121538) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_121538
    g32p_supplierForest_actual_043189

def g32p_supplierForest_node_121543 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121543 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121543 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127438 := by
  decide +kernel

theorem g32p_supplierForest_actual_121543 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121543) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_121543
    g32p_supplierForest_actual_127438

def g32p_supplierForest_node_121552 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_121552 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121552 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108093 := by
  decide +kernel

theorem g32p_supplierForest_actual_121552 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121552) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_121552
    g32p_supplierForest_actual_108093

def g32p_supplierForest_node_121604 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121604 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121604 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_125997 := by
  decide +kernel

theorem g32p_supplierForest_actual_121604 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121604) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_121604
    g32p_supplierForest_actual_125997

def g32p_supplierForest_node_121608 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_121608 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121608 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_119421 := by
  decide +kernel

theorem g32p_supplierForest_actual_121608 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121608) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_121608
    g32p_supplierForest_actual_119421

def g32p_supplierForest_node_121612 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_121612 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121612 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_027909 := by
  decide +kernel

theorem g32p_supplierForest_actual_121612 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121612) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_121612
    g32p_supplierForest_actual_027909

def g32p_supplierForest_node_121638 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121638 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121638 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126389 := by
  decide +kernel

theorem g32p_supplierForest_actual_121638 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121638) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_121638
    g32p_supplierForest_actual_126389

def g32p_supplierForest_node_121654 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_121654 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121654 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_106285 := by
  decide +kernel

theorem g32p_supplierForest_actual_121654 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121654) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_121654
    g32p_supplierForest_actual_106285

def g32p_supplierForest_node_121667 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121667 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121667 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_117029 := by
  decide +kernel

theorem g32p_supplierForest_actual_121667 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121667) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_121667
    g32p_supplierForest_actual_117029

def g32p_supplierForest_node_121706 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_121706 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121706 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_106623 := by
  decide +kernel

theorem g32p_supplierForest_actual_121706 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121706) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_121706
    g32p_supplierForest_actual_106623

def g32p_supplierForest_node_121717 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_121717 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121717 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_043425 := by
  decide +kernel

theorem g32p_supplierForest_actual_121717 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121717) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_121717
    g32p_supplierForest_actual_043425

def g32p_supplierForest_node_121725 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_121725 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121725 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152718 := by
  decide +kernel

theorem g32p_supplierForest_actual_121725 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121725) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_121725
    g32p_supplierForest_actual_152718

def g32p_supplierForest_node_121763 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_121763 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121763 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152850 := by
  decide +kernel

theorem g32p_supplierForest_actual_121763 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121763) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_121763
    g32p_supplierForest_actual_152850

def g32p_supplierForest_node_121796 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121796 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121796 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_039416 := by
  decide +kernel

theorem g32p_supplierForest_actual_121796 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121796) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_121796
    g32p_supplierForest_actual_039416

def g32p_supplierForest_node_121802 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121802 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121802 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_126221 := by
  decide +kernel

theorem g32p_supplierForest_actual_121802 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121802) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_121802
    g32p_supplierForest_actual_126221

def g32p_supplierForest_node_121808 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_121808 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121808 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121807 := by
  decide +kernel

theorem g32p_supplierForest_actual_121808 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121808) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_121808
    g32p_supplierForest_actual_121807

def g32p_supplierForest_node_121925 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_121925 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121925 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_118747 := by
  decide +kernel

theorem g32p_supplierForest_actual_121925 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121925) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 0 g32p_supplierForest_edge_121925
    g32p_supplierForest_actual_118747

def g32p_supplierForest_node_121955 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121955 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121955 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_030818 := by
  decide +kernel

theorem g32p_supplierForest_actual_121955 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121955) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_121955
    g32p_supplierForest_actual_030818

def g32p_supplierForest_node_121957 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_121957 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121957 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_108367 := by
  decide +kernel

theorem g32p_supplierForest_actual_121957 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121957) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_121957
    g32p_supplierForest_actual_108367

def g32p_supplierForest_node_121994 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_121994 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121994 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123783 := by
  decide +kernel

theorem g32p_supplierForest_actual_121994 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121994) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_121994
    g32p_supplierForest_actual_123783

def g32p_supplierForest_node_122020 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_122020 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122020 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_120776 := by
  decide +kernel

theorem g32p_supplierForest_actual_122020 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122020) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_122020
    g32p_supplierForest_actual_120776

def g32p_supplierForest_node_122062 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122062 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122062 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_027018 := by
  decide +kernel

theorem g32p_supplierForest_actual_122062 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122062) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_122062
    g32p_supplierForest_actual_027018

def g32p_supplierForest_node_122076 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_122076 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122076 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127150 := by
  decide +kernel

theorem g32p_supplierForest_actual_122076 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122076) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_122076
    g32p_supplierForest_actual_127150

def g32p_supplierForest_node_122113 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_122113 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122113 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_126999 := by
  decide +kernel

theorem g32p_supplierForest_actual_122113 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122113) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_122113
    g32p_supplierForest_actual_126999

def g32p_supplierForest_node_122132 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122132 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122132 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_126979 := by
  decide +kernel

theorem g32p_supplierForest_actual_122132 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122132) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_122132
    g32p_supplierForest_actual_126979

def g32p_supplierForest_node_122134 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_122134 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122134 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117062 := by
  decide +kernel

theorem g32p_supplierForest_actual_122134 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122134) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 1 g32p_supplierForest_edge_122134
    g32p_supplierForest_actual_117062

def g32p_supplierForest_node_122177 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_122177 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122177 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108473 := by
  decide +kernel

theorem g32p_supplierForest_actual_122177 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122177) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 3 g32p_supplierForest_edge_122177
    g32p_supplierForest_actual_108473

def g32p_supplierForest_node_122189 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_122189 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122189 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_121690 := by
  decide +kernel

theorem g32p_supplierForest_actual_122189 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122189) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_122189
    g32p_supplierForest_actual_121690

def g32p_supplierForest_node_122206 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_122206 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122206 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_104268 := by
  decide +kernel

theorem g32p_supplierForest_actual_122206 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122206) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_122206
    g32p_supplierForest_actual_104268

def g32p_supplierForest_node_122239 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_122239 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122239 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_125782 := by
  decide +kernel

theorem g32p_supplierForest_actual_122239 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122239) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_122239
    g32p_supplierForest_actual_125782

def g32p_supplierForest_node_122309 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122309 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122309 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154149 := by
  decide +kernel

theorem g32p_supplierForest_actual_122309 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122309) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_122309
    g32p_supplierForest_actual_154149

def g32p_supplierForest_node_122354 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122354 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122354 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_035140 := by
  decide +kernel

theorem g32p_supplierForest_actual_122354 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122354) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_122354
    g32p_supplierForest_actual_035140

def g32p_supplierForest_node_122356 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_122356 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122356 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_044383 := by
  decide +kernel

theorem g32p_supplierForest_actual_122356 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122356) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_122356
    g32p_supplierForest_actual_044383

def g32p_supplierForest_node_122369 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_122369 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122369 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117956 := by
  decide +kernel

theorem g32p_supplierForest_actual_122369 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122369) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_122369
    g32p_supplierForest_actual_117956

def g32p_supplierForest_node_122372 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_122372 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122372 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_125105 := by
  decide +kernel

theorem g32p_supplierForest_actual_122372 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122372) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_122372
    g32p_supplierForest_actual_125105

def g32p_supplierForest_node_122373 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_122373 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122373 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_117124 := by
  decide +kernel

theorem g32p_supplierForest_actual_122373 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122373) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_122373
    g32p_supplierForest_actual_117124

def g32p_supplierForest_node_122436 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_122436 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122436 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_120039 := by
  decide +kernel

theorem g32p_supplierForest_actual_122436 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122436) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 0 g32p_supplierForest_edge_122436
    g32p_supplierForest_actual_120039

def g32p_supplierForest_node_122452 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122452 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122452 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_034826 := by
  decide +kernel

theorem g32p_supplierForest_actual_122452 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122452) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_122452
    g32p_supplierForest_actual_034826

def g32p_supplierForest_node_122456 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_122456 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122456 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_106256 := by
  decide +kernel

theorem g32p_supplierForest_actual_122456 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122456) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_122456
    g32p_supplierForest_actual_106256

def g32p_supplierForest_node_122473 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_122473 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122473 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_107766 := by
  decide +kernel

theorem g32p_supplierForest_actual_122473 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122473) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_122473
    g32p_supplierForest_actual_107766

def g32p_supplierForest_node_122475 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_122475 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122475 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_107092 := by
  decide +kernel

theorem g32p_supplierForest_actual_122475 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122475) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 1 g32p_supplierForest_edge_122475
    g32p_supplierForest_actual_107092

def g32p_supplierForest_node_122497 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122497 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122497 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_118575 := by
  decide +kernel

theorem g32p_supplierForest_actual_122497 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122497) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_122497
    g32p_supplierForest_actual_118575

def g32p_supplierForest_node_122535 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_122535 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122535 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152586 := by
  decide +kernel

theorem g32p_supplierForest_actual_122535 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122535) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_122535
    g32p_supplierForest_actual_152586

def g32p_supplierForest_node_122594 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_122594 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122594 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118015 := by
  decide +kernel

theorem g32p_supplierForest_actual_122594 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122594) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_122594
    g32p_supplierForest_actual_118015

def g32p_supplierForest_node_122630 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122630 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122630 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_036654 := by
  decide +kernel

theorem g32p_supplierForest_actual_122630 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122630) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_122630
    g32p_supplierForest_actual_036654

def g32p_supplierForest_node_122664 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_122664 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122664 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127172 := by
  decide +kernel

theorem g32p_supplierForest_actual_122664 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122664) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_122664
    g32p_supplierForest_actual_127172

def g32p_supplierForest_node_122686 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122686 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122686 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154968 := by
  decide +kernel

theorem g32p_supplierForest_actual_122686 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122686) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_122686
    g32p_supplierForest_actual_154968

def g32p_supplierForest_node_122695 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_122695 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122695 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_108897 := by
  decide +kernel

theorem g32p_supplierForest_actual_122695 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122695) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 1 g32p_supplierForest_edge_122695
    g32p_supplierForest_actual_108897

def g32p_supplierForest_node_122707 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_122707 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122707 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_103170 := by
  decide +kernel

theorem g32p_supplierForest_actual_122707 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122707) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_122707
    g32p_supplierForest_actual_103170

def g32p_supplierForest_node_122727 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_122727 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122727 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109262 := by
  decide +kernel

theorem g32p_supplierForest_actual_122727 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122727) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_122727
    g32p_supplierForest_actual_109262

def g32p_supplierForest_node_122729 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_122729 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122729 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_035040 := by
  decide +kernel

theorem g32p_supplierForest_actual_122729 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122729) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_122729
    g32p_supplierForest_actual_035040

def g32p_supplierForest_node_122735 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122735 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122735 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109322 := by
  decide +kernel

theorem g32p_supplierForest_actual_122735 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122735) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_122735
    g32p_supplierForest_actual_109322

def g32p_supplierForest_node_122774 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122774 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122774 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_126224 := by
  decide +kernel

theorem g32p_supplierForest_actual_122774 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122774) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_122774
    g32p_supplierForest_actual_126224

def g32p_supplierForest_node_122776 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_122776 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122776 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_036462 := by
  decide +kernel

theorem g32p_supplierForest_actual_122776 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122776) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_122776
    g32p_supplierForest_actual_036462

def g32p_supplierForest_node_122811 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_122811 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122811 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109709 := by
  decide +kernel

theorem g32p_supplierForest_actual_122811 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122811) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_122811
    g32p_supplierForest_actual_109709

def g32p_supplierForest_node_122875 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122875 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122875 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_114334 := by
  decide +kernel

theorem g32p_supplierForest_actual_122875 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122875) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_122875
    g32p_supplierForest_actual_114334

def g32p_supplierForest_node_122879 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_122879 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122879 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_107754 := by
  decide +kernel

theorem g32p_supplierForest_actual_122879 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122879) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_122879
    g32p_supplierForest_actual_107754

def g32p_supplierForest_node_122903 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122903 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122903 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_103612 := by
  decide +kernel

theorem g32p_supplierForest_actual_122903 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122903) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_122903
    g32p_supplierForest_actual_103612

def g32p_supplierForest_node_122934 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_122934 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122934 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_107998 := by
  decide +kernel

theorem g32p_supplierForest_actual_122934 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122934) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 1 g32p_supplierForest_edge_122934
    g32p_supplierForest_actual_107998

def g32p_supplierForest_node_122941 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122941 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122941 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_111873 := by
  decide +kernel

theorem g32p_supplierForest_actual_122941 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122941) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_122941
    g32p_supplierForest_actual_111873

def g32p_supplierForest_node_122968 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_122968 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122968 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_123281 := by
  decide +kernel

theorem g32p_supplierForest_actual_122968 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122968) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_122968
    g32p_supplierForest_actual_123281

def g32p_supplierForest_node_122978 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_122978 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122978 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_102619 := by
  decide +kernel

theorem g32p_supplierForest_actual_122978 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122978) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_122978
    g32p_supplierForest_actual_102619

def g32p_supplierForest_node_123031 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_123031 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123031 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_043324 := by
  decide +kernel

theorem g32p_supplierForest_actual_123031 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123031) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_123031
    g32p_supplierForest_actual_043324

def g32p_supplierForest_node_123141 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_123141 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123141 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_118623 := by
  decide +kernel

theorem g32p_supplierForest_actual_123141 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123141) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_123141
    g32p_supplierForest_actual_118623

def g32p_supplierForest_node_123210 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123210 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123210 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112740 := by
  decide +kernel

theorem g32p_supplierForest_actual_123210 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123210) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_123210
    g32p_supplierForest_actual_112740

def g32p_supplierForest_node_123221 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_123221 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123221 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_039654 := by
  decide +kernel

theorem g32p_supplierForest_actual_123221 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123221) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_123221
    g32p_supplierForest_actual_039654

def g32p_supplierForest_node_123238 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_123238 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123238 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_039908 := by
  decide +kernel

theorem g32p_supplierForest_actual_123238 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123238) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 3 g32p_supplierForest_edge_123238
    g32p_supplierForest_actual_039908

def g32p_supplierForest_node_123276 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123276 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123276 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_127383 := by
  decide +kernel

theorem g32p_supplierForest_actual_123276 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123276) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 2 g32p_supplierForest_edge_123276
    g32p_supplierForest_actual_127383

def g32p_supplierForest_node_123291 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_123291 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123291 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112413 := by
  decide +kernel

theorem g32p_supplierForest_actual_123291 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123291) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_123291
    g32p_supplierForest_actual_112413

def g32p_supplierForest_node_123300 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_123300 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123300 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118697 := by
  decide +kernel

theorem g32p_supplierForest_actual_123300 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123300) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_123300
    g32p_supplierForest_actual_118697

def g32p_supplierForest_node_123331 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_123331 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123331 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123740 := by
  decide +kernel

theorem g32p_supplierForest_actual_123331 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123331) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_123331
    g32p_supplierForest_actual_123740

def g32p_supplierForest_node_123425 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_123425 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123425 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_127598 := by
  decide +kernel

theorem g32p_supplierForest_actual_123425 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123425) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_123425
    g32p_supplierForest_actual_127598

def g32p_supplierForest_node_123482 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_123482 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123482 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_118423 := by
  decide +kernel

theorem g32p_supplierForest_actual_123482 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123482) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_123482
    g32p_supplierForest_actual_118423

def g32p_supplierForest_node_123494 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_123494 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123494 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127129 := by
  decide +kernel

theorem g32p_supplierForest_actual_123494 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123494) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_123494
    g32p_supplierForest_actual_127129

def g32p_supplierForest_node_123496 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_123496 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123496 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_126188 := by
  decide +kernel

theorem g32p_supplierForest_actual_123496 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123496) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_123496
    g32p_supplierForest_actual_126188

def g32p_supplierForest_node_123505 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_123505 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123505 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123778 := by
  decide +kernel

theorem g32p_supplierForest_actual_123505 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123505) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_123505
    g32p_supplierForest_actual_123778

def g32p_supplierForest_node_123590 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_123590 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123590 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123591 := by
  decide +kernel

theorem g32p_supplierForest_actual_123590 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123590) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_123590
    g32p_supplierForest_actual_123591

def g32p_supplierForest_node_123611 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_123611 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123611 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_104663 := by
  decide +kernel

theorem g32p_supplierForest_actual_123611 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123611) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_123611
    g32p_supplierForest_actual_104663

def g32p_supplierForest_node_123712 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123712 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123712 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120331 := by
  decide +kernel

theorem g32p_supplierForest_actual_123712 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123712) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_123712
    g32p_supplierForest_actual_120331

def g32p_supplierForest_node_123762 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_123762 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123762 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_114797 := by
  decide +kernel

theorem g32p_supplierForest_actual_123762 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123762) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_123762
    g32p_supplierForest_actual_114797

def g32p_supplierForest_node_123766 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123766 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123766 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_102521 := by
  decide +kernel

theorem g32p_supplierForest_actual_123766 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123766) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 3 g32p_supplierForest_edge_123766
    g32p_supplierForest_actual_102521

def g32p_supplierForest_node_123780 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123780 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123780 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121836 := by
  decide +kernel

theorem g32p_supplierForest_actual_123780 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123780) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_123780
    g32p_supplierForest_actual_121836

def g32p_supplierForest_node_123805 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_123805 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123805 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_039550 := by
  decide +kernel

theorem g32p_supplierForest_actual_123805 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123805) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_123805
    g32p_supplierForest_actual_039550

def g32p_supplierForest_node_123818 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123818 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123818 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152956 := by
  decide +kernel

theorem g32p_supplierForest_actual_123818 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123818) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_123818
    g32p_supplierForest_actual_152956

def g32p_supplierForest_node_123865 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123865 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123865 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_116837 := by
  decide +kernel

theorem g32p_supplierForest_actual_123865 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123865) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_123865
    g32p_supplierForest_actual_116837

def g32p_supplierForest_node_123948 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_123948 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123948 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_125934 := by
  decide +kernel

theorem g32p_supplierForest_actual_123948 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123948) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_123948
    g32p_supplierForest_actual_125934

def g32p_supplierForest_node_123995 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123995 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123995 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_034639 := by
  decide +kernel

theorem g32p_supplierForest_actual_123995 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123995) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_123995
    g32p_supplierForest_actual_034639

def g32p_supplierForest_node_124032 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_124032 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124032 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152823 := by
  decide +kernel

theorem g32p_supplierForest_actual_124032 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124032) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_124032
    g32p_supplierForest_actual_152823

def g32p_supplierForest_node_124039 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_124039 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124039 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123764 := by
  decide +kernel

theorem g32p_supplierForest_actual_124039 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124039) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_124039
    g32p_supplierForest_actual_123764

def g32p_supplierForest_node_124052 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_124052 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124052 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_039540 := by
  decide +kernel

theorem g32p_supplierForest_actual_124052 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124052) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_124052
    g32p_supplierForest_actual_039540

def g32p_supplierForest_node_124054 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124054 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124054 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121357 := by
  decide +kernel

theorem g32p_supplierForest_actual_124054 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124054) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_124054
    g32p_supplierForest_actual_121357

def g32p_supplierForest_node_124134 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_124134 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124134 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_125781 := by
  decide +kernel

theorem g32p_supplierForest_actual_124134 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124134) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 3 g32p_supplierForest_edge_124134
    g32p_supplierForest_actual_125781

def g32p_supplierForest_node_124184 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_124184 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124184 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113795 := by
  decide +kernel

theorem g32p_supplierForest_actual_124184 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124184) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_124184
    g32p_supplierForest_actual_113795

def g32p_supplierForest_node_124205 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124205 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124205 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127476 := by
  decide +kernel

theorem g32p_supplierForest_actual_124205 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124205) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_124205
    g32p_supplierForest_actual_127476

def g32p_supplierForest_node_124210 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_124210 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124210 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122809 := by
  decide +kernel

theorem g32p_supplierForest_actual_124210 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124210) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_124210
    g32p_supplierForest_actual_122809

def g32p_supplierForest_node_124216 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_124216 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124216 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154288 := by
  decide +kernel

theorem g32p_supplierForest_actual_124216 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124216) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_124216
    g32p_supplierForest_actual_154288

def g32p_supplierForest_node_124362 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_124362 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124362 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_115735 := by
  decide +kernel

theorem g32p_supplierForest_actual_124362 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124362) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 3 g32p_supplierForest_edge_124362
    g32p_supplierForest_actual_115735

def g32p_supplierForest_node_124371 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124371 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124371 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121573 := by
  decide +kernel

theorem g32p_supplierForest_actual_124371 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124371) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_124371
    g32p_supplierForest_actual_121573

def g32p_supplierForest_node_124376 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_124376 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124376 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_106372 := by
  decide +kernel

theorem g32p_supplierForest_actual_124376 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124376) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_124376
    g32p_supplierForest_actual_106372

def g32p_supplierForest_node_124491 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124491 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124491 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_041217 := by
  decide +kernel

theorem g32p_supplierForest_actual_124491 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124491) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_124491
    g32p_supplierForest_actual_041217

def g32p_supplierForest_node_124499 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_124499 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124499 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_110010 := by
  decide +kernel

theorem g32p_supplierForest_actual_124499 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124499) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_124499
    g32p_supplierForest_actual_110010

def g32p_supplierForest_node_124534 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_124534 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124534 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_110237 := by
  decide +kernel

theorem g32p_supplierForest_actual_124534 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124534) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_124534
    g32p_supplierForest_actual_110237

def g32p_supplierForest_node_124541 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_124541 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124541 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_038582 := by
  decide +kernel

theorem g32p_supplierForest_actual_124541 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124541) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_124541
    g32p_supplierForest_actual_038582

def g32p_supplierForest_node_124557 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_124557 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124557 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122617 := by
  decide +kernel

theorem g32p_supplierForest_actual_124557 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124557) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_124557
    g32p_supplierForest_actual_122617

def g32p_supplierForest_node_124570 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124570 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124570 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153174 := by
  decide +kernel

theorem g32p_supplierForest_actual_124570 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124570) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 3 g32p_supplierForest_edge_124570
    g32p_supplierForest_actual_153174

def g32p_supplierForest_node_124609 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_124609 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124609 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153493 := by
  decide +kernel

theorem g32p_supplierForest_actual_124609 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124609) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 0 g32p_supplierForest_edge_124609
    g32p_supplierForest_actual_153493

def g32p_supplierForest_node_124625 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_124625 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124625 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_041223 := by
  decide +kernel

theorem g32p_supplierForest_actual_124625 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124625) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_124625
    g32p_supplierForest_actual_041223

def g32p_supplierForest_node_124640 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124640 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124640 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_039394 := by
  decide +kernel

theorem g32p_supplierForest_actual_124640 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124640) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_124640
    g32p_supplierForest_actual_039394

def g32p_supplierForest_node_124669 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_124669 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124669 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_104782 := by
  decide +kernel

theorem g32p_supplierForest_actual_124669 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124669) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_124669
    g32p_supplierForest_actual_104782

def g32p_supplierForest_node_124698 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_124698 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124698 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108112 := by
  decide +kernel

theorem g32p_supplierForest_actual_124698 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124698) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_124698
    g32p_supplierForest_actual_108112

def g32p_supplierForest_node_124712 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_124712 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124712 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122841 := by
  decide +kernel

theorem g32p_supplierForest_actual_124712 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124712) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_124712
    g32p_supplierForest_actual_122841

def g32p_supplierForest_node_124715 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124715 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124715 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121536 := by
  decide +kernel

theorem g32p_supplierForest_actual_124715 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124715) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_124715
    g32p_supplierForest_actual_121536

def g32p_supplierForest_node_124716 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124716 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124716 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_124180 := by
  decide +kernel

theorem g32p_supplierForest_actual_124716 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124716) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 3 g32p_supplierForest_edge_124716
    g32p_supplierForest_actual_124180

def g32p_supplierForest_node_124735 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_124735 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124735 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_125784 := by
  decide +kernel

theorem g32p_supplierForest_actual_124735 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124735) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_124735
    g32p_supplierForest_actual_125784

def g32p_supplierForest_node_124743 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_124743 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124743 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_127359 := by
  decide +kernel

theorem g32p_supplierForest_actual_124743 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124743) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_124743
    g32p_supplierForest_actual_127359

def g32p_supplierForest_node_124755 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_124755 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124755 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_044383 := by
  decide +kernel

theorem g32p_supplierForest_actual_124755 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124755) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_124755
    g32p_supplierForest_actual_044383

def g32p_supplierForest_node_124767 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_124767 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124767 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122539 := by
  decide +kernel

theorem g32p_supplierForest_actual_124767 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124767) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_124767
    g32p_supplierForest_actual_122539

def g32p_supplierForest_node_124768 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_124768 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124768 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_039980 := by
  decide +kernel

theorem g32p_supplierForest_actual_124768 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124768) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_124768
    g32p_supplierForest_actual_039980

def g32p_supplierForest_node_124791 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_124791 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124791 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123939 := by
  decide +kernel

theorem g32p_supplierForest_actual_124791 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124791) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_124791
    g32p_supplierForest_actual_123939

def g32p_supplierForest_node_124794 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_124794 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124794 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_124775 := by
  decide +kernel

theorem g32p_supplierForest_actual_124794 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124794) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_124794
    g32p_supplierForest_actual_124775

def g32p_supplierForest_node_124828 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_124828 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124828 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029786 := by
  decide +kernel

theorem g32p_supplierForest_actual_124828 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124828) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_124828
    g32p_supplierForest_actual_029786

def g32p_supplierForest_node_124872 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124872 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124872 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029546 := by
  decide +kernel

theorem g32p_supplierForest_actual_124872 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124872) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_124872
    g32p_supplierForest_actual_029546

def g32p_supplierForest_node_124900 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124900 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124900 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_030539 := by
  decide +kernel

theorem g32p_supplierForest_actual_124900 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124900) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_124900
    g32p_supplierForest_actual_030539

def g32p_supplierForest_node_124915 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_124915 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124915 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_114487 := by
  decide +kernel

theorem g32p_supplierForest_actual_124915 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124915) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_124915
    g32p_supplierForest_actual_114487

def g32p_supplierForest_node_124943 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_124943 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124943 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113769 := by
  decide +kernel

theorem g32p_supplierForest_actual_124943 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124943) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_124943
    g32p_supplierForest_actual_113769

def g32p_supplierForest_node_124969 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_124969 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124969 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_109851 := by
  decide +kernel

theorem g32p_supplierForest_actual_124969 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124969) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_124969
    g32p_supplierForest_actual_109851

def g32p_supplierForest_node_125057 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_125057 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125057 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123703 := by
  decide +kernel

theorem g32p_supplierForest_actual_125057 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125057) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_125057
    g32p_supplierForest_actual_123703

def g32p_supplierForest_node_125061 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_125061 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125061 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112975 := by
  decide +kernel

theorem g32p_supplierForest_actual_125061 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125061) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_125061
    g32p_supplierForest_actual_112975

def g32p_supplierForest_node_125065 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_125065 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125065 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_116123 := by
  decide +kernel

theorem g32p_supplierForest_actual_125065 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125065) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_125065
    g32p_supplierForest_actual_116123

def g32p_supplierForest_node_125074 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_125074 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125074 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_026741 := by
  decide +kernel

theorem g32p_supplierForest_actual_125074 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125074) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_125074
    g32p_supplierForest_actual_026741

def g32p_supplierForest_node_125215 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_125215 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125215 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_152809 := by
  decide +kernel

theorem g32p_supplierForest_actual_125215 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125215) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_125215
    g32p_supplierForest_actual_152809

def g32p_supplierForest_node_125290 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_125290 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125290 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104407 := by
  decide +kernel

theorem g32p_supplierForest_actual_125290 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125290) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_125290
    g32p_supplierForest_actual_104407

def g32p_supplierForest_node_125293 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_125293 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125293 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037461 := by
  decide +kernel

theorem g32p_supplierForest_actual_125293 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125293) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_125293
    g32p_supplierForest_actual_037461

def g32p_supplierForest_node_125320 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_125320 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125320 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_126871 := by
  decide +kernel

theorem g32p_supplierForest_actual_125320 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125320) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_125320
    g32p_supplierForest_actual_126871

def g32p_supplierForest_node_125326 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_125326 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125326 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_038644 := by
  decide +kernel

theorem g32p_supplierForest_actual_125326 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125326) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_125326
    g32p_supplierForest_actual_038644

def g32p_supplierForest_node_125374 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_125374 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125374 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104365 := by
  decide +kernel

theorem g32p_supplierForest_actual_125374 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125374) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_125374
    g32p_supplierForest_actual_104365

def g32p_supplierForest_node_125462 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_125462 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125462 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_121740 := by
  decide +kernel

theorem g32p_supplierForest_actual_125462 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125462) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_125462
    g32p_supplierForest_actual_121740

def g32p_supplierForest_node_125475 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_125475 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125475 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122604 := by
  decide +kernel

theorem g32p_supplierForest_actual_125475 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125475) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_125475
    g32p_supplierForest_actual_122604

def g32p_supplierForest_node_125480 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_125480 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125480 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118876 := by
  decide +kernel

theorem g32p_supplierForest_actual_125480 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125480) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_125480
    g32p_supplierForest_actual_118876

def g32p_supplierForest_node_125489 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_125489 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125489 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115374 := by
  decide +kernel

theorem g32p_supplierForest_actual_125489 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125489) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_125489
    g32p_supplierForest_actual_115374

def g32p_supplierForest_node_125511 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_125511 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125511 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_038807 := by
  decide +kernel

theorem g32p_supplierForest_actual_125511 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125511) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_125511
    g32p_supplierForest_actual_038807

def g32p_supplierForest_node_125522 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_125522 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125522 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_124081 := by
  decide +kernel

theorem g32p_supplierForest_actual_125522 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125522) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_125522
    g32p_supplierForest_actual_124081

def g32p_supplierForest_node_125529 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_125529 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125529 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153845 := by
  decide +kernel

theorem g32p_supplierForest_actual_125529 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125529) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_125529
    g32p_supplierForest_actual_153845

def g32p_supplierForest_node_125555 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_125555 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125555 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153853 := by
  decide +kernel

theorem g32p_supplierForest_actual_125555 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125555) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_125555
    g32p_supplierForest_actual_153853

def g32p_supplierForest_node_125587 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_125587 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125587 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_103340 := by
  decide +kernel

theorem g32p_supplierForest_actual_125587 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125587) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_125587
    g32p_supplierForest_actual_103340

def g32p_supplierForest_node_125628 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_125628 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125628 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_110063 := by
  decide +kernel

theorem g32p_supplierForest_actual_125628 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125628) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_125628
    g32p_supplierForest_actual_110063

def g32p_supplierForest_node_125645 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_125645 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125645 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127587 := by
  decide +kernel

theorem g32p_supplierForest_actual_125645 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125645) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_125645
    g32p_supplierForest_actual_127587

def g32p_supplierForest_node_125647 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_125647 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125647 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_123190 := by
  decide +kernel

theorem g32p_supplierForest_actual_125647 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125647) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_125647
    g32p_supplierForest_actual_123190

def g32p_supplierForest_node_125682 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_125682 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125682 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_103400 := by
  decide +kernel

theorem g32p_supplierForest_actual_125682 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125682) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_125682
    g32p_supplierForest_actual_103400

def g32p_supplierForest_node_125738 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_125738 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125738 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_126384 := by
  decide +kernel

theorem g32p_supplierForest_actual_125738 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125738) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_125738
    g32p_supplierForest_actual_126384

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_120 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_065882 else g32p_supplierForest_node_065890) else (if i.val < 3 then g32p_supplierForest_node_065919 else g32p_supplierForest_node_065940)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_066037 else g32p_supplierForest_node_066047) else (if i.val < 7 then g32p_supplierForest_node_066060 else g32p_supplierForest_node_066068))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_066140 else g32p_supplierForest_node_066169) else (if i.val < 11 then g32p_supplierForest_node_066204 else g32p_supplierForest_node_066232)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_066257 else g32p_supplierForest_node_066258) else (if i.val < 15 then g32p_supplierForest_node_066279 else g32p_supplierForest_node_066308)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_066341 else g32p_supplierForest_node_066362) else (if i.val < 19 then g32p_supplierForest_node_066375 else g32p_supplierForest_node_066398)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_066399 else g32p_supplierForest_node_066411) else (if i.val < 23 then g32p_supplierForest_node_066435 else g32p_supplierForest_node_066464))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_066519 else g32p_supplierForest_node_066524) else (if i.val < 27 then g32p_supplierForest_node_066598 else g32p_supplierForest_node_066628)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_066630 else g32p_supplierForest_node_066632) else (if i.val < 31 then g32p_supplierForest_node_066658 else g32p_supplierForest_node_066662))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_066678 else g32p_supplierForest_node_066689) else (if i.val < 35 then g32p_supplierForest_node_066690 else g32p_supplierForest_node_066722)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_066724 else g32p_supplierForest_node_066785) else (if i.val < 39 then g32p_supplierForest_node_066793 else g32p_supplierForest_node_066822))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_066831 else g32p_supplierForest_node_066840) else (if i.val < 43 then g32p_supplierForest_node_066880 else g32p_supplierForest_node_066938)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_066966 else g32p_supplierForest_node_067011) else (if i.val < 47 then g32p_supplierForest_node_067021 else g32p_supplierForest_node_067029)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_067035 else g32p_supplierForest_node_067077) else (if i.val < 51 then g32p_supplierForest_node_067079 else g32p_supplierForest_node_067115)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_067137 else g32p_supplierForest_node_067163) else (if i.val < 55 then g32p_supplierForest_node_067178 else g32p_supplierForest_node_067196))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_067286 else g32p_supplierForest_node_067303) else (if i.val < 59 then g32p_supplierForest_node_067360 else g32p_supplierForest_node_067372)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_067463 else g32p_supplierForest_node_067481) else (if i.val < 63 then g32p_supplierForest_node_067484 else g32p_supplierForest_node_067546)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_067669 else g32p_supplierForest_node_067688) else (if i.val < 67 then g32p_supplierForest_node_067738 else g32p_supplierForest_node_067790)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_067804 else g32p_supplierForest_node_067830) else (if i.val < 71 then g32p_supplierForest_node_067910 else g32p_supplierForest_node_067920))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_067933 else g32p_supplierForest_node_068013) else (if i.val < 75 then g32p_supplierForest_node_068015 else g32p_supplierForest_node_068021)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_068053 else g32p_supplierForest_node_068113) else (if i.val < 79 then g32p_supplierForest_node_068129 else g32p_supplierForest_node_068215)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_068253 else g32p_supplierForest_node_068281) else (if i.val < 83 then g32p_supplierForest_node_068283 else g32p_supplierForest_node_068285)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_068319 else g32p_supplierForest_node_068327) else (if i.val < 87 then g32p_supplierForest_node_068358 else g32p_supplierForest_node_068372))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_068465 else g32p_supplierForest_node_068473) else (if i.val < 91 then g32p_supplierForest_node_068500 else g32p_supplierForest_node_068538)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_068672 else g32p_supplierForest_node_068703) else (if i.val < 95 then g32p_supplierForest_node_068720 else g32p_supplierForest_node_068734))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_068747 else g32p_supplierForest_node_068757) else (if i.val < 99 then g32p_supplierForest_node_068763 else g32p_supplierForest_node_068785)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_068791 else g32p_supplierForest_node_068802) else (if i.val < 103 then g32p_supplierForest_node_068831 else g32p_supplierForest_node_068843))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_068855 else g32p_supplierForest_node_068886) else (if i.val < 107 then g32p_supplierForest_node_068942 else g32p_supplierForest_node_069010)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_069041 else g32p_supplierForest_node_069055) else (if i.val < 111 then g32p_supplierForest_node_069064 else g32p_supplierForest_node_069100)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_069162 else g32p_supplierForest_node_069170) else (if i.val < 115 then g32p_supplierForest_node_069180 else g32p_supplierForest_node_069197)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_069252 else g32p_supplierForest_node_069256) else (if i.val < 119 then g32p_supplierForest_node_069296 else g32p_supplierForest_node_069306))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_069356 else g32p_supplierForest_node_069421) else (if i.val < 123 then g32p_supplierForest_node_069463 else g32p_supplierForest_node_069464)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_069511 else g32p_supplierForest_node_069614) else (if i.val < 127 then g32p_supplierForest_node_069635 else g32p_supplierForest_node_069667))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_069695 else g32p_supplierForest_node_069697) else (if i.val < 131 then g32p_supplierForest_node_069708 else g32p_supplierForest_node_069874)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_069895 else g32p_supplierForest_node_069907) else (if i.val < 135 then g32p_supplierForest_node_069946 else g32p_supplierForest_node_069956))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_070004 else g32p_supplierForest_node_070045) else (if i.val < 139 then g32p_supplierForest_node_070103 else g32p_supplierForest_node_070108)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_070126 else g32p_supplierForest_node_070147) else (if i.val < 143 then g32p_supplierForest_node_070162 else g32p_supplierForest_node_070189)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_070195 else g32p_supplierForest_node_070305) else (if i.val < 147 then g32p_supplierForest_node_070327 else g32p_supplierForest_node_070329)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_070343 else g32p_supplierForest_node_070359) else (if i.val < 151 then g32p_supplierForest_node_070398 else g32p_supplierForest_node_070500))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_070519 else g32p_supplierForest_node_070524) else (if i.val < 155 then g32p_supplierForest_node_070527 else g32p_supplierForest_node_070534)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_070557 else g32p_supplierForest_node_070678) else (if i.val < 159 then g32p_supplierForest_node_070686 else g32p_supplierForest_node_070695))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_070696 else g32p_supplierForest_node_070813) else (if i.val < 163 then g32p_supplierForest_node_070880 else g32p_supplierForest_node_070901)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_070946 else g32p_supplierForest_node_070952) else (if i.val < 167 then g32p_supplierForest_node_070975 else g32p_supplierForest_node_071051))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_071062 else g32p_supplierForest_node_071069) else (if i.val < 171 then g32p_supplierForest_node_071082 else g32p_supplierForest_node_071102)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_071123 else g32p_supplierForest_node_071164) else (if i.val < 175 then g32p_supplierForest_node_071168 else g32p_supplierForest_node_071197)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_071207 else g32p_supplierForest_node_071280) else (if i.val < 179 then g32p_supplierForest_node_071305 else g32p_supplierForest_node_071313)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_071340 else g32p_supplierForest_node_071343) else (if i.val < 183 then g32p_supplierForest_node_071345 else g32p_supplierForest_node_071359))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_071387 else g32p_supplierForest_node_071431) else (if i.val < 187 then g32p_supplierForest_node_071492 else g32p_supplierForest_node_071498)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_071503 else g32p_supplierForest_node_071511) else (if i.val < 191 then g32p_supplierForest_node_071528 else g32p_supplierForest_node_071650)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_071703 else g32p_supplierForest_node_071787) else (if i.val < 195 then g32p_supplierForest_node_071801 else g32p_supplierForest_node_071863)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_071881 else g32p_supplierForest_node_071886) else (if i.val < 199 then g32p_supplierForest_node_071906 else g32p_supplierForest_node_071923))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_071936 else g32p_supplierForest_node_071982) else (if i.val < 203 then g32p_supplierForest_node_071988 else g32p_supplierForest_node_072004)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_072007 else g32p_supplierForest_node_072011) else (if i.val < 207 then g32p_supplierForest_node_072046 else g32p_supplierForest_node_072083)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_072104 else g32p_supplierForest_node_072135) else (if i.val < 211 then g32p_supplierForest_node_072166 else g32p_supplierForest_node_072170)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_072281 else g32p_supplierForest_node_072298) else (if i.val < 215 then g32p_supplierForest_node_072306 else g32p_supplierForest_node_072318))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_072364 else g32p_supplierForest_node_072367) else (if i.val < 219 then g32p_supplierForest_node_072424 else g32p_supplierForest_node_072471)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_072478 else g32p_supplierForest_node_072565) else (if i.val < 223 then g32p_supplierForest_node_072597 else g32p_supplierForest_node_072621))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_072656 else g32p_supplierForest_node_072674) else (if i.val < 227 then g32p_supplierForest_node_072677 else g32p_supplierForest_node_072678)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_072690 else g32p_supplierForest_node_072712) else (if i.val < 231 then g32p_supplierForest_node_072725 else g32p_supplierForest_node_072747))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_072748 else g32p_supplierForest_node_072845) else (if i.val < 235 then g32p_supplierForest_node_072852 else g32p_supplierForest_node_072869)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_072908 else g32p_supplierForest_node_072911) else (if i.val < 239 then g32p_supplierForest_node_072948 else g32p_supplierForest_node_072973)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_072980 else g32p_supplierForest_node_073013) else (if i.val < 243 then g32p_supplierForest_node_073038 else g32p_supplierForest_node_073056)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_073059 else g32p_supplierForest_node_073104) else (if i.val < 247 then g32p_supplierForest_node_073165 else g32p_supplierForest_node_073187))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_073257 else g32p_supplierForest_node_073319) else (if i.val < 251 then g32p_supplierForest_node_073361 else g32p_supplierForest_node_073400)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_073432 else g32p_supplierForest_node_073439) else (if i.val < 255 then g32p_supplierForest_node_073485 else g32p_supplierForest_node_073511))))))))

def g32p_supplierForest_classes_120 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 38 else 21) else (if i.val < 3 then 38 else 20)) else (if i.val < 6 then (if i.val < 5 then 7 else 20) else (if i.val < 7 then 21 else 75))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 74 else 22) else (if i.val < 11 then 39 else 21)) else (if i.val < 14 then (if i.val < 13 then 70 else 38) else (if i.val < 15 then 74 else 38)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 38 else 75) else (if i.val < 19 then 20 else 21)) else (if i.val < 22 then (if i.val < 21 then 21 else 42) else (if i.val < 23 then 41 else 68))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 21 else 21) else (if i.val < 27 then 73 else 73)) else (if i.val < 30 then (if i.val < 29 then 21 else 73) else (if i.val < 31 then 71 else 75))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 38 else 68) else (if i.val < 35 then 21 else 72)) else (if i.val < 38 then (if i.val < 37 then 71 else 73) else (if i.val < 39 then 40 else 74))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 21 else 22) else (if i.val < 43 then 75 else 21)) else (if i.val < 46 then (if i.val < 45 then 70 else 42) else (if i.val < 47 then 21 else 21)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 43 else 38) else (if i.val < 51 then 38 else 21)) else (if i.val < 54 then (if i.val < 53 then 43 else 38) else (if i.val < 55 then 71 else 21))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 7) else (if i.val < 59 then 68 else 40)) else (if i.val < 62 then (if i.val < 61 then 22 else 41) else (if i.val < 63 then 43 else 21)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 38 else 6) else (if i.val < 67 then 73 else 38)) else (if i.val < 70 then (if i.val < 69 then 38 else 21) else (if i.val < 71 then 38 else 38))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 38 else 21) else (if i.val < 75 then 38 else 20)) else (if i.val < 78 then (if i.val < 77 then 38 else 71) else (if i.val < 79 then 70 else 38)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 74 else 38) else (if i.val < 83 then 74 else 38)) else (if i.val < 86 then (if i.val < 85 then 38 else 21) else (if i.val < 87 then 72 else 43))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 21 else 21) else (if i.val < 91 then 21 else 40)) else (if i.val < 94 then (if i.val < 93 then 73 else 38) else (if i.val < 95 then 38 else 7))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 42 else 42) else (if i.val < 99 then 38 else 22)) else (if i.val < 102 then (if i.val < 101 then 38 else 38) else (if i.val < 103 then 21 else 38))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 21 else 38) else (if i.val < 107 then 38 else 40)) else (if i.val < 110 then (if i.val < 109 then 68 else 21) else (if i.val < 111 then 38 else 21)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 21 else 21) else (if i.val < 115 then 7 else 38)) else (if i.val < 118 then (if i.val < 117 then 38 else 73) else (if i.val < 119 then 38 else 21))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 7 else 38) else (if i.val < 123 then 21 else 21)) else (if i.val < 126 then (if i.val < 125 then 38 else 21) else (if i.val < 127 then 20 else 38))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 38 else 38) else (if i.val < 131 then 21 else 38)) else (if i.val < 134 then (if i.val < 133 then 74 else 68) else (if i.val < 135 then 42 else 38))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 70 else 38) else (if i.val < 139 then 21 else 21)) else (if i.val < 142 then (if i.val < 141 then 20 else 38) else (if i.val < 143 then 22 else 38)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 20 else 40) else (if i.val < 147 then 38 else 38)) else (if i.val < 150 then (if i.val < 149 then 70 else 68) else (if i.val < 151 then 21 else 71))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 38 else 38) else (if i.val < 155 then 38 else 21)) else (if i.val < 158 then (if i.val < 157 then 20 else 74) else (if i.val < 159 then 74 else 43))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 43 else 73) else (if i.val < 163 then 41 else 38)) else (if i.val < 166 then (if i.val < 165 then 42 else 41) else (if i.val < 167 then 21 else 21))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 41 else 70) else (if i.val < 171 then 21 else 21)) else (if i.val < 174 then (if i.val < 173 then 21 else 38) else (if i.val < 175 then 21 else 21)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 20 else 38) else (if i.val < 179 then 71 else 38)) else (if i.val < 182 then (if i.val < 181 then 38 else 71) else (if i.val < 183 then 38 else 73))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 22 else 21) else (if i.val < 187 then 41 else 42)) else (if i.val < 190 then (if i.val < 189 then 71 else 38) else (if i.val < 191 then 38 else 38)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 43 else 55) else (if i.val < 195 then 50 else 47)) else (if i.val < 198 then (if i.val < 197 then 49 else 49) else (if i.val < 199 then 49 else 46))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 49 else 46) else (if i.val < 203 then 49 else 49)) else (if i.val < 206 then (if i.val < 205 then 45 else 10) else (if i.val < 207 then 10 else 12)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 52 else 52) else (if i.val < 211 then 49 else 27)) else (if i.val < 214 then (if i.val < 213 then 46 else 49) else (if i.val < 215 then 49 else 10))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 49 else 49) else (if i.val < 219 then 9 else 46)) else (if i.val < 222 then (if i.val < 221 then 49 else 49) else (if i.val < 223 then 49 else 48))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 10 else 49) else (if i.val < 227 then 12 else 49)) else (if i.val < 230 then (if i.val < 229 then 49 else 46) else (if i.val < 231 then 49 else 26))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 10 else 49) else (if i.val < 235 then 49 else 50)) else (if i.val < 238 then (if i.val < 237 then 49 else 26) else (if i.val < 239 then 50 else 47)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 49 else 47) else (if i.val < 243 then 49 else 49)) else (if i.val < 246 then (if i.val < 245 then 47 else 9) else (if i.val < 247 then 49 else 49))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 46 else 49) else (if i.val < 251 then 47 else 46)) else (if i.val < 254 then (if i.val < 253 then 49 else 50) else (if i.val < 255 then 49 else 46))))))))

theorem g32p_supplierForest_actual_120 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_120 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_120 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_065882
  · exact g32p_supplierForest_actual_065890
  · exact g32p_supplierForest_actual_065919
  · exact g32p_supplierForest_actual_065940
  · exact g32p_supplierForest_actual_066037
  · exact g32p_supplierForest_actual_066047
  · exact g32p_supplierForest_actual_066060
  · exact g32p_supplierForest_actual_066068
  · exact g32p_supplierForest_actual_066140
  · exact g32p_supplierForest_actual_066169
  · exact g32p_supplierForest_actual_066204
  · exact g32p_supplierForest_actual_066232
  · exact g32p_supplierForest_actual_066257
  · exact g32p_supplierForest_actual_066258
  · exact g32p_supplierForest_actual_066279
  · exact g32p_supplierForest_actual_066308
  · exact g32p_supplierForest_actual_066341
  · exact g32p_supplierForest_actual_066362
  · exact g32p_supplierForest_actual_066375
  · exact g32p_supplierForest_actual_066398
  · exact g32p_supplierForest_actual_066399
  · exact g32p_supplierForest_actual_066411
  · exact g32p_supplierForest_actual_066435
  · exact g32p_supplierForest_actual_066464
  · exact g32p_supplierForest_actual_066519
  · exact g32p_supplierForest_actual_066524
  · exact g32p_supplierForest_actual_066598
  · exact g32p_supplierForest_actual_066628
  · exact g32p_supplierForest_actual_066630
  · exact g32p_supplierForest_actual_066632
  · exact g32p_supplierForest_actual_066658
  · exact g32p_supplierForest_actual_066662
  · exact g32p_supplierForest_actual_066678
  · exact g32p_supplierForest_actual_066689
  · exact g32p_supplierForest_actual_066690
  · exact g32p_supplierForest_actual_066722
  · exact g32p_supplierForest_actual_066724
  · exact g32p_supplierForest_actual_066785
  · exact g32p_supplierForest_actual_066793
  · exact g32p_supplierForest_actual_066822
  · exact g32p_supplierForest_actual_066831
  · exact g32p_supplierForest_actual_066840
  · exact g32p_supplierForest_actual_066880
  · exact g32p_supplierForest_actual_066938
  · exact g32p_supplierForest_actual_066966
  · exact g32p_supplierForest_actual_067011
  · exact g32p_supplierForest_actual_067021
  · exact g32p_supplierForest_actual_067029
  · exact g32p_supplierForest_actual_067035
  · exact g32p_supplierForest_actual_067077
  · exact g32p_supplierForest_actual_067079
  · exact g32p_supplierForest_actual_067115
  · exact g32p_supplierForest_actual_067137
  · exact g32p_supplierForest_actual_067163
  · exact g32p_supplierForest_actual_067178
  · exact g32p_supplierForest_actual_067196
  · exact g32p_supplierForest_actual_067286
  · exact g32p_supplierForest_actual_067303
  · exact g32p_supplierForest_actual_067360
  · exact g32p_supplierForest_actual_067372
  · exact g32p_supplierForest_actual_067463
  · exact g32p_supplierForest_actual_067481
  · exact g32p_supplierForest_actual_067484
  · exact g32p_supplierForest_actual_067546
  · exact g32p_supplierForest_actual_067669
  · exact g32p_supplierForest_actual_067688
  · exact g32p_supplierForest_actual_067738
  · exact g32p_supplierForest_actual_067790
  · exact g32p_supplierForest_actual_067804
  · exact g32p_supplierForest_actual_067830
  · exact g32p_supplierForest_actual_067910
  · exact g32p_supplierForest_actual_067920
  · exact g32p_supplierForest_actual_067933
  · exact g32p_supplierForest_actual_068013
  · exact g32p_supplierForest_actual_068015
  · exact g32p_supplierForest_actual_068021
  · exact g32p_supplierForest_actual_068053
  · exact g32p_supplierForest_actual_068113
  · exact g32p_supplierForest_actual_068129
  · exact g32p_supplierForest_actual_068215
  · exact g32p_supplierForest_actual_068253
  · exact g32p_supplierForest_actual_068281
  · exact g32p_supplierForest_actual_068283
  · exact g32p_supplierForest_actual_068285
  · exact g32p_supplierForest_actual_068319
  · exact g32p_supplierForest_actual_068327
  · exact g32p_supplierForest_actual_068358
  · exact g32p_supplierForest_actual_068372
  · exact g32p_supplierForest_actual_068465
  · exact g32p_supplierForest_actual_068473
  · exact g32p_supplierForest_actual_068500
  · exact g32p_supplierForest_actual_068538
  · exact g32p_supplierForest_actual_068672
  · exact g32p_supplierForest_actual_068703
  · exact g32p_supplierForest_actual_068720
  · exact g32p_supplierForest_actual_068734
  · exact g32p_supplierForest_actual_068747
  · exact g32p_supplierForest_actual_068757
  · exact g32p_supplierForest_actual_068763
  · exact g32p_supplierForest_actual_068785
  · exact g32p_supplierForest_actual_068791
  · exact g32p_supplierForest_actual_068802
  · exact g32p_supplierForest_actual_068831
  · exact g32p_supplierForest_actual_068843
  · exact g32p_supplierForest_actual_068855
  · exact g32p_supplierForest_actual_068886
  · exact g32p_supplierForest_actual_068942
  · exact g32p_supplierForest_actual_069010
  · exact g32p_supplierForest_actual_069041
  · exact g32p_supplierForest_actual_069055
  · exact g32p_supplierForest_actual_069064
  · exact g32p_supplierForest_actual_069100
  · exact g32p_supplierForest_actual_069162
  · exact g32p_supplierForest_actual_069170
  · exact g32p_supplierForest_actual_069180
  · exact g32p_supplierForest_actual_069197
  · exact g32p_supplierForest_actual_069252
  · exact g32p_supplierForest_actual_069256
  · exact g32p_supplierForest_actual_069296
  · exact g32p_supplierForest_actual_069306
  · exact g32p_supplierForest_actual_069356
  · exact g32p_supplierForest_actual_069421
  · exact g32p_supplierForest_actual_069463
  · exact g32p_supplierForest_actual_069464
  · exact g32p_supplierForest_actual_069511
  · exact g32p_supplierForest_actual_069614
  · exact g32p_supplierForest_actual_069635
  · exact g32p_supplierForest_actual_069667
  · exact g32p_supplierForest_actual_069695
  · exact g32p_supplierForest_actual_069697
  · exact g32p_supplierForest_actual_069708
  · exact g32p_supplierForest_actual_069874
  · exact g32p_supplierForest_actual_069895
  · exact g32p_supplierForest_actual_069907
  · exact g32p_supplierForest_actual_069946
  · exact g32p_supplierForest_actual_069956
  · exact g32p_supplierForest_actual_070004
  · exact g32p_supplierForest_actual_070045
  · exact g32p_supplierForest_actual_070103
  · exact g32p_supplierForest_actual_070108
  · exact g32p_supplierForest_actual_070126
  · exact g32p_supplierForest_actual_070147
  · exact g32p_supplierForest_actual_070162
  · exact g32p_supplierForest_actual_070189
  · exact g32p_supplierForest_actual_070195
  · exact g32p_supplierForest_actual_070305
  · exact g32p_supplierForest_actual_070327
  · exact g32p_supplierForest_actual_070329
  · exact g32p_supplierForest_actual_070343
  · exact g32p_supplierForest_actual_070359
  · exact g32p_supplierForest_actual_070398
  · exact g32p_supplierForest_actual_070500
  · exact g32p_supplierForest_actual_070519
  · exact g32p_supplierForest_actual_070524
  · exact g32p_supplierForest_actual_070527
  · exact g32p_supplierForest_actual_070534
  · exact g32p_supplierForest_actual_070557
  · exact g32p_supplierForest_actual_070678
  · exact g32p_supplierForest_actual_070686
  · exact g32p_supplierForest_actual_070695
  · exact g32p_supplierForest_actual_070696
  · exact g32p_supplierForest_actual_070813
  · exact g32p_supplierForest_actual_070880
  · exact g32p_supplierForest_actual_070901
  · exact g32p_supplierForest_actual_070946
  · exact g32p_supplierForest_actual_070952
  · exact g32p_supplierForest_actual_070975
  · exact g32p_supplierForest_actual_071051
  · exact g32p_supplierForest_actual_071062
  · exact g32p_supplierForest_actual_071069
  · exact g32p_supplierForest_actual_071082
  · exact g32p_supplierForest_actual_071102
  · exact g32p_supplierForest_actual_071123
  · exact g32p_supplierForest_actual_071164
  · exact g32p_supplierForest_actual_071168
  · exact g32p_supplierForest_actual_071197
  · exact g32p_supplierForest_actual_071207
  · exact g32p_supplierForest_actual_071280
  · exact g32p_supplierForest_actual_071305
  · exact g32p_supplierForest_actual_071313
  · exact g32p_supplierForest_actual_071340
  · exact g32p_supplierForest_actual_071343
  · exact g32p_supplierForest_actual_071345
  · exact g32p_supplierForest_actual_071359
  · exact g32p_supplierForest_actual_071387
  · exact g32p_supplierForest_actual_071431
  · exact g32p_supplierForest_actual_071492
  · exact g32p_supplierForest_actual_071498
  · exact g32p_supplierForest_actual_071503
  · exact g32p_supplierForest_actual_071511
  · exact g32p_supplierForest_actual_071528
  · exact g32p_supplierForest_actual_071650
  · exact g32p_supplierForest_actual_071703
  · exact g32p_supplierForest_actual_071787
  · exact g32p_supplierForest_actual_071801
  · exact g32p_supplierForest_actual_071863
  · exact g32p_supplierForest_actual_071881
  · exact g32p_supplierForest_actual_071886
  · exact g32p_supplierForest_actual_071906
  · exact g32p_supplierForest_actual_071923
  · exact g32p_supplierForest_actual_071936
  · exact g32p_supplierForest_actual_071982
  · exact g32p_supplierForest_actual_071988
  · exact g32p_supplierForest_actual_072004
  · exact g32p_supplierForest_actual_072007
  · exact g32p_supplierForest_actual_072011
  · exact g32p_supplierForest_actual_072046
  · exact g32p_supplierForest_actual_072083
  · exact g32p_supplierForest_actual_072104
  · exact g32p_supplierForest_actual_072135
  · exact g32p_supplierForest_actual_072166
  · exact g32p_supplierForest_actual_072170
  · exact g32p_supplierForest_actual_072281
  · exact g32p_supplierForest_actual_072298
  · exact g32p_supplierForest_actual_072306
  · exact g32p_supplierForest_actual_072318
  · exact g32p_supplierForest_actual_072364
  · exact g32p_supplierForest_actual_072367
  · exact g32p_supplierForest_actual_072424
  · exact g32p_supplierForest_actual_072471
  · exact g32p_supplierForest_actual_072478
  · exact g32p_supplierForest_actual_072565
  · exact g32p_supplierForest_actual_072597
  · exact g32p_supplierForest_actual_072621
  · exact g32p_supplierForest_actual_072656
  · exact g32p_supplierForest_actual_072674
  · exact g32p_supplierForest_actual_072677
  · exact g32p_supplierForest_actual_072678
  · exact g32p_supplierForest_actual_072690
  · exact g32p_supplierForest_actual_072712
  · exact g32p_supplierForest_actual_072725
  · exact g32p_supplierForest_actual_072747
  · exact g32p_supplierForest_actual_072748
  · exact g32p_supplierForest_actual_072845
  · exact g32p_supplierForest_actual_072852
  · exact g32p_supplierForest_actual_072869
  · exact g32p_supplierForest_actual_072908
  · exact g32p_supplierForest_actual_072911
  · exact g32p_supplierForest_actual_072948
  · exact g32p_supplierForest_actual_072973
  · exact g32p_supplierForest_actual_072980
  · exact g32p_supplierForest_actual_073013
  · exact g32p_supplierForest_actual_073038
  · exact g32p_supplierForest_actual_073056
  · exact g32p_supplierForest_actual_073059
  · exact g32p_supplierForest_actual_073104
  · exact g32p_supplierForest_actual_073165
  · exact g32p_supplierForest_actual_073187
  · exact g32p_supplierForest_actual_073257
  · exact g32p_supplierForest_actual_073319
  · exact g32p_supplierForest_actual_073361
  · exact g32p_supplierForest_actual_073400
  · exact g32p_supplierForest_actual_073432
  · exact g32p_supplierForest_actual_073439
  · exact g32p_supplierForest_actual_073485
  · exact g32p_supplierForest_actual_073511

def g32p_supplierForest_nodes_121 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_073539 else g32p_supplierForest_node_073550) else (if i.val < 3 then g32p_supplierForest_node_073569 else g32p_supplierForest_node_073577)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_073599 else g32p_supplierForest_node_073614) else (if i.val < 7 then g32p_supplierForest_node_073625 else g32p_supplierForest_node_073709))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_073719 else g32p_supplierForest_node_073739) else (if i.val < 11 then g32p_supplierForest_node_073762 else g32p_supplierForest_node_073853)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_073856 else g32p_supplierForest_node_073883) else (if i.val < 15 then g32p_supplierForest_node_073890 else g32p_supplierForest_node_073892)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_073922 else g32p_supplierForest_node_073929) else (if i.val < 19 then g32p_supplierForest_node_073950 else g32p_supplierForest_node_073961)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_074033 else g32p_supplierForest_node_074149) else (if i.val < 23 then g32p_supplierForest_node_074150 else g32p_supplierForest_node_074219))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_074370 else g32p_supplierForest_node_074391) else (if i.val < 27 then g32p_supplierForest_node_074494 else g32p_supplierForest_node_074508)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_074515 else g32p_supplierForest_node_074534) else (if i.val < 31 then g32p_supplierForest_node_074557 else g32p_supplierForest_node_074601))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_074648 else g32p_supplierForest_node_074661) else (if i.val < 35 then g32p_supplierForest_node_074687 else g32p_supplierForest_node_074696)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_074698 else g32p_supplierForest_node_074703) else (if i.val < 39 then g32p_supplierForest_node_074754 else g32p_supplierForest_node_074758))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_074776 else g32p_supplierForest_node_074790) else (if i.val < 43 then g32p_supplierForest_node_074859 else g32p_supplierForest_node_074866)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_074926 else g32p_supplierForest_node_074933) else (if i.val < 47 then g32p_supplierForest_node_074940 else g32p_supplierForest_node_074956)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_075003 else g32p_supplierForest_node_075021) else (if i.val < 51 then g32p_supplierForest_node_075030 else g32p_supplierForest_node_075058)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_075073 else g32p_supplierForest_node_075090) else (if i.val < 55 then g32p_supplierForest_node_075095 else g32p_supplierForest_node_075120))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_075260 else g32p_supplierForest_node_075300) else (if i.val < 59 then g32p_supplierForest_node_075309 else g32p_supplierForest_node_075346)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_075356 else g32p_supplierForest_node_075368) else (if i.val < 63 then g32p_supplierForest_node_075413 else g32p_supplierForest_node_075479)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_075499 else g32p_supplierForest_node_075506) else (if i.val < 67 then g32p_supplierForest_node_075551 else g32p_supplierForest_node_075603)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_075619 else g32p_supplierForest_node_075659) else (if i.val < 71 then g32p_supplierForest_node_075706 else g32p_supplierForest_node_075729))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_075762 else g32p_supplierForest_node_075764) else (if i.val < 75 then g32p_supplierForest_node_075805 else g32p_supplierForest_node_075824)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_075861 else g32p_supplierForest_node_075889) else (if i.val < 79 then g32p_supplierForest_node_075984 else g32p_supplierForest_node_076072)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_076121 else g32p_supplierForest_node_076132) else (if i.val < 83 then g32p_supplierForest_node_076134 else g32p_supplierForest_node_076141)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_076172 else g32p_supplierForest_node_076227) else (if i.val < 87 then g32p_supplierForest_node_076283 else g32p_supplierForest_node_076292))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_076307 else g32p_supplierForest_node_076363) else (if i.val < 91 then g32p_supplierForest_node_076365 else g32p_supplierForest_node_076371)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_076383 else g32p_supplierForest_node_076410) else (if i.val < 95 then g32p_supplierForest_node_076431 else g32p_supplierForest_node_076442))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_076445 else g32p_supplierForest_node_076458) else (if i.val < 99 then g32p_supplierForest_node_076485 else g32p_supplierForest_node_076503)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_076512 else g32p_supplierForest_node_076593) else (if i.val < 103 then g32p_supplierForest_node_076630 else g32p_supplierForest_node_076639))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_076649 else g32p_supplierForest_node_076670) else (if i.val < 107 then g32p_supplierForest_node_076676 else g32p_supplierForest_node_076688)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_076713 else g32p_supplierForest_node_076732) else (if i.val < 111 then g32p_supplierForest_node_076748 else g32p_supplierForest_node_076766)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_076804 else g32p_supplierForest_node_076822) else (if i.val < 115 then g32p_supplierForest_node_076832 else g32p_supplierForest_node_076845)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_076853 else g32p_supplierForest_node_076875) else (if i.val < 119 then g32p_supplierForest_node_076907 else g32p_supplierForest_node_076956))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_076961 else g32p_supplierForest_node_077059) else (if i.val < 123 then g32p_supplierForest_node_077169 else g32p_supplierForest_node_077195)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_077213 else g32p_supplierForest_node_077216) else (if i.val < 127 then g32p_supplierForest_node_077227 else g32p_supplierForest_node_077312))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_077318 else g32p_supplierForest_node_077319) else (if i.val < 131 then g32p_supplierForest_node_077344 else g32p_supplierForest_node_077382)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_077384 else g32p_supplierForest_node_077410) else (if i.val < 135 then g32p_supplierForest_node_077425 else g32p_supplierForest_node_077546))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_077572 else g32p_supplierForest_node_077590) else (if i.val < 139 then g32p_supplierForest_node_077625 else g32p_supplierForest_node_077677)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_077678 else g32p_supplierForest_node_077679) else (if i.val < 143 then g32p_supplierForest_node_077685 else g32p_supplierForest_node_077691)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_077720 else g32p_supplierForest_node_077732) else (if i.val < 147 then g32p_supplierForest_node_077770 else g32p_supplierForest_node_077775)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_077786 else g32p_supplierForest_node_077798) else (if i.val < 151 then g32p_supplierForest_node_077799 else g32p_supplierForest_node_077810))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_077831 else g32p_supplierForest_node_077835) else (if i.val < 155 then g32p_supplierForest_node_077873 else g32p_supplierForest_node_077908)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_077972 else g32p_supplierForest_node_077984) else (if i.val < 159 then g32p_supplierForest_node_077995 else g32p_supplierForest_node_078039))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_078046 else g32p_supplierForest_node_078049) else (if i.val < 163 then g32p_supplierForest_node_078053 else g32p_supplierForest_node_078113)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_078146 else g32p_supplierForest_node_078154) else (if i.val < 167 then g32p_supplierForest_node_078166 else g32p_supplierForest_node_078206))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_078229 else g32p_supplierForest_node_078244) else (if i.val < 171 then g32p_supplierForest_node_078265 else g32p_supplierForest_node_078292)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_078360 else g32p_supplierForest_node_078388) else (if i.val < 175 then g32p_supplierForest_node_078445 else g32p_supplierForest_node_078455)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_078562 else g32p_supplierForest_node_078628) else (if i.val < 179 then g32p_supplierForest_node_078629 else g32p_supplierForest_node_078645)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_078703 else g32p_supplierForest_node_078753) else (if i.val < 183 then g32p_supplierForest_node_078780 else g32p_supplierForest_node_078870))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_078906 else g32p_supplierForest_node_078941) else (if i.val < 187 then g32p_supplierForest_node_079014 else g32p_supplierForest_node_079038)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_079044 else g32p_supplierForest_node_079054) else (if i.val < 191 then g32p_supplierForest_node_079073 else g32p_supplierForest_node_079076)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_079082 else g32p_supplierForest_node_079136) else (if i.val < 195 then g32p_supplierForest_node_079166 else g32p_supplierForest_node_079180)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_079239 else g32p_supplierForest_node_079255) else (if i.val < 199 then g32p_supplierForest_node_079308 else g32p_supplierForest_node_079312))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_079322 else g32p_supplierForest_node_079344) else (if i.val < 203 then g32p_supplierForest_node_079351 else g32p_supplierForest_node_079358)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_079368 else g32p_supplierForest_node_079373) else (if i.val < 207 then g32p_supplierForest_node_079393 else g32p_supplierForest_node_079416)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_079425 else g32p_supplierForest_node_079478) else (if i.val < 211 then g32p_supplierForest_node_079502 else g32p_supplierForest_node_079539)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_079549 else g32p_supplierForest_node_079571) else (if i.val < 215 then g32p_supplierForest_node_079572 else g32p_supplierForest_node_079584))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_079709 else g32p_supplierForest_node_079711) else (if i.val < 219 then g32p_supplierForest_node_079825 else g32p_supplierForest_node_079875)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_079879 else g32p_supplierForest_node_079889) else (if i.val < 223 then g32p_supplierForest_node_079920 else g32p_supplierForest_node_079975))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_080008 else g32p_supplierForest_node_080029) else (if i.val < 227 then g32p_supplierForest_node_080066 else g32p_supplierForest_node_080148)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_080162 else g32p_supplierForest_node_080165) else (if i.val < 231 then g32p_supplierForest_node_080221 else g32p_supplierForest_node_080254))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_080269 else g32p_supplierForest_node_080313) else (if i.val < 235 then g32p_supplierForest_node_080319 else g32p_supplierForest_node_080328)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_080346 else g32p_supplierForest_node_080351) else (if i.val < 239 then g32p_supplierForest_node_080358 else g32p_supplierForest_node_080367)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_080376 else g32p_supplierForest_node_080449) else (if i.val < 243 then g32p_supplierForest_node_080486 else g32p_supplierForest_node_080512)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_080515 else g32p_supplierForest_node_080532) else (if i.val < 247 then g32p_supplierForest_node_080556 else g32p_supplierForest_node_080582))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_080596 else g32p_supplierForest_node_080599) else (if i.val < 251 then g32p_supplierForest_node_080606 else g32p_supplierForest_node_080634)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_080647 else g32p_supplierForest_node_080712) else (if i.val < 255 then g32p_supplierForest_node_080713 else g32p_supplierForest_node_080719))))))))

def g32p_supplierForest_classes_121 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 25 else 10) else (if i.val < 3 then 25 else 49)) else (if i.val < 6 then (if i.val < 5 then 26 else 26) else (if i.val < 7 then 46 else 49))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 46 else 25) else (if i.val < 11 then 26 else 49)) else (if i.val < 14 then (if i.val < 13 then 49 else 49) else (if i.val < 15 then 49 else 49)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 49 else 49) else (if i.val < 19 then 26 else 10)) else (if i.val < 22 then (if i.val < 21 then 84 else 9) else (if i.val < 23 then 25 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 46 else 10) else (if i.val < 27 then 46 else 53)) else (if i.val < 30 then (if i.val < 29 then 49 else 26) else (if i.val < 31 then 46 else 46))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 49 else 46) else (if i.val < 35 then 46 else 46)) else (if i.val < 38 then (if i.val < 37 then 47 else 46) else (if i.val < 39 then 26 else 25))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 49 else 9) else (if i.val < 43 then 46 else 46)) else (if i.val < 46 then (if i.val < 45 then 46 else 52) else (if i.val < 47 then 46 else 52)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 55 else 46) else (if i.val < 51 then 49 else 47)) else (if i.val < 54 then (if i.val < 53 then 9 else 46) else (if i.val < 55 then 26 else 25))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 46 else 46) else (if i.val < 59 then 25 else 46)) else (if i.val < 62 then (if i.val < 61 then 50 else 49) else (if i.val < 63 then 49 else 46)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 26 else 26) else (if i.val < 67 then 50 else 47)) else (if i.val < 70 then (if i.val < 69 then 46 else 47) else (if i.val < 71 then 46 else 84))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 49 else 50) else (if i.val < 75 then 49 else 26)) else (if i.val < 78 then (if i.val < 77 then 49 else 49) else (if i.val < 79 then 55 else 54)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 49 else 46) else (if i.val < 83 then 46 else 47)) else (if i.val < 86 then (if i.val < 85 then 46 else 46) else (if i.val < 87 then 84 else 48))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 46 else 49) else (if i.val < 91 then 49 else 46)) else (if i.val < 94 then (if i.val < 93 then 46 else 46) else (if i.val < 95 then 46 else 46))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 46 else 49) else (if i.val < 99 then 49 else 49)) else (if i.val < 102 then (if i.val < 101 then 47 else 47) else (if i.val < 103 then 50 else 47))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 46 else 49) else (if i.val < 107 then 49 else 50)) else (if i.val < 110 then (if i.val < 109 then 9 else 49) else (if i.val < 111 then 12 else 48)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 48 else 46) else (if i.val < 115 then 46 else 47)) else (if i.val < 118 then (if i.val < 117 then 49 else 45) else (if i.val < 119 then 48 else 25))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 55 else 49) else (if i.val < 123 then 46 else 46)) else (if i.val < 126 then (if i.val < 125 then 84 else 46) else (if i.val < 127 then 27 else 49))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 27 else 49) else (if i.val < 131 then 26 else 49)) else (if i.val < 134 then (if i.val < 133 then 9 else 49) else (if i.val < 135 then 49 else 46))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 46 else 49) else (if i.val < 139 then 49 else 49)) else (if i.val < 142 then (if i.val < 141 then 49 else 46) else (if i.val < 143 then 27 else 46)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 49 else 49) else (if i.val < 147 then 10 else 46)) else (if i.val < 150 then (if i.val < 149 then 26 else 49) else (if i.val < 151 then 46 else 46))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 25 else 49) else (if i.val < 155 then 46 else 84)) else (if i.val < 158 then (if i.val < 157 then 48 else 46) else (if i.val < 159 then 26 else 53))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 46 else 46) else (if i.val < 163 then 49 else 26)) else (if i.val < 166 then (if i.val < 165 then 46 else 46) else (if i.val < 167 then 49 else 46))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 46 else 86) else (if i.val < 171 then 46 else 49)) else (if i.val < 174 then (if i.val < 173 then 46 else 49) else (if i.val < 175 then 50 else 49)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 46 else 46) else (if i.val < 179 then 45 else 9)) else (if i.val < 182 then (if i.val < 181 then 86 else 26) else (if i.val < 183 then 46 else 49))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 46 else 10) else (if i.val < 187 then 26 else 46)) else (if i.val < 190 then (if i.val < 189 then 46 else 49) else (if i.val < 191 then 49 else 45)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 26 else 26) else (if i.val < 195 then 49 else 26)) else (if i.val < 198 then (if i.val < 197 then 49 else 50) else (if i.val < 199 then 26 else 49))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 46 else 46) else (if i.val < 203 then 49 else 49)) else (if i.val < 206 then (if i.val < 205 then 47 else 46) else (if i.val < 207 then 49 else 54)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 49 else 46) else (if i.val < 211 then 26 else 49)) else (if i.val < 214 then (if i.val < 213 then 48 else 46) else (if i.val < 215 then 46 else 85))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 49 else 49) else (if i.val < 219 then 26 else 50)) else (if i.val < 222 then (if i.val < 221 then 49 else 25) else (if i.val < 223 then 26 else 46))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 46 else 46) else (if i.val < 227 then 46 else 47)) else (if i.val < 230 then (if i.val < 229 then 26 else 53) else (if i.val < 231 then 46 else 46))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 50 else 46) else (if i.val < 235 then 25 else 9)) else (if i.val < 238 then (if i.val < 237 then 49 else 46) else (if i.val < 239 then 46 else 46)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 46 else 27) else (if i.val < 243 then 49 else 49)) else (if i.val < 246 then (if i.val < 245 then 46 else 46) else (if i.val < 247 then 49 else 46))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 47 else 49) else (if i.val < 251 then 49 else 46)) else (if i.val < 254 then (if i.val < 253 then 49 else 50) else (if i.val < 255 then 49 else 49))))))))

theorem g32p_supplierForest_actual_121 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_121 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_121 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_073539
  · exact g32p_supplierForest_actual_073550
  · exact g32p_supplierForest_actual_073569
  · exact g32p_supplierForest_actual_073577
  · exact g32p_supplierForest_actual_073599
  · exact g32p_supplierForest_actual_073614
  · exact g32p_supplierForest_actual_073625
  · exact g32p_supplierForest_actual_073709
  · exact g32p_supplierForest_actual_073719
  · exact g32p_supplierForest_actual_073739
  · exact g32p_supplierForest_actual_073762
  · exact g32p_supplierForest_actual_073853
  · exact g32p_supplierForest_actual_073856
  · exact g32p_supplierForest_actual_073883
  · exact g32p_supplierForest_actual_073890
  · exact g32p_supplierForest_actual_073892
  · exact g32p_supplierForest_actual_073922
  · exact g32p_supplierForest_actual_073929
  · exact g32p_supplierForest_actual_073950
  · exact g32p_supplierForest_actual_073961
  · exact g32p_supplierForest_actual_074033
  · exact g32p_supplierForest_actual_074149
  · exact g32p_supplierForest_actual_074150
  · exact g32p_supplierForest_actual_074219
  · exact g32p_supplierForest_actual_074370
  · exact g32p_supplierForest_actual_074391
  · exact g32p_supplierForest_actual_074494
  · exact g32p_supplierForest_actual_074508
  · exact g32p_supplierForest_actual_074515
  · exact g32p_supplierForest_actual_074534
  · exact g32p_supplierForest_actual_074557
  · exact g32p_supplierForest_actual_074601
  · exact g32p_supplierForest_actual_074648
  · exact g32p_supplierForest_actual_074661
  · exact g32p_supplierForest_actual_074687
  · exact g32p_supplierForest_actual_074696
  · exact g32p_supplierForest_actual_074698
  · exact g32p_supplierForest_actual_074703
  · exact g32p_supplierForest_actual_074754
  · exact g32p_supplierForest_actual_074758
  · exact g32p_supplierForest_actual_074776
  · exact g32p_supplierForest_actual_074790
  · exact g32p_supplierForest_actual_074859
  · exact g32p_supplierForest_actual_074866
  · exact g32p_supplierForest_actual_074926
  · exact g32p_supplierForest_actual_074933
  · exact g32p_supplierForest_actual_074940
  · exact g32p_supplierForest_actual_074956
  · exact g32p_supplierForest_actual_075003
  · exact g32p_supplierForest_actual_075021
  · exact g32p_supplierForest_actual_075030
  · exact g32p_supplierForest_actual_075058
  · exact g32p_supplierForest_actual_075073
  · exact g32p_supplierForest_actual_075090
  · exact g32p_supplierForest_actual_075095
  · exact g32p_supplierForest_actual_075120
  · exact g32p_supplierForest_actual_075260
  · exact g32p_supplierForest_actual_075300
  · exact g32p_supplierForest_actual_075309
  · exact g32p_supplierForest_actual_075346
  · exact g32p_supplierForest_actual_075356
  · exact g32p_supplierForest_actual_075368
  · exact g32p_supplierForest_actual_075413
  · exact g32p_supplierForest_actual_075479
  · exact g32p_supplierForest_actual_075499
  · exact g32p_supplierForest_actual_075506
  · exact g32p_supplierForest_actual_075551
  · exact g32p_supplierForest_actual_075603
  · exact g32p_supplierForest_actual_075619
  · exact g32p_supplierForest_actual_075659
  · exact g32p_supplierForest_actual_075706
  · exact g32p_supplierForest_actual_075729
  · exact g32p_supplierForest_actual_075762
  · exact g32p_supplierForest_actual_075764
  · exact g32p_supplierForest_actual_075805
  · exact g32p_supplierForest_actual_075824
  · exact g32p_supplierForest_actual_075861
  · exact g32p_supplierForest_actual_075889
  · exact g32p_supplierForest_actual_075984
  · exact g32p_supplierForest_actual_076072
  · exact g32p_supplierForest_actual_076121
  · exact g32p_supplierForest_actual_076132
  · exact g32p_supplierForest_actual_076134
  · exact g32p_supplierForest_actual_076141
  · exact g32p_supplierForest_actual_076172
  · exact g32p_supplierForest_actual_076227
  · exact g32p_supplierForest_actual_076283
  · exact g32p_supplierForest_actual_076292
  · exact g32p_supplierForest_actual_076307
  · exact g32p_supplierForest_actual_076363
  · exact g32p_supplierForest_actual_076365
  · exact g32p_supplierForest_actual_076371
  · exact g32p_supplierForest_actual_076383
  · exact g32p_supplierForest_actual_076410
  · exact g32p_supplierForest_actual_076431
  · exact g32p_supplierForest_actual_076442
  · exact g32p_supplierForest_actual_076445
  · exact g32p_supplierForest_actual_076458
  · exact g32p_supplierForest_actual_076485
  · exact g32p_supplierForest_actual_076503
  · exact g32p_supplierForest_actual_076512
  · exact g32p_supplierForest_actual_076593
  · exact g32p_supplierForest_actual_076630
  · exact g32p_supplierForest_actual_076639
  · exact g32p_supplierForest_actual_076649
  · exact g32p_supplierForest_actual_076670
  · exact g32p_supplierForest_actual_076676
  · exact g32p_supplierForest_actual_076688
  · exact g32p_supplierForest_actual_076713
  · exact g32p_supplierForest_actual_076732
  · exact g32p_supplierForest_actual_076748
  · exact g32p_supplierForest_actual_076766
  · exact g32p_supplierForest_actual_076804
  · exact g32p_supplierForest_actual_076822
  · exact g32p_supplierForest_actual_076832
  · exact g32p_supplierForest_actual_076845
  · exact g32p_supplierForest_actual_076853
  · exact g32p_supplierForest_actual_076875
  · exact g32p_supplierForest_actual_076907
  · exact g32p_supplierForest_actual_076956
  · exact g32p_supplierForest_actual_076961
  · exact g32p_supplierForest_actual_077059
  · exact g32p_supplierForest_actual_077169
  · exact g32p_supplierForest_actual_077195
  · exact g32p_supplierForest_actual_077213
  · exact g32p_supplierForest_actual_077216
  · exact g32p_supplierForest_actual_077227
  · exact g32p_supplierForest_actual_077312
  · exact g32p_supplierForest_actual_077318
  · exact g32p_supplierForest_actual_077319
  · exact g32p_supplierForest_actual_077344
  · exact g32p_supplierForest_actual_077382
  · exact g32p_supplierForest_actual_077384
  · exact g32p_supplierForest_actual_077410
  · exact g32p_supplierForest_actual_077425
  · exact g32p_supplierForest_actual_077546
  · exact g32p_supplierForest_actual_077572
  · exact g32p_supplierForest_actual_077590
  · exact g32p_supplierForest_actual_077625
  · exact g32p_supplierForest_actual_077677
  · exact g32p_supplierForest_actual_077678
  · exact g32p_supplierForest_actual_077679
  · exact g32p_supplierForest_actual_077685
  · exact g32p_supplierForest_actual_077691
  · exact g32p_supplierForest_actual_077720
  · exact g32p_supplierForest_actual_077732
  · exact g32p_supplierForest_actual_077770
  · exact g32p_supplierForest_actual_077775
  · exact g32p_supplierForest_actual_077786
  · exact g32p_supplierForest_actual_077798
  · exact g32p_supplierForest_actual_077799
  · exact g32p_supplierForest_actual_077810
  · exact g32p_supplierForest_actual_077831
  · exact g32p_supplierForest_actual_077835
  · exact g32p_supplierForest_actual_077873
  · exact g32p_supplierForest_actual_077908
  · exact g32p_supplierForest_actual_077972
  · exact g32p_supplierForest_actual_077984
  · exact g32p_supplierForest_actual_077995
  · exact g32p_supplierForest_actual_078039
  · exact g32p_supplierForest_actual_078046
  · exact g32p_supplierForest_actual_078049
  · exact g32p_supplierForest_actual_078053
  · exact g32p_supplierForest_actual_078113
  · exact g32p_supplierForest_actual_078146
  · exact g32p_supplierForest_actual_078154
  · exact g32p_supplierForest_actual_078166
  · exact g32p_supplierForest_actual_078206
  · exact g32p_supplierForest_actual_078229
  · exact g32p_supplierForest_actual_078244
  · exact g32p_supplierForest_actual_078265
  · exact g32p_supplierForest_actual_078292
  · exact g32p_supplierForest_actual_078360
  · exact g32p_supplierForest_actual_078388
  · exact g32p_supplierForest_actual_078445
  · exact g32p_supplierForest_actual_078455
  · exact g32p_supplierForest_actual_078562
  · exact g32p_supplierForest_actual_078628
  · exact g32p_supplierForest_actual_078629
  · exact g32p_supplierForest_actual_078645
  · exact g32p_supplierForest_actual_078703
  · exact g32p_supplierForest_actual_078753
  · exact g32p_supplierForest_actual_078780
  · exact g32p_supplierForest_actual_078870
  · exact g32p_supplierForest_actual_078906
  · exact g32p_supplierForest_actual_078941
  · exact g32p_supplierForest_actual_079014
  · exact g32p_supplierForest_actual_079038
  · exact g32p_supplierForest_actual_079044
  · exact g32p_supplierForest_actual_079054
  · exact g32p_supplierForest_actual_079073
  · exact g32p_supplierForest_actual_079076
  · exact g32p_supplierForest_actual_079082
  · exact g32p_supplierForest_actual_079136
  · exact g32p_supplierForest_actual_079166
  · exact g32p_supplierForest_actual_079180
  · exact g32p_supplierForest_actual_079239
  · exact g32p_supplierForest_actual_079255
  · exact g32p_supplierForest_actual_079308
  · exact g32p_supplierForest_actual_079312
  · exact g32p_supplierForest_actual_079322
  · exact g32p_supplierForest_actual_079344
  · exact g32p_supplierForest_actual_079351
  · exact g32p_supplierForest_actual_079358
  · exact g32p_supplierForest_actual_079368
  · exact g32p_supplierForest_actual_079373
  · exact g32p_supplierForest_actual_079393
  · exact g32p_supplierForest_actual_079416
  · exact g32p_supplierForest_actual_079425
  · exact g32p_supplierForest_actual_079478
  · exact g32p_supplierForest_actual_079502
  · exact g32p_supplierForest_actual_079539
  · exact g32p_supplierForest_actual_079549
  · exact g32p_supplierForest_actual_079571
  · exact g32p_supplierForest_actual_079572
  · exact g32p_supplierForest_actual_079584
  · exact g32p_supplierForest_actual_079709
  · exact g32p_supplierForest_actual_079711
  · exact g32p_supplierForest_actual_079825
  · exact g32p_supplierForest_actual_079875
  · exact g32p_supplierForest_actual_079879
  · exact g32p_supplierForest_actual_079889
  · exact g32p_supplierForest_actual_079920
  · exact g32p_supplierForest_actual_079975
  · exact g32p_supplierForest_actual_080008
  · exact g32p_supplierForest_actual_080029
  · exact g32p_supplierForest_actual_080066
  · exact g32p_supplierForest_actual_080148
  · exact g32p_supplierForest_actual_080162
  · exact g32p_supplierForest_actual_080165
  · exact g32p_supplierForest_actual_080221
  · exact g32p_supplierForest_actual_080254
  · exact g32p_supplierForest_actual_080269
  · exact g32p_supplierForest_actual_080313
  · exact g32p_supplierForest_actual_080319
  · exact g32p_supplierForest_actual_080328
  · exact g32p_supplierForest_actual_080346
  · exact g32p_supplierForest_actual_080351
  · exact g32p_supplierForest_actual_080358
  · exact g32p_supplierForest_actual_080367
  · exact g32p_supplierForest_actual_080376
  · exact g32p_supplierForest_actual_080449
  · exact g32p_supplierForest_actual_080486
  · exact g32p_supplierForest_actual_080512
  · exact g32p_supplierForest_actual_080515
  · exact g32p_supplierForest_actual_080532
  · exact g32p_supplierForest_actual_080556
  · exact g32p_supplierForest_actual_080582
  · exact g32p_supplierForest_actual_080596
  · exact g32p_supplierForest_actual_080599
  · exact g32p_supplierForest_actual_080606
  · exact g32p_supplierForest_actual_080634
  · exact g32p_supplierForest_actual_080647
  · exact g32p_supplierForest_actual_080712
  · exact g32p_supplierForest_actual_080713
  · exact g32p_supplierForest_actual_080719

def g32p_supplierForest_nodes_122 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_080721 else g32p_supplierForest_node_080786) else (if i.val < 3 then g32p_supplierForest_node_080807 else g32p_supplierForest_node_080873)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_080893 else g32p_supplierForest_node_080937) else (if i.val < 7 then g32p_supplierForest_node_080941 else g32p_supplierForest_node_080944))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_081020 else g32p_supplierForest_node_081027) else (if i.val < 11 then g32p_supplierForest_node_081030 else g32p_supplierForest_node_081089)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_081091 else g32p_supplierForest_node_081129) else (if i.val < 15 then g32p_supplierForest_node_081223 else g32p_supplierForest_node_081242)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_081259 else g32p_supplierForest_node_081290) else (if i.val < 19 then g32p_supplierForest_node_081515 else g32p_supplierForest_node_081569)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_081570 else g32p_supplierForest_node_081580) else (if i.val < 23 then g32p_supplierForest_node_081618 else g32p_supplierForest_node_081656))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_081671 else g32p_supplierForest_node_081683) else (if i.val < 27 then g32p_supplierForest_node_081721 else g32p_supplierForest_node_081802)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_081813 else g32p_supplierForest_node_081842) else (if i.val < 31 then g32p_supplierForest_node_081882 else g32p_supplierForest_node_081903))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_081995 else g32p_supplierForest_node_082037) else (if i.val < 35 then g32p_supplierForest_node_082071 else g32p_supplierForest_node_082075)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_082094 else g32p_supplierForest_node_082120) else (if i.val < 39 then g32p_supplierForest_node_082123 else g32p_supplierForest_node_082136))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_082144 else g32p_supplierForest_node_082154) else (if i.val < 43 then g32p_supplierForest_node_082180 else g32p_supplierForest_node_082201)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_082241 else g32p_supplierForest_node_082259) else (if i.val < 47 then g32p_supplierForest_node_082261 else g32p_supplierForest_node_082264)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_082277 else g32p_supplierForest_node_082280) else (if i.val < 51 then g32p_supplierForest_node_082318 else g32p_supplierForest_node_082338)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_082449 else g32p_supplierForest_node_082479) else (if i.val < 55 then g32p_supplierForest_node_082501 else g32p_supplierForest_node_082521))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_082526 else g32p_supplierForest_node_082613) else (if i.val < 59 then g32p_supplierForest_node_082699 else g32p_supplierForest_node_082733)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_082768 else g32p_supplierForest_node_082780) else (if i.val < 63 then g32p_supplierForest_node_082829 else g32p_supplierForest_node_082836)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_082856 else g32p_supplierForest_node_082861) else (if i.val < 67 then g32p_supplierForest_node_082877 else g32p_supplierForest_node_082897)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_082919 else g32p_supplierForest_node_082946) else (if i.val < 71 then g32p_supplierForest_node_082972 else g32p_supplierForest_node_082979))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_082990 else g32p_supplierForest_node_083030) else (if i.val < 75 then g32p_supplierForest_node_083032 else g32p_supplierForest_node_083037)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_083145 else g32p_supplierForest_node_083148) else (if i.val < 79 then g32p_supplierForest_node_083336 else g32p_supplierForest_node_083361)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_083425 else g32p_supplierForest_node_083463) else (if i.val < 83 then g32p_supplierForest_node_083491 else g32p_supplierForest_node_083526)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_083540 else g32p_supplierForest_node_083591) else (if i.val < 87 then g32p_supplierForest_node_083599 else g32p_supplierForest_node_083605))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_083728 else g32p_supplierForest_node_083734) else (if i.val < 91 then g32p_supplierForest_node_083754 else g32p_supplierForest_node_083775)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_083811 else g32p_supplierForest_node_083814) else (if i.val < 95 then g32p_supplierForest_node_083816 else g32p_supplierForest_node_083832))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_083962 else g32p_supplierForest_node_084006) else (if i.val < 99 then g32p_supplierForest_node_084009 else g32p_supplierForest_node_084021)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_084029 else g32p_supplierForest_node_084074) else (if i.val < 103 then g32p_supplierForest_node_084135 else g32p_supplierForest_node_084223))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_084229 else g32p_supplierForest_node_084233) else (if i.val < 107 then g32p_supplierForest_node_084309 else g32p_supplierForest_node_084380)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_084409 else g32p_supplierForest_node_084440) else (if i.val < 111 then g32p_supplierForest_node_084490 else g32p_supplierForest_node_084496)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_084497 else g32p_supplierForest_node_084516) else (if i.val < 115 then g32p_supplierForest_node_084542 else g32p_supplierForest_node_084566)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_084623 else g32p_supplierForest_node_084631) else (if i.val < 119 then g32p_supplierForest_node_084643 else g32p_supplierForest_node_084659))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_084683 else g32p_supplierForest_node_084727) else (if i.val < 123 then g32p_supplierForest_node_084825 else g32p_supplierForest_node_084860)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_084878 else g32p_supplierForest_node_085044) else (if i.val < 127 then g32p_supplierForest_node_085048 else g32p_supplierForest_node_085054))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_085057 else g32p_supplierForest_node_085060) else (if i.val < 131 then g32p_supplierForest_node_085064 else g32p_supplierForest_node_085070)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_085141 else g32p_supplierForest_node_085154) else (if i.val < 135 then g32p_supplierForest_node_085190 else g32p_supplierForest_node_085200))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_085203 else g32p_supplierForest_node_085219) else (if i.val < 139 then g32p_supplierForest_node_085272 else g32p_supplierForest_node_085287)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_085343 else g32p_supplierForest_node_085349) else (if i.val < 143 then g32p_supplierForest_node_085355 else g32p_supplierForest_node_085356)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_085362 else g32p_supplierForest_node_085368) else (if i.val < 147 then g32p_supplierForest_node_085376 else g32p_supplierForest_node_085419)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_085424 else g32p_supplierForest_node_085457) else (if i.val < 151 then g32p_supplierForest_node_085490 else g32p_supplierForest_node_085504))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_085552 else g32p_supplierForest_node_085562) else (if i.val < 155 then g32p_supplierForest_node_085574 else g32p_supplierForest_node_085575)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_085577 else g32p_supplierForest_node_085603) else (if i.val < 159 then g32p_supplierForest_node_085605 else g32p_supplierForest_node_085624))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_085639 else g32p_supplierForest_node_085710) else (if i.val < 163 then g32p_supplierForest_node_085730 else g32p_supplierForest_node_085748)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_085754 else g32p_supplierForest_node_085802) else (if i.val < 167 then g32p_supplierForest_node_085823 else g32p_supplierForest_node_085899))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_085921 else g32p_supplierForest_node_085945) else (if i.val < 171 then g32p_supplierForest_node_085957 else g32p_supplierForest_node_085982)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_085985 else g32p_supplierForest_node_085999) else (if i.val < 175 then g32p_supplierForest_node_086065 else g32p_supplierForest_node_086078)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_086092 else g32p_supplierForest_node_086124) else (if i.val < 179 then g32p_supplierForest_node_086127 else g32p_supplierForest_node_086134)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_086149 else g32p_supplierForest_node_086205) else (if i.val < 183 then g32p_supplierForest_node_086251 else g32p_supplierForest_node_086281))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_086425 else g32p_supplierForest_node_086461) else (if i.val < 187 then g32p_supplierForest_node_086489 else g32p_supplierForest_node_086516)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_086559 else g32p_supplierForest_node_086624) else (if i.val < 191 then g32p_supplierForest_node_086695 else g32p_supplierForest_node_086705)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_086707 else g32p_supplierForest_node_086718) else (if i.val < 195 then g32p_supplierForest_node_086777 else g32p_supplierForest_node_086813)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_086827 else g32p_supplierForest_node_086891) else (if i.val < 199 then g32p_supplierForest_node_086916 else g32p_supplierForest_node_086950))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_086982 else g32p_supplierForest_node_086993) else (if i.val < 203 then g32p_supplierForest_node_087007 else g32p_supplierForest_node_087012)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_087028 else g32p_supplierForest_node_087071) else (if i.val < 207 then g32p_supplierForest_node_087080 else g32p_supplierForest_node_087092)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_087098 else g32p_supplierForest_node_087158) else (if i.val < 211 then g32p_supplierForest_node_087165 else g32p_supplierForest_node_087187)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_087223 else g32p_supplierForest_node_087227) else (if i.val < 215 then g32p_supplierForest_node_087232 else g32p_supplierForest_node_087233))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_087248 else g32p_supplierForest_node_087280) else (if i.val < 219 then g32p_supplierForest_node_087283 else g32p_supplierForest_node_087292)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_087319 else g32p_supplierForest_node_087328) else (if i.val < 223 then g32p_supplierForest_node_087487 else g32p_supplierForest_node_087521))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_087523 else g32p_supplierForest_node_087555) else (if i.val < 227 then g32p_supplierForest_node_087557 else g32p_supplierForest_node_087619)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_087639 else g32p_supplierForest_node_087644) else (if i.val < 231 then g32p_supplierForest_node_087684 else g32p_supplierForest_node_087720))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_087771 else g32p_supplierForest_node_087827) else (if i.val < 235 then g32p_supplierForest_node_087861 else g32p_supplierForest_node_087883)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_087943 else g32p_supplierForest_node_087990) else (if i.val < 239 then g32p_supplierForest_node_088009 else g32p_supplierForest_node_088019)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_088023 else g32p_supplierForest_node_088039) else (if i.val < 243 then g32p_supplierForest_node_088077 else g32p_supplierForest_node_088104)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_088140 else g32p_supplierForest_node_088154) else (if i.val < 247 then g32p_supplierForest_node_088195 else g32p_supplierForest_node_088198))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_088219 else g32p_supplierForest_node_088231) else (if i.val < 251 then g32p_supplierForest_node_088271 else g32p_supplierForest_node_088272)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_088281 else g32p_supplierForest_node_088293) else (if i.val < 255 then g32p_supplierForest_node_088333 else g32p_supplierForest_node_088336))))))))

def g32p_supplierForest_classes_122 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 80 else 27) else (if i.val < 3 then 26 else 25)) else (if i.val < 6 then (if i.val < 5 then 46 else 82) else (if i.val < 7 then 50 else 80))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 46 else 49) else (if i.val < 11 then 50 else 26)) else (if i.val < 14 then (if i.val < 13 then 46 else 46) else (if i.val < 15 then 26 else 49)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 46 else 49) else (if i.val < 19 then 50 else 49)) else (if i.val < 22 then (if i.val < 21 then 50 else 49) else (if i.val < 23 then 46 else 49))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 12) else (if i.val < 27 then 50 else 46)) else (if i.val < 30 then (if i.val < 29 then 46 else 49) else (if i.val < 31 then 12 else 46))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 47 else 46) else (if i.val < 35 then 26 else 49)) else (if i.val < 38 then (if i.val < 37 then 46 else 46) else (if i.val < 39 then 46 else 26))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 47 else 49) else (if i.val < 43 then 50 else 49)) else (if i.val < 46 then (if i.val < 45 then 49 else 47) else (if i.val < 47 then 49 else 48)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 47 else 50) else (if i.val < 51 then 49 else 46)) else (if i.val < 54 then (if i.val < 53 then 26 else 49) else (if i.val < 55 then 49 else 49))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 50 else 46) else (if i.val < 59 then 46 else 47)) else (if i.val < 62 then (if i.val < 61 then 26 else 49) else (if i.val < 63 then 46 else 12)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 49) else (if i.val < 67 then 46 else 26)) else (if i.val < 70 then (if i.val < 69 then 49 else 49) else (if i.val < 71 then 54 else 49))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 49 else 49) else (if i.val < 75 then 49 else 47)) else (if i.val < 78 then (if i.val < 77 then 49 else 49) else (if i.val < 79 then 46 else 46)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 49 else 50) else (if i.val < 83 then 49 else 49)) else (if i.val < 86 then (if i.val < 85 then 26 else 85) else (if i.val < 87 then 49 else 80))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 46 else 46) else (if i.val < 91 then 46 else 45)) else (if i.val < 94 then (if i.val < 93 then 49 else 25) else (if i.val < 95 then 49 else 12))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 50 else 49) else (if i.val < 99 then 50 else 26)) else (if i.val < 102 then (if i.val < 101 then 46 else 50) else (if i.val < 103 then 25 else 48))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 46 else 25) else (if i.val < 107 then 80 else 46)) else (if i.val < 110 then (if i.val < 109 then 46 else 47) else (if i.val < 111 then 50 else 46)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 46 else 46) else (if i.val < 115 then 26 else 25)) else (if i.val < 118 then (if i.val < 117 then 49 else 49) else (if i.val < 119 then 26 else 49))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 25 else 26) else (if i.val < 123 then 49 else 49)) else (if i.val < 126 then (if i.val < 125 then 46 else 49) else (if i.val < 127 then 49 else 49))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 54 else 49) else (if i.val < 131 then 49 else 55)) else (if i.val < 134 then (if i.val < 133 then 52 else 26) else (if i.val < 135 then 46 else 25))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 26 else 49) else (if i.val < 139 then 46 else 47)) else (if i.val < 142 then (if i.val < 141 then 46 else 80) else (if i.val < 143 then 46 else 46)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 46 else 26) else (if i.val < 147 then 49 else 12)) else (if i.val < 150 then (if i.val < 149 then 50 else 26) else (if i.val < 151 then 80 else 49))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 55 else 46) else (if i.val < 155 then 49 else 46)) else (if i.val < 158 then (if i.val < 157 then 50 else 46) else (if i.val < 159 then 25 else 49))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 46 else 9) else (if i.val < 163 then 26 else 46)) else (if i.val < 166 then (if i.val < 165 then 46 else 46) else (if i.val < 167 then 49 else 26))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 49 else 49) else (if i.val < 171 then 46 else 47)) else (if i.val < 174 then (if i.val < 173 then 46 else 49) else (if i.val < 175 then 55 else 50)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 49 else 46) else (if i.val < 179 then 47 else 9)) else (if i.val < 182 then (if i.val < 181 then 46 else 49) else (if i.val < 183 then 84 else 47))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 49 else 49) else (if i.val < 187 then 27 else 26)) else (if i.val < 190 then (if i.val < 189 then 55 else 46) else (if i.val < 191 then 49 else 49)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 12 else 25) else (if i.val < 195 then 46 else 46)) else (if i.val < 198 then (if i.val < 197 then 46 else 49) else (if i.val < 199 then 49 else 49))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 47 else 49) else (if i.val < 203 then 53 else 49)) else (if i.val < 206 then (if i.val < 205 then 46 else 46) else (if i.val < 207 then 49 else 49)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 80 else 55) else (if i.val < 211 then 53 else 47)) else (if i.val < 214 then (if i.val < 213 then 49 else 49) else (if i.val < 215 then 49 else 26))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 53 else 49) else (if i.val < 219 then 47 else 49)) else (if i.val < 222 then (if i.val < 221 then 55 else 55) else (if i.val < 223 then 46 else 49))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 86 else 49) else (if i.val < 227 then 49 else 48)) else (if i.val < 230 then (if i.val < 229 then 46 else 49) else (if i.val < 231 then 50 else 49))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 48 else 47) else (if i.val < 235 then 47 else 54)) else (if i.val < 238 then (if i.val < 237 then 49 else 80) else (if i.val < 239 then 49 else 49)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 49 else 54) else (if i.val < 243 then 49 else 47)) else (if i.val < 246 then (if i.val < 245 then 12 else 49) else (if i.val < 247 then 55 else 46))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 25 else 25) else (if i.val < 251 then 49 else 50)) else (if i.val < 254 then (if i.val < 253 then 9 else 49) else (if i.val < 255 then 49 else 49))))))))

theorem g32p_supplierForest_actual_122 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_122 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_122 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_080721
  · exact g32p_supplierForest_actual_080786
  · exact g32p_supplierForest_actual_080807
  · exact g32p_supplierForest_actual_080873
  · exact g32p_supplierForest_actual_080893
  · exact g32p_supplierForest_actual_080937
  · exact g32p_supplierForest_actual_080941
  · exact g32p_supplierForest_actual_080944
  · exact g32p_supplierForest_actual_081020
  · exact g32p_supplierForest_actual_081027
  · exact g32p_supplierForest_actual_081030
  · exact g32p_supplierForest_actual_081089
  · exact g32p_supplierForest_actual_081091
  · exact g32p_supplierForest_actual_081129
  · exact g32p_supplierForest_actual_081223
  · exact g32p_supplierForest_actual_081242
  · exact g32p_supplierForest_actual_081259
  · exact g32p_supplierForest_actual_081290
  · exact g32p_supplierForest_actual_081515
  · exact g32p_supplierForest_actual_081569
  · exact g32p_supplierForest_actual_081570
  · exact g32p_supplierForest_actual_081580
  · exact g32p_supplierForest_actual_081618
  · exact g32p_supplierForest_actual_081656
  · exact g32p_supplierForest_actual_081671
  · exact g32p_supplierForest_actual_081683
  · exact g32p_supplierForest_actual_081721
  · exact g32p_supplierForest_actual_081802
  · exact g32p_supplierForest_actual_081813
  · exact g32p_supplierForest_actual_081842
  · exact g32p_supplierForest_actual_081882
  · exact g32p_supplierForest_actual_081903
  · exact g32p_supplierForest_actual_081995
  · exact g32p_supplierForest_actual_082037
  · exact g32p_supplierForest_actual_082071
  · exact g32p_supplierForest_actual_082075
  · exact g32p_supplierForest_actual_082094
  · exact g32p_supplierForest_actual_082120
  · exact g32p_supplierForest_actual_082123
  · exact g32p_supplierForest_actual_082136
  · exact g32p_supplierForest_actual_082144
  · exact g32p_supplierForest_actual_082154
  · exact g32p_supplierForest_actual_082180
  · exact g32p_supplierForest_actual_082201
  · exact g32p_supplierForest_actual_082241
  · exact g32p_supplierForest_actual_082259
  · exact g32p_supplierForest_actual_082261
  · exact g32p_supplierForest_actual_082264
  · exact g32p_supplierForest_actual_082277
  · exact g32p_supplierForest_actual_082280
  · exact g32p_supplierForest_actual_082318
  · exact g32p_supplierForest_actual_082338
  · exact g32p_supplierForest_actual_082449
  · exact g32p_supplierForest_actual_082479
  · exact g32p_supplierForest_actual_082501
  · exact g32p_supplierForest_actual_082521
  · exact g32p_supplierForest_actual_082526
  · exact g32p_supplierForest_actual_082613
  · exact g32p_supplierForest_actual_082699
  · exact g32p_supplierForest_actual_082733
  · exact g32p_supplierForest_actual_082768
  · exact g32p_supplierForest_actual_082780
  · exact g32p_supplierForest_actual_082829
  · exact g32p_supplierForest_actual_082836
  · exact g32p_supplierForest_actual_082856
  · exact g32p_supplierForest_actual_082861
  · exact g32p_supplierForest_actual_082877
  · exact g32p_supplierForest_actual_082897
  · exact g32p_supplierForest_actual_082919
  · exact g32p_supplierForest_actual_082946
  · exact g32p_supplierForest_actual_082972
  · exact g32p_supplierForest_actual_082979
  · exact g32p_supplierForest_actual_082990
  · exact g32p_supplierForest_actual_083030
  · exact g32p_supplierForest_actual_083032
  · exact g32p_supplierForest_actual_083037
  · exact g32p_supplierForest_actual_083145
  · exact g32p_supplierForest_actual_083148
  · exact g32p_supplierForest_actual_083336
  · exact g32p_supplierForest_actual_083361
  · exact g32p_supplierForest_actual_083425
  · exact g32p_supplierForest_actual_083463
  · exact g32p_supplierForest_actual_083491
  · exact g32p_supplierForest_actual_083526
  · exact g32p_supplierForest_actual_083540
  · exact g32p_supplierForest_actual_083591
  · exact g32p_supplierForest_actual_083599
  · exact g32p_supplierForest_actual_083605
  · exact g32p_supplierForest_actual_083728
  · exact g32p_supplierForest_actual_083734
  · exact g32p_supplierForest_actual_083754
  · exact g32p_supplierForest_actual_083775
  · exact g32p_supplierForest_actual_083811
  · exact g32p_supplierForest_actual_083814
  · exact g32p_supplierForest_actual_083816
  · exact g32p_supplierForest_actual_083832
  · exact g32p_supplierForest_actual_083962
  · exact g32p_supplierForest_actual_084006
  · exact g32p_supplierForest_actual_084009
  · exact g32p_supplierForest_actual_084021
  · exact g32p_supplierForest_actual_084029
  · exact g32p_supplierForest_actual_084074
  · exact g32p_supplierForest_actual_084135
  · exact g32p_supplierForest_actual_084223
  · exact g32p_supplierForest_actual_084229
  · exact g32p_supplierForest_actual_084233
  · exact g32p_supplierForest_actual_084309
  · exact g32p_supplierForest_actual_084380
  · exact g32p_supplierForest_actual_084409
  · exact g32p_supplierForest_actual_084440
  · exact g32p_supplierForest_actual_084490
  · exact g32p_supplierForest_actual_084496
  · exact g32p_supplierForest_actual_084497
  · exact g32p_supplierForest_actual_084516
  · exact g32p_supplierForest_actual_084542
  · exact g32p_supplierForest_actual_084566
  · exact g32p_supplierForest_actual_084623
  · exact g32p_supplierForest_actual_084631
  · exact g32p_supplierForest_actual_084643
  · exact g32p_supplierForest_actual_084659
  · exact g32p_supplierForest_actual_084683
  · exact g32p_supplierForest_actual_084727
  · exact g32p_supplierForest_actual_084825
  · exact g32p_supplierForest_actual_084860
  · exact g32p_supplierForest_actual_084878
  · exact g32p_supplierForest_actual_085044
  · exact g32p_supplierForest_actual_085048
  · exact g32p_supplierForest_actual_085054
  · exact g32p_supplierForest_actual_085057
  · exact g32p_supplierForest_actual_085060
  · exact g32p_supplierForest_actual_085064
  · exact g32p_supplierForest_actual_085070
  · exact g32p_supplierForest_actual_085141
  · exact g32p_supplierForest_actual_085154
  · exact g32p_supplierForest_actual_085190
  · exact g32p_supplierForest_actual_085200
  · exact g32p_supplierForest_actual_085203
  · exact g32p_supplierForest_actual_085219
  · exact g32p_supplierForest_actual_085272
  · exact g32p_supplierForest_actual_085287
  · exact g32p_supplierForest_actual_085343
  · exact g32p_supplierForest_actual_085349
  · exact g32p_supplierForest_actual_085355
  · exact g32p_supplierForest_actual_085356
  · exact g32p_supplierForest_actual_085362
  · exact g32p_supplierForest_actual_085368
  · exact g32p_supplierForest_actual_085376
  · exact g32p_supplierForest_actual_085419
  · exact g32p_supplierForest_actual_085424
  · exact g32p_supplierForest_actual_085457
  · exact g32p_supplierForest_actual_085490
  · exact g32p_supplierForest_actual_085504
  · exact g32p_supplierForest_actual_085552
  · exact g32p_supplierForest_actual_085562
  · exact g32p_supplierForest_actual_085574
  · exact g32p_supplierForest_actual_085575
  · exact g32p_supplierForest_actual_085577
  · exact g32p_supplierForest_actual_085603
  · exact g32p_supplierForest_actual_085605
  · exact g32p_supplierForest_actual_085624
  · exact g32p_supplierForest_actual_085639
  · exact g32p_supplierForest_actual_085710
  · exact g32p_supplierForest_actual_085730
  · exact g32p_supplierForest_actual_085748
  · exact g32p_supplierForest_actual_085754
  · exact g32p_supplierForest_actual_085802
  · exact g32p_supplierForest_actual_085823
  · exact g32p_supplierForest_actual_085899
  · exact g32p_supplierForest_actual_085921
  · exact g32p_supplierForest_actual_085945
  · exact g32p_supplierForest_actual_085957
  · exact g32p_supplierForest_actual_085982
  · exact g32p_supplierForest_actual_085985
  · exact g32p_supplierForest_actual_085999
  · exact g32p_supplierForest_actual_086065
  · exact g32p_supplierForest_actual_086078
  · exact g32p_supplierForest_actual_086092
  · exact g32p_supplierForest_actual_086124
  · exact g32p_supplierForest_actual_086127
  · exact g32p_supplierForest_actual_086134
  · exact g32p_supplierForest_actual_086149
  · exact g32p_supplierForest_actual_086205
  · exact g32p_supplierForest_actual_086251
  · exact g32p_supplierForest_actual_086281
  · exact g32p_supplierForest_actual_086425
  · exact g32p_supplierForest_actual_086461
  · exact g32p_supplierForest_actual_086489
  · exact g32p_supplierForest_actual_086516
  · exact g32p_supplierForest_actual_086559
  · exact g32p_supplierForest_actual_086624
  · exact g32p_supplierForest_actual_086695
  · exact g32p_supplierForest_actual_086705
  · exact g32p_supplierForest_actual_086707
  · exact g32p_supplierForest_actual_086718
  · exact g32p_supplierForest_actual_086777
  · exact g32p_supplierForest_actual_086813
  · exact g32p_supplierForest_actual_086827
  · exact g32p_supplierForest_actual_086891
  · exact g32p_supplierForest_actual_086916
  · exact g32p_supplierForest_actual_086950
  · exact g32p_supplierForest_actual_086982
  · exact g32p_supplierForest_actual_086993
  · exact g32p_supplierForest_actual_087007
  · exact g32p_supplierForest_actual_087012
  · exact g32p_supplierForest_actual_087028
  · exact g32p_supplierForest_actual_087071
  · exact g32p_supplierForest_actual_087080
  · exact g32p_supplierForest_actual_087092
  · exact g32p_supplierForest_actual_087098
  · exact g32p_supplierForest_actual_087158
  · exact g32p_supplierForest_actual_087165
  · exact g32p_supplierForest_actual_087187
  · exact g32p_supplierForest_actual_087223
  · exact g32p_supplierForest_actual_087227
  · exact g32p_supplierForest_actual_087232
  · exact g32p_supplierForest_actual_087233
  · exact g32p_supplierForest_actual_087248
  · exact g32p_supplierForest_actual_087280
  · exact g32p_supplierForest_actual_087283
  · exact g32p_supplierForest_actual_087292
  · exact g32p_supplierForest_actual_087319
  · exact g32p_supplierForest_actual_087328
  · exact g32p_supplierForest_actual_087487
  · exact g32p_supplierForest_actual_087521
  · exact g32p_supplierForest_actual_087523
  · exact g32p_supplierForest_actual_087555
  · exact g32p_supplierForest_actual_087557
  · exact g32p_supplierForest_actual_087619
  · exact g32p_supplierForest_actual_087639
  · exact g32p_supplierForest_actual_087644
  · exact g32p_supplierForest_actual_087684
  · exact g32p_supplierForest_actual_087720
  · exact g32p_supplierForest_actual_087771
  · exact g32p_supplierForest_actual_087827
  · exact g32p_supplierForest_actual_087861
  · exact g32p_supplierForest_actual_087883
  · exact g32p_supplierForest_actual_087943
  · exact g32p_supplierForest_actual_087990
  · exact g32p_supplierForest_actual_088009
  · exact g32p_supplierForest_actual_088019
  · exact g32p_supplierForest_actual_088023
  · exact g32p_supplierForest_actual_088039
  · exact g32p_supplierForest_actual_088077
  · exact g32p_supplierForest_actual_088104
  · exact g32p_supplierForest_actual_088140
  · exact g32p_supplierForest_actual_088154
  · exact g32p_supplierForest_actual_088195
  · exact g32p_supplierForest_actual_088198
  · exact g32p_supplierForest_actual_088219
  · exact g32p_supplierForest_actual_088231
  · exact g32p_supplierForest_actual_088271
  · exact g32p_supplierForest_actual_088272
  · exact g32p_supplierForest_actual_088281
  · exact g32p_supplierForest_actual_088293
  · exact g32p_supplierForest_actual_088333
  · exact g32p_supplierForest_actual_088336

def g32p_supplierForest_nodes_123 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_088377 else g32p_supplierForest_node_088383) else (if i.val < 3 then g32p_supplierForest_node_088387 else g32p_supplierForest_node_088398)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_088401 else g32p_supplierForest_node_088447) else (if i.val < 7 then g32p_supplierForest_node_088468 else g32p_supplierForest_node_088522))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_088526 else g32p_supplierForest_node_088532) else (if i.val < 11 then g32p_supplierForest_node_088546 else g32p_supplierForest_node_088614)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_088642 else g32p_supplierForest_node_088661) else (if i.val < 15 then g32p_supplierForest_node_088667 else g32p_supplierForest_node_088684)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_088711 else g32p_supplierForest_node_088726) else (if i.val < 19 then g32p_supplierForest_node_088732 else g32p_supplierForest_node_088737)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_088738 else g32p_supplierForest_node_088800) else (if i.val < 23 then g32p_supplierForest_node_088834 else g32p_supplierForest_node_088875))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_088886 else g32p_supplierForest_node_088910) else (if i.val < 27 then g32p_supplierForest_node_088921 else g32p_supplierForest_node_089020)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_089021 else g32p_supplierForest_node_089024) else (if i.val < 31 then g32p_supplierForest_node_089030 else g32p_supplierForest_node_089097))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_089115 else g32p_supplierForest_node_089143) else (if i.val < 35 then g32p_supplierForest_node_089153 else g32p_supplierForest_node_089224)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_089269 else g32p_supplierForest_node_089304) else (if i.val < 39 then g32p_supplierForest_node_089307 else g32p_supplierForest_node_089344))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_089376 else g32p_supplierForest_node_089400) else (if i.val < 43 then g32p_supplierForest_node_089434 else g32p_supplierForest_node_089439)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_089585 else g32p_supplierForest_node_089637) else (if i.val < 47 then g32p_supplierForest_node_089654 else g32p_supplierForest_node_089669)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_089690 else g32p_supplierForest_node_089692) else (if i.val < 51 then g32p_supplierForest_node_089756 else g32p_supplierForest_node_089761)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_089779 else g32p_supplierForest_node_089791) else (if i.val < 55 then g32p_supplierForest_node_089802 else g32p_supplierForest_node_089810))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_089819 else g32p_supplierForest_node_089820) else (if i.val < 59 then g32p_supplierForest_node_089834 else g32p_supplierForest_node_089866)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_090018 else g32p_supplierForest_node_090041) else (if i.val < 63 then g32p_supplierForest_node_090073 else g32p_supplierForest_node_090161)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_090162 else g32p_supplierForest_node_090194) else (if i.val < 67 then g32p_supplierForest_node_090237 else g32p_supplierForest_node_090256)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_090267 else g32p_supplierForest_node_090283) else (if i.val < 71 then g32p_supplierForest_node_090286 else g32p_supplierForest_node_090349))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_090374 else g32p_supplierForest_node_090423) else (if i.val < 75 then g32p_supplierForest_node_090437 else g32p_supplierForest_node_090440)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_090445 else g32p_supplierForest_node_090450) else (if i.val < 79 then g32p_supplierForest_node_090453 else g32p_supplierForest_node_090547)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_090556 else g32p_supplierForest_node_090572) else (if i.val < 83 then g32p_supplierForest_node_090582 else g32p_supplierForest_node_090712)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_090729 else g32p_supplierForest_node_090755) else (if i.val < 87 then g32p_supplierForest_node_090771 else g32p_supplierForest_node_090809))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_090823 else g32p_supplierForest_node_090827) else (if i.val < 91 then g32p_supplierForest_node_090838 else g32p_supplierForest_node_090867)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_090870 else g32p_supplierForest_node_090965) else (if i.val < 95 then g32p_supplierForest_node_090971 else g32p_supplierForest_node_090998))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_091003 else g32p_supplierForest_node_091039) else (if i.val < 99 then g32p_supplierForest_node_091086 else g32p_supplierForest_node_091099)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_091105 else g32p_supplierForest_node_091118) else (if i.val < 103 then g32p_supplierForest_node_091141 else g32p_supplierForest_node_091171))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_091173 else g32p_supplierForest_node_091210) else (if i.val < 107 then g32p_supplierForest_node_091215 else g32p_supplierForest_node_091238)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_091284 else g32p_supplierForest_node_091315) else (if i.val < 111 then g32p_supplierForest_node_091367 else g32p_supplierForest_node_091431)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_091453 else g32p_supplierForest_node_091460) else (if i.val < 115 then g32p_supplierForest_node_091463 else g32p_supplierForest_node_091503)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_091505 else g32p_supplierForest_node_091603) else (if i.val < 119 then g32p_supplierForest_node_091648 else g32p_supplierForest_node_091714))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_091736 else g32p_supplierForest_node_091764) else (if i.val < 123 then g32p_supplierForest_node_091802 else g32p_supplierForest_node_091822)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_091912 else g32p_supplierForest_node_091968) else (if i.val < 127 then g32p_supplierForest_node_092009 else g32p_supplierForest_node_092014))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_092025 else g32p_supplierForest_node_092085) else (if i.val < 131 then g32p_supplierForest_node_092109 else g32p_supplierForest_node_092167)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_092229 else g32p_supplierForest_node_092253) else (if i.val < 135 then g32p_supplierForest_node_092305 else g32p_supplierForest_node_092379))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_092396 else g32p_supplierForest_node_092434) else (if i.val < 139 then g32p_supplierForest_node_092456 else g32p_supplierForest_node_092507)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_092515 else g32p_supplierForest_node_092548) else (if i.val < 143 then g32p_supplierForest_node_092599 else g32p_supplierForest_node_092633)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_092725 else g32p_supplierForest_node_092743) else (if i.val < 147 then g32p_supplierForest_node_092782 else g32p_supplierForest_node_092822)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_092826 else g32p_supplierForest_node_092941) else (if i.val < 151 then g32p_supplierForest_node_092944 else g32p_supplierForest_node_092945))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_093005 else g32p_supplierForest_node_093084) else (if i.val < 155 then g32p_supplierForest_node_093098 else g32p_supplierForest_node_093108)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_093123 else g32p_supplierForest_node_093167) else (if i.val < 159 then g32p_supplierForest_node_093192 else g32p_supplierForest_node_093233))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_093246 else g32p_supplierForest_node_093253) else (if i.val < 163 then g32p_supplierForest_node_093282 else g32p_supplierForest_node_093289)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_093330 else g32p_supplierForest_node_093368) else (if i.val < 167 then g32p_supplierForest_node_093386 else g32p_supplierForest_node_093393))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_093412 else g32p_supplierForest_node_093424) else (if i.val < 171 then g32p_supplierForest_node_093429 else g32p_supplierForest_node_093458)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_093459 else g32p_supplierForest_node_093476) else (if i.val < 175 then g32p_supplierForest_node_093524 else g32p_supplierForest_node_093534)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_093594 else g32p_supplierForest_node_093602) else (if i.val < 179 then g32p_supplierForest_node_093622 else g32p_supplierForest_node_093733)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_093749 else g32p_supplierForest_node_093761) else (if i.val < 183 then g32p_supplierForest_node_093765 else g32p_supplierForest_node_093834))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_093886 else g32p_supplierForest_node_093906) else (if i.val < 187 then g32p_supplierForest_node_093926 else g32p_supplierForest_node_093957)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_093975 else g32p_supplierForest_node_094005) else (if i.val < 191 then g32p_supplierForest_node_094048 else g32p_supplierForest_node_094056)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_094065 else g32p_supplierForest_node_094095) else (if i.val < 195 then g32p_supplierForest_node_094130 else g32p_supplierForest_node_094153)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_094196 else g32p_supplierForest_node_094207) else (if i.val < 199 then g32p_supplierForest_node_094262 else g32p_supplierForest_node_094272))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_094298 else g32p_supplierForest_node_094307) else (if i.val < 203 then g32p_supplierForest_node_094349 else g32p_supplierForest_node_094409)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_094509 else g32p_supplierForest_node_094543) else (if i.val < 207 then g32p_supplierForest_node_094576 else g32p_supplierForest_node_094586)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_094629 else g32p_supplierForest_node_094639) else (if i.val < 211 then g32p_supplierForest_node_094646 else g32p_supplierForest_node_094684)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_094691 else g32p_supplierForest_node_094725) else (if i.val < 215 then g32p_supplierForest_node_094726 else g32p_supplierForest_node_094821))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_094857 else g32p_supplierForest_node_094861) else (if i.val < 219 then g32p_supplierForest_node_094865 else g32p_supplierForest_node_094868)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_094887 else g32p_supplierForest_node_094991) else (if i.val < 223 then g32p_supplierForest_node_094993 else g32p_supplierForest_node_095009))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_095013 else g32p_supplierForest_node_095052) else (if i.val < 227 then g32p_supplierForest_node_095080 else g32p_supplierForest_node_095082)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_095092 else g32p_supplierForest_node_095098) else (if i.val < 231 then g32p_supplierForest_node_095099 else g32p_supplierForest_node_095139))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_095161 else g32p_supplierForest_node_095177) else (if i.val < 235 then g32p_supplierForest_node_095216 else g32p_supplierForest_node_095287)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_095288 else g32p_supplierForest_node_095289) else (if i.val < 239 then g32p_supplierForest_node_095292 else g32p_supplierForest_node_095333)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_095344 else g32p_supplierForest_node_095365) else (if i.val < 243 then g32p_supplierForest_node_095388 else g32p_supplierForest_node_095397)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_095406 else g32p_supplierForest_node_095465) else (if i.val < 247 then g32p_supplierForest_node_095500 else g32p_supplierForest_node_095533))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_095551 else g32p_supplierForest_node_095554) else (if i.val < 251 then g32p_supplierForest_node_095558 else g32p_supplierForest_node_095581)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_095585 else g32p_supplierForest_node_095597) else (if i.val < 255 then g32p_supplierForest_node_095689 else g32p_supplierForest_node_095693))))))))

def g32p_supplierForest_classes_123 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 49 else 46) else (if i.val < 3 then 46 else 49)) else (if i.val < 6 then (if i.val < 5 then 47 else 46) else (if i.val < 7 then 49 else 48))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 47 else 47) else (if i.val < 11 then 25 else 12)) else (if i.val < 14 then (if i.val < 13 then 26 else 49) else (if i.val < 15 then 47 else 49)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 49 else 55) else (if i.val < 19 then 49 else 26)) else (if i.val < 22 then (if i.val < 21 then 49 else 46) else (if i.val < 23 then 80 else 53))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 12 else 26) else (if i.val < 27 then 46 else 46)) else (if i.val < 30 then (if i.val < 29 then 46 else 54) else (if i.val < 31 then 46 else 46))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 80 else 86) else (if i.val < 35 then 46 else 49)) else (if i.val < 38 then (if i.val < 37 then 49 else 46) else (if i.val < 39 then 46 else 53))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 46 else 49) else (if i.val < 43 then 80 else 48)) else (if i.val < 46 then (if i.val < 45 then 49 else 46) else (if i.val < 47 then 53 else 49)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 46 else 12) else (if i.val < 51 then 8 else 46)) else (if i.val < 54 then (if i.val < 53 then 46 else 86) else (if i.val < 55 then 50 else 47))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 46 else 46) else (if i.val < 59 then 53 else 46)) else (if i.val < 62 then (if i.val < 61 then 46 else 46) else (if i.val < 63 then 25 else 9)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 49) else (if i.val < 67 then 49 else 47)) else (if i.val < 70 then (if i.val < 69 then 50 else 49) else (if i.val < 71 then 26 else 81))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 50 else 49) else (if i.val < 75 then 46 else 85)) else (if i.val < 78 then (if i.val < 77 then 55 else 55) else (if i.val < 79 then 12 else 50)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 53 else 47) else (if i.val < 83 then 80 else 54)) else (if i.val < 86 then (if i.val < 85 then 49 else 49) else (if i.val < 87 then 25 else 26))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 80 else 53) else (if i.val < 91 then 49 else 46)) else (if i.val < 94 then (if i.val < 93 then 26 else 46) else (if i.val < 95 then 53 else 49))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 49 else 46) else (if i.val < 99 then 26 else 49)) else (if i.val < 102 then (if i.val < 101 then 49 else 49) else (if i.val < 103 then 49 else 45))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 49 else 49) else (if i.val < 107 then 47 else 49)) else (if i.val < 110 then (if i.val < 109 then 49 else 49) else (if i.val < 111 then 49 else 49)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 46 else 49) else (if i.val < 115 then 49 else 49)) else (if i.val < 118 then (if i.val < 117 then 49 else 47) else (if i.val < 119 then 9 else 26))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 47 else 12) else (if i.val < 123 then 49 else 26)) else (if i.val < 126 then (if i.val < 125 then 12 else 46) else (if i.val < 127 then 50 else 49))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 46 else 86) else (if i.val < 131 then 46 else 50)) else (if i.val < 134 then (if i.val < 133 then 49 else 55) else (if i.val < 135 then 80 else 53))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 50 else 46) else (if i.val < 139 then 26 else 49)) else (if i.val < 142 then (if i.val < 141 then 86 else 25) else (if i.val < 143 then 46 else 46)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 86 else 49) else (if i.val < 147 then 49 else 46)) else (if i.val < 150 then (if i.val < 149 then 49 else 47) else (if i.val < 151 then 50 else 26))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 49 else 46) else (if i.val < 155 then 46 else 46)) else (if i.val < 158 then (if i.val < 157 then 49 else 46) else (if i.val < 159 then 46 else 46))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 46 else 50) else (if i.val < 163 then 25 else 54)) else (if i.val < 166 then (if i.val < 165 then 46 else 45) else (if i.val < 167 then 46 else 53))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 46 else 49) else (if i.val < 171 then 49 else 26)) else (if i.val < 174 then (if i.val < 173 then 49 else 49) else (if i.val < 175 then 49 else 47)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 47 else 45) else (if i.val < 179 then 54 else 49)) else (if i.val < 182 then (if i.val < 181 then 49 else 49) else (if i.val < 183 then 49 else 46))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 86 else 49) else (if i.val < 187 then 47 else 46)) else (if i.val < 190 then (if i.val < 189 then 47 else 49) else (if i.val < 191 then 46 else 49)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 49 else 49) else (if i.val < 195 then 49 else 48)) else (if i.val < 198 then (if i.val < 197 then 53 else 54) else (if i.val < 199 then 26 else 49))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 55 else 49) else (if i.val < 203 then 49 else 12)) else (if i.val < 206 then (if i.val < 205 then 26 else 46) else (if i.val < 207 then 80 else 45)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 46 else 49) else (if i.val < 211 then 49 else 86)) else (if i.val < 214 then (if i.val < 213 then 49 else 26) else (if i.val < 215 then 49 else 26))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 46 else 49) else (if i.val < 219 then 46 else 49)) else (if i.val < 222 then (if i.val < 221 then 26 else 46) else (if i.val < 223 then 46 else 12))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 84 else 25) else (if i.val < 227 then 49 else 45)) else (if i.val < 230 then (if i.val < 229 then 45 else 46) else (if i.val < 231 then 49 else 26))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 47 else 49) else (if i.val < 235 then 49 else 45)) else (if i.val < 238 then (if i.val < 237 then 9 else 46) else (if i.val < 239 then 25 else 47)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 46 else 54) else (if i.val < 243 then 26 else 55)) else (if i.val < 246 then (if i.val < 245 then 46 else 49) else (if i.val < 247 then 49 else 12))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 49 else 54) else (if i.val < 251 then 55 else 49)) else (if i.val < 254 then (if i.val < 253 then 54 else 50) else (if i.val < 255 then 47 else 12))))))))

theorem g32p_supplierForest_actual_123 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_123 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_123 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_088377
  · exact g32p_supplierForest_actual_088383
  · exact g32p_supplierForest_actual_088387
  · exact g32p_supplierForest_actual_088398
  · exact g32p_supplierForest_actual_088401
  · exact g32p_supplierForest_actual_088447
  · exact g32p_supplierForest_actual_088468
  · exact g32p_supplierForest_actual_088522
  · exact g32p_supplierForest_actual_088526
  · exact g32p_supplierForest_actual_088532
  · exact g32p_supplierForest_actual_088546
  · exact g32p_supplierForest_actual_088614
  · exact g32p_supplierForest_actual_088642
  · exact g32p_supplierForest_actual_088661
  · exact g32p_supplierForest_actual_088667
  · exact g32p_supplierForest_actual_088684
  · exact g32p_supplierForest_actual_088711
  · exact g32p_supplierForest_actual_088726
  · exact g32p_supplierForest_actual_088732
  · exact g32p_supplierForest_actual_088737
  · exact g32p_supplierForest_actual_088738
  · exact g32p_supplierForest_actual_088800
  · exact g32p_supplierForest_actual_088834
  · exact g32p_supplierForest_actual_088875
  · exact g32p_supplierForest_actual_088886
  · exact g32p_supplierForest_actual_088910
  · exact g32p_supplierForest_actual_088921
  · exact g32p_supplierForest_actual_089020
  · exact g32p_supplierForest_actual_089021
  · exact g32p_supplierForest_actual_089024
  · exact g32p_supplierForest_actual_089030
  · exact g32p_supplierForest_actual_089097
  · exact g32p_supplierForest_actual_089115
  · exact g32p_supplierForest_actual_089143
  · exact g32p_supplierForest_actual_089153
  · exact g32p_supplierForest_actual_089224
  · exact g32p_supplierForest_actual_089269
  · exact g32p_supplierForest_actual_089304
  · exact g32p_supplierForest_actual_089307
  · exact g32p_supplierForest_actual_089344
  · exact g32p_supplierForest_actual_089376
  · exact g32p_supplierForest_actual_089400
  · exact g32p_supplierForest_actual_089434
  · exact g32p_supplierForest_actual_089439
  · exact g32p_supplierForest_actual_089585
  · exact g32p_supplierForest_actual_089637
  · exact g32p_supplierForest_actual_089654
  · exact g32p_supplierForest_actual_089669
  · exact g32p_supplierForest_actual_089690
  · exact g32p_supplierForest_actual_089692
  · exact g32p_supplierForest_actual_089756
  · exact g32p_supplierForest_actual_089761
  · exact g32p_supplierForest_actual_089779
  · exact g32p_supplierForest_actual_089791
  · exact g32p_supplierForest_actual_089802
  · exact g32p_supplierForest_actual_089810
  · exact g32p_supplierForest_actual_089819
  · exact g32p_supplierForest_actual_089820
  · exact g32p_supplierForest_actual_089834
  · exact g32p_supplierForest_actual_089866
  · exact g32p_supplierForest_actual_090018
  · exact g32p_supplierForest_actual_090041
  · exact g32p_supplierForest_actual_090073
  · exact g32p_supplierForest_actual_090161
  · exact g32p_supplierForest_actual_090162
  · exact g32p_supplierForest_actual_090194
  · exact g32p_supplierForest_actual_090237
  · exact g32p_supplierForest_actual_090256
  · exact g32p_supplierForest_actual_090267
  · exact g32p_supplierForest_actual_090283
  · exact g32p_supplierForest_actual_090286
  · exact g32p_supplierForest_actual_090349
  · exact g32p_supplierForest_actual_090374
  · exact g32p_supplierForest_actual_090423
  · exact g32p_supplierForest_actual_090437
  · exact g32p_supplierForest_actual_090440
  · exact g32p_supplierForest_actual_090445
  · exact g32p_supplierForest_actual_090450
  · exact g32p_supplierForest_actual_090453
  · exact g32p_supplierForest_actual_090547
  · exact g32p_supplierForest_actual_090556
  · exact g32p_supplierForest_actual_090572
  · exact g32p_supplierForest_actual_090582
  · exact g32p_supplierForest_actual_090712
  · exact g32p_supplierForest_actual_090729
  · exact g32p_supplierForest_actual_090755
  · exact g32p_supplierForest_actual_090771
  · exact g32p_supplierForest_actual_090809
  · exact g32p_supplierForest_actual_090823
  · exact g32p_supplierForest_actual_090827
  · exact g32p_supplierForest_actual_090838
  · exact g32p_supplierForest_actual_090867
  · exact g32p_supplierForest_actual_090870
  · exact g32p_supplierForest_actual_090965
  · exact g32p_supplierForest_actual_090971
  · exact g32p_supplierForest_actual_090998
  · exact g32p_supplierForest_actual_091003
  · exact g32p_supplierForest_actual_091039
  · exact g32p_supplierForest_actual_091086
  · exact g32p_supplierForest_actual_091099
  · exact g32p_supplierForest_actual_091105
  · exact g32p_supplierForest_actual_091118
  · exact g32p_supplierForest_actual_091141
  · exact g32p_supplierForest_actual_091171
  · exact g32p_supplierForest_actual_091173
  · exact g32p_supplierForest_actual_091210
  · exact g32p_supplierForest_actual_091215
  · exact g32p_supplierForest_actual_091238
  · exact g32p_supplierForest_actual_091284
  · exact g32p_supplierForest_actual_091315
  · exact g32p_supplierForest_actual_091367
  · exact g32p_supplierForest_actual_091431
  · exact g32p_supplierForest_actual_091453
  · exact g32p_supplierForest_actual_091460
  · exact g32p_supplierForest_actual_091463
  · exact g32p_supplierForest_actual_091503
  · exact g32p_supplierForest_actual_091505
  · exact g32p_supplierForest_actual_091603
  · exact g32p_supplierForest_actual_091648
  · exact g32p_supplierForest_actual_091714
  · exact g32p_supplierForest_actual_091736
  · exact g32p_supplierForest_actual_091764
  · exact g32p_supplierForest_actual_091802
  · exact g32p_supplierForest_actual_091822
  · exact g32p_supplierForest_actual_091912
  · exact g32p_supplierForest_actual_091968
  · exact g32p_supplierForest_actual_092009
  · exact g32p_supplierForest_actual_092014
  · exact g32p_supplierForest_actual_092025
  · exact g32p_supplierForest_actual_092085
  · exact g32p_supplierForest_actual_092109
  · exact g32p_supplierForest_actual_092167
  · exact g32p_supplierForest_actual_092229
  · exact g32p_supplierForest_actual_092253
  · exact g32p_supplierForest_actual_092305
  · exact g32p_supplierForest_actual_092379
  · exact g32p_supplierForest_actual_092396
  · exact g32p_supplierForest_actual_092434
  · exact g32p_supplierForest_actual_092456
  · exact g32p_supplierForest_actual_092507
  · exact g32p_supplierForest_actual_092515
  · exact g32p_supplierForest_actual_092548
  · exact g32p_supplierForest_actual_092599
  · exact g32p_supplierForest_actual_092633
  · exact g32p_supplierForest_actual_092725
  · exact g32p_supplierForest_actual_092743
  · exact g32p_supplierForest_actual_092782
  · exact g32p_supplierForest_actual_092822
  · exact g32p_supplierForest_actual_092826
  · exact g32p_supplierForest_actual_092941
  · exact g32p_supplierForest_actual_092944
  · exact g32p_supplierForest_actual_092945
  · exact g32p_supplierForest_actual_093005
  · exact g32p_supplierForest_actual_093084
  · exact g32p_supplierForest_actual_093098
  · exact g32p_supplierForest_actual_093108
  · exact g32p_supplierForest_actual_093123
  · exact g32p_supplierForest_actual_093167
  · exact g32p_supplierForest_actual_093192
  · exact g32p_supplierForest_actual_093233
  · exact g32p_supplierForest_actual_093246
  · exact g32p_supplierForest_actual_093253
  · exact g32p_supplierForest_actual_093282
  · exact g32p_supplierForest_actual_093289
  · exact g32p_supplierForest_actual_093330
  · exact g32p_supplierForest_actual_093368
  · exact g32p_supplierForest_actual_093386
  · exact g32p_supplierForest_actual_093393
  · exact g32p_supplierForest_actual_093412
  · exact g32p_supplierForest_actual_093424
  · exact g32p_supplierForest_actual_093429
  · exact g32p_supplierForest_actual_093458
  · exact g32p_supplierForest_actual_093459
  · exact g32p_supplierForest_actual_093476
  · exact g32p_supplierForest_actual_093524
  · exact g32p_supplierForest_actual_093534
  · exact g32p_supplierForest_actual_093594
  · exact g32p_supplierForest_actual_093602
  · exact g32p_supplierForest_actual_093622
  · exact g32p_supplierForest_actual_093733
  · exact g32p_supplierForest_actual_093749
  · exact g32p_supplierForest_actual_093761
  · exact g32p_supplierForest_actual_093765
  · exact g32p_supplierForest_actual_093834
  · exact g32p_supplierForest_actual_093886
  · exact g32p_supplierForest_actual_093906
  · exact g32p_supplierForest_actual_093926
  · exact g32p_supplierForest_actual_093957
  · exact g32p_supplierForest_actual_093975
  · exact g32p_supplierForest_actual_094005
  · exact g32p_supplierForest_actual_094048
  · exact g32p_supplierForest_actual_094056
  · exact g32p_supplierForest_actual_094065
  · exact g32p_supplierForest_actual_094095
  · exact g32p_supplierForest_actual_094130
  · exact g32p_supplierForest_actual_094153
  · exact g32p_supplierForest_actual_094196
  · exact g32p_supplierForest_actual_094207
  · exact g32p_supplierForest_actual_094262
  · exact g32p_supplierForest_actual_094272
  · exact g32p_supplierForest_actual_094298
  · exact g32p_supplierForest_actual_094307
  · exact g32p_supplierForest_actual_094349
  · exact g32p_supplierForest_actual_094409
  · exact g32p_supplierForest_actual_094509
  · exact g32p_supplierForest_actual_094543
  · exact g32p_supplierForest_actual_094576
  · exact g32p_supplierForest_actual_094586
  · exact g32p_supplierForest_actual_094629
  · exact g32p_supplierForest_actual_094639
  · exact g32p_supplierForest_actual_094646
  · exact g32p_supplierForest_actual_094684
  · exact g32p_supplierForest_actual_094691
  · exact g32p_supplierForest_actual_094725
  · exact g32p_supplierForest_actual_094726
  · exact g32p_supplierForest_actual_094821
  · exact g32p_supplierForest_actual_094857
  · exact g32p_supplierForest_actual_094861
  · exact g32p_supplierForest_actual_094865
  · exact g32p_supplierForest_actual_094868
  · exact g32p_supplierForest_actual_094887
  · exact g32p_supplierForest_actual_094991
  · exact g32p_supplierForest_actual_094993
  · exact g32p_supplierForest_actual_095009
  · exact g32p_supplierForest_actual_095013
  · exact g32p_supplierForest_actual_095052
  · exact g32p_supplierForest_actual_095080
  · exact g32p_supplierForest_actual_095082
  · exact g32p_supplierForest_actual_095092
  · exact g32p_supplierForest_actual_095098
  · exact g32p_supplierForest_actual_095099
  · exact g32p_supplierForest_actual_095139
  · exact g32p_supplierForest_actual_095161
  · exact g32p_supplierForest_actual_095177
  · exact g32p_supplierForest_actual_095216
  · exact g32p_supplierForest_actual_095287
  · exact g32p_supplierForest_actual_095288
  · exact g32p_supplierForest_actual_095289
  · exact g32p_supplierForest_actual_095292
  · exact g32p_supplierForest_actual_095333
  · exact g32p_supplierForest_actual_095344
  · exact g32p_supplierForest_actual_095365
  · exact g32p_supplierForest_actual_095388
  · exact g32p_supplierForest_actual_095397
  · exact g32p_supplierForest_actual_095406
  · exact g32p_supplierForest_actual_095465
  · exact g32p_supplierForest_actual_095500
  · exact g32p_supplierForest_actual_095533
  · exact g32p_supplierForest_actual_095551
  · exact g32p_supplierForest_actual_095554
  · exact g32p_supplierForest_actual_095558
  · exact g32p_supplierForest_actual_095581
  · exact g32p_supplierForest_actual_095585
  · exact g32p_supplierForest_actual_095597
  · exact g32p_supplierForest_actual_095689
  · exact g32p_supplierForest_actual_095693

def g32p_supplierForest_nodes_124 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_095738 else g32p_supplierForest_node_095761) else (if i.val < 3 then g32p_supplierForest_node_095817 else g32p_supplierForest_node_095850)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_095879 else g32p_supplierForest_node_095880) else (if i.val < 7 then g32p_supplierForest_node_095919 else g32p_supplierForest_node_095921))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_095922 else g32p_supplierForest_node_095930) else (if i.val < 11 then g32p_supplierForest_node_095958 else g32p_supplierForest_node_095965)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_096050 else g32p_supplierForest_node_096110) else (if i.val < 15 then g32p_supplierForest_node_096154 else g32p_supplierForest_node_096196)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_096260 else g32p_supplierForest_node_096293) else (if i.val < 19 then g32p_supplierForest_node_096299 else g32p_supplierForest_node_096308)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_096317 else g32p_supplierForest_node_096400) else (if i.val < 23 then g32p_supplierForest_node_096405 else g32p_supplierForest_node_096441))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_096514 else g32p_supplierForest_node_096542) else (if i.val < 27 then g32p_supplierForest_node_096626 else g32p_supplierForest_node_096633)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_096657 else g32p_supplierForest_node_096658) else (if i.val < 31 then g32p_supplierForest_node_096668 else g32p_supplierForest_node_096717))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_096761 else g32p_supplierForest_node_096780) else (if i.val < 35 then g32p_supplierForest_node_096807 else g32p_supplierForest_node_096820)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_096846 else g32p_supplierForest_node_096897) else (if i.val < 39 then g32p_supplierForest_node_096946 else g32p_supplierForest_node_096956))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_097032 else g32p_supplierForest_node_097033) else (if i.val < 43 then g32p_supplierForest_node_097067 else g32p_supplierForest_node_097095)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_097117 else g32p_supplierForest_node_097182) else (if i.val < 47 then g32p_supplierForest_node_097258 else g32p_supplierForest_node_097267)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_097355 else g32p_supplierForest_node_097357) else (if i.val < 51 then g32p_supplierForest_node_097384 else g32p_supplierForest_node_097393)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_097397 else g32p_supplierForest_node_097450) else (if i.val < 55 then g32p_supplierForest_node_097460 else g32p_supplierForest_node_097473))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_097479 else g32p_supplierForest_node_097484) else (if i.val < 59 then g32p_supplierForest_node_097508 else g32p_supplierForest_node_097513)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_097538 else g32p_supplierForest_node_097572) else (if i.val < 63 then g32p_supplierForest_node_097601 else g32p_supplierForest_node_097607)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_097628 else g32p_supplierForest_node_097647) else (if i.val < 67 then g32p_supplierForest_node_097669 else g32p_supplierForest_node_097711)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_097721 else g32p_supplierForest_node_097724) else (if i.val < 71 then g32p_supplierForest_node_097786 else g32p_supplierForest_node_097788))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_097793 else g32p_supplierForest_node_097794) else (if i.val < 75 then g32p_supplierForest_node_097817 else g32p_supplierForest_node_097827)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_097839 else g32p_supplierForest_node_097877) else (if i.val < 79 then g32p_supplierForest_node_097883 else g32p_supplierForest_node_097911)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_097976 else g32p_supplierForest_node_097982) else (if i.val < 83 then g32p_supplierForest_node_098007 else g32p_supplierForest_node_098019)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_098021 else g32p_supplierForest_node_098027) else (if i.val < 87 then g32p_supplierForest_node_098070 else g32p_supplierForest_node_098115))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_098151 else g32p_supplierForest_node_098203) else (if i.val < 91 then g32p_supplierForest_node_098243 else g32p_supplierForest_node_098249)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_098307 else g32p_supplierForest_node_098382) else (if i.val < 95 then g32p_supplierForest_node_098424 else g32p_supplierForest_node_098526))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_098562 else g32p_supplierForest_node_098592) else (if i.val < 99 then g32p_supplierForest_node_098632 else g32p_supplierForest_node_098649)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_098679 else g32p_supplierForest_node_098695) else (if i.val < 103 then g32p_supplierForest_node_098753 else g32p_supplierForest_node_098797))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_098801 else g32p_supplierForest_node_098822) else (if i.val < 107 then g32p_supplierForest_node_098854 else g32p_supplierForest_node_098902)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_098945 else g32p_supplierForest_node_098995) else (if i.val < 111 then g32p_supplierForest_node_098997 else g32p_supplierForest_node_099000)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_099025 else g32p_supplierForest_node_099052) else (if i.val < 115 then g32p_supplierForest_node_099119 else g32p_supplierForest_node_099286)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_099304 else g32p_supplierForest_node_099309) else (if i.val < 119 then g32p_supplierForest_node_099328 else g32p_supplierForest_node_099393))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_099448 else g32p_supplierForest_node_099514) else (if i.val < 123 then g32p_supplierForest_node_099600 else g32p_supplierForest_node_099636)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_099639 else g32p_supplierForest_node_099676) else (if i.val < 127 then g32p_supplierForest_node_099701 else g32p_supplierForest_node_099730))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_099740 else g32p_supplierForest_node_099761) else (if i.val < 131 then g32p_supplierForest_node_099814 else g32p_supplierForest_node_099853)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_099862 else g32p_supplierForest_node_099864) else (if i.val < 135 then g32p_supplierForest_node_099880 else g32p_supplierForest_node_099882))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_099897 else g32p_supplierForest_node_099921) else (if i.val < 139 then g32p_supplierForest_node_099923 else g32p_supplierForest_node_099927)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_099986 else g32p_supplierForest_node_099997) else (if i.val < 143 then g32p_supplierForest_node_100055 else g32p_supplierForest_node_100103)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_100150 else g32p_supplierForest_node_100163) else (if i.val < 147 then g32p_supplierForest_node_100189 else g32p_supplierForest_node_100201)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_100208 else g32p_supplierForest_node_100271) else (if i.val < 151 then g32p_supplierForest_node_100281 else g32p_supplierForest_node_100411))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_100418 else g32p_supplierForest_node_100421) else (if i.val < 155 then g32p_supplierForest_node_100438 else g32p_supplierForest_node_100447)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_100450 else g32p_supplierForest_node_100453) else (if i.val < 159 then g32p_supplierForest_node_100456 else g32p_supplierForest_node_100508))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_100567 else g32p_supplierForest_node_100687) else (if i.val < 163 then g32p_supplierForest_node_100713 else g32p_supplierForest_node_100715)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_100721 else g32p_supplierForest_node_100753) else (if i.val < 167 then g32p_supplierForest_node_100755 else g32p_supplierForest_node_100854))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_100859 else g32p_supplierForest_node_100905) else (if i.val < 171 then g32p_supplierForest_node_100962 else g32p_supplierForest_node_100985)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_100996 else g32p_supplierForest_node_100999) else (if i.val < 175 then g32p_supplierForest_node_101092 else g32p_supplierForest_node_101093)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_101100 else g32p_supplierForest_node_101102) else (if i.val < 179 then g32p_supplierForest_node_101216 else g32p_supplierForest_node_101307)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_101346 else g32p_supplierForest_node_101358) else (if i.val < 183 then g32p_supplierForest_node_101492 else g32p_supplierForest_node_101496))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_101519 else g32p_supplierForest_node_101541) else (if i.val < 187 then g32p_supplierForest_node_101606 else g32p_supplierForest_node_101715)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_101752 else g32p_supplierForest_node_101784) else (if i.val < 191 then g32p_supplierForest_node_101800 else g32p_supplierForest_node_101830)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_101896 else g32p_supplierForest_node_101926) else (if i.val < 195 then g32p_supplierForest_node_102024 else g32p_supplierForest_node_102036)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_102045 else g32p_supplierForest_node_102074) else (if i.val < 199 then g32p_supplierForest_node_102098 else g32p_supplierForest_node_102195))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_102198 else g32p_supplierForest_node_102213) else (if i.val < 203 then g32p_supplierForest_node_102303 else g32p_supplierForest_node_102321)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_102329 else g32p_supplierForest_node_102362) else (if i.val < 207 then g32p_supplierForest_node_102376 else g32p_supplierForest_node_102377)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_102423 else g32p_supplierForest_node_102447) else (if i.val < 211 then g32p_supplierForest_node_102450 else g32p_supplierForest_node_102470)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_102522 else g32p_supplierForest_node_102553) else (if i.val < 215 then g32p_supplierForest_node_102578 else g32p_supplierForest_node_102586))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_102609 else g32p_supplierForest_node_102615) else (if i.val < 219 then g32p_supplierForest_node_102631 else g32p_supplierForest_node_102634)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_102642 else g32p_supplierForest_node_102644) else (if i.val < 223 then g32p_supplierForest_node_102661 else g32p_supplierForest_node_102678))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_102725 else g32p_supplierForest_node_102740) else (if i.val < 227 then g32p_supplierForest_node_102743 else g32p_supplierForest_node_102749)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_102835 else g32p_supplierForest_node_102850) else (if i.val < 231 then g32p_supplierForest_node_102857 else g32p_supplierForest_node_102885))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_102886 else g32p_supplierForest_node_102904) else (if i.val < 235 then g32p_supplierForest_node_102914 else g32p_supplierForest_node_102928)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_102932 else g32p_supplierForest_node_102937) else (if i.val < 239 then g32p_supplierForest_node_102984 else g32p_supplierForest_node_103025)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_103037 else g32p_supplierForest_node_103041) else (if i.val < 243 then g32p_supplierForest_node_103116 else g32p_supplierForest_node_103153)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_103211 else g32p_supplierForest_node_103272) else (if i.val < 247 then g32p_supplierForest_node_103332 else g32p_supplierForest_node_103348))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_103370 else g32p_supplierForest_node_103387) else (if i.val < 251 then g32p_supplierForest_node_103414 else g32p_supplierForest_node_103415)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_103499 else g32p_supplierForest_node_103535) else (if i.val < 255 then g32p_supplierForest_node_103571 else g32p_supplierForest_node_103585))))))))

def g32p_supplierForest_classes_124 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 46 else 49) else (if i.val < 3 then 46 else 46)) else (if i.val < 6 then (if i.val < 5 then 26 else 49) else (if i.val < 7 then 26 else 47))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 46 else 25) else (if i.val < 11 then 46 else 46)) else (if i.val < 14 then (if i.val < 13 then 26 else 54) else (if i.val < 15 then 46 else 26)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 80 else 50) else (if i.val < 19 then 49 else 26)) else (if i.val < 22 then (if i.val < 21 then 46 else 55) else (if i.val < 23 then 49 else 49))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 46 else 49) else (if i.val < 27 then 46 else 46)) else (if i.val < 30 then (if i.val < 29 then 46 else 86) else (if i.val < 31 then 55 else 26))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 49 else 47) else (if i.val < 35 then 47 else 46)) else (if i.val < 38 then (if i.val < 37 then 55 else 49) else (if i.val < 39 then 46 else 45))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 47 else 49) else (if i.val < 43 then 55 else 47)) else (if i.val < 46 then (if i.val < 45 then 53 else 49) else (if i.val < 47 then 26 else 26)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 49 else 12) else (if i.val < 51 then 53 else 55)) else (if i.val < 54 then (if i.val < 53 then 26 else 47) else (if i.val < 55 then 25 else 49))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 49 else 46) else (if i.val < 59 then 46 else 46)) else (if i.val < 62 then (if i.val < 61 then 46 else 46) else (if i.val < 63 then 50 else 26)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 46) else (if i.val < 67 then 46 else 46)) else (if i.val < 70 then (if i.val < 69 then 47 else 49) else (if i.val < 71 then 46 else 26))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 47 else 49) else (if i.val < 75 then 25 else 26)) else (if i.val < 78 then (if i.val < 77 then 47 else 54) else (if i.val < 79 then 49 else 54)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 55 else 55) else (if i.val < 83 then 46 else 80)) else (if i.val < 86 then (if i.val < 85 then 47 else 49) else (if i.val < 87 then 83 else 45))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 83 else 46) else (if i.val < 91 then 46 else 50)) else (if i.val < 94 then (if i.val < 93 then 46 else 49) else (if i.val < 95 then 49 else 53))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 46 else 53) else (if i.val < 99 then 50 else 54)) else (if i.val < 102 then (if i.val < 101 then 46 else 49) else (if i.val < 103 then 86 else 26))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 49 else 46) else (if i.val < 107 then 49 else 46)) else (if i.val < 110 then (if i.val < 109 then 49 else 25) else (if i.val < 111 then 55 else 46)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 49 else 49) else (if i.val < 115 then 49 else 53)) else (if i.val < 118 then (if i.val < 117 then 55 else 49) else (if i.val < 119 then 26 else 47))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 47 else 53) else (if i.val < 123 then 49 else 46)) else (if i.val < 126 then (if i.val < 125 then 46 else 54) else (if i.val < 127 then 80 else 49))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 46 else 46) else (if i.val < 131 then 86 else 49)) else (if i.val < 134 then (if i.val < 133 then 27 else 55) else (if i.val < 135 then 49 else 25))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 54 else 54) else (if i.val < 139 then 26 else 55)) else (if i.val < 142 then (if i.val < 141 then 85 else 86) else (if i.val < 143 then 49 else 49)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 80 else 49) else (if i.val < 147 then 47 else 53)) else (if i.val < 150 then (if i.val < 149 then 49 else 46) else (if i.val < 151 then 47 else 46))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 26 else 49) else (if i.val < 155 then 26 else 49)) else (if i.val < 158 then (if i.val < 157 then 45 else 49) else (if i.val < 159 then 49 else 49))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 55 else 49) else (if i.val < 163 then 46 else 9)) else (if i.val < 166 then (if i.val < 165 then 49 else 47) else (if i.val < 167 then 25 else 46))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 26 else 80) else (if i.val < 171 then 49 else 46)) else (if i.val < 174 then (if i.val < 173 then 53 else 46) else (if i.val < 175 then 50 else 54)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 46 else 25) else (if i.val < 179 then 53 else 86)) else (if i.val < 182 then (if i.val < 181 then 45 else 53) else (if i.val < 183 then 26 else 46))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 80 else 49) else (if i.val < 187 then 48 else 25)) else (if i.val < 190 then (if i.val < 189 then 46 else 49) else (if i.val < 191 then 47 else 86)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 30 else 57) else (if i.val < 195 then 36 else 30)) else (if i.val < 198 then (if i.val < 197 then 57 else 57) else (if i.val < 199 then 30 else 57))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 57 else 60) else (if i.val < 203 then 57 else 57)) else (if i.val < 206 then (if i.val < 205 then 57 else 57) else (if i.val < 207 then 57 else 30)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 62 else 16) else (if i.val < 211 then 61 else 57)) else (if i.val < 214 then (if i.val < 213 then 60 else 16) else (if i.val < 215 then 57 else 16))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 57 else 30) else (if i.val < 219 then 14 else 30)) else (if i.val < 222 then (if i.val < 221 then 36 else 57) else (if i.val < 223 then 16 else 16))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 30 else 57) else (if i.val < 227 then 58 else 57)) else (if i.val < 230 then (if i.val < 229 then 29 else 63) else (if i.val < 231 then 30 else 30))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 30 else 57) else (if i.val < 235 then 30 else 30)) else (if i.val < 238 then (if i.val < 237 then 60 else 57) else (if i.val < 239 then 30 else 57)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 16 else 30) else (if i.val < 243 then 66 else 57)) else (if i.val < 246 then (if i.val < 245 then 66 else 57) else (if i.val < 247 then 30 else 30))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 16 else 59) else (if i.val < 251 then 59 else 57)) else (if i.val < 254 then (if i.val < 253 then 58 else 57) else (if i.val < 255 then 30 else 16))))))))

theorem g32p_supplierForest_actual_124 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_124 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_124 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_095738
  · exact g32p_supplierForest_actual_095761
  · exact g32p_supplierForest_actual_095817
  · exact g32p_supplierForest_actual_095850
  · exact g32p_supplierForest_actual_095879
  · exact g32p_supplierForest_actual_095880
  · exact g32p_supplierForest_actual_095919
  · exact g32p_supplierForest_actual_095921
  · exact g32p_supplierForest_actual_095922
  · exact g32p_supplierForest_actual_095930
  · exact g32p_supplierForest_actual_095958
  · exact g32p_supplierForest_actual_095965
  · exact g32p_supplierForest_actual_096050
  · exact g32p_supplierForest_actual_096110
  · exact g32p_supplierForest_actual_096154
  · exact g32p_supplierForest_actual_096196
  · exact g32p_supplierForest_actual_096260
  · exact g32p_supplierForest_actual_096293
  · exact g32p_supplierForest_actual_096299
  · exact g32p_supplierForest_actual_096308
  · exact g32p_supplierForest_actual_096317
  · exact g32p_supplierForest_actual_096400
  · exact g32p_supplierForest_actual_096405
  · exact g32p_supplierForest_actual_096441
  · exact g32p_supplierForest_actual_096514
  · exact g32p_supplierForest_actual_096542
  · exact g32p_supplierForest_actual_096626
  · exact g32p_supplierForest_actual_096633
  · exact g32p_supplierForest_actual_096657
  · exact g32p_supplierForest_actual_096658
  · exact g32p_supplierForest_actual_096668
  · exact g32p_supplierForest_actual_096717
  · exact g32p_supplierForest_actual_096761
  · exact g32p_supplierForest_actual_096780
  · exact g32p_supplierForest_actual_096807
  · exact g32p_supplierForest_actual_096820
  · exact g32p_supplierForest_actual_096846
  · exact g32p_supplierForest_actual_096897
  · exact g32p_supplierForest_actual_096946
  · exact g32p_supplierForest_actual_096956
  · exact g32p_supplierForest_actual_097032
  · exact g32p_supplierForest_actual_097033
  · exact g32p_supplierForest_actual_097067
  · exact g32p_supplierForest_actual_097095
  · exact g32p_supplierForest_actual_097117
  · exact g32p_supplierForest_actual_097182
  · exact g32p_supplierForest_actual_097258
  · exact g32p_supplierForest_actual_097267
  · exact g32p_supplierForest_actual_097355
  · exact g32p_supplierForest_actual_097357
  · exact g32p_supplierForest_actual_097384
  · exact g32p_supplierForest_actual_097393
  · exact g32p_supplierForest_actual_097397
  · exact g32p_supplierForest_actual_097450
  · exact g32p_supplierForest_actual_097460
  · exact g32p_supplierForest_actual_097473
  · exact g32p_supplierForest_actual_097479
  · exact g32p_supplierForest_actual_097484
  · exact g32p_supplierForest_actual_097508
  · exact g32p_supplierForest_actual_097513
  · exact g32p_supplierForest_actual_097538
  · exact g32p_supplierForest_actual_097572
  · exact g32p_supplierForest_actual_097601
  · exact g32p_supplierForest_actual_097607
  · exact g32p_supplierForest_actual_097628
  · exact g32p_supplierForest_actual_097647
  · exact g32p_supplierForest_actual_097669
  · exact g32p_supplierForest_actual_097711
  · exact g32p_supplierForest_actual_097721
  · exact g32p_supplierForest_actual_097724
  · exact g32p_supplierForest_actual_097786
  · exact g32p_supplierForest_actual_097788
  · exact g32p_supplierForest_actual_097793
  · exact g32p_supplierForest_actual_097794
  · exact g32p_supplierForest_actual_097817
  · exact g32p_supplierForest_actual_097827
  · exact g32p_supplierForest_actual_097839
  · exact g32p_supplierForest_actual_097877
  · exact g32p_supplierForest_actual_097883
  · exact g32p_supplierForest_actual_097911
  · exact g32p_supplierForest_actual_097976
  · exact g32p_supplierForest_actual_097982
  · exact g32p_supplierForest_actual_098007
  · exact g32p_supplierForest_actual_098019
  · exact g32p_supplierForest_actual_098021
  · exact g32p_supplierForest_actual_098027
  · exact g32p_supplierForest_actual_098070
  · exact g32p_supplierForest_actual_098115
  · exact g32p_supplierForest_actual_098151
  · exact g32p_supplierForest_actual_098203
  · exact g32p_supplierForest_actual_098243
  · exact g32p_supplierForest_actual_098249
  · exact g32p_supplierForest_actual_098307
  · exact g32p_supplierForest_actual_098382
  · exact g32p_supplierForest_actual_098424
  · exact g32p_supplierForest_actual_098526
  · exact g32p_supplierForest_actual_098562
  · exact g32p_supplierForest_actual_098592
  · exact g32p_supplierForest_actual_098632
  · exact g32p_supplierForest_actual_098649
  · exact g32p_supplierForest_actual_098679
  · exact g32p_supplierForest_actual_098695
  · exact g32p_supplierForest_actual_098753
  · exact g32p_supplierForest_actual_098797
  · exact g32p_supplierForest_actual_098801
  · exact g32p_supplierForest_actual_098822
  · exact g32p_supplierForest_actual_098854
  · exact g32p_supplierForest_actual_098902
  · exact g32p_supplierForest_actual_098945
  · exact g32p_supplierForest_actual_098995
  · exact g32p_supplierForest_actual_098997
  · exact g32p_supplierForest_actual_099000
  · exact g32p_supplierForest_actual_099025
  · exact g32p_supplierForest_actual_099052
  · exact g32p_supplierForest_actual_099119
  · exact g32p_supplierForest_actual_099286
  · exact g32p_supplierForest_actual_099304
  · exact g32p_supplierForest_actual_099309
  · exact g32p_supplierForest_actual_099328
  · exact g32p_supplierForest_actual_099393
  · exact g32p_supplierForest_actual_099448
  · exact g32p_supplierForest_actual_099514
  · exact g32p_supplierForest_actual_099600
  · exact g32p_supplierForest_actual_099636
  · exact g32p_supplierForest_actual_099639
  · exact g32p_supplierForest_actual_099676
  · exact g32p_supplierForest_actual_099701
  · exact g32p_supplierForest_actual_099730
  · exact g32p_supplierForest_actual_099740
  · exact g32p_supplierForest_actual_099761
  · exact g32p_supplierForest_actual_099814
  · exact g32p_supplierForest_actual_099853
  · exact g32p_supplierForest_actual_099862
  · exact g32p_supplierForest_actual_099864
  · exact g32p_supplierForest_actual_099880
  · exact g32p_supplierForest_actual_099882
  · exact g32p_supplierForest_actual_099897
  · exact g32p_supplierForest_actual_099921
  · exact g32p_supplierForest_actual_099923
  · exact g32p_supplierForest_actual_099927
  · exact g32p_supplierForest_actual_099986
  · exact g32p_supplierForest_actual_099997
  · exact g32p_supplierForest_actual_100055
  · exact g32p_supplierForest_actual_100103
  · exact g32p_supplierForest_actual_100150
  · exact g32p_supplierForest_actual_100163
  · exact g32p_supplierForest_actual_100189
  · exact g32p_supplierForest_actual_100201
  · exact g32p_supplierForest_actual_100208
  · exact g32p_supplierForest_actual_100271
  · exact g32p_supplierForest_actual_100281
  · exact g32p_supplierForest_actual_100411
  · exact g32p_supplierForest_actual_100418
  · exact g32p_supplierForest_actual_100421
  · exact g32p_supplierForest_actual_100438
  · exact g32p_supplierForest_actual_100447
  · exact g32p_supplierForest_actual_100450
  · exact g32p_supplierForest_actual_100453
  · exact g32p_supplierForest_actual_100456
  · exact g32p_supplierForest_actual_100508
  · exact g32p_supplierForest_actual_100567
  · exact g32p_supplierForest_actual_100687
  · exact g32p_supplierForest_actual_100713
  · exact g32p_supplierForest_actual_100715
  · exact g32p_supplierForest_actual_100721
  · exact g32p_supplierForest_actual_100753
  · exact g32p_supplierForest_actual_100755
  · exact g32p_supplierForest_actual_100854
  · exact g32p_supplierForest_actual_100859
  · exact g32p_supplierForest_actual_100905
  · exact g32p_supplierForest_actual_100962
  · exact g32p_supplierForest_actual_100985
  · exact g32p_supplierForest_actual_100996
  · exact g32p_supplierForest_actual_100999
  · exact g32p_supplierForest_actual_101092
  · exact g32p_supplierForest_actual_101093
  · exact g32p_supplierForest_actual_101100
  · exact g32p_supplierForest_actual_101102
  · exact g32p_supplierForest_actual_101216
  · exact g32p_supplierForest_actual_101307
  · exact g32p_supplierForest_actual_101346
  · exact g32p_supplierForest_actual_101358
  · exact g32p_supplierForest_actual_101492
  · exact g32p_supplierForest_actual_101496
  · exact g32p_supplierForest_actual_101519
  · exact g32p_supplierForest_actual_101541
  · exact g32p_supplierForest_actual_101606
  · exact g32p_supplierForest_actual_101715
  · exact g32p_supplierForest_actual_101752
  · exact g32p_supplierForest_actual_101784
  · exact g32p_supplierForest_actual_101800
  · exact g32p_supplierForest_actual_101830
  · exact g32p_supplierForest_actual_101896
  · exact g32p_supplierForest_actual_101926
  · exact g32p_supplierForest_actual_102024
  · exact g32p_supplierForest_actual_102036
  · exact g32p_supplierForest_actual_102045
  · exact g32p_supplierForest_actual_102074
  · exact g32p_supplierForest_actual_102098
  · exact g32p_supplierForest_actual_102195
  · exact g32p_supplierForest_actual_102198
  · exact g32p_supplierForest_actual_102213
  · exact g32p_supplierForest_actual_102303
  · exact g32p_supplierForest_actual_102321
  · exact g32p_supplierForest_actual_102329
  · exact g32p_supplierForest_actual_102362
  · exact g32p_supplierForest_actual_102376
  · exact g32p_supplierForest_actual_102377
  · exact g32p_supplierForest_actual_102423
  · exact g32p_supplierForest_actual_102447
  · exact g32p_supplierForest_actual_102450
  · exact g32p_supplierForest_actual_102470
  · exact g32p_supplierForest_actual_102522
  · exact g32p_supplierForest_actual_102553
  · exact g32p_supplierForest_actual_102578
  · exact g32p_supplierForest_actual_102586
  · exact g32p_supplierForest_actual_102609
  · exact g32p_supplierForest_actual_102615
  · exact g32p_supplierForest_actual_102631
  · exact g32p_supplierForest_actual_102634
  · exact g32p_supplierForest_actual_102642
  · exact g32p_supplierForest_actual_102644
  · exact g32p_supplierForest_actual_102661
  · exact g32p_supplierForest_actual_102678
  · exact g32p_supplierForest_actual_102725
  · exact g32p_supplierForest_actual_102740
  · exact g32p_supplierForest_actual_102743
  · exact g32p_supplierForest_actual_102749
  · exact g32p_supplierForest_actual_102835
  · exact g32p_supplierForest_actual_102850
  · exact g32p_supplierForest_actual_102857
  · exact g32p_supplierForest_actual_102885
  · exact g32p_supplierForest_actual_102886
  · exact g32p_supplierForest_actual_102904
  · exact g32p_supplierForest_actual_102914
  · exact g32p_supplierForest_actual_102928
  · exact g32p_supplierForest_actual_102932
  · exact g32p_supplierForest_actual_102937
  · exact g32p_supplierForest_actual_102984
  · exact g32p_supplierForest_actual_103025
  · exact g32p_supplierForest_actual_103037
  · exact g32p_supplierForest_actual_103041
  · exact g32p_supplierForest_actual_103116
  · exact g32p_supplierForest_actual_103153
  · exact g32p_supplierForest_actual_103211
  · exact g32p_supplierForest_actual_103272
  · exact g32p_supplierForest_actual_103332
  · exact g32p_supplierForest_actual_103348
  · exact g32p_supplierForest_actual_103370
  · exact g32p_supplierForest_actual_103387
  · exact g32p_supplierForest_actual_103414
  · exact g32p_supplierForest_actual_103415
  · exact g32p_supplierForest_actual_103499
  · exact g32p_supplierForest_actual_103535
  · exact g32p_supplierForest_actual_103571
  · exact g32p_supplierForest_actual_103585

def g32p_supplierForest_nodes_125 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_103593 else g32p_supplierForest_node_103598) else (if i.val < 3 then g32p_supplierForest_node_103617 else g32p_supplierForest_node_103654)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_103673 else g32p_supplierForest_node_103691) else (if i.val < 7 then g32p_supplierForest_node_103739 else g32p_supplierForest_node_103762))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_103800 else g32p_supplierForest_node_103935) else (if i.val < 11 then g32p_supplierForest_node_103955 else g32p_supplierForest_node_103962)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_104004 else g32p_supplierForest_node_104049) else (if i.val < 15 then g32p_supplierForest_node_104055 else g32p_supplierForest_node_104057)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_104093 else g32p_supplierForest_node_104101) else (if i.val < 19 then g32p_supplierForest_node_104170 else g32p_supplierForest_node_104190)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_104209 else g32p_supplierForest_node_104214) else (if i.val < 23 then g32p_supplierForest_node_104281 else g32p_supplierForest_node_104297))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_104322 else g32p_supplierForest_node_104361) else (if i.val < 27 then g32p_supplierForest_node_104443 else g32p_supplierForest_node_104457)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_104517 else g32p_supplierForest_node_104518) else (if i.val < 31 then g32p_supplierForest_node_104522 else g32p_supplierForest_node_104596))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_104601 else g32p_supplierForest_node_104602) else (if i.val < 35 then g32p_supplierForest_node_104609 else g32p_supplierForest_node_104637)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_104645 else g32p_supplierForest_node_104706) else (if i.val < 39 then g32p_supplierForest_node_104736 else g32p_supplierForest_node_104746))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_104768 else g32p_supplierForest_node_104822) else (if i.val < 43 then g32p_supplierForest_node_104829 else g32p_supplierForest_node_104830)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_104836 else g32p_supplierForest_node_104840) else (if i.val < 47 then g32p_supplierForest_node_104876 else g32p_supplierForest_node_104894)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_104929 else g32p_supplierForest_node_104934) else (if i.val < 51 then g32p_supplierForest_node_105004 else g32p_supplierForest_node_105039)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_105055 else g32p_supplierForest_node_105083) else (if i.val < 55 then g32p_supplierForest_node_105089 else g32p_supplierForest_node_105099))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_105109 else g32p_supplierForest_node_105111) else (if i.val < 59 then g32p_supplierForest_node_105141 else g32p_supplierForest_node_105144)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_105216 else g32p_supplierForest_node_105240) else (if i.val < 63 then g32p_supplierForest_node_105314 else g32p_supplierForest_node_105318)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_105338 else g32p_supplierForest_node_105375) else (if i.val < 67 then g32p_supplierForest_node_105378 else g32p_supplierForest_node_105386)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_105396 else g32p_supplierForest_node_105399) else (if i.val < 71 then g32p_supplierForest_node_105430 else g32p_supplierForest_node_105453))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_105472 else g32p_supplierForest_node_105475) else (if i.val < 75 then g32p_supplierForest_node_105485 else g32p_supplierForest_node_105514)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_105570 else g32p_supplierForest_node_105614) else (if i.val < 79 then g32p_supplierForest_node_105642 else g32p_supplierForest_node_105671)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_105687 else g32p_supplierForest_node_105707) else (if i.val < 83 then g32p_supplierForest_node_105712 else g32p_supplierForest_node_105768)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_105775 else g32p_supplierForest_node_105785) else (if i.val < 87 then g32p_supplierForest_node_105843 else g32p_supplierForest_node_105917))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_105923 else g32p_supplierForest_node_105951) else (if i.val < 91 then g32p_supplierForest_node_106078 else g32p_supplierForest_node_106090)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_106092 else g32p_supplierForest_node_106095) else (if i.val < 95 then g32p_supplierForest_node_106109 else g32p_supplierForest_node_106139))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_106236 else g32p_supplierForest_node_106237) else (if i.val < 99 then g32p_supplierForest_node_106281 else g32p_supplierForest_node_106308)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_106309 else g32p_supplierForest_node_106315) else (if i.val < 103 then g32p_supplierForest_node_106368 else g32p_supplierForest_node_106391))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_106412 else g32p_supplierForest_node_106420) else (if i.val < 107 then g32p_supplierForest_node_106470 else g32p_supplierForest_node_106546)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_106574 else g32p_supplierForest_node_106584) else (if i.val < 111 then g32p_supplierForest_node_106685 else g32p_supplierForest_node_106734)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_106758 else g32p_supplierForest_node_106793) else (if i.val < 115 then g32p_supplierForest_node_106824 else g32p_supplierForest_node_106844)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_106904 else g32p_supplierForest_node_106909) else (if i.val < 119 then g32p_supplierForest_node_106928 else g32p_supplierForest_node_106972))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_107008 else g32p_supplierForest_node_107114) else (if i.val < 123 then g32p_supplierForest_node_107184 else g32p_supplierForest_node_107198)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_107208 else g32p_supplierForest_node_107232) else (if i.val < 127 then g32p_supplierForest_node_107236 else g32p_supplierForest_node_107344))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_107399 else g32p_supplierForest_node_107463) else (if i.val < 131 then g32p_supplierForest_node_107468 else g32p_supplierForest_node_107479)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_107488 else g32p_supplierForest_node_107493) else (if i.val < 135 then g32p_supplierForest_node_107503 else g32p_supplierForest_node_107531))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_107541 else g32p_supplierForest_node_107569) else (if i.val < 139 then g32p_supplierForest_node_107572 else g32p_supplierForest_node_107629)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_107667 else g32p_supplierForest_node_107695) else (if i.val < 143 then g32p_supplierForest_node_107705 else g32p_supplierForest_node_107719)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_107730 else g32p_supplierForest_node_107738) else (if i.val < 147 then g32p_supplierForest_node_107764 else g32p_supplierForest_node_107774)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_107778 else g32p_supplierForest_node_107815) else (if i.val < 151 then g32p_supplierForest_node_107885 else g32p_supplierForest_node_107942))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_107957 else g32p_supplierForest_node_107970) else (if i.val < 155 then g32p_supplierForest_node_108042 else g32p_supplierForest_node_108077)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_108091 else g32p_supplierForest_node_108128) else (if i.val < 159 then g32p_supplierForest_node_108143 else g32p_supplierForest_node_108148))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_108160 else g32p_supplierForest_node_108179) else (if i.val < 163 then g32p_supplierForest_node_108242 else g32p_supplierForest_node_108269)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_108323 else g32p_supplierForest_node_108386) else (if i.val < 167 then g32p_supplierForest_node_108402 else g32p_supplierForest_node_108487))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_108593 else g32p_supplierForest_node_108632) else (if i.val < 171 then g32p_supplierForest_node_108637 else g32p_supplierForest_node_108676)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_108700 else g32p_supplierForest_node_108741) else (if i.val < 175 then g32p_supplierForest_node_108777 else g32p_supplierForest_node_108883)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_108907 else g32p_supplierForest_node_108972) else (if i.val < 179 then g32p_supplierForest_node_109053 else g32p_supplierForest_node_109086)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_109129 else g32p_supplierForest_node_109138) else (if i.val < 183 then g32p_supplierForest_node_109146 else g32p_supplierForest_node_109151))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_109189 else g32p_supplierForest_node_109190) else (if i.val < 187 then g32p_supplierForest_node_109199 else g32p_supplierForest_node_109211)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_109212 else g32p_supplierForest_node_109250) else (if i.val < 191 then g32p_supplierForest_node_109344 else g32p_supplierForest_node_109391)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_109398 else g32p_supplierForest_node_109399) else (if i.val < 195 then g32p_supplierForest_node_109411 else g32p_supplierForest_node_109413)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_109441 else g32p_supplierForest_node_109453) else (if i.val < 199 then g32p_supplierForest_node_109459 else g32p_supplierForest_node_109513))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_109544 else g32p_supplierForest_node_109556) else (if i.val < 203 then g32p_supplierForest_node_109585 else g32p_supplierForest_node_109659)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_109660 else g32p_supplierForest_node_109668) else (if i.val < 207 then g32p_supplierForest_node_109688 else g32p_supplierForest_node_109714)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_109741 else g32p_supplierForest_node_109757) else (if i.val < 211 then g32p_supplierForest_node_109791 else g32p_supplierForest_node_109795)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_109798 else g32p_supplierForest_node_109826) else (if i.val < 215 then g32p_supplierForest_node_109830 else g32p_supplierForest_node_109843))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_109847 else g32p_supplierForest_node_109876) else (if i.val < 219 then g32p_supplierForest_node_109889 else g32p_supplierForest_node_109928)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_109935 else g32p_supplierForest_node_109947) else (if i.val < 223 then g32p_supplierForest_node_109968 else g32p_supplierForest_node_110022))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_110031 else g32p_supplierForest_node_110034) else (if i.val < 227 then g32p_supplierForest_node_110051 else g32p_supplierForest_node_110088)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_110137 else g32p_supplierForest_node_110191) else (if i.val < 231 then g32p_supplierForest_node_110227 else g32p_supplierForest_node_110264))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_110297 else g32p_supplierForest_node_110335) else (if i.val < 235 then g32p_supplierForest_node_110366 else g32p_supplierForest_node_110419)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_110422 else g32p_supplierForest_node_110438) else (if i.val < 239 then g32p_supplierForest_node_110454 else g32p_supplierForest_node_110478)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_110542 else g32p_supplierForest_node_110561) else (if i.val < 243 then g32p_supplierForest_node_110589 else g32p_supplierForest_node_110590)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_110615 else g32p_supplierForest_node_110646) else (if i.val < 247 then g32p_supplierForest_node_110682 else g32p_supplierForest_node_110685))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_110704 else g32p_supplierForest_node_110709) else (if i.val < 251 then g32p_supplierForest_node_110713 else g32p_supplierForest_node_110812)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_110834 else g32p_supplierForest_node_110871) else (if i.val < 255 then g32p_supplierForest_node_110882 else g32p_supplierForest_node_110884))))))))

def g32p_supplierForest_classes_125 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 60 else 63) else (if i.val < 3 then 60 else 60)) else (if i.val < 6 then (if i.val < 5 then 61 else 58) else (if i.val < 7 then 57 else 30))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 63 else 57) else (if i.val < 11 then 16 else 30)) else (if i.val < 14 then (if i.val < 13 then 59 else 57) else (if i.val < 15 then 30 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 33 else 57) else (if i.val < 19 then 57 else 60)) else (if i.val < 22 then (if i.val < 21 then 16 else 59) else (if i.val < 23 then 60 else 57))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 16 else 36) else (if i.val < 27 then 17 else 36)) else (if i.val < 30 then (if i.val < 29 then 60 else 29) else (if i.val < 31 then 60 else 57))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 57 else 57) else (if i.val < 35 then 30 else 16)) else (if i.val < 38 then (if i.val < 37 then 16 else 59) else (if i.val < 39 then 57 else 60))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 30 else 62) else (if i.val < 43 then 36 else 30)) else (if i.val < 46 then (if i.val < 45 then 57 else 15) else (if i.val < 47 then 57 else 33)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 29 else 30) else (if i.val < 51 then 58 else 30)) else (if i.val < 54 then (if i.val < 53 then 29 else 36) else (if i.val < 55 then 59 else 57))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 16 else 57) else (if i.val < 59 then 33 else 36)) else (if i.val < 62 then (if i.val < 61 then 57 else 66) else (if i.val < 63 then 57 else 59)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 57 else 57) else (if i.val < 67 then 14 else 63)) else (if i.val < 70 then (if i.val < 69 then 30 else 57) else (if i.val < 71 then 57 else 57))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 35 else 30) else (if i.val < 75 then 60 else 29)) else (if i.val < 78 then (if i.val < 77 then 60 else 59) else (if i.val < 79 then 29 else 60)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 57 else 15) else (if i.val < 83 then 17 else 60)) else (if i.val < 86 then (if i.val < 85 then 30 else 30) else (if i.val < 87 then 15 else 16))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 30 else 16) else (if i.val < 91 then 16 else 57)) else (if i.val < 94 then (if i.val < 93 then 57 else 59) else (if i.val < 95 then 30 else 30))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 29 else 30) else (if i.val < 99 then 29 else 57)) else (if i.val < 102 then (if i.val < 101 then 30 else 30) else (if i.val < 103 then 30 else 29))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 30 else 57) else (if i.val < 107 then 30 else 29)) else (if i.val < 110 then (if i.val < 109 then 57 else 60) else (if i.val < 111 then 30 else 29)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 57 else 57) else (if i.val < 115 then 57 else 57)) else (if i.val < 118 then (if i.val < 117 then 57 else 59) else (if i.val < 119 then 30 else 16))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 57 else 59) else (if i.val < 123 then 57 else 62)) else (if i.val < 126 then (if i.val < 125 then 29 else 30) else (if i.val < 127 then 57 else 57))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 66 else 66) else (if i.val < 131 then 30 else 29)) else (if i.val < 134 then (if i.val < 133 then 30 else 16) else (if i.val < 135 then 59 else 57))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 30 else 30) else (if i.val < 139 then 59 else 33)) else (if i.val < 142 then (if i.val < 141 then 16 else 57) else (if i.val < 143 then 30 else 57)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 29 else 62) else (if i.val < 147 then 60 else 30)) else (if i.val < 150 then (if i.val < 149 then 57 else 36) else (if i.val < 151 then 66 else 57))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 57 else 59) else (if i.val < 155 then 57 else 64)) else (if i.val < 158 then (if i.val < 157 then 66 else 57) else (if i.val < 159 then 30 else 16))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 66 else 36) else (if i.val < 163 then 57 else 30)) else (if i.val < 166 then (if i.val < 165 then 57 else 36) else (if i.val < 167 then 30 else 57))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 57 else 30) else (if i.val < 171 then 63 else 30)) else (if i.val < 174 then (if i.val < 173 then 60 else 90) else (if i.val < 175 then 66 else 63)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 29 else 30) else (if i.val < 179 then 57 else 57)) else (if i.val < 182 then (if i.val < 181 then 57 else 57) else (if i.val < 183 then 57 else 57))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 57 else 16) else (if i.val < 187 then 57 else 58)) else (if i.val < 190 then (if i.val < 189 then 30 else 58) else (if i.val < 191 then 16 else 60)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 35 else 57) else (if i.val < 195 then 60 else 33)) else (if i.val < 198 then (if i.val < 197 then 57 else 58) else (if i.val < 199 then 36 else 62))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 58 else 57) else (if i.val < 203 then 60 else 15)) else (if i.val < 206 then (if i.val < 205 then 58 else 66) else (if i.val < 207 then 30 else 60)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 36 else 63) else (if i.val < 211 then 66 else 29)) else (if i.val < 214 then (if i.val < 213 then 30 else 57) else (if i.val < 215 then 36 else 30))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 62 else 57) else (if i.val < 219 then 63 else 30)) else (if i.val < 222 then (if i.val < 221 then 33 else 60) else (if i.val < 223 then 57 else 57))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 36 else 30) else (if i.val < 227 then 29 else 16)) else (if i.val < 230 then (if i.val < 229 then 14 else 58) else (if i.val < 231 then 60 else 60))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 16 else 66) else (if i.val < 235 then 60 else 59)) else (if i.val < 238 then (if i.val < 237 then 30 else 16) else (if i.val < 239 then 57 else 60)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 57 else 33) else (if i.val < 243 then 62 else 29)) else (if i.val < 246 then (if i.val < 245 then 30 else 30) else (if i.val < 247 then 15 else 30))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 30 else 57) else (if i.val < 251 then 57 else 57)) else (if i.val < 254 then (if i.val < 253 then 57 else 57) else (if i.val < 255 then 59 else 30))))))))

theorem g32p_supplierForest_actual_125 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_125 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_125 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_103593
  · exact g32p_supplierForest_actual_103598
  · exact g32p_supplierForest_actual_103617
  · exact g32p_supplierForest_actual_103654
  · exact g32p_supplierForest_actual_103673
  · exact g32p_supplierForest_actual_103691
  · exact g32p_supplierForest_actual_103739
  · exact g32p_supplierForest_actual_103762
  · exact g32p_supplierForest_actual_103800
  · exact g32p_supplierForest_actual_103935
  · exact g32p_supplierForest_actual_103955
  · exact g32p_supplierForest_actual_103962
  · exact g32p_supplierForest_actual_104004
  · exact g32p_supplierForest_actual_104049
  · exact g32p_supplierForest_actual_104055
  · exact g32p_supplierForest_actual_104057
  · exact g32p_supplierForest_actual_104093
  · exact g32p_supplierForest_actual_104101
  · exact g32p_supplierForest_actual_104170
  · exact g32p_supplierForest_actual_104190
  · exact g32p_supplierForest_actual_104209
  · exact g32p_supplierForest_actual_104214
  · exact g32p_supplierForest_actual_104281
  · exact g32p_supplierForest_actual_104297
  · exact g32p_supplierForest_actual_104322
  · exact g32p_supplierForest_actual_104361
  · exact g32p_supplierForest_actual_104443
  · exact g32p_supplierForest_actual_104457
  · exact g32p_supplierForest_actual_104517
  · exact g32p_supplierForest_actual_104518
  · exact g32p_supplierForest_actual_104522
  · exact g32p_supplierForest_actual_104596
  · exact g32p_supplierForest_actual_104601
  · exact g32p_supplierForest_actual_104602
  · exact g32p_supplierForest_actual_104609
  · exact g32p_supplierForest_actual_104637
  · exact g32p_supplierForest_actual_104645
  · exact g32p_supplierForest_actual_104706
  · exact g32p_supplierForest_actual_104736
  · exact g32p_supplierForest_actual_104746
  · exact g32p_supplierForest_actual_104768
  · exact g32p_supplierForest_actual_104822
  · exact g32p_supplierForest_actual_104829
  · exact g32p_supplierForest_actual_104830
  · exact g32p_supplierForest_actual_104836
  · exact g32p_supplierForest_actual_104840
  · exact g32p_supplierForest_actual_104876
  · exact g32p_supplierForest_actual_104894
  · exact g32p_supplierForest_actual_104929
  · exact g32p_supplierForest_actual_104934
  · exact g32p_supplierForest_actual_105004
  · exact g32p_supplierForest_actual_105039
  · exact g32p_supplierForest_actual_105055
  · exact g32p_supplierForest_actual_105083
  · exact g32p_supplierForest_actual_105089
  · exact g32p_supplierForest_actual_105099
  · exact g32p_supplierForest_actual_105109
  · exact g32p_supplierForest_actual_105111
  · exact g32p_supplierForest_actual_105141
  · exact g32p_supplierForest_actual_105144
  · exact g32p_supplierForest_actual_105216
  · exact g32p_supplierForest_actual_105240
  · exact g32p_supplierForest_actual_105314
  · exact g32p_supplierForest_actual_105318
  · exact g32p_supplierForest_actual_105338
  · exact g32p_supplierForest_actual_105375
  · exact g32p_supplierForest_actual_105378
  · exact g32p_supplierForest_actual_105386
  · exact g32p_supplierForest_actual_105396
  · exact g32p_supplierForest_actual_105399
  · exact g32p_supplierForest_actual_105430
  · exact g32p_supplierForest_actual_105453
  · exact g32p_supplierForest_actual_105472
  · exact g32p_supplierForest_actual_105475
  · exact g32p_supplierForest_actual_105485
  · exact g32p_supplierForest_actual_105514
  · exact g32p_supplierForest_actual_105570
  · exact g32p_supplierForest_actual_105614
  · exact g32p_supplierForest_actual_105642
  · exact g32p_supplierForest_actual_105671
  · exact g32p_supplierForest_actual_105687
  · exact g32p_supplierForest_actual_105707
  · exact g32p_supplierForest_actual_105712
  · exact g32p_supplierForest_actual_105768
  · exact g32p_supplierForest_actual_105775
  · exact g32p_supplierForest_actual_105785
  · exact g32p_supplierForest_actual_105843
  · exact g32p_supplierForest_actual_105917
  · exact g32p_supplierForest_actual_105923
  · exact g32p_supplierForest_actual_105951
  · exact g32p_supplierForest_actual_106078
  · exact g32p_supplierForest_actual_106090
  · exact g32p_supplierForest_actual_106092
  · exact g32p_supplierForest_actual_106095
  · exact g32p_supplierForest_actual_106109
  · exact g32p_supplierForest_actual_106139
  · exact g32p_supplierForest_actual_106236
  · exact g32p_supplierForest_actual_106237
  · exact g32p_supplierForest_actual_106281
  · exact g32p_supplierForest_actual_106308
  · exact g32p_supplierForest_actual_106309
  · exact g32p_supplierForest_actual_106315
  · exact g32p_supplierForest_actual_106368
  · exact g32p_supplierForest_actual_106391
  · exact g32p_supplierForest_actual_106412
  · exact g32p_supplierForest_actual_106420
  · exact g32p_supplierForest_actual_106470
  · exact g32p_supplierForest_actual_106546
  · exact g32p_supplierForest_actual_106574
  · exact g32p_supplierForest_actual_106584
  · exact g32p_supplierForest_actual_106685
  · exact g32p_supplierForest_actual_106734
  · exact g32p_supplierForest_actual_106758
  · exact g32p_supplierForest_actual_106793
  · exact g32p_supplierForest_actual_106824
  · exact g32p_supplierForest_actual_106844
  · exact g32p_supplierForest_actual_106904
  · exact g32p_supplierForest_actual_106909
  · exact g32p_supplierForest_actual_106928
  · exact g32p_supplierForest_actual_106972
  · exact g32p_supplierForest_actual_107008
  · exact g32p_supplierForest_actual_107114
  · exact g32p_supplierForest_actual_107184
  · exact g32p_supplierForest_actual_107198
  · exact g32p_supplierForest_actual_107208
  · exact g32p_supplierForest_actual_107232
  · exact g32p_supplierForest_actual_107236
  · exact g32p_supplierForest_actual_107344
  · exact g32p_supplierForest_actual_107399
  · exact g32p_supplierForest_actual_107463
  · exact g32p_supplierForest_actual_107468
  · exact g32p_supplierForest_actual_107479
  · exact g32p_supplierForest_actual_107488
  · exact g32p_supplierForest_actual_107493
  · exact g32p_supplierForest_actual_107503
  · exact g32p_supplierForest_actual_107531
  · exact g32p_supplierForest_actual_107541
  · exact g32p_supplierForest_actual_107569
  · exact g32p_supplierForest_actual_107572
  · exact g32p_supplierForest_actual_107629
  · exact g32p_supplierForest_actual_107667
  · exact g32p_supplierForest_actual_107695
  · exact g32p_supplierForest_actual_107705
  · exact g32p_supplierForest_actual_107719
  · exact g32p_supplierForest_actual_107730
  · exact g32p_supplierForest_actual_107738
  · exact g32p_supplierForest_actual_107764
  · exact g32p_supplierForest_actual_107774
  · exact g32p_supplierForest_actual_107778
  · exact g32p_supplierForest_actual_107815
  · exact g32p_supplierForest_actual_107885
  · exact g32p_supplierForest_actual_107942
  · exact g32p_supplierForest_actual_107957
  · exact g32p_supplierForest_actual_107970
  · exact g32p_supplierForest_actual_108042
  · exact g32p_supplierForest_actual_108077
  · exact g32p_supplierForest_actual_108091
  · exact g32p_supplierForest_actual_108128
  · exact g32p_supplierForest_actual_108143
  · exact g32p_supplierForest_actual_108148
  · exact g32p_supplierForest_actual_108160
  · exact g32p_supplierForest_actual_108179
  · exact g32p_supplierForest_actual_108242
  · exact g32p_supplierForest_actual_108269
  · exact g32p_supplierForest_actual_108323
  · exact g32p_supplierForest_actual_108386
  · exact g32p_supplierForest_actual_108402
  · exact g32p_supplierForest_actual_108487
  · exact g32p_supplierForest_actual_108593
  · exact g32p_supplierForest_actual_108632
  · exact g32p_supplierForest_actual_108637
  · exact g32p_supplierForest_actual_108676
  · exact g32p_supplierForest_actual_108700
  · exact g32p_supplierForest_actual_108741
  · exact g32p_supplierForest_actual_108777
  · exact g32p_supplierForest_actual_108883
  · exact g32p_supplierForest_actual_108907
  · exact g32p_supplierForest_actual_108972
  · exact g32p_supplierForest_actual_109053
  · exact g32p_supplierForest_actual_109086
  · exact g32p_supplierForest_actual_109129
  · exact g32p_supplierForest_actual_109138
  · exact g32p_supplierForest_actual_109146
  · exact g32p_supplierForest_actual_109151
  · exact g32p_supplierForest_actual_109189
  · exact g32p_supplierForest_actual_109190
  · exact g32p_supplierForest_actual_109199
  · exact g32p_supplierForest_actual_109211
  · exact g32p_supplierForest_actual_109212
  · exact g32p_supplierForest_actual_109250
  · exact g32p_supplierForest_actual_109344
  · exact g32p_supplierForest_actual_109391
  · exact g32p_supplierForest_actual_109398
  · exact g32p_supplierForest_actual_109399
  · exact g32p_supplierForest_actual_109411
  · exact g32p_supplierForest_actual_109413
  · exact g32p_supplierForest_actual_109441
  · exact g32p_supplierForest_actual_109453
  · exact g32p_supplierForest_actual_109459
  · exact g32p_supplierForest_actual_109513
  · exact g32p_supplierForest_actual_109544
  · exact g32p_supplierForest_actual_109556
  · exact g32p_supplierForest_actual_109585
  · exact g32p_supplierForest_actual_109659
  · exact g32p_supplierForest_actual_109660
  · exact g32p_supplierForest_actual_109668
  · exact g32p_supplierForest_actual_109688
  · exact g32p_supplierForest_actual_109714
  · exact g32p_supplierForest_actual_109741
  · exact g32p_supplierForest_actual_109757
  · exact g32p_supplierForest_actual_109791
  · exact g32p_supplierForest_actual_109795
  · exact g32p_supplierForest_actual_109798
  · exact g32p_supplierForest_actual_109826
  · exact g32p_supplierForest_actual_109830
  · exact g32p_supplierForest_actual_109843
  · exact g32p_supplierForest_actual_109847
  · exact g32p_supplierForest_actual_109876
  · exact g32p_supplierForest_actual_109889
  · exact g32p_supplierForest_actual_109928
  · exact g32p_supplierForest_actual_109935
  · exact g32p_supplierForest_actual_109947
  · exact g32p_supplierForest_actual_109968
  · exact g32p_supplierForest_actual_110022
  · exact g32p_supplierForest_actual_110031
  · exact g32p_supplierForest_actual_110034
  · exact g32p_supplierForest_actual_110051
  · exact g32p_supplierForest_actual_110088
  · exact g32p_supplierForest_actual_110137
  · exact g32p_supplierForest_actual_110191
  · exact g32p_supplierForest_actual_110227
  · exact g32p_supplierForest_actual_110264
  · exact g32p_supplierForest_actual_110297
  · exact g32p_supplierForest_actual_110335
  · exact g32p_supplierForest_actual_110366
  · exact g32p_supplierForest_actual_110419
  · exact g32p_supplierForest_actual_110422
  · exact g32p_supplierForest_actual_110438
  · exact g32p_supplierForest_actual_110454
  · exact g32p_supplierForest_actual_110478
  · exact g32p_supplierForest_actual_110542
  · exact g32p_supplierForest_actual_110561
  · exact g32p_supplierForest_actual_110589
  · exact g32p_supplierForest_actual_110590
  · exact g32p_supplierForest_actual_110615
  · exact g32p_supplierForest_actual_110646
  · exact g32p_supplierForest_actual_110682
  · exact g32p_supplierForest_actual_110685
  · exact g32p_supplierForest_actual_110704
  · exact g32p_supplierForest_actual_110709
  · exact g32p_supplierForest_actual_110713
  · exact g32p_supplierForest_actual_110812
  · exact g32p_supplierForest_actual_110834
  · exact g32p_supplierForest_actual_110871
  · exact g32p_supplierForest_actual_110882
  · exact g32p_supplierForest_actual_110884

def g32p_supplierForest_nodes_126 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_110890 else g32p_supplierForest_node_110894) else (if i.val < 3 then g32p_supplierForest_node_110905 else g32p_supplierForest_node_110942)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_110943 else g32p_supplierForest_node_110946) else (if i.val < 7 then g32p_supplierForest_node_110996 else g32p_supplierForest_node_111073))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_111140 else g32p_supplierForest_node_111169) else (if i.val < 11 then g32p_supplierForest_node_111232 else g32p_supplierForest_node_111262)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_111266 else g32p_supplierForest_node_111377) else (if i.val < 15 then g32p_supplierForest_node_111388 else g32p_supplierForest_node_111400)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_111452 else g32p_supplierForest_node_111459) else (if i.val < 19 then g32p_supplierForest_node_111464 else g32p_supplierForest_node_111468)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_111488 else g32p_supplierForest_node_111489) else (if i.val < 23 then g32p_supplierForest_node_111492 else g32p_supplierForest_node_111498))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_111500 else g32p_supplierForest_node_111513) else (if i.val < 27 then g32p_supplierForest_node_111550 else g32p_supplierForest_node_111552)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_111635 else g32p_supplierForest_node_111671) else (if i.val < 31 then g32p_supplierForest_node_111676 else g32p_supplierForest_node_111680))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_111685 else g32p_supplierForest_node_111692) else (if i.val < 35 then g32p_supplierForest_node_111711 else g32p_supplierForest_node_111739)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_111758 else g32p_supplierForest_node_111802) else (if i.val < 39 then g32p_supplierForest_node_111809 else g32p_supplierForest_node_111845))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_111849 else g32p_supplierForest_node_111867) else (if i.val < 43 then g32p_supplierForest_node_111875 else g32p_supplierForest_node_111880)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_111884 else g32p_supplierForest_node_111889) else (if i.val < 47 then g32p_supplierForest_node_111911 else g32p_supplierForest_node_111913)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_111920 else g32p_supplierForest_node_111927) else (if i.val < 51 then g32p_supplierForest_node_111994 else g32p_supplierForest_node_111998)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_112002 else g32p_supplierForest_node_112010) else (if i.val < 55 then g32p_supplierForest_node_112020 else g32p_supplierForest_node_112028))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_112077 else g32p_supplierForest_node_112092) else (if i.val < 59 then g32p_supplierForest_node_112113 else g32p_supplierForest_node_112135)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_112153 else g32p_supplierForest_node_112167) else (if i.val < 63 then g32p_supplierForest_node_112175 else g32p_supplierForest_node_112203)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_112213 else g32p_supplierForest_node_112314) else (if i.val < 67 then g32p_supplierForest_node_112368 else g32p_supplierForest_node_112386)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_112401 else g32p_supplierForest_node_112404) else (if i.val < 71 then g32p_supplierForest_node_112435 else g32p_supplierForest_node_112479))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_112530 else g32p_supplierForest_node_112667) else (if i.val < 75 then g32p_supplierForest_node_112672 else g32p_supplierForest_node_112695)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_112729 else g32p_supplierForest_node_112731) else (if i.val < 79 then g32p_supplierForest_node_112773 else g32p_supplierForest_node_112792)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_112801 else g32p_supplierForest_node_112825) else (if i.val < 83 then g32p_supplierForest_node_112836 else g32p_supplierForest_node_112881)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_112890 else g32p_supplierForest_node_112963) else (if i.val < 87 then g32p_supplierForest_node_113101 else g32p_supplierForest_node_113151))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_113181 else g32p_supplierForest_node_113222) else (if i.val < 91 then g32p_supplierForest_node_113245 else g32p_supplierForest_node_113279)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_113298 else g32p_supplierForest_node_113312) else (if i.val < 95 then g32p_supplierForest_node_113320 else g32p_supplierForest_node_113341))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_113356 else g32p_supplierForest_node_113357) else (if i.val < 99 then g32p_supplierForest_node_113370 else g32p_supplierForest_node_113371)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_113376 else g32p_supplierForest_node_113386) else (if i.val < 103 then g32p_supplierForest_node_113412 else g32p_supplierForest_node_113443))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_113457 else g32p_supplierForest_node_113460) else (if i.val < 107 then g32p_supplierForest_node_113488 else g32p_supplierForest_node_113572)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_113642 else g32p_supplierForest_node_113680) else (if i.val < 111 then g32p_supplierForest_node_113768 else g32p_supplierForest_node_113782)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_113799 else g32p_supplierForest_node_113822) else (if i.val < 115 then g32p_supplierForest_node_113874 else g32p_supplierForest_node_113893)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_113901 else g32p_supplierForest_node_113909) else (if i.val < 119 then g32p_supplierForest_node_113942 else g32p_supplierForest_node_114029))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_114056 else g32p_supplierForest_node_114059) else (if i.val < 123 then g32p_supplierForest_node_114066 else g32p_supplierForest_node_114084)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_114111 else g32p_supplierForest_node_114112) else (if i.val < 127 then g32p_supplierForest_node_114119 else g32p_supplierForest_node_114124))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_114139 else g32p_supplierForest_node_114149) else (if i.val < 131 then g32p_supplierForest_node_114161 else g32p_supplierForest_node_114166)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_114186 else g32p_supplierForest_node_114222) else (if i.val < 135 then g32p_supplierForest_node_114230 else g32p_supplierForest_node_114237))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_114286 else g32p_supplierForest_node_114347) else (if i.val < 139 then g32p_supplierForest_node_114366 else g32p_supplierForest_node_114381)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_114482 else g32p_supplierForest_node_114486) else (if i.val < 143 then g32p_supplierForest_node_114552 else g32p_supplierForest_node_114634)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_114653 else g32p_supplierForest_node_114684) else (if i.val < 147 then g32p_supplierForest_node_114820 else g32p_supplierForest_node_114825)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_114830 else g32p_supplierForest_node_114951) else (if i.val < 151 then g32p_supplierForest_node_114993 else g32p_supplierForest_node_115001))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_115024 else g32p_supplierForest_node_115028) else (if i.val < 155 then g32p_supplierForest_node_115045 else g32p_supplierForest_node_115052)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_115061 else g32p_supplierForest_node_115090) else (if i.val < 159 then g32p_supplierForest_node_115092 else g32p_supplierForest_node_115154))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_115186 else g32p_supplierForest_node_115193) else (if i.val < 163 then g32p_supplierForest_node_115205 else g32p_supplierForest_node_115221)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_115223 else g32p_supplierForest_node_115232) else (if i.val < 167 then g32p_supplierForest_node_115290 else g32p_supplierForest_node_115315))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_115321 else g32p_supplierForest_node_115323) else (if i.val < 171 then g32p_supplierForest_node_115324 else g32p_supplierForest_node_115428)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_115441 else g32p_supplierForest_node_115573) else (if i.val < 175 then g32p_supplierForest_node_115601 else g32p_supplierForest_node_115606)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_115619 else g32p_supplierForest_node_115620) else (if i.val < 179 then g32p_supplierForest_node_115712 else g32p_supplierForest_node_115726)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_115755 else g32p_supplierForest_node_115775) else (if i.val < 183 then g32p_supplierForest_node_115881 else g32p_supplierForest_node_115934))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_116021 else g32p_supplierForest_node_116077) else (if i.val < 187 then g32p_supplierForest_node_116099 else g32p_supplierForest_node_116165)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_116170 else g32p_supplierForest_node_116194) else (if i.val < 191 then g32p_supplierForest_node_116224 else g32p_supplierForest_node_116258)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_116264 else g32p_supplierForest_node_116281) else (if i.val < 195 then g32p_supplierForest_node_116332 else g32p_supplierForest_node_116337)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_116348 else g32p_supplierForest_node_116365) else (if i.val < 199 then g32p_supplierForest_node_116420 else g32p_supplierForest_node_116442))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_116467 else g32p_supplierForest_node_116501) else (if i.val < 203 then g32p_supplierForest_node_116525 else g32p_supplierForest_node_116568)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_116613 else g32p_supplierForest_node_116666) else (if i.val < 207 then g32p_supplierForest_node_116718 else g32p_supplierForest_node_116727)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_116748 else g32p_supplierForest_node_116788) else (if i.val < 211 then g32p_supplierForest_node_116793 else g32p_supplierForest_node_116829)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_116861 else g32p_supplierForest_node_116864) else (if i.val < 215 then g32p_supplierForest_node_116865 else g32p_supplierForest_node_116886))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_116960 else g32p_supplierForest_node_116983) else (if i.val < 219 then g32p_supplierForest_node_117017 else g32p_supplierForest_node_117050)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_117054 else g32p_supplierForest_node_117135) else (if i.val < 223 then g32p_supplierForest_node_117180 else g32p_supplierForest_node_117206))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_117265 else g32p_supplierForest_node_117278) else (if i.val < 227 then g32p_supplierForest_node_117315 else g32p_supplierForest_node_117374)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_117429 else g32p_supplierForest_node_117438) else (if i.val < 231 then g32p_supplierForest_node_117455 else g32p_supplierForest_node_117476))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_117507 else g32p_supplierForest_node_117540) else (if i.val < 235 then g32p_supplierForest_node_117627 else g32p_supplierForest_node_117646)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_117769 else g32p_supplierForest_node_117819) else (if i.val < 239 then g32p_supplierForest_node_117824 else g32p_supplierForest_node_117875)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_117902 else g32p_supplierForest_node_117911) else (if i.val < 243 then g32p_supplierForest_node_117941 else g32p_supplierForest_node_118002)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_118028 else g32p_supplierForest_node_118093) else (if i.val < 247 then g32p_supplierForest_node_118109 else g32p_supplierForest_node_118133))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_118183 else g32p_supplierForest_node_118258) else (if i.val < 251 then g32p_supplierForest_node_118275 else g32p_supplierForest_node_118292)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_118295 else g32p_supplierForest_node_118332) else (if i.val < 255 then g32p_supplierForest_node_118349 else g32p_supplierForest_node_118381))))))))

def g32p_supplierForest_classes_126 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 29) else (if i.val < 3 then 60 else 30)) else (if i.val < 6 then (if i.val < 5 then 59 else 16) else (if i.val < 7 then 57 else 59))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 33 else 57) else (if i.val < 11 then 17 else 29)) else (if i.val < 14 then (if i.val < 13 then 57 else 33) else (if i.val < 15 then 30 else 57)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 30 else 57) else (if i.val < 19 then 30 else 30)) else (if i.val < 22 then (if i.val < 21 then 15 else 57) else (if i.val < 23 then 57 else 29))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 57 else 30) else (if i.val < 27 then 33 else 57)) else (if i.val < 30 then (if i.val < 29 then 57 else 57) else (if i.val < 31 then 57 else 59))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 57 else 61) else (if i.val < 35 then 57 else 57)) else (if i.val < 38 then (if i.val < 37 then 60 else 59) else (if i.val < 39 then 30 else 57))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 57 else 60) else (if i.val < 43 then 57 else 57)) else (if i.val < 46 then (if i.val < 45 then 33 else 59) else (if i.val < 47 then 29 else 59)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 30 else 57) else (if i.val < 51 then 16 else 63)) else (if i.val < 54 then (if i.val < 53 then 57 else 60) else (if i.val < 55 then 30 else 57))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 60 else 29) else (if i.val < 59 then 57 else 36)) else (if i.val < 62 then (if i.val < 61 then 29 else 57) else (if i.val < 63 then 57 else 57)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 59 else 57) else (if i.val < 67 then 66 else 30)) else (if i.val < 70 then (if i.val < 69 then 57 else 57) else (if i.val < 71 then 66 else 59))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 30 else 30) else (if i.val < 75 then 57 else 29)) else (if i.val < 78 then (if i.val < 77 then 15 else 30) else (if i.val < 79 then 33 else 60)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 57 else 60) else (if i.val < 83 then 35 else 29)) else (if i.val < 86 then (if i.val < 85 then 62 else 62) else (if i.val < 87 then 66 else 57))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 30 else 57) else (if i.val < 91 then 57 else 57)) else (if i.val < 94 then (if i.val < 93 then 60 else 57) else (if i.val < 95 then 62 else 57))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 59 else 57) else (if i.val < 99 then 58 else 15)) else (if i.val < 102 then (if i.val < 101 then 57 else 57) else (if i.val < 103 then 62 else 66))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 30 else 66) else (if i.val < 107 then 57 else 16)) else (if i.val < 110 then (if i.val < 109 then 30 else 29) else (if i.val < 111 then 30 else 57)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 29 else 16) else (if i.val < 115 then 57 else 30)) else (if i.val < 118 then (if i.val < 117 then 60 else 60) else (if i.val < 119 then 57 else 57))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 66 else 57) else (if i.val < 123 then 30 else 63)) else (if i.val < 126 then (if i.val < 125 then 57 else 29) else (if i.val < 127 then 29 else 35))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 57 else 62) else (if i.val < 131 then 57 else 59)) else (if i.val < 134 then (if i.val < 133 then 30 else 57) else (if i.val < 135 then 61 else 57))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 30 else 57) else (if i.val < 139 then 30 else 63)) else (if i.val < 142 then (if i.val < 141 then 14 else 60) else (if i.val < 143 then 57 else 57)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 60 else 30) else (if i.val < 147 then 61 else 57)) else (if i.val < 150 then (if i.val < 149 then 62 else 59) else (if i.val < 151 then 4 else 57))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 57 else 57) else (if i.val < 155 then 30 else 57)) else (if i.val < 158 then (if i.val < 157 then 16 else 15) else (if i.val < 159 then 30 else 66))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 30 else 57) else (if i.val < 163 then 57 else 30)) else (if i.val < 166 then (if i.val < 165 then 15 else 35) else (if i.val < 167 then 60 else 33))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 36 else 16) else (if i.val < 171 then 60 else 57)) else (if i.val < 174 then (if i.val < 173 then 57 else 57) else (if i.val < 175 then 60 else 60)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 57 else 57) else (if i.val < 179 then 36 else 60)) else (if i.val < 182 then (if i.val < 181 then 62 else 30) else (if i.val < 183 then 60 else 57))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 29 else 89) else (if i.val < 187 then 91 else 57)) else (if i.val < 190 then (if i.val < 189 then 58 else 57) else (if i.val < 191 then 57 else 36)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 30 else 30) else (if i.val < 195 then 57 else 57)) else (if i.val < 198 then (if i.val < 197 then 57 else 35) else (if i.val < 199 then 16 else 60))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 29 else 29) else (if i.val < 203 then 57 else 57)) else (if i.val < 206 then (if i.val < 205 then 57 else 15) else (if i.val < 207 then 57 else 57)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 29 else 36) else (if i.val < 211 then 57 else 57)) else (if i.val < 214 then (if i.val < 213 then 29 else 57) else (if i.val < 215 then 57 else 66))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 57 else 57) else (if i.val < 219 then 59 else 30)) else (if i.val < 222 then (if i.val < 221 then 60 else 66) else (if i.val < 223 then 30 else 30))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 66 else 57) else (if i.val < 227 then 57 else 66)) else (if i.val < 230 then (if i.val < 229 then 59 else 29) else (if i.val < 231 then 29 else 57))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 60 else 60) else (if i.val < 235 then 60 else 30)) else (if i.val < 238 then (if i.val < 237 then 15 else 66) else (if i.val < 239 then 16 else 60)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 60 else 30) else (if i.val < 243 then 30 else 62)) else (if i.val < 246 then (if i.val < 245 then 29 else 30) else (if i.val < 247 then 57 else 36))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 66 else 57) else (if i.val < 251 then 59 else 57)) else (if i.val < 254 then (if i.val < 253 then 30 else 29) else (if i.val < 255 then 30 else 57))))))))

theorem g32p_supplierForest_actual_126 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_126 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_126 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_110890
  · exact g32p_supplierForest_actual_110894
  · exact g32p_supplierForest_actual_110905
  · exact g32p_supplierForest_actual_110942
  · exact g32p_supplierForest_actual_110943
  · exact g32p_supplierForest_actual_110946
  · exact g32p_supplierForest_actual_110996
  · exact g32p_supplierForest_actual_111073
  · exact g32p_supplierForest_actual_111140
  · exact g32p_supplierForest_actual_111169
  · exact g32p_supplierForest_actual_111232
  · exact g32p_supplierForest_actual_111262
  · exact g32p_supplierForest_actual_111266
  · exact g32p_supplierForest_actual_111377
  · exact g32p_supplierForest_actual_111388
  · exact g32p_supplierForest_actual_111400
  · exact g32p_supplierForest_actual_111452
  · exact g32p_supplierForest_actual_111459
  · exact g32p_supplierForest_actual_111464
  · exact g32p_supplierForest_actual_111468
  · exact g32p_supplierForest_actual_111488
  · exact g32p_supplierForest_actual_111489
  · exact g32p_supplierForest_actual_111492
  · exact g32p_supplierForest_actual_111498
  · exact g32p_supplierForest_actual_111500
  · exact g32p_supplierForest_actual_111513
  · exact g32p_supplierForest_actual_111550
  · exact g32p_supplierForest_actual_111552
  · exact g32p_supplierForest_actual_111635
  · exact g32p_supplierForest_actual_111671
  · exact g32p_supplierForest_actual_111676
  · exact g32p_supplierForest_actual_111680
  · exact g32p_supplierForest_actual_111685
  · exact g32p_supplierForest_actual_111692
  · exact g32p_supplierForest_actual_111711
  · exact g32p_supplierForest_actual_111739
  · exact g32p_supplierForest_actual_111758
  · exact g32p_supplierForest_actual_111802
  · exact g32p_supplierForest_actual_111809
  · exact g32p_supplierForest_actual_111845
  · exact g32p_supplierForest_actual_111849
  · exact g32p_supplierForest_actual_111867
  · exact g32p_supplierForest_actual_111875
  · exact g32p_supplierForest_actual_111880
  · exact g32p_supplierForest_actual_111884
  · exact g32p_supplierForest_actual_111889
  · exact g32p_supplierForest_actual_111911
  · exact g32p_supplierForest_actual_111913
  · exact g32p_supplierForest_actual_111920
  · exact g32p_supplierForest_actual_111927
  · exact g32p_supplierForest_actual_111994
  · exact g32p_supplierForest_actual_111998
  · exact g32p_supplierForest_actual_112002
  · exact g32p_supplierForest_actual_112010
  · exact g32p_supplierForest_actual_112020
  · exact g32p_supplierForest_actual_112028
  · exact g32p_supplierForest_actual_112077
  · exact g32p_supplierForest_actual_112092
  · exact g32p_supplierForest_actual_112113
  · exact g32p_supplierForest_actual_112135
  · exact g32p_supplierForest_actual_112153
  · exact g32p_supplierForest_actual_112167
  · exact g32p_supplierForest_actual_112175
  · exact g32p_supplierForest_actual_112203
  · exact g32p_supplierForest_actual_112213
  · exact g32p_supplierForest_actual_112314
  · exact g32p_supplierForest_actual_112368
  · exact g32p_supplierForest_actual_112386
  · exact g32p_supplierForest_actual_112401
  · exact g32p_supplierForest_actual_112404
  · exact g32p_supplierForest_actual_112435
  · exact g32p_supplierForest_actual_112479
  · exact g32p_supplierForest_actual_112530
  · exact g32p_supplierForest_actual_112667
  · exact g32p_supplierForest_actual_112672
  · exact g32p_supplierForest_actual_112695
  · exact g32p_supplierForest_actual_112729
  · exact g32p_supplierForest_actual_112731
  · exact g32p_supplierForest_actual_112773
  · exact g32p_supplierForest_actual_112792
  · exact g32p_supplierForest_actual_112801
  · exact g32p_supplierForest_actual_112825
  · exact g32p_supplierForest_actual_112836
  · exact g32p_supplierForest_actual_112881
  · exact g32p_supplierForest_actual_112890
  · exact g32p_supplierForest_actual_112963
  · exact g32p_supplierForest_actual_113101
  · exact g32p_supplierForest_actual_113151
  · exact g32p_supplierForest_actual_113181
  · exact g32p_supplierForest_actual_113222
  · exact g32p_supplierForest_actual_113245
  · exact g32p_supplierForest_actual_113279
  · exact g32p_supplierForest_actual_113298
  · exact g32p_supplierForest_actual_113312
  · exact g32p_supplierForest_actual_113320
  · exact g32p_supplierForest_actual_113341
  · exact g32p_supplierForest_actual_113356
  · exact g32p_supplierForest_actual_113357
  · exact g32p_supplierForest_actual_113370
  · exact g32p_supplierForest_actual_113371
  · exact g32p_supplierForest_actual_113376
  · exact g32p_supplierForest_actual_113386
  · exact g32p_supplierForest_actual_113412
  · exact g32p_supplierForest_actual_113443
  · exact g32p_supplierForest_actual_113457
  · exact g32p_supplierForest_actual_113460
  · exact g32p_supplierForest_actual_113488
  · exact g32p_supplierForest_actual_113572
  · exact g32p_supplierForest_actual_113642
  · exact g32p_supplierForest_actual_113680
  · exact g32p_supplierForest_actual_113768
  · exact g32p_supplierForest_actual_113782
  · exact g32p_supplierForest_actual_113799
  · exact g32p_supplierForest_actual_113822
  · exact g32p_supplierForest_actual_113874
  · exact g32p_supplierForest_actual_113893
  · exact g32p_supplierForest_actual_113901
  · exact g32p_supplierForest_actual_113909
  · exact g32p_supplierForest_actual_113942
  · exact g32p_supplierForest_actual_114029
  · exact g32p_supplierForest_actual_114056
  · exact g32p_supplierForest_actual_114059
  · exact g32p_supplierForest_actual_114066
  · exact g32p_supplierForest_actual_114084
  · exact g32p_supplierForest_actual_114111
  · exact g32p_supplierForest_actual_114112
  · exact g32p_supplierForest_actual_114119
  · exact g32p_supplierForest_actual_114124
  · exact g32p_supplierForest_actual_114139
  · exact g32p_supplierForest_actual_114149
  · exact g32p_supplierForest_actual_114161
  · exact g32p_supplierForest_actual_114166
  · exact g32p_supplierForest_actual_114186
  · exact g32p_supplierForest_actual_114222
  · exact g32p_supplierForest_actual_114230
  · exact g32p_supplierForest_actual_114237
  · exact g32p_supplierForest_actual_114286
  · exact g32p_supplierForest_actual_114347
  · exact g32p_supplierForest_actual_114366
  · exact g32p_supplierForest_actual_114381
  · exact g32p_supplierForest_actual_114482
  · exact g32p_supplierForest_actual_114486
  · exact g32p_supplierForest_actual_114552
  · exact g32p_supplierForest_actual_114634
  · exact g32p_supplierForest_actual_114653
  · exact g32p_supplierForest_actual_114684
  · exact g32p_supplierForest_actual_114820
  · exact g32p_supplierForest_actual_114825
  · exact g32p_supplierForest_actual_114830
  · exact g32p_supplierForest_actual_114951
  · exact g32p_supplierForest_actual_114993
  · exact g32p_supplierForest_actual_115001
  · exact g32p_supplierForest_actual_115024
  · exact g32p_supplierForest_actual_115028
  · exact g32p_supplierForest_actual_115045
  · exact g32p_supplierForest_actual_115052
  · exact g32p_supplierForest_actual_115061
  · exact g32p_supplierForest_actual_115090
  · exact g32p_supplierForest_actual_115092
  · exact g32p_supplierForest_actual_115154
  · exact g32p_supplierForest_actual_115186
  · exact g32p_supplierForest_actual_115193
  · exact g32p_supplierForest_actual_115205
  · exact g32p_supplierForest_actual_115221
  · exact g32p_supplierForest_actual_115223
  · exact g32p_supplierForest_actual_115232
  · exact g32p_supplierForest_actual_115290
  · exact g32p_supplierForest_actual_115315
  · exact g32p_supplierForest_actual_115321
  · exact g32p_supplierForest_actual_115323
  · exact g32p_supplierForest_actual_115324
  · exact g32p_supplierForest_actual_115428
  · exact g32p_supplierForest_actual_115441
  · exact g32p_supplierForest_actual_115573
  · exact g32p_supplierForest_actual_115601
  · exact g32p_supplierForest_actual_115606
  · exact g32p_supplierForest_actual_115619
  · exact g32p_supplierForest_actual_115620
  · exact g32p_supplierForest_actual_115712
  · exact g32p_supplierForest_actual_115726
  · exact g32p_supplierForest_actual_115755
  · exact g32p_supplierForest_actual_115775
  · exact g32p_supplierForest_actual_115881
  · exact g32p_supplierForest_actual_115934
  · exact g32p_supplierForest_actual_116021
  · exact g32p_supplierForest_actual_116077
  · exact g32p_supplierForest_actual_116099
  · exact g32p_supplierForest_actual_116165
  · exact g32p_supplierForest_actual_116170
  · exact g32p_supplierForest_actual_116194
  · exact g32p_supplierForest_actual_116224
  · exact g32p_supplierForest_actual_116258
  · exact g32p_supplierForest_actual_116264
  · exact g32p_supplierForest_actual_116281
  · exact g32p_supplierForest_actual_116332
  · exact g32p_supplierForest_actual_116337
  · exact g32p_supplierForest_actual_116348
  · exact g32p_supplierForest_actual_116365
  · exact g32p_supplierForest_actual_116420
  · exact g32p_supplierForest_actual_116442
  · exact g32p_supplierForest_actual_116467
  · exact g32p_supplierForest_actual_116501
  · exact g32p_supplierForest_actual_116525
  · exact g32p_supplierForest_actual_116568
  · exact g32p_supplierForest_actual_116613
  · exact g32p_supplierForest_actual_116666
  · exact g32p_supplierForest_actual_116718
  · exact g32p_supplierForest_actual_116727
  · exact g32p_supplierForest_actual_116748
  · exact g32p_supplierForest_actual_116788
  · exact g32p_supplierForest_actual_116793
  · exact g32p_supplierForest_actual_116829
  · exact g32p_supplierForest_actual_116861
  · exact g32p_supplierForest_actual_116864
  · exact g32p_supplierForest_actual_116865
  · exact g32p_supplierForest_actual_116886
  · exact g32p_supplierForest_actual_116960
  · exact g32p_supplierForest_actual_116983
  · exact g32p_supplierForest_actual_117017
  · exact g32p_supplierForest_actual_117050
  · exact g32p_supplierForest_actual_117054
  · exact g32p_supplierForest_actual_117135
  · exact g32p_supplierForest_actual_117180
  · exact g32p_supplierForest_actual_117206
  · exact g32p_supplierForest_actual_117265
  · exact g32p_supplierForest_actual_117278
  · exact g32p_supplierForest_actual_117315
  · exact g32p_supplierForest_actual_117374
  · exact g32p_supplierForest_actual_117429
  · exact g32p_supplierForest_actual_117438
  · exact g32p_supplierForest_actual_117455
  · exact g32p_supplierForest_actual_117476
  · exact g32p_supplierForest_actual_117507
  · exact g32p_supplierForest_actual_117540
  · exact g32p_supplierForest_actual_117627
  · exact g32p_supplierForest_actual_117646
  · exact g32p_supplierForest_actual_117769
  · exact g32p_supplierForest_actual_117819
  · exact g32p_supplierForest_actual_117824
  · exact g32p_supplierForest_actual_117875
  · exact g32p_supplierForest_actual_117902
  · exact g32p_supplierForest_actual_117911
  · exact g32p_supplierForest_actual_117941
  · exact g32p_supplierForest_actual_118002
  · exact g32p_supplierForest_actual_118028
  · exact g32p_supplierForest_actual_118093
  · exact g32p_supplierForest_actual_118109
  · exact g32p_supplierForest_actual_118133
  · exact g32p_supplierForest_actual_118183
  · exact g32p_supplierForest_actual_118258
  · exact g32p_supplierForest_actual_118275
  · exact g32p_supplierForest_actual_118292
  · exact g32p_supplierForest_actual_118295
  · exact g32p_supplierForest_actual_118332
  · exact g32p_supplierForest_actual_118349
  · exact g32p_supplierForest_actual_118381

def g32p_supplierForest_nodes_127 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_118384 else g32p_supplierForest_node_118392) else (if i.val < 3 then g32p_supplierForest_node_118521 else g32p_supplierForest_node_118530)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_118542 else g32p_supplierForest_node_118569) else (if i.val < 7 then g32p_supplierForest_node_118592 else g32p_supplierForest_node_118601))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_118604 else g32p_supplierForest_node_118639) else (if i.val < 11 then g32p_supplierForest_node_118640 else g32p_supplierForest_node_118646)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_118718 else g32p_supplierForest_node_118753) else (if i.val < 15 then g32p_supplierForest_node_118763 else g32p_supplierForest_node_118782)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_118844 else g32p_supplierForest_node_118846) else (if i.val < 19 then g32p_supplierForest_node_118908 else g32p_supplierForest_node_118912)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_118914 else g32p_supplierForest_node_118930) else (if i.val < 23 then g32p_supplierForest_node_118967 else g32p_supplierForest_node_118972))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_118979 else g32p_supplierForest_node_119028) else (if i.val < 27 then g32p_supplierForest_node_119056 else g32p_supplierForest_node_119099)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_119232 else g32p_supplierForest_node_119276) else (if i.val < 31 then g32p_supplierForest_node_119283 else g32p_supplierForest_node_119288))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_119298 else g32p_supplierForest_node_119302) else (if i.val < 35 then g32p_supplierForest_node_119357 else g32p_supplierForest_node_119360)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_119377 else g32p_supplierForest_node_119382) else (if i.val < 39 then g32p_supplierForest_node_119396 else g32p_supplierForest_node_119428))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_119450 else g32p_supplierForest_node_119455) else (if i.val < 43 then g32p_supplierForest_node_119461 else g32p_supplierForest_node_119511)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_119544 else g32p_supplierForest_node_119594) else (if i.val < 47 then g32p_supplierForest_node_119641 else g32p_supplierForest_node_119643)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_119688 else g32p_supplierForest_node_119711) else (if i.val < 51 then g32p_supplierForest_node_119756 else g32p_supplierForest_node_119768)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_119776 else g32p_supplierForest_node_119817) else (if i.val < 55 then g32p_supplierForest_node_119821 else g32p_supplierForest_node_119837))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_119854 else g32p_supplierForest_node_119923) else (if i.val < 59 then g32p_supplierForest_node_119954 else g32p_supplierForest_node_119974)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_120019 else g32p_supplierForest_node_120138) else (if i.val < 63 then g32p_supplierForest_node_120146 else g32p_supplierForest_node_120156)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_120164 else g32p_supplierForest_node_120171) else (if i.val < 67 then g32p_supplierForest_node_120180 else g32p_supplierForest_node_120200)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_120206 else g32p_supplierForest_node_120230) else (if i.val < 71 then g32p_supplierForest_node_120277 else g32p_supplierForest_node_120284))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_120393 else g32p_supplierForest_node_120443) else (if i.val < 75 then g32p_supplierForest_node_120451 else g32p_supplierForest_node_120457)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_120653 else g32p_supplierForest_node_120658) else (if i.val < 79 then g32p_supplierForest_node_120688 else g32p_supplierForest_node_120742)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_120762 else g32p_supplierForest_node_120763) else (if i.val < 83 then g32p_supplierForest_node_120813 else g32p_supplierForest_node_120817)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_120822 else g32p_supplierForest_node_120892) else (if i.val < 87 then g32p_supplierForest_node_120938 else g32p_supplierForest_node_121006))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_121015 else g32p_supplierForest_node_121103) else (if i.val < 91 then g32p_supplierForest_node_121165 else g32p_supplierForest_node_121199)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_121219 else g32p_supplierForest_node_121235) else (if i.val < 95 then g32p_supplierForest_node_121254 else g32p_supplierForest_node_121269))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_121282 else g32p_supplierForest_node_121310) else (if i.val < 99 then g32p_supplierForest_node_121349 else g32p_supplierForest_node_121393)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_121406 else g32p_supplierForest_node_121408) else (if i.val < 103 then g32p_supplierForest_node_121436 else g32p_supplierForest_node_121485))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_121497 else g32p_supplierForest_node_121515) else (if i.val < 107 then g32p_supplierForest_node_121538 else g32p_supplierForest_node_121543)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_121552 else g32p_supplierForest_node_121604) else (if i.val < 111 then g32p_supplierForest_node_121608 else g32p_supplierForest_node_121612)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_121638 else g32p_supplierForest_node_121654) else (if i.val < 115 then g32p_supplierForest_node_121667 else g32p_supplierForest_node_121706)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_121717 else g32p_supplierForest_node_121725) else (if i.val < 119 then g32p_supplierForest_node_121763 else g32p_supplierForest_node_121796))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_121802 else g32p_supplierForest_node_121808) else (if i.val < 123 then g32p_supplierForest_node_121925 else g32p_supplierForest_node_121955)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_121957 else g32p_supplierForest_node_121994) else (if i.val < 127 then g32p_supplierForest_node_122020 else g32p_supplierForest_node_122062))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_122076 else g32p_supplierForest_node_122113) else (if i.val < 131 then g32p_supplierForest_node_122132 else g32p_supplierForest_node_122134)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_122177 else g32p_supplierForest_node_122189) else (if i.val < 135 then g32p_supplierForest_node_122206 else g32p_supplierForest_node_122239))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_122309 else g32p_supplierForest_node_122354) else (if i.val < 139 then g32p_supplierForest_node_122356 else g32p_supplierForest_node_122369)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_122372 else g32p_supplierForest_node_122373) else (if i.val < 143 then g32p_supplierForest_node_122436 else g32p_supplierForest_node_122452)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_122456 else g32p_supplierForest_node_122473) else (if i.val < 147 then g32p_supplierForest_node_122475 else g32p_supplierForest_node_122497)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_122535 else g32p_supplierForest_node_122594) else (if i.val < 151 then g32p_supplierForest_node_122630 else g32p_supplierForest_node_122664))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_122686 else g32p_supplierForest_node_122695) else (if i.val < 155 then g32p_supplierForest_node_122707 else g32p_supplierForest_node_122727)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_122729 else g32p_supplierForest_node_122735) else (if i.val < 159 then g32p_supplierForest_node_122774 else g32p_supplierForest_node_122776))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_122811 else g32p_supplierForest_node_122875) else (if i.val < 163 then g32p_supplierForest_node_122879 else g32p_supplierForest_node_122903)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_122934 else g32p_supplierForest_node_122941) else (if i.val < 167 then g32p_supplierForest_node_122968 else g32p_supplierForest_node_122978))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_123031 else g32p_supplierForest_node_123141) else (if i.val < 171 then g32p_supplierForest_node_123210 else g32p_supplierForest_node_123221)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_123238 else g32p_supplierForest_node_123276) else (if i.val < 175 then g32p_supplierForest_node_123291 else g32p_supplierForest_node_123300)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_123331 else g32p_supplierForest_node_123425) else (if i.val < 179 then g32p_supplierForest_node_123482 else g32p_supplierForest_node_123494)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_123496 else g32p_supplierForest_node_123505) else (if i.val < 183 then g32p_supplierForest_node_123590 else g32p_supplierForest_node_123611))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_123712 else g32p_supplierForest_node_123762) else (if i.val < 187 then g32p_supplierForest_node_123766 else g32p_supplierForest_node_123780)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_123805 else g32p_supplierForest_node_123818) else (if i.val < 191 then g32p_supplierForest_node_123865 else g32p_supplierForest_node_123948)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_123995 else g32p_supplierForest_node_124032) else (if i.val < 195 then g32p_supplierForest_node_124039 else g32p_supplierForest_node_124052)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_124054 else g32p_supplierForest_node_124134) else (if i.val < 199 then g32p_supplierForest_node_124184 else g32p_supplierForest_node_124205))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_124210 else g32p_supplierForest_node_124216) else (if i.val < 203 then g32p_supplierForest_node_124362 else g32p_supplierForest_node_124371)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_124376 else g32p_supplierForest_node_124491) else (if i.val < 207 then g32p_supplierForest_node_124499 else g32p_supplierForest_node_124534)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_124541 else g32p_supplierForest_node_124557) else (if i.val < 211 then g32p_supplierForest_node_124570 else g32p_supplierForest_node_124609)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_124625 else g32p_supplierForest_node_124640) else (if i.val < 215 then g32p_supplierForest_node_124669 else g32p_supplierForest_node_124698))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_124712 else g32p_supplierForest_node_124715) else (if i.val < 219 then g32p_supplierForest_node_124716 else g32p_supplierForest_node_124735)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_124743 else g32p_supplierForest_node_124755) else (if i.val < 223 then g32p_supplierForest_node_124767 else g32p_supplierForest_node_124768))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_124791 else g32p_supplierForest_node_124794) else (if i.val < 227 then g32p_supplierForest_node_124828 else g32p_supplierForest_node_124872)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_124900 else g32p_supplierForest_node_124915) else (if i.val < 231 then g32p_supplierForest_node_124943 else g32p_supplierForest_node_124969))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_125057 else g32p_supplierForest_node_125061) else (if i.val < 235 then g32p_supplierForest_node_125065 else g32p_supplierForest_node_125074)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_125215 else g32p_supplierForest_node_125290) else (if i.val < 239 then g32p_supplierForest_node_125293 else g32p_supplierForest_node_125320)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_125326 else g32p_supplierForest_node_125374) else (if i.val < 243 then g32p_supplierForest_node_125462 else g32p_supplierForest_node_125475)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_125480 else g32p_supplierForest_node_125489) else (if i.val < 247 then g32p_supplierForest_node_125511 else g32p_supplierForest_node_125522))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_125529 else g32p_supplierForest_node_125555) else (if i.val < 251 then g32p_supplierForest_node_125587 else g32p_supplierForest_node_125628)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_125645 else g32p_supplierForest_node_125647) else (if i.val < 255 then g32p_supplierForest_node_125682 else g32p_supplierForest_node_125738))))))))

def g32p_supplierForest_classes_127 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 62 else 57) else (if i.val < 3 then 30 else 30)) else (if i.val < 6 then (if i.val < 5 then 30 else 62) else (if i.val < 7 then 61 else 29))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 66 else 57) else (if i.val < 11 then 89 else 36)) else (if i.val < 14 then (if i.val < 13 then 30 else 36) else (if i.val < 15 then 57 else 66)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 66) else (if i.val < 19 then 66 else 57)) else (if i.val < 22 then (if i.val < 21 then 64 else 30) else (if i.val < 23 then 30 else 30))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 57 else 61) else (if i.val < 27 then 33 else 57)) else (if i.val < 30 then (if i.val < 29 then 60 else 30) else (if i.val < 31 then 57 else 60))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 36 else 57) else (if i.val < 35 then 58 else 63)) else (if i.val < 38 then (if i.val < 37 then 57 else 30) else (if i.val < 39 then 36 else 57))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 29 else 57) else (if i.val < 43 then 29 else 30)) else (if i.val < 46 then (if i.val < 45 then 59 else 66) else (if i.val < 47 then 60 else 60)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 59 else 66) else (if i.val < 51 then 30 else 57)) else (if i.val < 54 then (if i.val < 53 then 57 else 17) else (if i.val < 55 then 60 else 57))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 30 else 57) else (if i.val < 59 then 66 else 60)) else (if i.val < 62 then (if i.val < 61 then 29 else 66) else (if i.val < 63 then 36 else 63)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 66 else 57) else (if i.val < 67 then 63 else 62)) else (if i.val < 70 then (if i.val < 69 then 57 else 30) else (if i.val < 71 then 57 else 57))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 57 else 90) else (if i.val < 75 then 59 else 59)) else (if i.val < 78 then (if i.val < 77 then 57 else 30) else (if i.val < 79 then 30 else 57)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 57 else 62) else (if i.val < 83 then 29 else 29)) else (if i.val < 86 then (if i.val < 85 then 59 else 59) else (if i.val < 87 then 60 else 57))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 66 else 57) else (if i.val < 91 then 57 else 57)) else (if i.val < 94 then (if i.val < 93 then 60 else 33) else (if i.val < 95 then 33 else 62))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 57 else 57) else (if i.val < 99 then 59 else 60)) else (if i.val < 102 then (if i.val < 101 then 62 else 57) else (if i.val < 103 then 60 else 57))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 29 else 57) else (if i.val < 107 then 60 else 60)) else (if i.val < 110 then (if i.val < 109 then 16 else 59) else (if i.val < 111 then 30 else 30)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 57 else 30) else (if i.val < 115 then 57 else 57)) else (if i.val < 118 then (if i.val < 117 then 57 else 62) else (if i.val < 119 then 35 else 30))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 57 else 57) else (if i.val < 123 then 62 else 30)) else (if i.val < 126 then (if i.val < 125 then 60 else 30) else (if i.val < 127 then 57 else 57))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 30 else 60) else (if i.val < 131 then 66 else 89)) else (if i.val < 134 then (if i.val < 133 then 17 else 57) else (if i.val < 135 then 60 else 57))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 90 else 62) else (if i.val < 139 then 30 else 61)) else (if i.val < 142 then (if i.val < 141 then 29 else 29) else (if i.val < 143 then 58 else 60)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 60 else 90) else (if i.val < 147 then 90 else 30)) else (if i.val < 150 then (if i.val < 149 then 59 else 30) else (if i.val < 151 then 15 else 57))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 62 else 36) else (if i.val < 155 then 57 else 16)) else (if i.val < 158 then (if i.val < 157 then 16 else 30) else (if i.val < 159 then 35 else 57))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 30 else 36) else (if i.val < 163 then 60 else 29)) else (if i.val < 166 then (if i.val < 165 then 90 else 36) else (if i.val < 167 then 57 else 57))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 59 else 57) else (if i.val < 171 then 30 else 30)) else (if i.val < 174 then (if i.val < 173 then 63 else 89) else (if i.val < 175 then 30 else 66)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 63 else 61) else (if i.val < 179 then 61 else 30)) else (if i.val < 182 then (if i.val < 181 then 90 else 30) else (if i.val < 183 then 61 else 60))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 30 else 57) else (if i.val < 187 then 17 else 66)) else (if i.val < 190 then (if i.val < 189 then 33 else 61) else (if i.val < 191 then 29 else 30)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 33 else 61) else (if i.val < 195 then 61 else 57)) else (if i.val < 198 then (if i.val < 197 then 60 else 58) else (if i.val < 199 then 30 else 66))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 66 else 90) else (if i.val < 203 then 58 else 29)) else (if i.val < 206 then (if i.val < 205 then 30 else 63) else (if i.val < 207 then 30 else 66)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 57 else 60) else (if i.val < 211 then 58 else 62)) else (if i.val < 214 then (if i.val < 213 then 63 else 57) else (if i.val < 215 then 60 else 30))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 57 else 30) else (if i.val < 219 then 58 else 60)) else (if i.val < 222 then (if i.val < 221 then 60 else 30) else (if i.val < 223 then 30 else 30))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 60 else 60) else (if i.val < 227 then 60 else 60)) else (if i.val < 230 then (if i.val < 229 then 57 else 57) else (if i.val < 231 then 60 else 59))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 57 else 29) else (if i.val < 235 then 58 else 15)) else (if i.val < 238 then (if i.val < 237 then 60 else 29) else (if i.val < 239 then 30 else 57)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 59 else 30) else (if i.val < 243 then 60 else 57)) else (if i.val < 246 then (if i.val < 245 then 30 else 57) else (if i.val < 247 then 57 else 29))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 57 else 57) else (if i.val < 251 then 63 else 30)) else (if i.val < 254 then (if i.val < 253 then 60 else 60) else (if i.val < 255 then 57 else 30))))))))

theorem g32p_supplierForest_actual_127 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_127 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_127 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_118384
  · exact g32p_supplierForest_actual_118392
  · exact g32p_supplierForest_actual_118521
  · exact g32p_supplierForest_actual_118530
  · exact g32p_supplierForest_actual_118542
  · exact g32p_supplierForest_actual_118569
  · exact g32p_supplierForest_actual_118592
  · exact g32p_supplierForest_actual_118601
  · exact g32p_supplierForest_actual_118604
  · exact g32p_supplierForest_actual_118639
  · exact g32p_supplierForest_actual_118640
  · exact g32p_supplierForest_actual_118646
  · exact g32p_supplierForest_actual_118718
  · exact g32p_supplierForest_actual_118753
  · exact g32p_supplierForest_actual_118763
  · exact g32p_supplierForest_actual_118782
  · exact g32p_supplierForest_actual_118844
  · exact g32p_supplierForest_actual_118846
  · exact g32p_supplierForest_actual_118908
  · exact g32p_supplierForest_actual_118912
  · exact g32p_supplierForest_actual_118914
  · exact g32p_supplierForest_actual_118930
  · exact g32p_supplierForest_actual_118967
  · exact g32p_supplierForest_actual_118972
  · exact g32p_supplierForest_actual_118979
  · exact g32p_supplierForest_actual_119028
  · exact g32p_supplierForest_actual_119056
  · exact g32p_supplierForest_actual_119099
  · exact g32p_supplierForest_actual_119232
  · exact g32p_supplierForest_actual_119276
  · exact g32p_supplierForest_actual_119283
  · exact g32p_supplierForest_actual_119288
  · exact g32p_supplierForest_actual_119298
  · exact g32p_supplierForest_actual_119302
  · exact g32p_supplierForest_actual_119357
  · exact g32p_supplierForest_actual_119360
  · exact g32p_supplierForest_actual_119377
  · exact g32p_supplierForest_actual_119382
  · exact g32p_supplierForest_actual_119396
  · exact g32p_supplierForest_actual_119428
  · exact g32p_supplierForest_actual_119450
  · exact g32p_supplierForest_actual_119455
  · exact g32p_supplierForest_actual_119461
  · exact g32p_supplierForest_actual_119511
  · exact g32p_supplierForest_actual_119544
  · exact g32p_supplierForest_actual_119594
  · exact g32p_supplierForest_actual_119641
  · exact g32p_supplierForest_actual_119643
  · exact g32p_supplierForest_actual_119688
  · exact g32p_supplierForest_actual_119711
  · exact g32p_supplierForest_actual_119756
  · exact g32p_supplierForest_actual_119768
  · exact g32p_supplierForest_actual_119776
  · exact g32p_supplierForest_actual_119817
  · exact g32p_supplierForest_actual_119821
  · exact g32p_supplierForest_actual_119837
  · exact g32p_supplierForest_actual_119854
  · exact g32p_supplierForest_actual_119923
  · exact g32p_supplierForest_actual_119954
  · exact g32p_supplierForest_actual_119974
  · exact g32p_supplierForest_actual_120019
  · exact g32p_supplierForest_actual_120138
  · exact g32p_supplierForest_actual_120146
  · exact g32p_supplierForest_actual_120156
  · exact g32p_supplierForest_actual_120164
  · exact g32p_supplierForest_actual_120171
  · exact g32p_supplierForest_actual_120180
  · exact g32p_supplierForest_actual_120200
  · exact g32p_supplierForest_actual_120206
  · exact g32p_supplierForest_actual_120230
  · exact g32p_supplierForest_actual_120277
  · exact g32p_supplierForest_actual_120284
  · exact g32p_supplierForest_actual_120393
  · exact g32p_supplierForest_actual_120443
  · exact g32p_supplierForest_actual_120451
  · exact g32p_supplierForest_actual_120457
  · exact g32p_supplierForest_actual_120653
  · exact g32p_supplierForest_actual_120658
  · exact g32p_supplierForest_actual_120688
  · exact g32p_supplierForest_actual_120742
  · exact g32p_supplierForest_actual_120762
  · exact g32p_supplierForest_actual_120763
  · exact g32p_supplierForest_actual_120813
  · exact g32p_supplierForest_actual_120817
  · exact g32p_supplierForest_actual_120822
  · exact g32p_supplierForest_actual_120892
  · exact g32p_supplierForest_actual_120938
  · exact g32p_supplierForest_actual_121006
  · exact g32p_supplierForest_actual_121015
  · exact g32p_supplierForest_actual_121103
  · exact g32p_supplierForest_actual_121165
  · exact g32p_supplierForest_actual_121199
  · exact g32p_supplierForest_actual_121219
  · exact g32p_supplierForest_actual_121235
  · exact g32p_supplierForest_actual_121254
  · exact g32p_supplierForest_actual_121269
  · exact g32p_supplierForest_actual_121282
  · exact g32p_supplierForest_actual_121310
  · exact g32p_supplierForest_actual_121349
  · exact g32p_supplierForest_actual_121393
  · exact g32p_supplierForest_actual_121406
  · exact g32p_supplierForest_actual_121408
  · exact g32p_supplierForest_actual_121436
  · exact g32p_supplierForest_actual_121485
  · exact g32p_supplierForest_actual_121497
  · exact g32p_supplierForest_actual_121515
  · exact g32p_supplierForest_actual_121538
  · exact g32p_supplierForest_actual_121543
  · exact g32p_supplierForest_actual_121552
  · exact g32p_supplierForest_actual_121604
  · exact g32p_supplierForest_actual_121608
  · exact g32p_supplierForest_actual_121612
  · exact g32p_supplierForest_actual_121638
  · exact g32p_supplierForest_actual_121654
  · exact g32p_supplierForest_actual_121667
  · exact g32p_supplierForest_actual_121706
  · exact g32p_supplierForest_actual_121717
  · exact g32p_supplierForest_actual_121725
  · exact g32p_supplierForest_actual_121763
  · exact g32p_supplierForest_actual_121796
  · exact g32p_supplierForest_actual_121802
  · exact g32p_supplierForest_actual_121808
  · exact g32p_supplierForest_actual_121925
  · exact g32p_supplierForest_actual_121955
  · exact g32p_supplierForest_actual_121957
  · exact g32p_supplierForest_actual_121994
  · exact g32p_supplierForest_actual_122020
  · exact g32p_supplierForest_actual_122062
  · exact g32p_supplierForest_actual_122076
  · exact g32p_supplierForest_actual_122113
  · exact g32p_supplierForest_actual_122132
  · exact g32p_supplierForest_actual_122134
  · exact g32p_supplierForest_actual_122177
  · exact g32p_supplierForest_actual_122189
  · exact g32p_supplierForest_actual_122206
  · exact g32p_supplierForest_actual_122239
  · exact g32p_supplierForest_actual_122309
  · exact g32p_supplierForest_actual_122354
  · exact g32p_supplierForest_actual_122356
  · exact g32p_supplierForest_actual_122369
  · exact g32p_supplierForest_actual_122372
  · exact g32p_supplierForest_actual_122373
  · exact g32p_supplierForest_actual_122436
  · exact g32p_supplierForest_actual_122452
  · exact g32p_supplierForest_actual_122456
  · exact g32p_supplierForest_actual_122473
  · exact g32p_supplierForest_actual_122475
  · exact g32p_supplierForest_actual_122497
  · exact g32p_supplierForest_actual_122535
  · exact g32p_supplierForest_actual_122594
  · exact g32p_supplierForest_actual_122630
  · exact g32p_supplierForest_actual_122664
  · exact g32p_supplierForest_actual_122686
  · exact g32p_supplierForest_actual_122695
  · exact g32p_supplierForest_actual_122707
  · exact g32p_supplierForest_actual_122727
  · exact g32p_supplierForest_actual_122729
  · exact g32p_supplierForest_actual_122735
  · exact g32p_supplierForest_actual_122774
  · exact g32p_supplierForest_actual_122776
  · exact g32p_supplierForest_actual_122811
  · exact g32p_supplierForest_actual_122875
  · exact g32p_supplierForest_actual_122879
  · exact g32p_supplierForest_actual_122903
  · exact g32p_supplierForest_actual_122934
  · exact g32p_supplierForest_actual_122941
  · exact g32p_supplierForest_actual_122968
  · exact g32p_supplierForest_actual_122978
  · exact g32p_supplierForest_actual_123031
  · exact g32p_supplierForest_actual_123141
  · exact g32p_supplierForest_actual_123210
  · exact g32p_supplierForest_actual_123221
  · exact g32p_supplierForest_actual_123238
  · exact g32p_supplierForest_actual_123276
  · exact g32p_supplierForest_actual_123291
  · exact g32p_supplierForest_actual_123300
  · exact g32p_supplierForest_actual_123331
  · exact g32p_supplierForest_actual_123425
  · exact g32p_supplierForest_actual_123482
  · exact g32p_supplierForest_actual_123494
  · exact g32p_supplierForest_actual_123496
  · exact g32p_supplierForest_actual_123505
  · exact g32p_supplierForest_actual_123590
  · exact g32p_supplierForest_actual_123611
  · exact g32p_supplierForest_actual_123712
  · exact g32p_supplierForest_actual_123762
  · exact g32p_supplierForest_actual_123766
  · exact g32p_supplierForest_actual_123780
  · exact g32p_supplierForest_actual_123805
  · exact g32p_supplierForest_actual_123818
  · exact g32p_supplierForest_actual_123865
  · exact g32p_supplierForest_actual_123948
  · exact g32p_supplierForest_actual_123995
  · exact g32p_supplierForest_actual_124032
  · exact g32p_supplierForest_actual_124039
  · exact g32p_supplierForest_actual_124052
  · exact g32p_supplierForest_actual_124054
  · exact g32p_supplierForest_actual_124134
  · exact g32p_supplierForest_actual_124184
  · exact g32p_supplierForest_actual_124205
  · exact g32p_supplierForest_actual_124210
  · exact g32p_supplierForest_actual_124216
  · exact g32p_supplierForest_actual_124362
  · exact g32p_supplierForest_actual_124371
  · exact g32p_supplierForest_actual_124376
  · exact g32p_supplierForest_actual_124491
  · exact g32p_supplierForest_actual_124499
  · exact g32p_supplierForest_actual_124534
  · exact g32p_supplierForest_actual_124541
  · exact g32p_supplierForest_actual_124557
  · exact g32p_supplierForest_actual_124570
  · exact g32p_supplierForest_actual_124609
  · exact g32p_supplierForest_actual_124625
  · exact g32p_supplierForest_actual_124640
  · exact g32p_supplierForest_actual_124669
  · exact g32p_supplierForest_actual_124698
  · exact g32p_supplierForest_actual_124712
  · exact g32p_supplierForest_actual_124715
  · exact g32p_supplierForest_actual_124716
  · exact g32p_supplierForest_actual_124735
  · exact g32p_supplierForest_actual_124743
  · exact g32p_supplierForest_actual_124755
  · exact g32p_supplierForest_actual_124767
  · exact g32p_supplierForest_actual_124768
  · exact g32p_supplierForest_actual_124791
  · exact g32p_supplierForest_actual_124794
  · exact g32p_supplierForest_actual_124828
  · exact g32p_supplierForest_actual_124872
  · exact g32p_supplierForest_actual_124900
  · exact g32p_supplierForest_actual_124915
  · exact g32p_supplierForest_actual_124943
  · exact g32p_supplierForest_actual_124969
  · exact g32p_supplierForest_actual_125057
  · exact g32p_supplierForest_actual_125061
  · exact g32p_supplierForest_actual_125065
  · exact g32p_supplierForest_actual_125074
  · exact g32p_supplierForest_actual_125215
  · exact g32p_supplierForest_actual_125290
  · exact g32p_supplierForest_actual_125293
  · exact g32p_supplierForest_actual_125320
  · exact g32p_supplierForest_actual_125326
  · exact g32p_supplierForest_actual_125374
  · exact g32p_supplierForest_actual_125462
  · exact g32p_supplierForest_actual_125475
  · exact g32p_supplierForest_actual_125480
  · exact g32p_supplierForest_actual_125489
  · exact g32p_supplierForest_actual_125511
  · exact g32p_supplierForest_actual_125522
  · exact g32p_supplierForest_actual_125529
  · exact g32p_supplierForest_actual_125555
  · exact g32p_supplierForest_actual_125587
  · exact g32p_supplierForest_actual_125628
  · exact g32p_supplierForest_actual_125645
  · exact g32p_supplierForest_actual_125647
  · exact g32p_supplierForest_actual_125682
  · exact g32p_supplierForest_actual_125738

end HodgeLean.Foundations.Program

end
end
