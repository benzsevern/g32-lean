import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0283
import HodgeLean.Foundations.Program.G32PropFourSixPacked0284
import HodgeLean.Foundations.Program.G32PropFourSixPacked0285
import HodgeLean.Foundations.Program.G32PropFourSixPacked0286
import HodgeLean.Foundations.Program.G32PropFourSixPacked0287
import HodgeLean.Foundations.Program.G32PropFourSixPacked0288
import HodgeLean.Foundations.Program.G32PropFourSixPacked0289
import HodgeLean.Foundations.Program.G32PropFourSixPacked0213
import HodgeLean.Foundations.Program.G32PropFourSixPacked0217
import HodgeLean.Foundations.Program.G32PropFourSixPacked0222
import HodgeLean.Foundations.Program.G32PropFourSixPacked0226
import HodgeLean.Foundations.Program.G32PropFourSixPacked0231
import HodgeLean.Foundations.Program.G32PropFourSixPacked0235
import HodgeLean.Foundations.Program.G32PropFourSixPacked0240
import HodgeLean.Foundations.Program.G32PropFourSixPacked0244
import HodgeLean.Foundations.Program.G32PropFourSixPacked0249
import HodgeLean.Foundations.Program.G32PropFourSixPacked0253
import HodgeLean.Foundations.Program.G32PropFourSixPacked0258
import HodgeLean.Foundations.Program.G32PropFourSixPacked0262
import HodgeLean.Foundations.Program.G32PropFourSixPacked0267
import HodgeLean.Foundations.Program.G32PropFourSixPacked0271
import HodgeLean.Foundations.Program.G32PropFourSixPacked0276
import HodgeLean.Foundations.Program.G32PropFourSixPacked0280
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow02
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_095215 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_095215 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095215 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_101144 := by
  decide +kernel

theorem g32p_supplierForest_actual_095215 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095215) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_095215
    g32p_supplierForest_actual_101144

def g32p_supplierForest_node_095317 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_095317 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095317 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096020 := by
  decide +kernel

theorem g32p_supplierForest_actual_095317 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095317) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_095317
    g32p_supplierForest_actual_096020

def g32p_supplierForest_node_095771 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_095771 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095771 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146795 := by
  decide +kernel

theorem g32p_supplierForest_actual_095771 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095771) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_095771
    g32p_supplierForest_actual_146795

def g32p_supplierForest_node_096010 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096010 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096010 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097270 := by
  decide +kernel

theorem g32p_supplierForest_actual_096010 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096010) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_096010
    g32p_supplierForest_actual_097270

def g32p_supplierForest_node_096811 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_096811 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096811 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087318 := by
  decide +kernel

theorem g32p_supplierForest_actual_096811 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096811) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_096811
    g32p_supplierForest_actual_087318

def g32p_supplierForest_node_097371 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097371 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097371 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_097432 := by
  decide +kernel

theorem g32p_supplierForest_actual_097371 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097371) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_097371
    g32p_supplierForest_actual_097432

def g32p_supplierForest_node_097771 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097771 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097771 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_085927 := by
  decide +kernel

theorem g32p_supplierForest_actual_097771 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097771) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_097771
    g32p_supplierForest_actual_085927

def g32p_supplierForest_node_097811 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097811 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097811 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100011 := by
  decide +kernel

theorem g32p_supplierForest_actual_097811 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097811) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_097811
    g32p_supplierForest_actual_100011

def g32p_supplierForest_node_098448 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_098448 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098448 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_101497 := by
  decide +kernel

theorem g32p_supplierForest_actual_098448 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098448) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_098448
    g32p_supplierForest_actual_101497

def g32p_supplierForest_node_098554 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_098554 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098554 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_086847 := by
  decide +kernel

theorem g32p_supplierForest_actual_098554 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098554) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_098554
    g32p_supplierForest_actual_086847

def g32p_supplierForest_node_098707 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098707 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098707 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_081228 := by
  decide +kernel

theorem g32p_supplierForest_actual_098707 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098707) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_098707
    g32p_supplierForest_actual_081228

def g32p_supplierForest_node_098873 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_098873 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098873 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_089852 := by
  decide +kernel

theorem g32p_supplierForest_actual_098873 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098873) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 3 g32p_supplierForest_edge_098873
    g32p_supplierForest_actual_089852

def g32p_supplierForest_node_099141 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_099141 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099141 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_098836 := by
  decide +kernel

theorem g32p_supplierForest_actual_099141 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099141) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_099141
    g32p_supplierForest_actual_098836

def g32p_supplierForest_node_099162 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_099162 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099162 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_096366 := by
  decide +kernel

theorem g32p_supplierForest_actual_099162 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099162) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_099162
    g32p_supplierForest_actual_096366

def g32p_supplierForest_node_099513 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_099513 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099513 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_096792 := by
  decide +kernel

theorem g32p_supplierForest_actual_099513 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099513) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_099513
    g32p_supplierForest_actual_096792

def g32p_supplierForest_node_099773 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_099773 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099773 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_094460 := by
  decide +kernel

theorem g32p_supplierForest_actual_099773 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099773) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_099773
    g32p_supplierForest_actual_094460

def g32p_supplierForest_node_099942 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_099942 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099942 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086374 := by
  decide +kernel

theorem g32p_supplierForest_actual_099942 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099942) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_099942
    g32p_supplierForest_actual_086374

def g32p_supplierForest_node_100087 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_100087 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_100087 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_150541 := by
  decide +kernel

theorem g32p_supplierForest_actual_100087 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_100087) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_100087
    g32p_supplierForest_actual_150541

def g32p_supplierForest_node_101044 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_101044 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101044 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078620 := by
  decide +kernel

theorem g32p_supplierForest_actual_101044 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101044) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_101044
    g32p_supplierForest_actual_078620

def g32p_supplierForest_node_101114 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_101114 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101114 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097069 := by
  decide +kernel

theorem g32p_supplierForest_actual_101114 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101114) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_101114
    g32p_supplierForest_actual_097069

def g32p_supplierForest_node_101161 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_101161 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101161 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_072215 := by
  decide +kernel

theorem g32p_supplierForest_actual_101161 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101161) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_101161
    g32p_supplierForest_actual_072215

def g32p_supplierForest_node_101564 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_101564 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101564 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_144751 := by
  decide +kernel

theorem g32p_supplierForest_actual_101564 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101564) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_101564
    g32p_supplierForest_actual_144751

def g32p_supplierForest_node_101823 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_101823 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_101823 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_101885 := by
  decide +kernel

theorem g32p_supplierForest_actual_101823 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_101823) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_101823
    g32p_supplierForest_actual_101885

def g32p_supplierForest_node_102530 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_102530 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_102530 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_026636 := by
  decide +kernel

theorem g32p_supplierForest_actual_102530 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_102530) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_102530
    g32p_supplierForest_actual_026636

def g32p_supplierForest_node_102592 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_102592 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_102592 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_115752 := by
  decide +kernel

theorem g32p_supplierForest_actual_102592 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_102592) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_102592
    g32p_supplierForest_actual_115752

def g32p_supplierForest_node_103446 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_103446 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_103446 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_040320 := by
  decide +kernel

theorem g32p_supplierForest_actual_103446 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_103446) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_103446
    g32p_supplierForest_actual_040320

def g32p_supplierForest_node_103589 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_103589 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_103589 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_114323 := by
  decide +kernel

theorem g32p_supplierForest_actual_103589 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_103589) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_103589
    g32p_supplierForest_actual_114323

def g32p_supplierForest_node_103826 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_103826 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_103826 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_110638 := by
  decide +kernel

theorem g32p_supplierForest_actual_103826 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_103826) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_103826
    g32p_supplierForest_actual_110638

def g32p_supplierForest_node_105350 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_105350 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_105350 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_030389 := by
  decide +kernel

theorem g32p_supplierForest_actual_105350 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_105350) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_105350
    g32p_supplierForest_actual_030389

def g32p_supplierForest_node_105444 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_105444 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_105444 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122144 := by
  decide +kernel

theorem g32p_supplierForest_actual_105444 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_105444) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_105444
    g32p_supplierForest_actual_122144

def g32p_supplierForest_node_105554 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_105554 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_105554 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_040906 := by
  decide +kernel

theorem g32p_supplierForest_actual_105554 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_105554) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_105554
    g32p_supplierForest_actual_040906

def g32p_supplierForest_node_105599 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_105599 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_105599 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_042340 := by
  decide +kernel

theorem g32p_supplierForest_actual_105599 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_105599) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_105599
    g32p_supplierForest_actual_042340

def g32p_supplierForest_node_106002 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_106002 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106002 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_106917 := by
  decide +kernel

theorem g32p_supplierForest_actual_106002 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106002) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_106002
    g32p_supplierForest_actual_106917

def g32p_supplierForest_node_106140 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_106140 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106140 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_112728 := by
  decide +kernel

theorem g32p_supplierForest_actual_106140 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106140) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_106140
    g32p_supplierForest_actual_112728

def g32p_supplierForest_node_106375 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_106375 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106375 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_026570 := by
  decide +kernel

theorem g32p_supplierForest_actual_106375 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106375) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_106375
    g32p_supplierForest_actual_026570

def g32p_supplierForest_node_106919 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_106919 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106919 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_101988 := by
  decide +kernel

theorem g32p_supplierForest_actual_106919 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106919) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_106919
    g32p_supplierForest_actual_101988

def g32p_supplierForest_node_109120 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_109120 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109120 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_032667 := by
  decide +kernel

theorem g32p_supplierForest_actual_109120 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109120) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_109120
    g32p_supplierForest_actual_032667

def g32p_supplierForest_node_110130 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110130 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110130 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_112625 := by
  decide +kernel

theorem g32p_supplierForest_actual_110130 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110130) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_110130
    g32p_supplierForest_actual_112625

def g32p_supplierForest_node_110372 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110372 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110372 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_102777 := by
  decide +kernel

theorem g32p_supplierForest_actual_110372 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110372) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_110372
    g32p_supplierForest_actual_102777

def g32p_supplierForest_node_110374 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨2, 2⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_110374 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110374 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_124172 := by
  decide +kernel

theorem g32p_supplierForest_actual_110374 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110374) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_110374
    g32p_supplierForest_actual_124172

def g32p_supplierForest_node_110786 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110786 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110786 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_110469 := by
  decide +kernel

theorem g32p_supplierForest_actual_110786 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110786) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_110786
    g32p_supplierForest_actual_110469

def g32p_supplierForest_node_111058 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111058 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111058 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121041 := by
  decide +kernel

theorem g32p_supplierForest_actual_111058 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111058) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_111058
    g32p_supplierForest_actual_121041

def g32p_supplierForest_node_111080 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111080 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111080 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_038865 := by
  decide +kernel

theorem g32p_supplierForest_actual_111080 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111080) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_111080
    g32p_supplierForest_actual_038865

def g32p_supplierForest_node_111089 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111089 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111089 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_111068 := by
  decide +kernel

theorem g32p_supplierForest_actual_111089 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111089) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_111089
    g32p_supplierForest_actual_111068

def g32p_supplierForest_node_111694 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111694 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111694 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121491 := by
  decide +kernel

theorem g32p_supplierForest_actual_111694 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111694) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_111694
    g32p_supplierForest_actual_121491

def g32p_supplierForest_node_111938 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111938 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111938 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121928 := by
  decide +kernel

theorem g32p_supplierForest_actual_111938 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111938) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_111938
    g32p_supplierForest_actual_121928

def g32p_supplierForest_node_112025 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112025 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112025 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_043252 := by
  decide +kernel

theorem g32p_supplierForest_actual_112025 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112025) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_112025
    g32p_supplierForest_actual_043252

def g32p_supplierForest_node_112162 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112162 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112162 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_026532 := by
  decide +kernel

theorem g32p_supplierForest_actual_112162 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112162) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_112162
    g32p_supplierForest_actual_026532

def g32p_supplierForest_node_112174 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112174 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112174 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118329 := by
  decide +kernel

theorem g32p_supplierForest_actual_112174 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112174) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_112174
    g32p_supplierForest_actual_118329

def g32p_supplierForest_node_112879 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_112879 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112879 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_124646 := by
  decide +kernel

theorem g32p_supplierForest_actual_112879 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112879) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_112879
    g32p_supplierForest_actual_124646

def g32p_supplierForest_node_113155 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_113155 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113155 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115173 := by
  decide +kernel

theorem g32p_supplierForest_actual_113155 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113155) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_113155
    g32p_supplierForest_actual_115173

def g32p_supplierForest_node_113388 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113388 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113388 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_031618 := by
  decide +kernel

theorem g32p_supplierForest_actual_113388 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113388) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_113388
    g32p_supplierForest_actual_031618

def g32p_supplierForest_node_114083 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_114083 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114083 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_115127 := by
  decide +kernel

theorem g32p_supplierForest_actual_114083 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114083) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_114083
    g32p_supplierForest_actual_115127

def g32p_supplierForest_node_114099 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114099 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114099 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_112505 := by
  decide +kernel

theorem g32p_supplierForest_actual_114099 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114099) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_114099
    g32p_supplierForest_actual_112505

def g32p_supplierForest_node_114423 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114423 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114423 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_105259 := by
  decide +kernel

theorem g32p_supplierForest_actual_114423 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114423) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_114423
    g32p_supplierForest_actual_105259

def g32p_supplierForest_node_114543 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114543 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114543 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_115360 := by
  decide +kernel

theorem g32p_supplierForest_actual_114543 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114543) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_114543
    g32p_supplierForest_actual_115360

def g32p_supplierForest_node_114591 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114591 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114591 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_111502 := by
  decide +kernel

theorem g32p_supplierForest_actual_114591 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114591) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_114591
    g32p_supplierForest_actual_111502

def g32p_supplierForest_node_114598 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_114598 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114598 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118071 := by
  decide +kernel

theorem g32p_supplierForest_actual_114598 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114598) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_114598
    g32p_supplierForest_actual_118071

def g32p_supplierForest_node_114710 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_114710 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114710 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_119701 := by
  decide +kernel

theorem g32p_supplierForest_actual_114710 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114710) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_114710
    g32p_supplierForest_actual_119701

def g32p_supplierForest_node_114814 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114814 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114814 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_112907 := by
  decide +kernel

theorem g32p_supplierForest_actual_114814 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114814) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_114814
    g32p_supplierForest_actual_112907

def g32p_supplierForest_node_115116 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_115116 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115116 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118883 := by
  decide +kernel

theorem g32p_supplierForest_actual_115116 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115116) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_115116
    g32p_supplierForest_actual_118883

def g32p_supplierForest_node_115684 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115684 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115684 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_030210 := by
  decide +kernel

theorem g32p_supplierForest_actual_115684 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115684) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_115684
    g32p_supplierForest_actual_030210

def g32p_supplierForest_node_116399 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_116399 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116399 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113738 := by
  decide +kernel

theorem g32p_supplierForest_actual_116399 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116399) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_116399
    g32p_supplierForest_actual_113738

def g32p_supplierForest_node_116547 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_116547 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116547 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_119831 := by
  decide +kernel

theorem g32p_supplierForest_actual_116547 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116547) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_116547
    g32p_supplierForest_actual_119831

def g32p_supplierForest_node_116686 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_116686 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_116686 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102040 := by
  decide +kernel

theorem g32p_supplierForest_actual_116686 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_116686) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_116686
    g32p_supplierForest_actual_102040

def g32p_supplierForest_node_117424 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_117424 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117424 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_106602 := by
  decide +kernel

theorem g32p_supplierForest_actual_117424 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117424) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_117424
    g32p_supplierForest_actual_106602

def g32p_supplierForest_node_117528 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_117528 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117528 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_116524 := by
  decide +kernel

theorem g32p_supplierForest_actual_117528 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117528) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_117528
    g32p_supplierForest_actual_116524

def g32p_supplierForest_node_117689 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117689 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117689 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_119647 := by
  decide +kernel

theorem g32p_supplierForest_actual_117689 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117689) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_117689
    g32p_supplierForest_actual_119647

def g32p_supplierForest_node_117785 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_117785 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117785 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_106421 := by
  decide +kernel

theorem g32p_supplierForest_actual_117785 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117785) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_117785
    g32p_supplierForest_actual_106421

def g32p_supplierForest_node_117991 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_117991 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_117991 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118205 := by
  decide +kernel

theorem g32p_supplierForest_actual_117991 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_117991) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_117991
    g32p_supplierForest_actual_118205

def g32p_supplierForest_node_118122 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118122 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118122 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_040682 := by
  decide +kernel

theorem g32p_supplierForest_actual_118122 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118122) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_118122
    g32p_supplierForest_actual_040682

def g32p_supplierForest_node_118617 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118617 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118617 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_126665 := by
  decide +kernel

theorem g32p_supplierForest_actual_118617 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118617) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 3 g32p_supplierForest_edge_118617
    g32p_supplierForest_actual_126665

def g32p_supplierForest_node_118895 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_118895 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118895 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_124447 := by
  decide +kernel

theorem g32p_supplierForest_actual_118895 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118895) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_118895
    g32p_supplierForest_actual_124447

def g32p_supplierForest_node_119311 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_119311 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119311 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_119307 := by
  decide +kernel

theorem g32p_supplierForest_actual_119311 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119311) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_119311
    g32p_supplierForest_actual_119307

def g32p_supplierForest_node_119965 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119965 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119965 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_117084 := by
  decide +kernel

theorem g32p_supplierForest_actual_119965 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119965) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_119965
    g32p_supplierForest_actual_117084

def g32p_supplierForest_node_120097 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_120097 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120097 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123463 := by
  decide +kernel

theorem g32p_supplierForest_actual_120097 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120097) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_120097
    g32p_supplierForest_actual_123463

def g32p_supplierForest_node_120439 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_120439 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120439 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109071 := by
  decide +kernel

theorem g32p_supplierForest_actual_120439 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120439) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_120439
    g32p_supplierForest_actual_109071

def g32p_supplierForest_node_120492 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120492 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120492 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122225 := by
  decide +kernel

theorem g32p_supplierForest_actual_120492 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120492) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_120492
    g32p_supplierForest_actual_122225

def g32p_supplierForest_node_120670 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_120670 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120670 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_108733 := by
  decide +kernel

theorem g32p_supplierForest_actual_120670 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120670) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_120670
    g32p_supplierForest_actual_108733

def g32p_supplierForest_node_120841 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_120841 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_120841 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_036191 := by
  decide +kernel

theorem g32p_supplierForest_actual_120841 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_120841) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_120841
    g32p_supplierForest_actual_036191

def g32p_supplierForest_node_121048 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_121048 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121048 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_107651 := by
  decide +kernel

theorem g32p_supplierForest_actual_121048 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121048) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 0 g32p_supplierForest_edge_121048
    g32p_supplierForest_actual_107651

def g32p_supplierForest_node_121060 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_121060 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121060 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_121707 := by
  decide +kernel

theorem g32p_supplierForest_actual_121060 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121060) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_121060
    g32p_supplierForest_actual_121707

def g32p_supplierForest_node_121061 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_121061 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121061 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_041166 := by
  decide +kernel

theorem g32p_supplierForest_actual_121061 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121061) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_121061
    g32p_supplierForest_actual_041166

def g32p_supplierForest_node_121389 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_121389 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121389 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_107036 := by
  decide +kernel

theorem g32p_supplierForest_actual_121389 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121389) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_121389
    g32p_supplierForest_actual_107036

def g32p_supplierForest_node_121965 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_121965 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_121965 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_116968 := by
  decide +kernel

theorem g32p_supplierForest_actual_121965 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_121965) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_121965
    g32p_supplierForest_actual_116968

def g32p_supplierForest_node_122061 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_122061 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122061 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_120725 := by
  decide +kernel

theorem g32p_supplierForest_actual_122061 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122061) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_122061
    g32p_supplierForest_actual_120725

def g32p_supplierForest_node_122109 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_122109 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122109 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115131 := by
  decide +kernel

theorem g32p_supplierForest_actual_122109 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122109) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_122109
    g32p_supplierForest_actual_115131

def g32p_supplierForest_node_122560 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_122560 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122560 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_114128 := by
  decide +kernel

theorem g32p_supplierForest_actual_122560 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122560) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_122560
    g32p_supplierForest_actual_114128

def g32p_supplierForest_node_122883 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_122883 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_122883 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_126503 := by
  decide +kernel

theorem g32p_supplierForest_actual_122883 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_122883) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_122883
    g32p_supplierForest_actual_126503

def g32p_supplierForest_node_123444 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_123444 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123444 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_121303 := by
  decide +kernel

theorem g32p_supplierForest_actual_123444 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123444) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_123444
    g32p_supplierForest_actual_121303

def g32p_supplierForest_node_123535 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_123535 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123535 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_104085 := by
  decide +kernel

theorem g32p_supplierForest_actual_123535 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123535) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_123535
    g32p_supplierForest_actual_104085

def g32p_supplierForest_node_123536 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_123536 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_123536 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_124056 := by
  decide +kernel

theorem g32p_supplierForest_actual_123536 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_123536) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_123536
    g32p_supplierForest_actual_124056

def g32p_supplierForest_node_124645 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_124645 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_124645 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153506 := by
  decide +kernel

theorem g32p_supplierForest_actual_124645 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_124645) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_124645
    g32p_supplierForest_actual_153506

def g32p_supplierForest_node_125060 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_125060 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125060 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124686 := by
  decide +kernel

theorem g32p_supplierForest_actual_125060 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125060) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 0 g32p_supplierForest_edge_125060
    g32p_supplierForest_actual_124686

def g32p_supplierForest_node_125346 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_125346 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125346 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_102674 := by
  decide +kernel

theorem g32p_supplierForest_actual_125346 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125346) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_125346
    g32p_supplierForest_actual_102674

def g32p_supplierForest_node_125400 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_125400 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125400 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_125046 := by
  decide +kernel

theorem g32p_supplierForest_actual_125400 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125400) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_125400
    g32p_supplierForest_actual_125046

def g32p_supplierForest_node_125544 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_125544 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_125544 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_109183 := by
  decide +kernel

theorem g32p_supplierForest_actual_125544 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_125544) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_125544
    g32p_supplierForest_actual_109183

def g32p_supplierForest_node_126572 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_126572 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_126572 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122603 := by
  decide +kernel

theorem g32p_supplierForest_actual_126572 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_126572) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_126572
    g32p_supplierForest_actual_122603

def g32p_supplierForest_node_127018 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_127018 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_127018 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126380 := by
  decide +kernel

theorem g32p_supplierForest_actual_127018 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_127018) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_127018
    g32p_supplierForest_actual_126380

def g32p_supplierForest_node_127207 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_127207 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_127207 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_126352 := by
  decide +kernel

theorem g32p_supplierForest_actual_127207 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_127207) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_127207
    g32p_supplierForest_actual_126352

def g32p_supplierForest_node_127294 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_127294 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_127294 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_114171 := by
  decide +kernel

theorem g32p_supplierForest_actual_127294 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_127294) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_127294
    g32p_supplierForest_actual_114171

def g32p_supplierForest_node_127976 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_127976 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_127976 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_135384 := by
  decide +kernel

theorem g32p_supplierForest_actual_127976 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_127976) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_127976
    g32p_supplierForest_actual_135384

def g32p_supplierForest_node_128224 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_128224 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_128224 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_137474 := by
  decide +kernel

theorem g32p_supplierForest_actual_128224 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_128224) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_128224
    g32p_supplierForest_actual_137474

def g32p_supplierForest_node_128427 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_128427 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_128427 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067420 := by
  decide +kernel

theorem g32p_supplierForest_actual_128427 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_128427) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_128427
    g32p_supplierForest_actual_067420

def g32p_supplierForest_node_128467 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_128467 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_128467 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_058971 := by
  decide +kernel

theorem g32p_supplierForest_actual_128467 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_128467) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_128467
    g32p_supplierForest_actual_058971

def g32p_supplierForest_node_128749 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_128749 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_128749 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_130699 := by
  decide +kernel

theorem g32p_supplierForest_actual_128749 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_128749) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_128749
    g32p_supplierForest_actual_130699

def g32p_supplierForest_node_128922 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_128922 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_128922 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_135894 := by
  decide +kernel

theorem g32p_supplierForest_actual_128922 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_128922) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_128922
    g32p_supplierForest_actual_135894

def g32p_supplierForest_node_128977 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_128977 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_128977 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_137921 := by
  decide +kernel

theorem g32p_supplierForest_actual_128977 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_128977) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 0 g32p_supplierForest_edge_128977
    g32p_supplierForest_actual_137921

def g32p_supplierForest_node_129376 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_129376 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_129376 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_142195 := by
  decide +kernel

theorem g32p_supplierForest_actual_129376 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_129376) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_129376
    g32p_supplierForest_actual_142195

def g32p_supplierForest_node_129634 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_129634 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_129634 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_047146 := by
  decide +kernel

theorem g32p_supplierForest_actual_129634 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_129634) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_129634
    g32p_supplierForest_actual_047146

def g32p_supplierForest_node_130690 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_130690 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_130690 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_131644 := by
  decide +kernel

theorem g32p_supplierForest_actual_130690 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_130690) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_130690
    g32p_supplierForest_actual_131644

def g32p_supplierForest_node_130728 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_130728 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_130728 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_136669 := by
  decide +kernel

theorem g32p_supplierForest_actual_130728 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_130728) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_130728
    g32p_supplierForest_actual_136669

def g32p_supplierForest_node_130812 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_130812 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_130812 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_052850 := by
  decide +kernel

theorem g32p_supplierForest_actual_130812 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_130812) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_130812
    g32p_supplierForest_actual_052850

def g32p_supplierForest_node_130908 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_130908 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_130908 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_137698 := by
  decide +kernel

theorem g32p_supplierForest_actual_130908 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_130908) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_130908
    g32p_supplierForest_actual_137698

def g32p_supplierForest_node_131742 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_131742 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_131742 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_132718 := by
  decide +kernel

theorem g32p_supplierForest_actual_131742 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_131742) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_131742
    g32p_supplierForest_actual_132718

def g32p_supplierForest_node_132325 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_132325 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_132325 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_132790 := by
  decide +kernel

theorem g32p_supplierForest_actual_132325 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_132325) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_132325
    g32p_supplierForest_actual_132790

def g32p_supplierForest_node_132699 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_132699 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_132699 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_139361 := by
  decide +kernel

theorem g32p_supplierForest_actual_132699 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_132699) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_132699
    g32p_supplierForest_actual_139361

def g32p_supplierForest_node_133580 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_133580 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_133580 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_134376 := by
  decide +kernel

theorem g32p_supplierForest_actual_133580 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_133580) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_133580
    g32p_supplierForest_actual_134376

def g32p_supplierForest_node_133611 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_133611 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_133611 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_140010 := by
  decide +kernel

theorem g32p_supplierForest_actual_133611 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_133611) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_133611
    g32p_supplierForest_actual_140010

def g32p_supplierForest_node_133662 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_133662 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_133662 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_141191 := by
  decide +kernel

theorem g32p_supplierForest_actual_133662 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_133662) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_133662
    g32p_supplierForest_actual_141191

def g32p_supplierForest_node_133945 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_133945 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_133945 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_133996 := by
  decide +kernel

theorem g32p_supplierForest_actual_133945 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_133945) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_133945
    g32p_supplierForest_actual_133996

def g32p_supplierForest_node_134039 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_134039 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_134039 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_136604 := by
  decide +kernel

theorem g32p_supplierForest_actual_134039 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_134039) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_134039
    g32p_supplierForest_actual_136604

def g32p_supplierForest_node_134505 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_134505 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_134505 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_071008 := by
  decide +kernel

theorem g32p_supplierForest_actual_134505 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_134505) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_134505
    g32p_supplierForest_actual_071008

def g32p_supplierForest_node_134645 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_134645 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_134645 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_131539 := by
  decide +kernel

theorem g32p_supplierForest_actual_134645 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_134645) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 2 g32p_supplierForest_edge_134645
    g32p_supplierForest_actual_131539

def g32p_supplierForest_node_135485 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_135485 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_135485 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_048191 := by
  decide +kernel

theorem g32p_supplierForest_actual_135485 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_135485) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_135485
    g32p_supplierForest_actual_048191

def g32p_supplierForest_node_135553 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_135553 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_135553 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_056950 := by
  decide +kernel

theorem g32p_supplierForest_actual_135553 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_135553) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_135553
    g32p_supplierForest_actual_056950

def g32p_supplierForest_node_135655 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_135655 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_135655 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_133231 := by
  decide +kernel

theorem g32p_supplierForest_actual_135655 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_135655) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_135655
    g32p_supplierForest_actual_133231

def g32p_supplierForest_node_135865 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_135865 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_135865 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_049204 := by
  decide +kernel

theorem g32p_supplierForest_actual_135865 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_135865) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_135865
    g32p_supplierForest_actual_049204

def g32p_supplierForest_node_135881 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_135881 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_135881 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_130469 := by
  decide +kernel

theorem g32p_supplierForest_actual_135881 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_135881) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_135881
    g32p_supplierForest_actual_130469

def g32p_supplierForest_node_136012 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_136012 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_136012 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_143020 := by
  decide +kernel

theorem g32p_supplierForest_actual_136012 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_136012) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_136012
    g32p_supplierForest_actual_143020

def g32p_supplierForest_node_136402 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_136402 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_136402 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065156 := by
  decide +kernel

theorem g32p_supplierForest_actual_136402 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_136402) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_136402
    g32p_supplierForest_actual_065156

def g32p_supplierForest_node_136878 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_136878 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_136878 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071142 := by
  decide +kernel

theorem g32p_supplierForest_actual_136878 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_136878) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_136878
    g32p_supplierForest_actual_071142

def g32p_supplierForest_node_137205 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_137205 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_137205 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_137250 := by
  decide +kernel

theorem g32p_supplierForest_actual_137205 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_137205) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_137205
    g32p_supplierForest_actual_137250

def g32p_supplierForest_node_137306 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_137306 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_137306 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_060199 := by
  decide +kernel

theorem g32p_supplierForest_actual_137306 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_137306) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_137306
    g32p_supplierForest_actual_060199

def g32p_supplierForest_node_137398 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_137398 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_137398 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_134114 := by
  decide +kernel

theorem g32p_supplierForest_actual_137398 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_137398) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_137398
    g32p_supplierForest_actual_134114

def g32p_supplierForest_node_137978 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_137978 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_137978 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_130114 := by
  decide +kernel

theorem g32p_supplierForest_actual_137978 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_137978) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_137978
    g32p_supplierForest_actual_130114

def g32p_supplierForest_node_138413 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_138413 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_138413 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_133015 := by
  decide +kernel

theorem g32p_supplierForest_actual_138413 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_138413) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_138413
    g32p_supplierForest_actual_133015

def g32p_supplierForest_node_138417 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_138417 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_138417 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_134166 := by
  decide +kernel

theorem g32p_supplierForest_actual_138417 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_138417) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_138417
    g32p_supplierForest_actual_134166

def g32p_supplierForest_node_138450 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_138450 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_138450 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_052938 := by
  decide +kernel

theorem g32p_supplierForest_actual_138450 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_138450) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_138450
    g32p_supplierForest_actual_052938

def g32p_supplierForest_node_138492 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_138492 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_138492 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_070353 := by
  decide +kernel

theorem g32p_supplierForest_actual_138492 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_138492) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_138492
    g32p_supplierForest_actual_070353

def g32p_supplierForest_node_139376 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_139376 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_139376 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_135413 := by
  decide +kernel

theorem g32p_supplierForest_actual_139376 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_139376) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_139376
    g32p_supplierForest_actual_135413

def g32p_supplierForest_node_139682 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_139682 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_139682 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_055933 := by
  decide +kernel

theorem g32p_supplierForest_actual_139682 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_139682) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_139682
    g32p_supplierForest_actual_055933

def g32p_supplierForest_node_139822 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_139822 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_139822 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_139757 := by
  decide +kernel

theorem g32p_supplierForest_actual_139822 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_139822) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_139822
    g32p_supplierForest_actual_139757

def g32p_supplierForest_node_140113 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_140113 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_140113 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_070971 := by
  decide +kernel

theorem g32p_supplierForest_actual_140113 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_140113) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 3 g32p_supplierForest_edge_140113
    g32p_supplierForest_actual_070971

def g32p_supplierForest_node_140233 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_140233 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_140233 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_140445 := by
  decide +kernel

theorem g32p_supplierForest_actual_140233 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_140233) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_140233
    g32p_supplierForest_actual_140445

def g32p_supplierForest_node_141152 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_141152 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_141152 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_138906 := by
  decide +kernel

theorem g32p_supplierForest_actual_141152 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_141152) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_141152
    g32p_supplierForest_actual_138906

def g32p_supplierForest_node_141260 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_141260 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_141260 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_135888 := by
  decide +kernel

theorem g32p_supplierForest_actual_141260 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_141260) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_141260
    g32p_supplierForest_actual_135888

def g32p_supplierForest_node_141277 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_141277 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_141277 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_138785 := by
  decide +kernel

theorem g32p_supplierForest_actual_141277 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_141277) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_141277
    g32p_supplierForest_actual_138785

def g32p_supplierForest_node_142531 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_142531 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_142531 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_134158 := by
  decide +kernel

theorem g32p_supplierForest_actual_142531 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_142531) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_142531
    g32p_supplierForest_actual_134158

def g32p_supplierForest_node_142591 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_142591 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_142591 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_133821 := by
  decide +kernel

theorem g32p_supplierForest_actual_142591 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_142591) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_142591
    g32p_supplierForest_actual_133821

def g32p_supplierForest_node_142890 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_142890 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_142890 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_142499 := by
  decide +kernel

theorem g32p_supplierForest_actual_142890 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_142890) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_142890
    g32p_supplierForest_actual_142499

def g32p_supplierForest_node_142946 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_142946 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_142946 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_136016 := by
  decide +kernel

theorem g32p_supplierForest_actual_142946 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_142946) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_142946
    g32p_supplierForest_actual_136016

def g32p_supplierForest_node_142980 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_142980 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_142980 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064408 := by
  decide +kernel

theorem g32p_supplierForest_actual_142980 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_142980) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_142980
    g32p_supplierForest_actual_064408

def g32p_supplierForest_node_144807 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_144807 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_144807 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_148968 := by
  decide +kernel

theorem g32p_supplierForest_actual_144807 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_144807) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_144807
    g32p_supplierForest_actual_148968

def g32p_supplierForest_node_145908 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_145908 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_145908 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_090735 := by
  decide +kernel

theorem g32p_supplierForest_actual_145908 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_145908) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_145908
    g32p_supplierForest_actual_090735

def g32p_supplierForest_node_145930 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_145930 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_145930 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_146872 := by
  decide +kernel

theorem g32p_supplierForest_actual_145930 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_145930) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_145930
    g32p_supplierForest_actual_146872

def g32p_supplierForest_node_146001 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_146001 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_146001 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_146724 := by
  decide +kernel

theorem g32p_supplierForest_actual_146001 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_146001) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_146001
    g32p_supplierForest_actual_146724

def g32p_supplierForest_node_146722 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_146722 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_146722 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071916 := by
  decide +kernel

theorem g32p_supplierForest_actual_146722 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_146722) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_146722
    g32p_supplierForest_actual_071916

def g32p_supplierForest_node_147082 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_147082 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_147082 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146941 := by
  decide +kernel

theorem g32p_supplierForest_actual_147082 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_147082) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_147082
    g32p_supplierForest_actual_146941

def g32p_supplierForest_node_147993 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_147993 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_147993 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_144909 := by
  decide +kernel

theorem g32p_supplierForest_actual_147993 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_147993) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_147993
    g32p_supplierForest_actual_144909

def g32p_supplierForest_node_148360 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_148360 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148360 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_096744 := by
  decide +kernel

theorem g32p_supplierForest_actual_148360 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148360) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_148360
    g32p_supplierForest_actual_096744

def g32p_supplierForest_node_148740 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_148740 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148740 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_089515 := by
  decide +kernel

theorem g32p_supplierForest_actual_148740 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148740) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_148740
    g32p_supplierForest_actual_089515

def g32p_supplierForest_node_148813 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_148813 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_148813 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078153 := by
  decide +kernel

theorem g32p_supplierForest_actual_148813 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_148813) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_148813
    g32p_supplierForest_actual_078153

def g32p_supplierForest_node_149976 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_149976 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_149976 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_087115 := by
  decide +kernel

theorem g32p_supplierForest_actual_149976 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_149976) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_149976
    g32p_supplierForest_actual_087115

def g32p_supplierForest_node_150358 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_150358 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_150358 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_148155 := by
  decide +kernel

theorem g32p_supplierForest_actual_150358 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_150358) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_150358
    g32p_supplierForest_actual_148155

def g32p_supplierForest_node_152564 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_152564 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152564 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118205 := by
  decide +kernel

theorem g32p_supplierForest_actual_152564 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152564) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_152564
    g32p_supplierForest_actual_118205

def g32p_supplierForest_node_154256 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_154256 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154256 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_120896 := by
  decide +kernel

theorem g32p_supplierForest_actual_154256 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154256) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_154256
    g32p_supplierForest_actual_120896

def g32p_supplierForest_node_154691 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_154691 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154691 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_127013 := by
  decide +kernel

theorem g32p_supplierForest_actual_154691 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154691) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_154691
    g32p_supplierForest_actual_127013

def g32p_supplierForest_node_155087 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155087 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155087 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_138109 := by
  decide +kernel

theorem g32p_supplierForest_actual_155087 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155087) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_155087
    g32p_supplierForest_actual_138109

def g32p_supplierForest_node_000753 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_000753 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000753 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_005948 := by
  decide +kernel

theorem g32p_supplierForest_actual_000753 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000753) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_000753
    g32p_supplierForest_actual_005948

def g32p_supplierForest_node_001048 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_001048 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001048 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_011293 := by
  decide +kernel

theorem g32p_supplierForest_actual_001048 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001048) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_001048
    g32p_supplierForest_actual_011293

def g32p_supplierForest_node_001699 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001699 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001699 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_012442 := by
  decide +kernel

theorem g32p_supplierForest_actual_001699 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001699) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_001699
    g32p_supplierForest_actual_012442

def g32p_supplierForest_node_004903 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_004903 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_004903 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_004111 := by
  decide +kernel

theorem g32p_supplierForest_actual_004903 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_004903) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_004903
    g32p_supplierForest_actual_004111

def g32p_supplierForest_node_005552 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_005552 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_005552 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_003432 := by
  decide +kernel

theorem g32p_supplierForest_actual_005552 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_005552) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_005552
    g32p_supplierForest_actual_003432

def g32p_supplierForest_node_006526 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_006526 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_006526 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_063174 := by
  decide +kernel

theorem g32p_supplierForest_actual_006526 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_006526) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_006526
    g32p_supplierForest_actual_063174

def g32p_supplierForest_node_007362 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_007362 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_007362 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_007432 := by
  decide +kernel

theorem g32p_supplierForest_actual_007362 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_007362) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_007362
    g32p_supplierForest_actual_007432

def g32p_supplierForest_node_010692 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_010692 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_010692 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_008806 := by
  decide +kernel

theorem g32p_supplierForest_actual_010692 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_010692) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_010692
    g32p_supplierForest_actual_008806

def g32p_supplierForest_node_010965 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_010965 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_010965 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_045013 := by
  decide +kernel

theorem g32p_supplierForest_actual_010965 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_010965) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_010965
    g32p_supplierForest_actual_045013

def g32p_supplierForest_node_011739 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_011739 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_011739 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_009720 := by
  decide +kernel

theorem g32p_supplierForest_actual_011739 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_011739) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_011739
    g32p_supplierForest_actual_009720

def g32p_supplierForest_node_012320 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_012320 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_012320 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_054435 := by
  decide +kernel

theorem g32p_supplierForest_actual_012320 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_012320) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_012320
    g32p_supplierForest_actual_054435

def g32p_supplierForest_node_012738 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_012738 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_012738 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_013591 := by
  decide +kernel

theorem g32p_supplierForest_actual_012738 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_012738) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_012738
    g32p_supplierForest_actual_013591

def g32p_supplierForest_node_015820 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_015820 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_015820 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_084731 := by
  decide +kernel

theorem g32p_supplierForest_actual_015820 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_015820) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_015820
    g32p_supplierForest_actual_084731

def g32p_supplierForest_node_017278 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_017278 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_017278 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_090576 := by
  decide +kernel

theorem g32p_supplierForest_actual_017278 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_017278) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_017278
    g32p_supplierForest_actual_090576

def g32p_supplierForest_node_018188 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_018188 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_018188 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_072105 := by
  decide +kernel

theorem g32p_supplierForest_actual_018188 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_018188) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_018188
    g32p_supplierForest_actual_072105

def g32p_supplierForest_node_018757 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_018757 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_018757 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023641 := by
  decide +kernel

theorem g32p_supplierForest_actual_018757 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_018757) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_018757
    g32p_supplierForest_actual_023641

def g32p_supplierForest_node_019221 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_019221 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019221 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019410 := by
  decide +kernel

theorem g32p_supplierForest_actual_019221 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019221) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_019221
    g32p_supplierForest_actual_019410

def g32p_supplierForest_node_019443 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_019443 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_019443 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019222 := by
  decide +kernel

theorem g32p_supplierForest_actual_019443 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_019443) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_019443
    g32p_supplierForest_actual_019222

def g32p_supplierForest_node_023163 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_023163 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_023163 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013737 := by
  decide +kernel

theorem g32p_supplierForest_actual_023163 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_023163) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_023163
    g32p_supplierForest_actual_013737

def g32p_supplierForest_node_024705 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_024705 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_024705 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_029713 := by
  decide +kernel

theorem g32p_supplierForest_actual_024705 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_024705) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_024705
    g32p_supplierForest_actual_029713

def g32p_supplierForest_node_026786 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_026786 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026786 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_026787 := by
  decide +kernel

theorem g32p_supplierForest_actual_026786 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026786) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_026786
    g32p_supplierForest_actual_026787

def g32p_supplierForest_node_026983 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_026983 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_026983 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_032687 := by
  decide +kernel

theorem g32p_supplierForest_actual_026983 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_026983) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_026983
    g32p_supplierForest_actual_032687

def g32p_supplierForest_node_027153 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_027153 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027153 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_032974 := by
  decide +kernel

theorem g32p_supplierForest_actual_027153 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027153) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_027153
    g32p_supplierForest_actual_032974

def g32p_supplierForest_node_027799 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_027799 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_027799 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_038361 := by
  decide +kernel

theorem g32p_supplierForest_actual_027799 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_027799) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_027799
    g32p_supplierForest_actual_038361

def g32p_supplierForest_node_028089 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_028089 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_028089 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_038686 := by
  decide +kernel

theorem g32p_supplierForest_actual_028089 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_028089) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_028089
    g32p_supplierForest_actual_038686

def g32p_supplierForest_node_030760 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_030760 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_030760 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_038695 := by
  decide +kernel

theorem g32p_supplierForest_actual_030760 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_030760) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_030760
    g32p_supplierForest_actual_038695

def g32p_supplierForest_node_031921 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_031921 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_031921 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_036238 := by
  decide +kernel

theorem g32p_supplierForest_actual_031921 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_031921) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_031921
    g32p_supplierForest_actual_036238

def g32p_supplierForest_node_032243 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_032243 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_032243 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_030125 := by
  decide +kernel

theorem g32p_supplierForest_actual_032243 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_032243) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_032243
    g32p_supplierForest_actual_030125

def g32p_supplierForest_node_034263 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_034263 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_034263 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_043751 := by
  decide +kernel

theorem g32p_supplierForest_actual_034263 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_034263) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_034263
    g32p_supplierForest_actual_043751

def g32p_supplierForest_node_042112 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_042112 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_042112 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_031860 := by
  decide +kernel

theorem g32p_supplierForest_actual_042112 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_042112) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_042112
    g32p_supplierForest_actual_031860

def g32p_supplierForest_node_043192 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_043192 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_043192 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_027060 := by
  decide +kernel

theorem g32p_supplierForest_actual_043192 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_043192) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_043192
    g32p_supplierForest_actual_027060

def g32p_supplierForest_node_044924 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_044924 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_044924 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_053485 := by
  decide +kernel

theorem g32p_supplierForest_actual_044924 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_044924) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_044924
    g32p_supplierForest_actual_053485

def g32p_supplierForest_node_045908 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_045908 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_045908 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_046478 := by
  decide +kernel

theorem g32p_supplierForest_actual_045908 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_045908) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_045908
    g32p_supplierForest_actual_046478

def g32p_supplierForest_node_050054 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_050054 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_050054 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_056855 := by
  decide +kernel

theorem g32p_supplierForest_actual_050054 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_050054) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_050054
    g32p_supplierForest_actual_056855

def g32p_supplierForest_node_056899 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056899 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056899 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_046911 := by
  decide +kernel

theorem g32p_supplierForest_actual_056899 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056899) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_056899
    g32p_supplierForest_actual_046911

def g32p_supplierForest_node_059187 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_059187 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059187 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_061670 := by
  decide +kernel

theorem g32p_supplierForest_actual_059187 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059187) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_059187
    g32p_supplierForest_actual_061670

def g32p_supplierForest_node_059459 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_059459 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059459 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_069077 := by
  decide +kernel

theorem g32p_supplierForest_actual_059459 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059459) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_059459
    g32p_supplierForest_actual_069077

def g32p_supplierForest_node_059933 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059933 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059933 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068173 := by
  decide +kernel

theorem g32p_supplierForest_actual_059933 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059933) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_059933
    g32p_supplierForest_actual_068173

def g32p_supplierForest_node_060483 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_060483 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060483 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_058327 := by
  decide +kernel

theorem g32p_supplierForest_actual_060483 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060483) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_060483
    g32p_supplierForest_actual_058327

def g32p_supplierForest_node_063223 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_063223 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063223 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065364 := by
  decide +kernel

theorem g32p_supplierForest_actual_063223 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063223) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_063223
    g32p_supplierForest_actual_065364

def g32p_supplierForest_node_072291 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_072291 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072291 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_014999 := by
  decide +kernel

theorem g32p_supplierForest_actual_072291 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072291) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_072291
    g32p_supplierForest_actual_014999

def g32p_supplierForest_node_072310 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_072310 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072310 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_017172 := by
  decide +kernel

theorem g32p_supplierForest_actual_072310 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072310) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_072310
    g32p_supplierForest_actual_017172

def g32p_supplierForest_node_074892 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074892 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074892 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_074230 := by
  decide +kernel

theorem g32p_supplierForest_actual_074892 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074892) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_074892
    g32p_supplierForest_actual_074230

def g32p_supplierForest_node_076430 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_076430 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076430 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077880 := by
  decide +kernel

theorem g32p_supplierForest_actual_076430 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076430) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 3 g32p_supplierForest_edge_076430
    g32p_supplierForest_actual_077880

def g32p_supplierForest_node_079007 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_079007 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079007 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_079547 := by
  decide +kernel

theorem g32p_supplierForest_actual_079007 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079007) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_079007
    g32p_supplierForest_actual_079547

def g32p_supplierForest_node_080703 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_080703 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080703 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_078522 := by
  decide +kernel

theorem g32p_supplierForest_actual_080703 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080703) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_080703
    g32p_supplierForest_actual_078522

def g32p_supplierForest_node_091198 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091198 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091198 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097771 := by
  decide +kernel

theorem g32p_supplierForest_actual_091198 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091198) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_091198
    g32p_supplierForest_actual_097771

def g32p_supplierForest_node_091580 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091580 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091580 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_080053 := by
  decide +kernel

theorem g32p_supplierForest_actual_091580 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091580) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_091580
    g32p_supplierForest_actual_080053

def g32p_supplierForest_node_093474 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_093474 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093474 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_090881 := by
  decide +kernel

theorem g32p_supplierForest_actual_093474 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093474) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_093474
    g32p_supplierForest_actual_090881

def g32p_supplierForest_node_095165 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_095165 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095165 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_095215 := by
  decide +kernel

theorem g32p_supplierForest_actual_095165 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095165) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_095165
    g32p_supplierForest_actual_095215

def g32p_supplierForest_node_097190 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_097190 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097190 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088268 := by
  decide +kernel

theorem g32p_supplierForest_actual_097190 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097190) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_097190
    g32p_supplierForest_actual_088268

def g32p_supplierForest_node_102652 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_102652 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_102652 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_034885 := by
  decide +kernel

theorem g32p_supplierForest_actual_102652 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_102652) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_102652
    g32p_supplierForest_actual_034885

def g32p_supplierForest_node_106044 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_106044 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_106044 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_105599 := by
  decide +kernel

theorem g32p_supplierForest_actual_106044 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_106044) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_106044
    g32p_supplierForest_actual_105599

def g32p_supplierForest_node_111083 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_111083 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111083 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112174 := by
  decide +kernel

theorem g32p_supplierForest_actual_111083 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111083) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_111083
    g32p_supplierForest_actual_112174

def g32p_supplierForest_node_115824 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_115824 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115824 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_036864 := by
  decide +kernel

theorem g32p_supplierForest_actual_115824 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115824) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_115824
    g32p_supplierForest_actual_036864

def g32p_supplierForest_node_118099 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_118099 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118099 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_117528 := by
  decide +kernel

theorem g32p_supplierForest_actual_118099 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118099) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_118099
    g32p_supplierForest_actual_117528

def g32p_supplierForest_node_118904 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_118904 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_118904 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_110786 := by
  decide +kernel

theorem g32p_supplierForest_actual_118904 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_118904) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_118904
    g32p_supplierForest_actual_110786

def g32p_supplierForest_node_119372 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_119372 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_119372 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_041043 := by
  decide +kernel

theorem g32p_supplierForest_actual_119372 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_119372) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_119372
    g32p_supplierForest_actual_041043

def g32p_supplierForest_node_135507 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_135507 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_135507 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_060531 := by
  decide +kernel

theorem g32p_supplierForest_actual_135507 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_135507) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_135507
    g32p_supplierForest_actual_060531

def g32p_supplierForest_node_137354 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_137354 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_137354 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_138450 := by
  decide +kernel

theorem g32p_supplierForest_actual_137354 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_137354) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_137354
    g32p_supplierForest_actual_138450

def g32p_supplierForest_node_143047 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_143047 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_143047 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_155087 := by
  decide +kernel

theorem g32p_supplierForest_actual_143047 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_143047) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_143047
    g32p_supplierForest_actual_155087

def g32p_supplierForest_node_050162 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_050162 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_050162 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_137354 := by
  decide +kernel

theorem g32p_supplierForest_actual_050162 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_050162) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_050162
    g32p_supplierForest_actual_137354

def g32p_supplierForest_node_088306 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_088306 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088306 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_091198 := by
  decide +kernel

theorem g32p_supplierForest_actual_088306 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088306) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_088306
    g32p_supplierForest_actual_091198

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_144 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_095215 else g32p_supplierForest_node_095317) else (if i.val < 3 then g32p_supplierForest_node_095771 else g32p_supplierForest_node_096010)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_096811 else g32p_supplierForest_node_097371) else (if i.val < 7 then g32p_supplierForest_node_097771 else g32p_supplierForest_node_097811))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_098448 else g32p_supplierForest_node_098554) else (if i.val < 11 then g32p_supplierForest_node_098707 else g32p_supplierForest_node_098873)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_099141 else g32p_supplierForest_node_099162) else (if i.val < 15 then g32p_supplierForest_node_099513 else g32p_supplierForest_node_099773)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_099942 else g32p_supplierForest_node_100087) else (if i.val < 19 then g32p_supplierForest_node_101044 else g32p_supplierForest_node_101114)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_101161 else g32p_supplierForest_node_101564) else (if i.val < 23 then g32p_supplierForest_node_101823 else g32p_supplierForest_node_102530))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_102592 else g32p_supplierForest_node_103446) else (if i.val < 27 then g32p_supplierForest_node_103589 else g32p_supplierForest_node_103826)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_105350 else g32p_supplierForest_node_105444) else (if i.val < 31 then g32p_supplierForest_node_105554 else g32p_supplierForest_node_105599))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_106002 else g32p_supplierForest_node_106140) else (if i.val < 35 then g32p_supplierForest_node_106375 else g32p_supplierForest_node_106919)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_109120 else g32p_supplierForest_node_110130) else (if i.val < 39 then g32p_supplierForest_node_110372 else g32p_supplierForest_node_110374))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_110786 else g32p_supplierForest_node_111058) else (if i.val < 43 then g32p_supplierForest_node_111080 else g32p_supplierForest_node_111089)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_111694 else g32p_supplierForest_node_111938) else (if i.val < 47 then g32p_supplierForest_node_112025 else g32p_supplierForest_node_112162)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_112174 else g32p_supplierForest_node_112879) else (if i.val < 51 then g32p_supplierForest_node_113155 else g32p_supplierForest_node_113388)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_114083 else g32p_supplierForest_node_114099) else (if i.val < 55 then g32p_supplierForest_node_114423 else g32p_supplierForest_node_114543))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_114591 else g32p_supplierForest_node_114598) else (if i.val < 59 then g32p_supplierForest_node_114710 else g32p_supplierForest_node_114814)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_115116 else g32p_supplierForest_node_115684) else (if i.val < 63 then g32p_supplierForest_node_116399 else g32p_supplierForest_node_116547)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_116686 else g32p_supplierForest_node_117424) else (if i.val < 67 then g32p_supplierForest_node_117528 else g32p_supplierForest_node_117689)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_117785 else g32p_supplierForest_node_117991) else (if i.val < 71 then g32p_supplierForest_node_118122 else g32p_supplierForest_node_118617))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_118895 else g32p_supplierForest_node_119311) else (if i.val < 75 then g32p_supplierForest_node_119965 else g32p_supplierForest_node_120097)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_120439 else g32p_supplierForest_node_120492) else (if i.val < 79 then g32p_supplierForest_node_120670 else g32p_supplierForest_node_120841)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_121048 else g32p_supplierForest_node_121060) else (if i.val < 83 then g32p_supplierForest_node_121061 else g32p_supplierForest_node_121389)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_121965 else g32p_supplierForest_node_122061) else (if i.val < 87 then g32p_supplierForest_node_122109 else g32p_supplierForest_node_122560))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_122883 else g32p_supplierForest_node_123444) else (if i.val < 91 then g32p_supplierForest_node_123535 else g32p_supplierForest_node_123536)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_124645 else g32p_supplierForest_node_125060) else (if i.val < 95 then g32p_supplierForest_node_125346 else g32p_supplierForest_node_125400))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_125544 else g32p_supplierForest_node_126572) else (if i.val < 99 then g32p_supplierForest_node_127018 else g32p_supplierForest_node_127207)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_127294 else g32p_supplierForest_node_127976) else (if i.val < 103 then g32p_supplierForest_node_128224 else g32p_supplierForest_node_128427))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_128467 else g32p_supplierForest_node_128749) else (if i.val < 107 then g32p_supplierForest_node_128922 else g32p_supplierForest_node_128977)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_129376 else g32p_supplierForest_node_129634) else (if i.val < 111 then g32p_supplierForest_node_130690 else g32p_supplierForest_node_130728)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_130812 else g32p_supplierForest_node_130908) else (if i.val < 115 then g32p_supplierForest_node_131742 else g32p_supplierForest_node_132325)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_132699 else g32p_supplierForest_node_133580) else (if i.val < 119 then g32p_supplierForest_node_133611 else g32p_supplierForest_node_133662))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_133945 else g32p_supplierForest_node_134039) else (if i.val < 123 then g32p_supplierForest_node_134505 else g32p_supplierForest_node_134645)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_135485 else g32p_supplierForest_node_135553) else (if i.val < 127 then g32p_supplierForest_node_135655 else g32p_supplierForest_node_135865))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_135881 else g32p_supplierForest_node_136012) else (if i.val < 131 then g32p_supplierForest_node_136402 else g32p_supplierForest_node_136878)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_137205 else g32p_supplierForest_node_137306) else (if i.val < 135 then g32p_supplierForest_node_137398 else g32p_supplierForest_node_137978))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_138413 else g32p_supplierForest_node_138417) else (if i.val < 139 then g32p_supplierForest_node_138450 else g32p_supplierForest_node_138492)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_139376 else g32p_supplierForest_node_139682) else (if i.val < 143 then g32p_supplierForest_node_139822 else g32p_supplierForest_node_140113)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_140233 else g32p_supplierForest_node_141152) else (if i.val < 147 then g32p_supplierForest_node_141260 else g32p_supplierForest_node_141277)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_142531 else g32p_supplierForest_node_142591) else (if i.val < 151 then g32p_supplierForest_node_142890 else g32p_supplierForest_node_142946))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_142980 else g32p_supplierForest_node_144807) else (if i.val < 155 then g32p_supplierForest_node_145908 else g32p_supplierForest_node_145930)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_146001 else g32p_supplierForest_node_146722) else (if i.val < 159 then g32p_supplierForest_node_147082 else g32p_supplierForest_node_147993))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_148360 else g32p_supplierForest_node_148740) else (if i.val < 163 then g32p_supplierForest_node_148813 else g32p_supplierForest_node_149976)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_150358 else g32p_supplierForest_node_152564) else (if i.val < 167 then g32p_supplierForest_node_154256 else g32p_supplierForest_node_154691))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_155087 else g32p_supplierForest_node_000753) else (if i.val < 171 then g32p_supplierForest_node_001048 else g32p_supplierForest_node_001699)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_004903 else g32p_supplierForest_node_005552) else (if i.val < 175 then g32p_supplierForest_node_006526 else g32p_supplierForest_node_007362)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_010692 else g32p_supplierForest_node_010965) else (if i.val < 179 then g32p_supplierForest_node_011739 else g32p_supplierForest_node_012320)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_012738 else g32p_supplierForest_node_015820) else (if i.val < 183 then g32p_supplierForest_node_017278 else g32p_supplierForest_node_018188))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_018757 else g32p_supplierForest_node_019221) else (if i.val < 187 then g32p_supplierForest_node_019443 else g32p_supplierForest_node_023163)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_024705 else g32p_supplierForest_node_026786) else (if i.val < 191 then g32p_supplierForest_node_026983 else g32p_supplierForest_node_027153)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_027799 else g32p_supplierForest_node_028089) else (if i.val < 195 then g32p_supplierForest_node_030760 else g32p_supplierForest_node_031921)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_032243 else g32p_supplierForest_node_034263) else (if i.val < 199 then g32p_supplierForest_node_042112 else g32p_supplierForest_node_043192))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_044924 else g32p_supplierForest_node_045908) else (if i.val < 203 then g32p_supplierForest_node_050054 else g32p_supplierForest_node_056899)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_059187 else g32p_supplierForest_node_059459) else (if i.val < 207 then g32p_supplierForest_node_059933 else g32p_supplierForest_node_060483)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_063223 else g32p_supplierForest_node_072291) else (if i.val < 211 then g32p_supplierForest_node_072310 else g32p_supplierForest_node_074892)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_076430 else g32p_supplierForest_node_079007) else (if i.val < 215 then g32p_supplierForest_node_080703 else g32p_supplierForest_node_091198))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_091580 else g32p_supplierForest_node_093474) else (if i.val < 219 then g32p_supplierForest_node_095165 else g32p_supplierForest_node_097190)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_102652 else g32p_supplierForest_node_106044) else (if i.val < 223 then g32p_supplierForest_node_111083 else g32p_supplierForest_node_115824))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_118099 else g32p_supplierForest_node_118904) else (if i.val < 227 then g32p_supplierForest_node_119372 else g32p_supplierForest_node_135507)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_137354 else g32p_supplierForest_node_143047) else (if i.val < 231 then g32p_supplierForest_node_050162 else g32p_supplierForest_node_088306))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_095215 else g32p_supplierForest_node_095317) else (if i.val < 235 then g32p_supplierForest_node_095771 else g32p_supplierForest_node_096010)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_096811 else g32p_supplierForest_node_097371) else (if i.val < 239 then g32p_supplierForest_node_097771 else g32p_supplierForest_node_097811)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_098448 else g32p_supplierForest_node_098554) else (if i.val < 243 then g32p_supplierForest_node_098707 else g32p_supplierForest_node_098873)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_099141 else g32p_supplierForest_node_099162) else (if i.val < 247 then g32p_supplierForest_node_099513 else g32p_supplierForest_node_099773))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_099942 else g32p_supplierForest_node_100087) else (if i.val < 251 then g32p_supplierForest_node_101044 else g32p_supplierForest_node_101114)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_101161 else g32p_supplierForest_node_101564) else (if i.val < 255 then g32p_supplierForest_node_101823 else g32p_supplierForest_node_102530))))))))

def g32p_supplierForest_classes_144 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 49 else 47) else (if i.val < 3 then 46 else 26)) else (if i.val < 6 then (if i.val < 5 then 49 else 49) else (if i.val < 7 then 49 else 46))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 46 else 49) else (if i.val < 11 then 46 else 54)) else (if i.val < 14 then (if i.val < 13 then 46 else 46) else (if i.val < 15 then 25 else 26)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 49 else 49) else (if i.val < 19 then 46 else 49)) else (if i.val < 22 then (if i.val < 21 then 49 else 47) else (if i.val < 23 then 49 else 57))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 60 else 57) else (if i.val < 27 then 57 else 57)) else (if i.val < 30 then (if i.val < 29 then 57 else 60) else (if i.val < 31 then 57 else 57))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 57 else 57) else (if i.val < 35 then 57 else 57)) else (if i.val < 38 then (if i.val < 37 then 30 else 60) else (if i.val < 39 then 57 else 60))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 57 else 60) else (if i.val < 43 then 57 else 57)) else (if i.val < 46 then (if i.val < 45 then 57 else 30) else (if i.val < 47 then 57 else 29)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 57 else 30) else (if i.val < 51 then 57 else 30)) else (if i.val < 54 then (if i.val < 53 then 57 else 59) else (if i.val < 55 then 36 else 30))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 57 else 30) else (if i.val < 59 then 57 else 60)) else (if i.val < 62 then (if i.val < 61 then 57 else 57) else (if i.val < 63 then 29 else 57)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 57 else 57) else (if i.val < 67 then 57 else 57)) else (if i.val < 70 then (if i.val < 69 then 60 else 60) else (if i.val < 71 then 57 else 62))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 57 else 57) else (if i.val < 75 then 60 else 60)) else (if i.val < 78 then (if i.val < 77 then 60 else 60) else (if i.val < 79 then 30 else 16)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 33 else 57) else (if i.val < 83 then 57 else 57)) else (if i.val < 86 then (if i.val < 85 then 57 else 57) else (if i.val < 87 then 57 else 57))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 57 else 30) else (if i.val < 91 then 57 else 57)) else (if i.val < 94 then (if i.val < 93 then 30 else 62) else (if i.val < 95 then 57 else 57))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 57 else 57) else (if i.val < 99 then 60 else 57)) else (if i.val < 102 then (if i.val < 101 then 30 else 38) else (if i.val < 103 then 38 else 22))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 38 else 21) else (if i.val < 107 then 73 else 68)) else (if i.val < 110 then (if i.val < 109 then 38 else 38) else (if i.val < 111 then 73 else 38)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 22 else 38) else (if i.val < 115 then 38 else 73)) else (if i.val < 118 then (if i.val < 117 then 73 else 38) else (if i.val < 119 then 21 else 73))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 38 else 38) else (if i.val < 123 then 38 else 68)) else (if i.val < 126 then (if i.val < 125 then 38 else 38) else (if i.val < 127 then 21 else 38))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 38 else 38) else (if i.val < 131 then 21 else 22)) else (if i.val < 134 then (if i.val < 133 then 38 else 38) else (if i.val < 135 then 21 else 38))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 21 else 73) else (if i.val < 139 then 21 else 38)) else (if i.val < 142 then (if i.val < 141 then 73 else 38) else (if i.val < 143 then 73 else 40)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 73 else 73) else (if i.val < 147 then 73 else 21)) else (if i.val < 150 then (if i.val < 149 then 73 else 38) else (if i.val < 151 then 21 else 38))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 38 else 86) else (if i.val < 155 then 49 else 46)) else (if i.val < 158 then (if i.val < 157 then 47 else 49) else (if i.val < 159 then 54 else 26))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 49 else 54) else (if i.val < 163 then 25 else 46)) else (if i.val < 166 then (if i.val < 165 then 46 else 60) else (if i.val < 167 then 57 else 60))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 21 else 21) else (if i.val < 171 then 21 else 26)) else (if i.val < 174 then (if i.val < 173 then 30 else 30) else (if i.val < 175 then 38 else 38)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 21 else 43) else (if i.val < 179 then 38 else 38)) else (if i.val < 182 then (if i.val < 181 then 26 else 47) else (if i.val < 183 then 49 else 49))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 49 else 49) else (if i.val < 187 then 26 else 49)) else (if i.val < 190 then (if i.val < 189 then 30 else 57) else (if i.val < 191 then 16 else 57)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 57 else 57) else (if i.val < 195 then 57 else 30)) else (if i.val < 198 then (if i.val < 197 then 57 else 16) else (if i.val < 199 then 57 else 57))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 38 else 21) else (if i.val < 203 then 21 else 38)) else (if i.val < 206 then (if i.val < 205 then 38 else 21) else (if i.val < 207 then 38 else 21)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 22 else 49) else (if i.val < 211 then 49 else 46)) else (if i.val < 214 then (if i.val < 213 then 53 else 49) else (if i.val < 215 then 49 else 49))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 49 else 46) else (if i.val < 219 then 49 else 26)) else (if i.val < 222 then (if i.val < 221 then 57 else 57) else (if i.val < 223 then 57 else 57))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 57 else 57) else (if i.val < 227 then 57 else 38)) else (if i.val < 230 then (if i.val < 229 then 21 else 21) else (if i.val < 231 then 21 else 49))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 49 else 47) else (if i.val < 235 then 46 else 26)) else (if i.val < 238 then (if i.val < 237 then 49 else 49) else (if i.val < 239 then 49 else 46)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 46 else 49) else (if i.val < 243 then 46 else 54)) else (if i.val < 246 then (if i.val < 245 then 46 else 46) else (if i.val < 247 then 25 else 26))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 49 else 49) else (if i.val < 251 then 46 else 49)) else (if i.val < 254 then (if i.val < 253 then 49 else 47) else (if i.val < 255 then 49 else 57))))))))

theorem g32p_supplierForest_actual_144 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_144 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_144 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_095215
  · exact g32p_supplierForest_actual_095317
  · exact g32p_supplierForest_actual_095771
  · exact g32p_supplierForest_actual_096010
  · exact g32p_supplierForest_actual_096811
  · exact g32p_supplierForest_actual_097371
  · exact g32p_supplierForest_actual_097771
  · exact g32p_supplierForest_actual_097811
  · exact g32p_supplierForest_actual_098448
  · exact g32p_supplierForest_actual_098554
  · exact g32p_supplierForest_actual_098707
  · exact g32p_supplierForest_actual_098873
  · exact g32p_supplierForest_actual_099141
  · exact g32p_supplierForest_actual_099162
  · exact g32p_supplierForest_actual_099513
  · exact g32p_supplierForest_actual_099773
  · exact g32p_supplierForest_actual_099942
  · exact g32p_supplierForest_actual_100087
  · exact g32p_supplierForest_actual_101044
  · exact g32p_supplierForest_actual_101114
  · exact g32p_supplierForest_actual_101161
  · exact g32p_supplierForest_actual_101564
  · exact g32p_supplierForest_actual_101823
  · exact g32p_supplierForest_actual_102530
  · exact g32p_supplierForest_actual_102592
  · exact g32p_supplierForest_actual_103446
  · exact g32p_supplierForest_actual_103589
  · exact g32p_supplierForest_actual_103826
  · exact g32p_supplierForest_actual_105350
  · exact g32p_supplierForest_actual_105444
  · exact g32p_supplierForest_actual_105554
  · exact g32p_supplierForest_actual_105599
  · exact g32p_supplierForest_actual_106002
  · exact g32p_supplierForest_actual_106140
  · exact g32p_supplierForest_actual_106375
  · exact g32p_supplierForest_actual_106919
  · exact g32p_supplierForest_actual_109120
  · exact g32p_supplierForest_actual_110130
  · exact g32p_supplierForest_actual_110372
  · exact g32p_supplierForest_actual_110374
  · exact g32p_supplierForest_actual_110786
  · exact g32p_supplierForest_actual_111058
  · exact g32p_supplierForest_actual_111080
  · exact g32p_supplierForest_actual_111089
  · exact g32p_supplierForest_actual_111694
  · exact g32p_supplierForest_actual_111938
  · exact g32p_supplierForest_actual_112025
  · exact g32p_supplierForest_actual_112162
  · exact g32p_supplierForest_actual_112174
  · exact g32p_supplierForest_actual_112879
  · exact g32p_supplierForest_actual_113155
  · exact g32p_supplierForest_actual_113388
  · exact g32p_supplierForest_actual_114083
  · exact g32p_supplierForest_actual_114099
  · exact g32p_supplierForest_actual_114423
  · exact g32p_supplierForest_actual_114543
  · exact g32p_supplierForest_actual_114591
  · exact g32p_supplierForest_actual_114598
  · exact g32p_supplierForest_actual_114710
  · exact g32p_supplierForest_actual_114814
  · exact g32p_supplierForest_actual_115116
  · exact g32p_supplierForest_actual_115684
  · exact g32p_supplierForest_actual_116399
  · exact g32p_supplierForest_actual_116547
  · exact g32p_supplierForest_actual_116686
  · exact g32p_supplierForest_actual_117424
  · exact g32p_supplierForest_actual_117528
  · exact g32p_supplierForest_actual_117689
  · exact g32p_supplierForest_actual_117785
  · exact g32p_supplierForest_actual_117991
  · exact g32p_supplierForest_actual_118122
  · exact g32p_supplierForest_actual_118617
  · exact g32p_supplierForest_actual_118895
  · exact g32p_supplierForest_actual_119311
  · exact g32p_supplierForest_actual_119965
  · exact g32p_supplierForest_actual_120097
  · exact g32p_supplierForest_actual_120439
  · exact g32p_supplierForest_actual_120492
  · exact g32p_supplierForest_actual_120670
  · exact g32p_supplierForest_actual_120841
  · exact g32p_supplierForest_actual_121048
  · exact g32p_supplierForest_actual_121060
  · exact g32p_supplierForest_actual_121061
  · exact g32p_supplierForest_actual_121389
  · exact g32p_supplierForest_actual_121965
  · exact g32p_supplierForest_actual_122061
  · exact g32p_supplierForest_actual_122109
  · exact g32p_supplierForest_actual_122560
  · exact g32p_supplierForest_actual_122883
  · exact g32p_supplierForest_actual_123444
  · exact g32p_supplierForest_actual_123535
  · exact g32p_supplierForest_actual_123536
  · exact g32p_supplierForest_actual_124645
  · exact g32p_supplierForest_actual_125060
  · exact g32p_supplierForest_actual_125346
  · exact g32p_supplierForest_actual_125400
  · exact g32p_supplierForest_actual_125544
  · exact g32p_supplierForest_actual_126572
  · exact g32p_supplierForest_actual_127018
  · exact g32p_supplierForest_actual_127207
  · exact g32p_supplierForest_actual_127294
  · exact g32p_supplierForest_actual_127976
  · exact g32p_supplierForest_actual_128224
  · exact g32p_supplierForest_actual_128427
  · exact g32p_supplierForest_actual_128467
  · exact g32p_supplierForest_actual_128749
  · exact g32p_supplierForest_actual_128922
  · exact g32p_supplierForest_actual_128977
  · exact g32p_supplierForest_actual_129376
  · exact g32p_supplierForest_actual_129634
  · exact g32p_supplierForest_actual_130690
  · exact g32p_supplierForest_actual_130728
  · exact g32p_supplierForest_actual_130812
  · exact g32p_supplierForest_actual_130908
  · exact g32p_supplierForest_actual_131742
  · exact g32p_supplierForest_actual_132325
  · exact g32p_supplierForest_actual_132699
  · exact g32p_supplierForest_actual_133580
  · exact g32p_supplierForest_actual_133611
  · exact g32p_supplierForest_actual_133662
  · exact g32p_supplierForest_actual_133945
  · exact g32p_supplierForest_actual_134039
  · exact g32p_supplierForest_actual_134505
  · exact g32p_supplierForest_actual_134645
  · exact g32p_supplierForest_actual_135485
  · exact g32p_supplierForest_actual_135553
  · exact g32p_supplierForest_actual_135655
  · exact g32p_supplierForest_actual_135865
  · exact g32p_supplierForest_actual_135881
  · exact g32p_supplierForest_actual_136012
  · exact g32p_supplierForest_actual_136402
  · exact g32p_supplierForest_actual_136878
  · exact g32p_supplierForest_actual_137205
  · exact g32p_supplierForest_actual_137306
  · exact g32p_supplierForest_actual_137398
  · exact g32p_supplierForest_actual_137978
  · exact g32p_supplierForest_actual_138413
  · exact g32p_supplierForest_actual_138417
  · exact g32p_supplierForest_actual_138450
  · exact g32p_supplierForest_actual_138492
  · exact g32p_supplierForest_actual_139376
  · exact g32p_supplierForest_actual_139682
  · exact g32p_supplierForest_actual_139822
  · exact g32p_supplierForest_actual_140113
  · exact g32p_supplierForest_actual_140233
  · exact g32p_supplierForest_actual_141152
  · exact g32p_supplierForest_actual_141260
  · exact g32p_supplierForest_actual_141277
  · exact g32p_supplierForest_actual_142531
  · exact g32p_supplierForest_actual_142591
  · exact g32p_supplierForest_actual_142890
  · exact g32p_supplierForest_actual_142946
  · exact g32p_supplierForest_actual_142980
  · exact g32p_supplierForest_actual_144807
  · exact g32p_supplierForest_actual_145908
  · exact g32p_supplierForest_actual_145930
  · exact g32p_supplierForest_actual_146001
  · exact g32p_supplierForest_actual_146722
  · exact g32p_supplierForest_actual_147082
  · exact g32p_supplierForest_actual_147993
  · exact g32p_supplierForest_actual_148360
  · exact g32p_supplierForest_actual_148740
  · exact g32p_supplierForest_actual_148813
  · exact g32p_supplierForest_actual_149976
  · exact g32p_supplierForest_actual_150358
  · exact g32p_supplierForest_actual_152564
  · exact g32p_supplierForest_actual_154256
  · exact g32p_supplierForest_actual_154691
  · exact g32p_supplierForest_actual_155087
  · exact g32p_supplierForest_actual_000753
  · exact g32p_supplierForest_actual_001048
  · exact g32p_supplierForest_actual_001699
  · exact g32p_supplierForest_actual_004903
  · exact g32p_supplierForest_actual_005552
  · exact g32p_supplierForest_actual_006526
  · exact g32p_supplierForest_actual_007362
  · exact g32p_supplierForest_actual_010692
  · exact g32p_supplierForest_actual_010965
  · exact g32p_supplierForest_actual_011739
  · exact g32p_supplierForest_actual_012320
  · exact g32p_supplierForest_actual_012738
  · exact g32p_supplierForest_actual_015820
  · exact g32p_supplierForest_actual_017278
  · exact g32p_supplierForest_actual_018188
  · exact g32p_supplierForest_actual_018757
  · exact g32p_supplierForest_actual_019221
  · exact g32p_supplierForest_actual_019443
  · exact g32p_supplierForest_actual_023163
  · exact g32p_supplierForest_actual_024705
  · exact g32p_supplierForest_actual_026786
  · exact g32p_supplierForest_actual_026983
  · exact g32p_supplierForest_actual_027153
  · exact g32p_supplierForest_actual_027799
  · exact g32p_supplierForest_actual_028089
  · exact g32p_supplierForest_actual_030760
  · exact g32p_supplierForest_actual_031921
  · exact g32p_supplierForest_actual_032243
  · exact g32p_supplierForest_actual_034263
  · exact g32p_supplierForest_actual_042112
  · exact g32p_supplierForest_actual_043192
  · exact g32p_supplierForest_actual_044924
  · exact g32p_supplierForest_actual_045908
  · exact g32p_supplierForest_actual_050054
  · exact g32p_supplierForest_actual_056899
  · exact g32p_supplierForest_actual_059187
  · exact g32p_supplierForest_actual_059459
  · exact g32p_supplierForest_actual_059933
  · exact g32p_supplierForest_actual_060483
  · exact g32p_supplierForest_actual_063223
  · exact g32p_supplierForest_actual_072291
  · exact g32p_supplierForest_actual_072310
  · exact g32p_supplierForest_actual_074892
  · exact g32p_supplierForest_actual_076430
  · exact g32p_supplierForest_actual_079007
  · exact g32p_supplierForest_actual_080703
  · exact g32p_supplierForest_actual_091198
  · exact g32p_supplierForest_actual_091580
  · exact g32p_supplierForest_actual_093474
  · exact g32p_supplierForest_actual_095165
  · exact g32p_supplierForest_actual_097190
  · exact g32p_supplierForest_actual_102652
  · exact g32p_supplierForest_actual_106044
  · exact g32p_supplierForest_actual_111083
  · exact g32p_supplierForest_actual_115824
  · exact g32p_supplierForest_actual_118099
  · exact g32p_supplierForest_actual_118904
  · exact g32p_supplierForest_actual_119372
  · exact g32p_supplierForest_actual_135507
  · exact g32p_supplierForest_actual_137354
  · exact g32p_supplierForest_actual_143047
  · exact g32p_supplierForest_actual_050162
  · exact g32p_supplierForest_actual_088306
  · exact g32p_supplierForest_actual_095215
  · exact g32p_supplierForest_actual_095317
  · exact g32p_supplierForest_actual_095771
  · exact g32p_supplierForest_actual_096010
  · exact g32p_supplierForest_actual_096811
  · exact g32p_supplierForest_actual_097371
  · exact g32p_supplierForest_actual_097771
  · exact g32p_supplierForest_actual_097811
  · exact g32p_supplierForest_actual_098448
  · exact g32p_supplierForest_actual_098554
  · exact g32p_supplierForest_actual_098707
  · exact g32p_supplierForest_actual_098873
  · exact g32p_supplierForest_actual_099141
  · exact g32p_supplierForest_actual_099162
  · exact g32p_supplierForest_actual_099513
  · exact g32p_supplierForest_actual_099773
  · exact g32p_supplierForest_actual_099942
  · exact g32p_supplierForest_actual_100087
  · exact g32p_supplierForest_actual_101044
  · exact g32p_supplierForest_actual_101114
  · exact g32p_supplierForest_actual_101161
  · exact g32p_supplierForest_actual_101564
  · exact g32p_supplierForest_actual_101823
  · exact g32p_supplierForest_actual_102530

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes : Fin 145 → Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_nodes_000 else g32p_supplierForest_nodes_001) else (if i.val < 3 then g32p_supplierForest_nodes_002 else g32p_supplierForest_nodes_003)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_nodes_004 else g32p_supplierForest_nodes_005) else (if i.val < 7 then g32p_supplierForest_nodes_006 else (if i.val < 8 then g32p_supplierForest_nodes_007 else g32p_supplierForest_nodes_008)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then g32p_supplierForest_nodes_009 else g32p_supplierForest_nodes_010) else (if i.val < 12 then g32p_supplierForest_nodes_011 else g32p_supplierForest_nodes_012)) else (if i.val < 15 then (if i.val < 14 then g32p_supplierForest_nodes_013 else g32p_supplierForest_nodes_014) else (if i.val < 16 then g32p_supplierForest_nodes_015 else (if i.val < 17 then g32p_supplierForest_nodes_016 else g32p_supplierForest_nodes_017))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then g32p_supplierForest_nodes_018 else g32p_supplierForest_nodes_019) else (if i.val < 21 then g32p_supplierForest_nodes_020 else g32p_supplierForest_nodes_021)) else (if i.val < 24 then (if i.val < 23 then g32p_supplierForest_nodes_022 else g32p_supplierForest_nodes_023) else (if i.val < 25 then g32p_supplierForest_nodes_024 else (if i.val < 26 then g32p_supplierForest_nodes_025 else g32p_supplierForest_nodes_026)))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then g32p_supplierForest_nodes_027 else g32p_supplierForest_nodes_028) else (if i.val < 30 then g32p_supplierForest_nodes_029 else g32p_supplierForest_nodes_030)) else (if i.val < 33 then (if i.val < 32 then g32p_supplierForest_nodes_031 else g32p_supplierForest_nodes_032) else (if i.val < 34 then g32p_supplierForest_nodes_033 else (if i.val < 35 then g32p_supplierForest_nodes_034 else g32p_supplierForest_nodes_035)))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_nodes_036 else g32p_supplierForest_nodes_037) else (if i.val < 39 then g32p_supplierForest_nodes_038 else g32p_supplierForest_nodes_039)) else (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_nodes_040 else g32p_supplierForest_nodes_041) else (if i.val < 43 then g32p_supplierForest_nodes_042 else (if i.val < 44 then g32p_supplierForest_nodes_043 else g32p_supplierForest_nodes_044)))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then g32p_supplierForest_nodes_045 else g32p_supplierForest_nodes_046) else (if i.val < 48 then g32p_supplierForest_nodes_047 else g32p_supplierForest_nodes_048)) else (if i.val < 51 then (if i.val < 50 then g32p_supplierForest_nodes_049 else g32p_supplierForest_nodes_050) else (if i.val < 52 then g32p_supplierForest_nodes_051 else (if i.val < 53 then g32p_supplierForest_nodes_052 else g32p_supplierForest_nodes_053))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then g32p_supplierForest_nodes_054 else g32p_supplierForest_nodes_055) else (if i.val < 57 then g32p_supplierForest_nodes_056 else g32p_supplierForest_nodes_057)) else (if i.val < 60 then (if i.val < 59 then g32p_supplierForest_nodes_058 else g32p_supplierForest_nodes_059) else (if i.val < 61 then g32p_supplierForest_nodes_060 else (if i.val < 62 then g32p_supplierForest_nodes_061 else g32p_supplierForest_nodes_062)))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then g32p_supplierForest_nodes_063 else g32p_supplierForest_nodes_064) else (if i.val < 66 then g32p_supplierForest_nodes_065 else g32p_supplierForest_nodes_066)) else (if i.val < 69 then (if i.val < 68 then g32p_supplierForest_nodes_067 else g32p_supplierForest_nodes_068) else (if i.val < 70 then g32p_supplierForest_nodes_069 else (if i.val < 71 then g32p_supplierForest_nodes_070 else g32p_supplierForest_nodes_071))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_nodes_072 else g32p_supplierForest_nodes_073) else (if i.val < 75 then g32p_supplierForest_nodes_074 else g32p_supplierForest_nodes_075)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_nodes_076 else g32p_supplierForest_nodes_077) else (if i.val < 79 then g32p_supplierForest_nodes_078 else (if i.val < 80 then g32p_supplierForest_nodes_079 else g32p_supplierForest_nodes_080)))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then g32p_supplierForest_nodes_081 else g32p_supplierForest_nodes_082) else (if i.val < 84 then g32p_supplierForest_nodes_083 else g32p_supplierForest_nodes_084)) else (if i.val < 87 then (if i.val < 86 then g32p_supplierForest_nodes_085 else g32p_supplierForest_nodes_086) else (if i.val < 88 then g32p_supplierForest_nodes_087 else (if i.val < 89 then g32p_supplierForest_nodes_088 else g32p_supplierForest_nodes_089))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then g32p_supplierForest_nodes_090 else g32p_supplierForest_nodes_091) else (if i.val < 93 then g32p_supplierForest_nodes_092 else g32p_supplierForest_nodes_093)) else (if i.val < 96 then (if i.val < 95 then g32p_supplierForest_nodes_094 else g32p_supplierForest_nodes_095) else (if i.val < 97 then g32p_supplierForest_nodes_096 else (if i.val < 98 then g32p_supplierForest_nodes_097 else g32p_supplierForest_nodes_098)))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then g32p_supplierForest_nodes_099 else g32p_supplierForest_nodes_100) else (if i.val < 102 then g32p_supplierForest_nodes_101 else g32p_supplierForest_nodes_102)) else (if i.val < 105 then (if i.val < 104 then g32p_supplierForest_nodes_103 else g32p_supplierForest_nodes_104) else (if i.val < 106 then g32p_supplierForest_nodes_105 else (if i.val < 107 then g32p_supplierForest_nodes_106 else g32p_supplierForest_nodes_107)))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_nodes_108 else g32p_supplierForest_nodes_109) else (if i.val < 111 then g32p_supplierForest_nodes_110 else g32p_supplierForest_nodes_111)) else (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_nodes_112 else g32p_supplierForest_nodes_113) else (if i.val < 115 then g32p_supplierForest_nodes_114 else (if i.val < 116 then g32p_supplierForest_nodes_115 else g32p_supplierForest_nodes_116)))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then g32p_supplierForest_nodes_117 else g32p_supplierForest_nodes_118) else (if i.val < 120 then g32p_supplierForest_nodes_119 else g32p_supplierForest_nodes_120)) else (if i.val < 123 then (if i.val < 122 then g32p_supplierForest_nodes_121 else g32p_supplierForest_nodes_122) else (if i.val < 124 then g32p_supplierForest_nodes_123 else (if i.val < 125 then g32p_supplierForest_nodes_124 else g32p_supplierForest_nodes_125))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then g32p_supplierForest_nodes_126 else g32p_supplierForest_nodes_127) else (if i.val < 129 then g32p_supplierForest_nodes_128 else g32p_supplierForest_nodes_129)) else (if i.val < 132 then (if i.val < 131 then g32p_supplierForest_nodes_130 else g32p_supplierForest_nodes_131) else (if i.val < 133 then g32p_supplierForest_nodes_132 else (if i.val < 134 then g32p_supplierForest_nodes_133 else g32p_supplierForest_nodes_134)))) else (if i.val < 140 then (if i.val < 137 then (if i.val < 136 then g32p_supplierForest_nodes_135 else g32p_supplierForest_nodes_136) else (if i.val < 138 then g32p_supplierForest_nodes_137 else (if i.val < 139 then g32p_supplierForest_nodes_138 else g32p_supplierForest_nodes_139))) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_nodes_140 else g32p_supplierForest_nodes_141) else (if i.val < 143 then g32p_supplierForest_nodes_142 else (if i.val < 144 then g32p_supplierForest_nodes_143 else g32p_supplierForest_nodes_144))))))))

def g32p_supplierForest_classes : Fin 145 → Fin 256 → Fin 102 :=
  fun i => (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_classes_000 else g32p_supplierForest_classes_001) else (if i.val < 3 then g32p_supplierForest_classes_002 else g32p_supplierForest_classes_003)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_classes_004 else g32p_supplierForest_classes_005) else (if i.val < 7 then g32p_supplierForest_classes_006 else (if i.val < 8 then g32p_supplierForest_classes_007 else g32p_supplierForest_classes_008)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then g32p_supplierForest_classes_009 else g32p_supplierForest_classes_010) else (if i.val < 12 then g32p_supplierForest_classes_011 else g32p_supplierForest_classes_012)) else (if i.val < 15 then (if i.val < 14 then g32p_supplierForest_classes_013 else g32p_supplierForest_classes_014) else (if i.val < 16 then g32p_supplierForest_classes_015 else (if i.val < 17 then g32p_supplierForest_classes_016 else g32p_supplierForest_classes_017))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then g32p_supplierForest_classes_018 else g32p_supplierForest_classes_019) else (if i.val < 21 then g32p_supplierForest_classes_020 else g32p_supplierForest_classes_021)) else (if i.val < 24 then (if i.val < 23 then g32p_supplierForest_classes_022 else g32p_supplierForest_classes_023) else (if i.val < 25 then g32p_supplierForest_classes_024 else (if i.val < 26 then g32p_supplierForest_classes_025 else g32p_supplierForest_classes_026)))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then g32p_supplierForest_classes_027 else g32p_supplierForest_classes_028) else (if i.val < 30 then g32p_supplierForest_classes_029 else g32p_supplierForest_classes_030)) else (if i.val < 33 then (if i.val < 32 then g32p_supplierForest_classes_031 else g32p_supplierForest_classes_032) else (if i.val < 34 then g32p_supplierForest_classes_033 else (if i.val < 35 then g32p_supplierForest_classes_034 else g32p_supplierForest_classes_035)))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_classes_036 else g32p_supplierForest_classes_037) else (if i.val < 39 then g32p_supplierForest_classes_038 else g32p_supplierForest_classes_039)) else (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_classes_040 else g32p_supplierForest_classes_041) else (if i.val < 43 then g32p_supplierForest_classes_042 else (if i.val < 44 then g32p_supplierForest_classes_043 else g32p_supplierForest_classes_044)))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then g32p_supplierForest_classes_045 else g32p_supplierForest_classes_046) else (if i.val < 48 then g32p_supplierForest_classes_047 else g32p_supplierForest_classes_048)) else (if i.val < 51 then (if i.val < 50 then g32p_supplierForest_classes_049 else g32p_supplierForest_classes_050) else (if i.val < 52 then g32p_supplierForest_classes_051 else (if i.val < 53 then g32p_supplierForest_classes_052 else g32p_supplierForest_classes_053))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then g32p_supplierForest_classes_054 else g32p_supplierForest_classes_055) else (if i.val < 57 then g32p_supplierForest_classes_056 else g32p_supplierForest_classes_057)) else (if i.val < 60 then (if i.val < 59 then g32p_supplierForest_classes_058 else g32p_supplierForest_classes_059) else (if i.val < 61 then g32p_supplierForest_classes_060 else (if i.val < 62 then g32p_supplierForest_classes_061 else g32p_supplierForest_classes_062)))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then g32p_supplierForest_classes_063 else g32p_supplierForest_classes_064) else (if i.val < 66 then g32p_supplierForest_classes_065 else g32p_supplierForest_classes_066)) else (if i.val < 69 then (if i.val < 68 then g32p_supplierForest_classes_067 else g32p_supplierForest_classes_068) else (if i.val < 70 then g32p_supplierForest_classes_069 else (if i.val < 71 then g32p_supplierForest_classes_070 else g32p_supplierForest_classes_071))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_classes_072 else g32p_supplierForest_classes_073) else (if i.val < 75 then g32p_supplierForest_classes_074 else g32p_supplierForest_classes_075)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_classes_076 else g32p_supplierForest_classes_077) else (if i.val < 79 then g32p_supplierForest_classes_078 else (if i.val < 80 then g32p_supplierForest_classes_079 else g32p_supplierForest_classes_080)))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then g32p_supplierForest_classes_081 else g32p_supplierForest_classes_082) else (if i.val < 84 then g32p_supplierForest_classes_083 else g32p_supplierForest_classes_084)) else (if i.val < 87 then (if i.val < 86 then g32p_supplierForest_classes_085 else g32p_supplierForest_classes_086) else (if i.val < 88 then g32p_supplierForest_classes_087 else (if i.val < 89 then g32p_supplierForest_classes_088 else g32p_supplierForest_classes_089))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then g32p_supplierForest_classes_090 else g32p_supplierForest_classes_091) else (if i.val < 93 then g32p_supplierForest_classes_092 else g32p_supplierForest_classes_093)) else (if i.val < 96 then (if i.val < 95 then g32p_supplierForest_classes_094 else g32p_supplierForest_classes_095) else (if i.val < 97 then g32p_supplierForest_classes_096 else (if i.val < 98 then g32p_supplierForest_classes_097 else g32p_supplierForest_classes_098)))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then g32p_supplierForest_classes_099 else g32p_supplierForest_classes_100) else (if i.val < 102 then g32p_supplierForest_classes_101 else g32p_supplierForest_classes_102)) else (if i.val < 105 then (if i.val < 104 then g32p_supplierForest_classes_103 else g32p_supplierForest_classes_104) else (if i.val < 106 then g32p_supplierForest_classes_105 else (if i.val < 107 then g32p_supplierForest_classes_106 else g32p_supplierForest_classes_107)))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_classes_108 else g32p_supplierForest_classes_109) else (if i.val < 111 then g32p_supplierForest_classes_110 else g32p_supplierForest_classes_111)) else (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_classes_112 else g32p_supplierForest_classes_113) else (if i.val < 115 then g32p_supplierForest_classes_114 else (if i.val < 116 then g32p_supplierForest_classes_115 else g32p_supplierForest_classes_116)))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then g32p_supplierForest_classes_117 else g32p_supplierForest_classes_118) else (if i.val < 120 then g32p_supplierForest_classes_119 else g32p_supplierForest_classes_120)) else (if i.val < 123 then (if i.val < 122 then g32p_supplierForest_classes_121 else g32p_supplierForest_classes_122) else (if i.val < 124 then g32p_supplierForest_classes_123 else (if i.val < 125 then g32p_supplierForest_classes_124 else g32p_supplierForest_classes_125))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then g32p_supplierForest_classes_126 else g32p_supplierForest_classes_127) else (if i.val < 129 then g32p_supplierForest_classes_128 else g32p_supplierForest_classes_129)) else (if i.val < 132 then (if i.val < 131 then g32p_supplierForest_classes_130 else g32p_supplierForest_classes_131) else (if i.val < 133 then g32p_supplierForest_classes_132 else (if i.val < 134 then g32p_supplierForest_classes_133 else g32p_supplierForest_classes_134)))) else (if i.val < 140 then (if i.val < 137 then (if i.val < 136 then g32p_supplierForest_classes_135 else g32p_supplierForest_classes_136) else (if i.val < 138 then g32p_supplierForest_classes_137 else (if i.val < 139 then g32p_supplierForest_classes_138 else g32p_supplierForest_classes_139))) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_classes_140 else g32p_supplierForest_classes_141) else (if i.val < 143 then g32p_supplierForest_classes_142 else (if i.val < 144 then g32p_supplierForest_classes_143 else g32p_supplierForest_classes_144))))))))

theorem g32p_supplierForest_actual (q : Fin 145) (r : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes q r)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes q r)) := by
  fin_cases q
  · exact g32p_supplierForest_actual_000 r
  · exact g32p_supplierForest_actual_001 r
  · exact g32p_supplierForest_actual_002 r
  · exact g32p_supplierForest_actual_003 r
  · exact g32p_supplierForest_actual_004 r
  · exact g32p_supplierForest_actual_005 r
  · exact g32p_supplierForest_actual_006 r
  · exact g32p_supplierForest_actual_007 r
  · exact g32p_supplierForest_actual_008 r
  · exact g32p_supplierForest_actual_009 r
  · exact g32p_supplierForest_actual_010 r
  · exact g32p_supplierForest_actual_011 r
  · exact g32p_supplierForest_actual_012 r
  · exact g32p_supplierForest_actual_013 r
  · exact g32p_supplierForest_actual_014 r
  · exact g32p_supplierForest_actual_015 r
  · exact g32p_supplierForest_actual_016 r
  · exact g32p_supplierForest_actual_017 r
  · exact g32p_supplierForest_actual_018 r
  · exact g32p_supplierForest_actual_019 r
  · exact g32p_supplierForest_actual_020 r
  · exact g32p_supplierForest_actual_021 r
  · exact g32p_supplierForest_actual_022 r
  · exact g32p_supplierForest_actual_023 r
  · exact g32p_supplierForest_actual_024 r
  · exact g32p_supplierForest_actual_025 r
  · exact g32p_supplierForest_actual_026 r
  · exact g32p_supplierForest_actual_027 r
  · exact g32p_supplierForest_actual_028 r
  · exact g32p_supplierForest_actual_029 r
  · exact g32p_supplierForest_actual_030 r
  · exact g32p_supplierForest_actual_031 r
  · exact g32p_supplierForest_actual_032 r
  · exact g32p_supplierForest_actual_033 r
  · exact g32p_supplierForest_actual_034 r
  · exact g32p_supplierForest_actual_035 r
  · exact g32p_supplierForest_actual_036 r
  · exact g32p_supplierForest_actual_037 r
  · exact g32p_supplierForest_actual_038 r
  · exact g32p_supplierForest_actual_039 r
  · exact g32p_supplierForest_actual_040 r
  · exact g32p_supplierForest_actual_041 r
  · exact g32p_supplierForest_actual_042 r
  · exact g32p_supplierForest_actual_043 r
  · exact g32p_supplierForest_actual_044 r
  · exact g32p_supplierForest_actual_045 r
  · exact g32p_supplierForest_actual_046 r
  · exact g32p_supplierForest_actual_047 r
  · exact g32p_supplierForest_actual_048 r
  · exact g32p_supplierForest_actual_049 r
  · exact g32p_supplierForest_actual_050 r
  · exact g32p_supplierForest_actual_051 r
  · exact g32p_supplierForest_actual_052 r
  · exact g32p_supplierForest_actual_053 r
  · exact g32p_supplierForest_actual_054 r
  · exact g32p_supplierForest_actual_055 r
  · exact g32p_supplierForest_actual_056 r
  · exact g32p_supplierForest_actual_057 r
  · exact g32p_supplierForest_actual_058 r
  · exact g32p_supplierForest_actual_059 r
  · exact g32p_supplierForest_actual_060 r
  · exact g32p_supplierForest_actual_061 r
  · exact g32p_supplierForest_actual_062 r
  · exact g32p_supplierForest_actual_063 r
  · exact g32p_supplierForest_actual_064 r
  · exact g32p_supplierForest_actual_065 r
  · exact g32p_supplierForest_actual_066 r
  · exact g32p_supplierForest_actual_067 r
  · exact g32p_supplierForest_actual_068 r
  · exact g32p_supplierForest_actual_069 r
  · exact g32p_supplierForest_actual_070 r
  · exact g32p_supplierForest_actual_071 r
  · exact g32p_supplierForest_actual_072 r
  · exact g32p_supplierForest_actual_073 r
  · exact g32p_supplierForest_actual_074 r
  · exact g32p_supplierForest_actual_075 r
  · exact g32p_supplierForest_actual_076 r
  · exact g32p_supplierForest_actual_077 r
  · exact g32p_supplierForest_actual_078 r
  · exact g32p_supplierForest_actual_079 r
  · exact g32p_supplierForest_actual_080 r
  · exact g32p_supplierForest_actual_081 r
  · exact g32p_supplierForest_actual_082 r
  · exact g32p_supplierForest_actual_083 r
  · exact g32p_supplierForest_actual_084 r
  · exact g32p_supplierForest_actual_085 r
  · exact g32p_supplierForest_actual_086 r
  · exact g32p_supplierForest_actual_087 r
  · exact g32p_supplierForest_actual_088 r
  · exact g32p_supplierForest_actual_089 r
  · exact g32p_supplierForest_actual_090 r
  · exact g32p_supplierForest_actual_091 r
  · exact g32p_supplierForest_actual_092 r
  · exact g32p_supplierForest_actual_093 r
  · exact g32p_supplierForest_actual_094 r
  · exact g32p_supplierForest_actual_095 r
  · exact g32p_supplierForest_actual_096 r
  · exact g32p_supplierForest_actual_097 r
  · exact g32p_supplierForest_actual_098 r
  · exact g32p_supplierForest_actual_099 r
  · exact g32p_supplierForest_actual_100 r
  · exact g32p_supplierForest_actual_101 r
  · exact g32p_supplierForest_actual_102 r
  · exact g32p_supplierForest_actual_103 r
  · exact g32p_supplierForest_actual_104 r
  · exact g32p_supplierForest_actual_105 r
  · exact g32p_supplierForest_actual_106 r
  · exact g32p_supplierForest_actual_107 r
  · exact g32p_supplierForest_actual_108 r
  · exact g32p_supplierForest_actual_109 r
  · exact g32p_supplierForest_actual_110 r
  · exact g32p_supplierForest_actual_111 r
  · exact g32p_supplierForest_actual_112 r
  · exact g32p_supplierForest_actual_113 r
  · exact g32p_supplierForest_actual_114 r
  · exact g32p_supplierForest_actual_115 r
  · exact g32p_supplierForest_actual_116 r
  · exact g32p_supplierForest_actual_117 r
  · exact g32p_supplierForest_actual_118 r
  · exact g32p_supplierForest_actual_119 r
  · exact g32p_supplierForest_actual_120 r
  · exact g32p_supplierForest_actual_121 r
  · exact g32p_supplierForest_actual_122 r
  · exact g32p_supplierForest_actual_123 r
  · exact g32p_supplierForest_actual_124 r
  · exact g32p_supplierForest_actual_125 r
  · exact g32p_supplierForest_actual_126 r
  · exact g32p_supplierForest_actual_127 r
  · exact g32p_supplierForest_actual_128 r
  · exact g32p_supplierForest_actual_129 r
  · exact g32p_supplierForest_actual_130 r
  · exact g32p_supplierForest_actual_131 r
  · exact g32p_supplierForest_actual_132 r
  · exact g32p_supplierForest_actual_133 r
  · exact g32p_supplierForest_actual_134 r
  · exact g32p_supplierForest_actual_135 r
  · exact g32p_supplierForest_actual_136 r
  · exact g32p_supplierForest_actual_137 r
  · exact g32p_supplierForest_actual_138 r
  · exact g32p_supplierForest_actual_139 r
  · exact g32p_supplierForest_actual_140 r
  · exact g32p_supplierForest_actual_141 r
  · exact g32p_supplierForest_actual_142 r
  · exact g32p_supplierForest_actual_143 r
  · exact g32p_supplierForest_actual_144 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup00_source : Fin 3456 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 1728 then (if i.val < 864 then (if i.val < 432 then (if i.val < 216 then (if i.val < 108 then (if i.val < 54 then (if i.val < 27 then (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (0, 0) else (if i.val < 2 then (42, 225) else (0, 101))) else (if i.val < 4 then (70, 68) else (if i.val < 5 then (128, 28) else (21, 88)))) else (if i.val < 9 then (if i.val < 7 then (0, 99) else (if i.val < 8 then (91, 14) else (70, 20))) else (if i.val < 11 then (if i.val < 10 then (62, 109) else (22, 234)) else (if i.val < 12 then (0, 96) else (31, 197))))) else (if i.val < 20 then (if i.val < 16 then (if i.val < 14 then (71, 9) else (if i.val < 15 then (111, 160) else (136, 197))) else (if i.val < 18 then (if i.val < 17 then (61, 91) else (22, 28)) else (if i.val < 19 then (141, 184) else (62, 19)))) else (if i.val < 23 then (if i.val < 21 then (70, 159) else (if i.val < 22 then (85, 84) else (23, 205))) else (if i.val < 25 then (if i.val < 24 then (85, 71) else (67, 74)) else (if i.val < 26 then (0, 37) else (99, 191)))))) else (if i.val < 40 then (if i.val < 33 then (if i.val < 30 then (if i.val < 28 then (63, 112) else (if i.val < 29 then (95, 221) else (96, 251))) else (if i.val < 31 then (128, 177) else (if i.val < 32 then (110, 131) else (19, 230)))) else (if i.val < 36 then (if i.val < 34 then (113, 158) else (if i.val < 35 then (127, 233) else (33, 139))) else (if i.val < 38 then (if i.val < 37 then (100, 171) else (85, 197)) else (if i.val < 39 then (74, 132) else (102, 161))))) else (if i.val < 47 then (if i.val < 43 then (if i.val < 41 then (90, 118) else (if i.val < 42 then (89, 83) else (86, 110))) else (if i.val < 45 then (if i.val < 44 then (5, 148) else (29, 21)) else (if i.val < 46 then (97, 89) else (6, 109)))) else (if i.val < 50 then (if i.val < 48 then (144, 177) else (if i.val < 49 then (98, 12) else (86, 35))) else (if i.val < 52 then (if i.val < 51 then (1, 111) else (20, 222)) else (if i.val < 53 then (24, 247) else (28, 86))))))) else (if i.val < 81 then (if i.val < 67 then (if i.val < 60 then (if i.val < 57 then (if i.val < 55 then (41, 194) else (if i.val < 56 then (99, 52) else (139, 248))) else (if i.val < 58 then (6, 17) else (if i.val < 59 then (106, 242) else (96, 134)))) else (if i.val < 63 then (if i.val < 61 then (6, 114) else (if i.val < 62 then (141, 88) else (100, 164))) else (if i.val < 65 then (if i.val < 64 then (141, 65) else (57, 98)) else (if i.val < 66 then (11, 132) else (144, 91))))) else (if i.val < 74 then (if i.val < 70 then (if i.val < 68 then (83, 197) else (if i.val < 69 then (61, 88) else (138, 177))) else (if i.val < 72 then (if i.val < 71 then (126, 35) else (80, 136)) else (if i.val < 73 then (128, 38) else (91, 186)))) else (if i.val < 77 then (if i.val < 75 then (121, 2) else (if i.val < 76 then (28, 10) else (0, 97))) else (if i.val < 79 then (if i.val < 78 then (58, 24) else (4, 192)) else (if i.val < 80 then (31, 94) else (97, 195)))))) else (if i.val < 94 then (if i.val < 87 then (if i.val < 84 then (if i.val < 82 then (80, 70) else (if i.val < 83 then (5, 142) else (113, 49))) else (if i.val < 85 then (50, 159) else (if i.val < 86 then (24, 249) else (0, 65)))) else (if i.val < 90 then (if i.val < 88 then (8, 161) else (if i.val < 89 then (139, 137) else (94, 22))) else (if i.val < 92 then (if i.val < 91 then (4, 191) else (56, 172)) else (if i.val < 93 then (74, 54) else (27, 159))))) else (if i.val < 101 then (if i.val < 97 then (if i.val < 95 then (119, 13) else (if i.val < 96 then (11, 216) else (95, 24))) else (if i.val < 99 then (if i.val < 98 then (74, 236) else (136, 220)) else (if i.val < 100 then (35, 169) else (95, 67)))) else (if i.val < 104 then (if i.val < 102 then (114, 74) else (if i.val < 103 then (51, 5) else (114, 114))) else (if i.val < 106 then (if i.val < 105 then (128, 35) else (5, 128)) else (if i.val < 107 then (142, 123) else (53, 253)))))))) else (if i.val < 162 then (if i.val < 135 then (if i.val < 121 then (if i.val < 114 then (if i.val < 111 then (if i.val < 109 then (113, 145) else (if i.val < 110 then (95, 113) else (134, 150))) else (if i.val < 112 then (38, 115) else (if i.val < 113 then (46, 203) else (36, 212)))) else (if i.val < 117 then (if i.val < 115 then (36, 176) else (if i.val < 116 then (28, 136) else (77, 202))) else (if i.val < 119 then (if i.val < 118 then (83, 118) else (56, 154)) else (if i.val < 120 then (133, 115) else (81, 248))))) else (if i.val < 128 then (if i.val < 124 then (if i.val < 122 then (0, 18) else (if i.val < 123 then (45, 126) else (5, 217))) else (if i.val < 126 then (if i.val < 125 then (46, 67) else (61, 206)) else (if i.val < 127 then (136, 61) else (98, 116)))) else (if i.val < 131 then (if i.val < 129 then (31, 184) else (if i.val < 130 then (131, 167) else (90, 3))) else (if i.val < 133 then (if i.val < 132 then (56, 153) else (112, 38)) else (if i.val < 134 then (136, 14) else (112, 30)))))) else (if i.val < 148 then (if i.val < 141 then (if i.val < 138 then (if i.val < 136 then (50, 191) else (if i.val < 137 then (112, 165) else (143, 123))) else (if i.val < 139 then (39, 229) else (if i.val < 140 then (142, 71) else (117, 244)))) else (if i.val < 144 then (if i.val < 142 then (144, 218) else (if i.val < 143 then (143, 190) else (32, 96))) else (if i.val < 146 then (if i.val < 145 then (53, 59) else (45, 19)) else (if i.val < 147 then (75, 149) else (86, 98))))) else (if i.val < 155 then (if i.val < 151 then (if i.val < 149 then (140, 21) else (if i.val < 150 then (69, 24) else (65, 170))) else (if i.val < 153 then (if i.val < 152 then (53, 160) else (99, 154)) else (if i.val < 154 then (90, 222) else (121, 212)))) else (if i.val < 158 then (if i.val < 156 then (31, 187) else (if i.val < 157 then (113, 147) else (134, 42))) else (if i.val < 160 then (if i.val < 159 then (113, 110) else (98, 235)) else (if i.val < 161 then (61, 140) else (82, 176))))))) else (if i.val < 189 then (if i.val < 175 then (if i.val < 168 then (if i.val < 165 then (if i.val < 163 then (79, 190) else (if i.val < 164 then (66, 115) else (126, 38))) else (if i.val < 166 then (68, 173) else (if i.val < 167 then (82, 223) else (22, 84)))) else (if i.val < 171 then (if i.val < 169 then (57, 215) else (if i.val < 170 then (73, 181) else (77, 36))) else (if i.val < 173 then (if i.val < 172 then (29, 136) else (13, 253)) else (if i.val < 174 then (12, 41) else (114, 137))))) else (if i.val < 182 then (if i.val < 178 then (if i.val < 176 then (116, 128) else (if i.val < 177 then (40, 179) else (60, 51))) else (if i.val < 180 then (if i.val < 179 then (135, 121) else (99, 227)) else (if i.val < 181 then (127, 206) else (54, 54)))) else (if i.val < 185 then (if i.val < 183 then (3, 219) else (if i.val < 184 then (136, 189) else (62, 76))) else (if i.val < 187 then (if i.val < 186 then (29, 227) else (11, 250)) else (if i.val < 188 then (61, 4) else (51, 98)))))) else (if i.val < 202 then (if i.val < 195 then (if i.val < 192 then (if i.val < 190 then (98, 99) else (if i.val < 191 then (129, 121) else (100, 251))) else (if i.val < 193 then (3, 66) else (if i.val < 194 then (127, 163) else (82, 19)))) else (if i.val < 198 then (if i.val < 196 then (90, 253) else (if i.val < 197 then (55, 75) else (142, 211))) else (if i.val < 200 then (if i.val < 199 then (13, 79) else (82, 136)) else (if i.val < 201 then (130, 144) else (107, 174))))) else (if i.val < 209 then (if i.val < 205 then (if i.val < 203 then (70, 246) else (if i.val < 204 then (1, 149) else (30, 180))) else (if i.val < 207 then (if i.val < 206 then (84, 37) else (82, 200)) else (if i.val < 208 then (25, 236) else (99, 149)))) else (if i.val < 212 then (if i.val < 210 then (139, 148) else (if i.val < 211 then (119, 164) else (126, 109))) else (if i.val < 214 then (if i.val < 213 then (14, 176) else (115, 87)) else (if i.val < 215 then (96, 59) else (28, 165))))))))) else (if i.val < 324 then (if i.val < 270 then (if i.val < 243 then (if i.val < 229 then (if i.val < 222 then (if i.val < 219 then (if i.val < 217 then (93, 236) else (if i.val < 218 then (94, 203) else (109, 203))) else (if i.val < 220 then (44, 237) else (if i.val < 221 then (133, 172) else (62, 171)))) else (if i.val < 225 then (if i.val < 223 then (49, 91) else (if i.val < 224 then (67, 135) else (83, 145))) else (if i.val < 227 then (if i.val < 226 then (49, 179) else (119, 83)) else (if i.val < 228 then (39, 202) else (109, 70))))) else (if i.val < 236 then (if i.val < 232 then (if i.val < 230 then (85, 150) else (if i.val < 231 then (77, 189) else (0, 43))) else (if i.val < 234 then (if i.val < 233 then (3, 67) else (107, 209)) else (if i.val < 235 then (71, 17) else (28, 197)))) else (if i.val < 239 then (if i.val < 237 then (132, 169) else (if i.val < 238 then (139, 139) else (132, 63))) else (if i.val < 241 then (if i.val < 240 then (103, 150) else (36, 70)) else (if i.val < 242 then (72, 24) else (11, 8)))))) else (if i.val < 256 then (if i.val < 249 then (if i.val < 246 then (if i.val < 244 then (126, 75) else (if i.val < 245 then (64, 184) else (122, 0))) else (if i.val < 247 then (8, 145) else (if i.val < 248 then (53, 188) else (102, 201)))) else (if i.val < 252 then (if i.val < 250 then (132, 43) else (if i.val < 251 then (7, 27) else (66, 50))) else (if i.val < 254 then (if i.val < 253 then (137, 103) else (133, 223)) else (if i.val < 255 then (31, 80) else (118, 81))))) else (if i.val < 263 then (if i.val < 259 then (if i.val < 257 then (101, 45) else (if i.val < 258 then (8, 255) else (132, 194))) else (if i.val < 261 then (if i.val < 260 then (46, 155) else (102, 204)) else (if i.val < 262 then (94, 184) else (28, 170)))) else (if i.val < 266 then (if i.val < 264 then (95, 246) else (if i.val < 265 then (139, 31) else (107, 232))) else (if i.val < 268 then (if i.val < 267 then (95, 199) else (128, 96)) else (if i.val < 269 then (53, 181) else (58, 101))))))) else (if i.val < 297 then (if i.val < 283 then (if i.val < 276 then (if i.val < 273 then (if i.val < 271 then (23, 160) else (if i.val < 272 then (99, 77) else (133, 175))) else (if i.val < 274 then (65, 234) else (if i.val < 275 then (12, 46) else (117, 162)))) else (if i.val < 279 then (if i.val < 277 then (59, 66) else (if i.val < 278 then (117, 155) else (91, 98))) else (if i.val < 281 then (if i.val < 280 then (85, 187) else (94, 138)) else (if i.val < 282 then (102, 108) else (139, 60))))) else (if i.val < 290 then (if i.val < 286 then (if i.val < 284 then (94, 225) else (if i.val < 285 then (52, 88) else (130, 90))) else (if i.val < 288 then (if i.val < 287 then (102, 12) else (74, 81)) else (if i.val < 289 then (75, 188) else (102, 56)))) else (if i.val < 293 then (if i.val < 291 then (111, 81) else (if i.val < 292 then (118, 67) else (108, 45))) else (if i.val < 295 then (if i.val < 294 then (48, 184) else (117, 109)) else (if i.val < 296 then (118, 184) else (110, 142)))))) else (if i.val < 310 then (if i.val < 303 then (if i.val < 300 then (if i.val < 298 then (76, 144) else (if i.val < 299 then (94, 145) else (130, 213))) else (if i.val < 301 then (13, 123) else (if i.val < 302 then (69, 141) else (125, 96)))) else (if i.val < 306 then (if i.val < 304 then (126, 229) else (if i.val < 305 then (106, 197) else (120, 5))) else (if i.val < 308 then (if i.val < 307 then (101, 95) else (118, 225)) else (if i.val < 309 then (51, 224) else (130, 25))))) else (if i.val < 317 then (if i.val < 313 then (if i.val < 311 then (138, 188) else (if i.val < 312 then (53, 234) else (108, 139))) else (if i.val < 315 then (if i.val < 314 then (132, 247) else (78, 72)) else (if i.val < 316 then (113, 207) else (64, 5)))) else (if i.val < 320 then (if i.val < 318 then (110, 50) else (if i.val < 319 then (103, 23) else (126, 212))) else (if i.val < 322 then (if i.val < 321 then (56, 34) else (120, 18)) else (if i.val < 323 then (59, 2) else (77, 69)))))))) else (if i.val < 378 then (if i.val < 351 then (if i.val < 337 then (if i.val < 330 then (if i.val < 327 then (if i.val < 325 then (78, 166) else (if i.val < 326 then (4, 97) else (143, 13))) else (if i.val < 328 then (87, 190) else (if i.val < 329 then (9, 178) else (140, 243)))) else (if i.val < 333 then (if i.val < 331 then (126, 244) else (if i.val < 332 then (134, 184) else (11, 129))) else (if i.val < 335 then (if i.val < 334 then (28, 103) else (53, 249)) else (if i.val < 336 then (77, 41) else (42, 191))))) else (if i.val < 344 then (if i.val < 340 then (if i.val < 338 then (66, 75) else (if i.val < 339 then (55, 128) else (35, 154))) else (if i.val < 342 then (if i.val < 341 then (42, 144) else (36, 26)) else (if i.val < 343 then (53, 128) else (124, 184)))) else (if i.val < 347 then (if i.val < 345 then (65, 35) else (if i.val < 346 then (124, 166) else (116, 140))) else (if i.val < 349 then (if i.val < 348 then (113, 83) else (113, 106)) else (if i.val < 350 then (96, 202) else (128, 23)))))) else (if i.val < 364 then (if i.val < 357 then (if i.val < 354 then (if i.val < 352 then (119, 180) else (if i.val < 353 then (143, 89) else (96, 220))) else (if i.val < 355 then (39, 172) else (if i.val < 356 then (123, 86) else (37, 60)))) else (if i.val < 360 then (if i.val < 358 then (10, 43) else (if i.val < 359 then (58, 123) else (94, 146))) else (if i.val < 362 then (if i.val < 361 then (25, 244) else (71, 114)) else (if i.val < 363 then (60, 180) else (135, 174))))) else (if i.val < 371 then (if i.val < 367 then (if i.val < 365 then (138, 74) else (if i.val < 366 then (94, 183) else (132, 146))) else (if i.val < 369 then (if i.val < 368 then (66, 240) else (102, 69)) else (if i.val < 370 then (48, 85) else (6, 11)))) else (if i.val < 374 then (if i.val < 372 then (124, 144) else (if i.val < 373 then (20, 191) else (66, 219))) else (if i.val < 376 then (if i.val < 375 then (101, 145) else (25, 172)) else (if i.val < 377 then (20, 167) else (78, 199))))))) else (if i.val < 405 then (if i.val < 391 then (if i.val < 384 then (if i.val < 381 then (if i.val < 379 then (65, 27) else (if i.val < 380 then (114, 35) else (134, 2))) else (if i.val < 382 then (71, 248) else (if i.val < 383 then (103, 94) else (13, 208)))) else (if i.val < 387 then (if i.val < 385 then (47, 123) else (if i.val < 386 then (135, 212) else (50, 189))) else (if i.val < 389 then (if i.val < 388 then (136, 124) else (102, 107)) else (if i.val < 390 then (134, 84) else (119, 172))))) else (if i.val < 398 then (if i.val < 394 then (if i.val < 392 then (43, 53) else (if i.val < 393 then (101, 183) else (126, 188))) else (if i.val < 396 then (if i.val < 395 then (141, 235) else (88, 116)) else (if i.val < 397 then (108, 3) else (101, 243)))) else (if i.val < 401 then (if i.val < 399 then (127, 176) else (if i.val < 400 then (138, 114) else (90, 52))) else (if i.val < 403 then (if i.val < 402 then (108, 246) else (89, 45)) else (if i.val < 404 then (5, 80) else (17, 84)))))) else (if i.val < 418 then (if i.val < 411 then (if i.val < 408 then (if i.val < 406 then (56, 67) else (if i.val < 407 then (66, 188) else (58, 252))) else (if i.val < 409 then (126, 253) else (if i.val < 410 then (117, 118) else (40, 178)))) else (if i.val < 414 then (if i.val < 412 then (60, 40) else (if i.val < 413 then (79, 17) else (40, 140))) else (if i.val < 416 then (if i.val < 415 then (48, 65) else (102, 113)) else (if i.val < 417 then (93, 119) else (125, 29))))) else (if i.val < 425 then (if i.val < 421 then (if i.val < 419 then (132, 47) else (if i.val < 420 then (135, 244) else (6, 192))) else (if i.val < 423 then (if i.val < 422 then (102, 55) else (144, 195)) else (if i.val < 424 then (86, 20) else (118, 72)))) else (if i.val < 428 then (if i.val < 426 then (121, 178) else (if i.val < 427 then (17, 89) else (82, 162))) else (if i.val < 430 then (if i.val < 429 then (47, 103) else (79, 33)) else (if i.val < 431 then (96, 172) else (4, 13)))))))))) else (if i.val < 648 then (if i.val < 540 then (if i.val < 486 then (if i.val < 459 then (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then (if i.val < 433 then (74, 190) else (if i.val < 434 then (115, 111) else (66, 51))) else (if i.val < 436 then (49, 191) else (if i.val < 437 then (117, 192) else (2, 96)))) else (if i.val < 441 then (if i.val < 439 then (137, 128) else (if i.val < 440 then (1, 152) else (102, 172))) else (if i.val < 443 then (if i.val < 442 then (95, 19) else (143, 61)) else (if i.val < 444 then (125, 121) else (22, 253))))) else (if i.val < 452 then (if i.val < 448 then (if i.val < 446 then (7, 136) else (if i.val < 447 then (127, 42) else (39, 25))) else (if i.val < 450 then (if i.val < 449 then (83, 30) else (82, 254)) else (if i.val < 451 then (100, 133) else (80, 120)))) else (if i.val < 455 then (if i.val < 453 then (120, 253) else (if i.val < 454 then (7, 85) else (131, 93))) else (if i.val < 457 then (if i.val < 456 then (140, 33) else (7, 167)) else (if i.val < 458 then (140, 95) else (127, 247)))))) else (if i.val < 472 then (if i.val < 465 then (if i.val < 462 then (if i.val < 460 then (91, 81) else (if i.val < 461 then (81, 195) else (76, 247))) else (if i.val < 463 then (80, 192) else (if i.val < 464 then (100, 104) else (128, 82)))) else (if i.val < 468 then (if i.val < 466 then (61, 187) else (if i.val < 467 then (66, 212) else (29, 41))) else (if i.val < 470 then (if i.val < 469 then (141, 117) else (123, 88)) else (if i.val < 471 then (7, 8) else (123, 10))))) else (if i.val < 479 then (if i.val < 475 then (if i.val < 473 then (137, 246) else (if i.val < 474 then (102, 121) else (61, 237))) else (if i.val < 477 then (if i.val < 476 then (66, 110) else (5, 133)) else (if i.val < 478 then (80, 163) else (73, 165)))) else (if i.val < 482 then (if i.val < 480 then (105, 228) else (if i.val < 481 then (135, 11) else (81, 217))) else (if i.val < 484 then (if i.val < 483 then (102, 7) else (50, 235)) else (if i.val < 485 then (1, 227) else (124, 210))))))) else (if i.val < 513 then (if i.val < 499 then (if i.val < 492 then (if i.val < 489 then (if i.val < 487 then (92, 181) else (if i.val < 488 then (0, 28) else (87, 223))) else (if i.val < 490 then (48, 235) else (if i.val < 491 then (137, 243) else (73, 102)))) else (if i.val < 495 then (if i.val < 493 then (98, 115) else (if i.val < 494 then (2, 103) else (94, 90))) else (if i.val < 497 then (if i.val < 496 then (98, 51) else (126, 51)) else (if i.val < 498 then (102, 6) else (126, 73))))) else (if i.val < 506 then (if i.val < 502 then (if i.val < 500 then (103, 131) else (if i.val < 501 then (2, 106) else (132, 60))) else (if i.val < 504 then (if i.val < 503 then (58, 221) else (6, 234)) else (if i.val < 505 then (90, 155) else (22, 209)))) else (if i.val < 509 then (if i.val < 507 then (59, 221) else (if i.val < 508 then (64, 187) else (135, 82))) else (if i.val < 511 then (if i.val < 510 then (136, 237) else (76, 230)) else (if i.val < 512 then (56, 204) else (79, 34)))))) else (if i.val < 526 then (if i.val < 519 then (if i.val < 516 then (if i.val < 514 then (112, 19) else (if i.val < 515 then (133, 125) else (28, 115))) else (if i.val < 517 then (79, 254) else (if i.val < 518 then (142, 14) else (125, 132)))) else (if i.val < 522 then (if i.val < 520 then (73, 13) else (if i.val < 521 then (9, 97) else (41, 212))) else (if i.val < 524 then (if i.val < 523 then (101, 5) else (90, 255)) else (if i.val < 525 then (104, 4) else (23, 59))))) else (if i.val < 533 then (if i.val < 529 then (if i.val < 527 then (84, 119) else (if i.val < 528 then (94, 79) else (24, 243))) else (if i.val < 531 then (if i.val < 530 then (63, 65) else (138, 15)) else (if i.val < 532 then (110, 199) else (118, 119)))) else (if i.val < 536 then (if i.val < 534 then (104, 106) else (if i.val < 535 then (22, 199) else (119, 39))) else (if i.val < 538 then (if i.val < 537 then (95, 66) else (34, 198)) else (if i.val < 539 then (85, 191) else (21, 60)))))))) else (if i.val < 594 then (if i.val < 567 then (if i.val < 553 then (if i.val < 546 then (if i.val < 543 then (if i.val < 541 then (44, 244) else (if i.val < 542 then (7, 63) else (138, 91))) else (if i.val < 544 then (100, 172) else (if i.val < 545 then (79, 54) else (120, 186)))) else (if i.val < 549 then (if i.val < 547 then (99, 213) else (if i.val < 548 then (6, 239) else (25, 248))) else (if i.val < 551 then (if i.val < 550 then (41, 25) else (99, 75)) else (if i.val < 552 then (47, 209) else (123, 134))))) else (if i.val < 560 then (if i.val < 556 then (if i.val < 554 then (124, 169) else (if i.val < 555 then (20, 4) else (85, 109))) else (if i.val < 558 then (if i.val < 557 then (121, 59) else (34, 186)) else (if i.val < 559 then (125, 111) else (111, 150)))) else (if i.val < 563 then (if i.val < 561 then (135, 144) else (if i.val < 562 then (88, 90) else (104, 119))) else (if i.val < 565 then (if i.val < 564 then (137, 213) else (141, 224)) else (if i.val < 566 then (39, 42) else (97, 66)))))) else (if i.val < 580 then (if i.val < 573 then (if i.val < 570 then (if i.val < 568 then (23, 144) else (if i.val < 569 then (61, 199) else (92, 188))) else (if i.val < 571 then (4, 166) else (if i.val < 572 then (8, 228) else (107, 123)))) else (if i.val < 576 then (if i.val < 574 then (30, 40) else (if i.val < 575 then (25, 242) else (31, 149))) else (if i.val < 578 then (if i.val < 577 then (67, 250) else (110, 213)) else (if i.val < 579 then (138, 116) else (119, 243))))) else (if i.val < 587 then (if i.val < 583 then (if i.val < 581 then (105, 151) else (if i.val < 582 then (115, 181) else (86, 213))) else (if i.val < 585 then (if i.val < 584 then (113, 119) else (103, 4)) else (if i.val < 586 then (120, 248) else (114, 183)))) else (if i.val < 590 then (if i.val < 588 then (119, 210) else (if i.val < 589 then (69, 195) else (68, 182))) else (if i.val < 592 then (if i.val < 591 then (39, 143) else (66, 36)) else (if i.val < 593 then (98, 191) else (13, 13))))))) else (if i.val < 621 then (if i.val < 607 then (if i.val < 600 then (if i.val < 597 then (if i.val < 595 then (95, 98) else (if i.val < 596 then (97, 231) else (132, 124))) else (if i.val < 598 then (138, 12) else (if i.val < 599 then (75, 104) else (52, 66)))) else (if i.val < 603 then (if i.val < 601 then (107, 206) else (if i.val < 602 then (103, 149) else (103, 12))) else (if i.val < 605 then (if i.val < 604 then (140, 126) else (139, 5)) else (if i.val < 606 then (106, 247) else (108, 118))))) else (if i.val < 614 then (if i.val < 610 then (if i.val < 608 then (132, 148) else (if i.val < 609 then (71, 176) else (120, 185))) else (if i.val < 612 then (if i.val < 611 then (7, 184) else (17, 15)) else (if i.val < 613 then (99, 214) else (105, 134)))) else (if i.val < 617 then (if i.val < 615 then (99, 182) else (if i.val < 616 then (116, 142) else (122, 42))) else (if i.val < 619 then (if i.val < 618 then (115, 125) else (117, 191)) else (if i.val < 620 then (114, 97) else (99, 68)))))) else (if i.val < 634 then (if i.val < 627 then (if i.val < 624 then (if i.val < 622 then (18, 200) else (if i.val < 623 then (93, 79) else (131, 29))) else (if i.val < 625 then (60, 136) else (if i.val < 626 then (72, 94) else (13, 64)))) else (if i.val < 630 then (if i.val < 628 then (129, 164) else (if i.val < 629 then (88, 191) else (119, 75))) else (if i.val < 632 then (if i.val < 631 then (58, 90) else (129, 181)) else (if i.val < 633 then (119, 254) else (139, 120))))) else (if i.val < 641 then (if i.val < 637 then (if i.val < 635 then (97, 220) else (if i.val < 636 then (61, 202) else (109, 99))) else (if i.val < 639 then (if i.val < 638 then (74, 120) else (78, 252)) else (if i.val < 640 then (82, 137) else (112, 94)))) else (if i.val < 644 then (if i.val < 642 then (107, 196) else (if i.val < 643 then (96, 40) else (74, 244))) else (if i.val < 646 then (if i.val < 645 then (89, 29) else (119, 86)) else (if i.val < 647 then (60, 127) else (120, 158))))))))) else (if i.val < 756 then (if i.val < 702 then (if i.val < 675 then (if i.val < 661 then (if i.val < 654 then (if i.val < 651 then (if i.val < 649 then (13, 14) else (if i.val < 650 then (81, 238) else (69, 45))) else (if i.val < 652 then (135, 133) else (if i.val < 653 then (74, 141) else (131, 230)))) else (if i.val < 657 then (if i.val < 655 then (68, 212) else (if i.val < 656 then (95, 165) else (138, 24))) else (if i.val < 659 then (if i.val < 658 then (3, 75) else (85, 243)) else (if i.val < 660 then (52, 116) else (73, 122))))) else (if i.val < 668 then (if i.val < 664 then (if i.val < 662 then (96, 210) else (if i.val < 663 then (143, 181) else (50, 89))) else (if i.val < 666 then (if i.val < 665 then (120, 39) else (104, 246)) else (if i.val < 667 then (45, 128) else (120, 80)))) else (if i.val < 671 then (if i.val < 669 then (99, 43) else (if i.val < 670 then (128, 221) else (124, 36))) else (if i.val < 673 then (if i.val < 672 then (79, 244) else (64, 178)) else (if i.val < 674 then (112, 56) else (109, 140)))))) else (if i.val < 688 then (if i.val < 681 then (if i.val < 678 then (if i.val < 676 then (71, 236) else (if i.val < 677 then (93, 175) else (101, 26))) else (if i.val < 679 then (8, 151) else (if i.val < 680 then (137, 192) else (78, 178)))) else (if i.val < 684 then (if i.val < 682 then (99, 216) else (if i.val < 683 then (104, 250) else (10, 235))) else (if i.val < 686 then (if i.val < 685 then (73, 128) else (133, 183)) else (if i.val < 687 then (94, 76) else (114, 123))))) else (if i.val < 695 then (if i.val < 691 then (if i.val < 689 then (120, 157) else (if i.val < 690 then (99, 244) else (144, 100))) else (if i.val < 693 then (if i.val < 692 then (82, 97) else (138, 31)) else (if i.val < 694 then (115, 219) else (112, 159)))) else (if i.val < 698 then (if i.val < 696 then (87, 134) else (if i.val < 697 then (78, 161) else (66, 85))) else (if i.val < 700 then (if i.val < 699 then (94, 139) else (137, 168)) else (if i.val < 701 then (122, 160) else (32, 115))))))) else (if i.val < 729 then (if i.val < 715 then (if i.val < 708 then (if i.val < 705 then (if i.val < 703 then (78, 233) else (if i.val < 704 then (1, 120) else (144, 90))) else (if i.val < 706 then (114, 179) else (if i.val < 707 then (9, 108) else (15, 237)))) else (if i.val < 711 then (if i.val < 709 then (123, 5) else (if i.val < 710 then (129, 132) else (100, 158))) else (if i.val < 713 then (if i.val < 712 then (22, 54) else (99, 234)) else (if i.val < 714 then (143, 205) else (99, 23))))) else (if i.val < 722 then (if i.val < 718 then (if i.val < 716 then (123, 71) else (if i.val < 717 then (85, 185) else (138, 32))) else (if i.val < 720 then (if i.val < 719 then (27, 10) else (23, 74)) else (if i.val < 721 then (59, 62) else (143, 223)))) else (if i.val < 725 then (if i.val < 723 then (106, 5) else (if i.val < 724 then (45, 151) else (112, 169))) else (if i.val < 727 then (if i.val < 726 then (101, 200) else (106, 82)) else (if i.val < 728 then (44, 93) else (86, 105)))))) else (if i.val < 742 then (if i.val < 735 then (if i.val < 732 then (if i.val < 730 then (74, 103) else (if i.val < 731 then (104, 60) else (102, 48))) else (if i.val < 733 then (140, 11) else (if i.val < 734 then (105, 42) else (62, 124)))) else (if i.val < 738 then (if i.val < 736 then (110, 216) else (if i.val < 737 then (141, 19) else (24, 60))) else (if i.val < 740 then (if i.val < 739 then (121, 37) else (14, 137)) else (if i.val < 741 then (105, 123) else (113, 18))))) else (if i.val < 749 then (if i.val < 745 then (if i.val < 743 then (12, 101) else (if i.val < 744 then (127, 126) else (117, 8))) else (if i.val < 747 then (if i.val < 746 then (80, 195) else (95, 0)) else (if i.val < 748 then (47, 220) else (49, 54)))) else (if i.val < 752 then (if i.val < 750 then (67, 128) else (if i.val < 751 then (116, 209) else (94, 9))) else (if i.val < 754 then (if i.val < 753 then (138, 170) else (105, 36)) else (if i.val < 755 then (141, 128) else (119, 198)))))))) else (if i.val < 810 then (if i.val < 783 then (if i.val < 769 then (if i.val < 762 then (if i.val < 759 then (if i.val < 757 then (98, 202) else (if i.val < 758 then (126, 246) else (108, 95))) else (if i.val < 760 then (69, 228) else (if i.val < 761 then (123, 22) else (126, 70)))) else (if i.val < 765 then (if i.val < 763 then (96, 209) else (if i.val < 764 then (137, 229) else (115, 52))) else (if i.val < 767 then (if i.val < 766 then (99, 95) else (77, 56)) else (if i.val < 768 then (15, 238) else (126, 23))))) else (if i.val < 776 then (if i.val < 772 then (if i.val < 770 then (135, 196) else (if i.val < 771 then (69, 245) else (41, 11))) else (if i.val < 774 then (if i.val < 773 then (122, 105) else (139, 72)) else (if i.val < 775 then (135, 134) else (48, 7)))) else (if i.val < 779 then (if i.val < 777 then (63, 95) else (if i.val < 778 then (95, 248) else (43, 152))) else (if i.val < 781 then (if i.val < 780 then (132, 215) else (144, 52)) else (if i.val < 782 then (68, 252) else (114, 16)))))) else (if i.val < 796 then (if i.val < 789 then (if i.val < 786 then (if i.val < 784 then (126, 131) else (if i.val < 785 then (106, 234) else (123, 27))) else (if i.val < 787 then (53, 214) else (if i.val < 788 then (44, 57) else (48, 50)))) else (if i.val < 792 then (if i.val < 790 then (123, 51) else (if i.val < 791 then (126, 15) else (23, 10))) else (if i.val < 794 then (if i.val < 793 then (73, 64) else (132, 238)) else (if i.val < 795 then (115, 102) else (103, 240))))) else (if i.val < 803 then (if i.val < 799 then (if i.val < 797 then (101, 97) else (if i.val < 798 then (105, 173) else (126, 86))) else (if i.val < 801 then (if i.val < 800 then (93, 161) else (69, 111)) else (if i.val < 802 then (78, 249) else (45, 102)))) else (if i.val < 806 then (if i.val < 804 then (51, 219) else (if i.val < 805 then (125, 11) else (19, 207))) else (if i.val < 808 then (if i.val < 807 then (93, 47) else (137, 50)) else (if i.val < 809 then (128, 144) else (38, 197))))))) else (if i.val < 837 then (if i.val < 823 then (if i.val < 816 then (if i.val < 813 then (if i.val < 811 then (68, 76) else (if i.val < 812 then (97, 201) else (134, 161))) else (if i.val < 814 then (17, 183) else (if i.val < 815 then (80, 132) else (25, 239)))) else (if i.val < 819 then (if i.val < 817 then (6, 100) else (if i.val < 818 then (138, 103) else (139, 198))) else (if i.val < 821 then (if i.val < 820 then (114, 197) else (61, 20)) else (if i.val < 822 then (73, 195) else (129, 78))))) else (if i.val < 830 then (if i.val < 826 then (if i.val < 824 then (45, 156) else (if i.val < 825 then (92, 150) else (105, 67))) else (if i.val < 828 then (if i.val < 827 then (22, 133) else (122, 115)) else (if i.val < 829 then (113, 210) else (133, 48)))) else (if i.val < 833 then (if i.val < 831 then (132, 141) else (if i.val < 832 then (22, 23) else (139, 218))) else (if i.val < 835 then (if i.val < 834 then (34, 30) else (125, 12)) else (if i.val < 836 then (46, 59) else (92, 97)))))) else (if i.val < 850 then (if i.val < 843 then (if i.val < 840 then (if i.val < 838 then (17, 205) else (if i.val < 839 then (121, 205) else (77, 134))) else (if i.val < 841 then (68, 128) else (if i.val < 842 then (124, 82) else (137, 48)))) else (if i.val < 846 then (if i.val < 844 then (140, 97) else (if i.val < 845 then (132, 36) else (43, 210))) else (if i.val < 848 then (if i.val < 847 then (96, 34) else (122, 103)) else (if i.val < 849 then (127, 141) else (45, 211))))) else (if i.val < 857 then (if i.val < 853 then (if i.val < 851 then (139, 29) else (if i.val < 852 then (129, 3) else (115, 189))) else (if i.val < 855 then (if i.val < 854 then (99, 184) else (125, 93)) else (if i.val < 856 then (112, 52) else (69, 68)))) else (if i.val < 860 then (if i.val < 858 then (18, 70) else (if i.val < 859 then (44, 164) else (125, 218))) else (if i.val < 862 then (if i.val < 861 then (113, 157) else (118, 8)) else (if i.val < 863 then (6, 94) else (84, 108))))))))))) else (if i.val < 1296 then (if i.val < 1080 then (if i.val < 972 then (if i.val < 918 then (if i.val < 891 then (if i.val < 877 then (if i.val < 870 then (if i.val < 867 then (if i.val < 865 then (48, 218) else (if i.val < 866 then (88, 118) else (86, 166))) else (if i.val < 868 then (49, 197) else (if i.val < 869 then (129, 66) else (138, 150)))) else (if i.val < 873 then (if i.val < 871 then (5, 254) else (if i.val < 872 then (128, 152) else (17, 218))) else (if i.val < 875 then (if i.val < 874 then (88, 102) else (6, 73)) else (if i.val < 876 then (39, 88) else (138, 78))))) else (if i.val < 884 then (if i.val < 880 then (if i.val < 878 then (93, 211) else (if i.val < 879 then (136, 202) else (93, 170))) else (if i.val < 882 then (if i.val < 881 then (12, 184) else (135, 198)) else (if i.val < 883 then (88, 83) else (142, 92)))) else (if i.val < 887 then (if i.val < 885 then (59, 54) else (if i.val < 886 then (87, 159) else (34, 63))) else (if i.val < 889 then (if i.val < 888 then (77, 20) else (64, 166)) else (if i.val < 890 then (101, 149) else (106, 213)))))) else (if i.val < 904 then (if i.val < 897 then (if i.val < 894 then (if i.val < 892 then (93, 159) else (if i.val < 893 then (93, 120) else (12, 210))) else (if i.val < 895 then (39, 150) else (if i.val < 896 then (134, 160) else (64, 64)))) else (if i.val < 900 then (if i.val < 898 then (101, 248) else (if i.val < 899 then (89, 228) else (65, 188))) else (if i.val < 902 then (if i.val < 901 then (111, 56) else (40, 158)) else (if i.val < 903 then (59, 4) else (62, 172))))) else (if i.val < 911 then (if i.val < 907 then (if i.val < 905 then (121, 118) else (if i.val < 906 then (135, 69) else (113, 48))) else (if i.val < 909 then (if i.val < 908 then (136, 150) else (45, 182)) else (if i.val < 910 then (80, 66) else (122, 150)))) else (if i.val < 914 then (if i.val < 912 then (10, 221) else (if i.val < 913 then (138, 7) else (56, 57))) else (if i.val < 916 then (if i.val < 915 then (40, 171) else (113, 132)) else (if i.val < 917 then (1, 174) else (58, 238))))))) else (if i.val < 945 then (if i.val < 931 then (if i.val < 924 then (if i.val < 921 then (if i.val < 919 then (38, 229) else (if i.val < 920 then (108, 201) else (71, 244))) else (if i.val < 922 then (96, 232) else (if i.val < 923 then (115, 227) else (122, 237)))) else (if i.val < 927 then (if i.val < 925 then (115, 108) else (if i.val < 926 then (120, 176) else (109, 177))) else (if i.val < 929 then (if i.val < 928 then (88, 64) else (107, 146)) else (if i.val < 930 then (11, 127) else (116, 111))))) else (if i.val < 938 then (if i.val < 934 then (if i.val < 932 then (94, 61) else (if i.val < 933 then (11, 93) else (24, 125))) else (if i.val < 936 then (if i.val < 935 then (136, 243) else (55, 35)) else (if i.val < 937 then (85, 32) else (95, 110)))) else (if i.val < 941 then (if i.val < 939 then (49, 227) else (if i.val < 940 then (63, 185) else (134, 158))) else (if i.val < 943 then (if i.val < 942 then (106, 16) else (76, 76)) else (if i.val < 944 then (81, 62) else (99, 171)))))) else (if i.val < 958 then (if i.val < 951 then (if i.val < 948 then (if i.val < 946 then (99, 80) else (if i.val < 947 then (107, 88) else (123, 160))) else (if i.val < 949 then (72, 194) else (if i.val < 950 then (98, 165) else (79, 159)))) else (if i.val < 954 then (if i.val < 952 then (38, 216) else (if i.val < 953 then (117, 96) else (113, 224))) else (if i.val < 956 then (if i.val < 955 then (99, 4) else (60, 155)) else (if i.val < 957 then (94, 144) else (116, 109))))) else (if i.val < 965 then (if i.val < 961 then (if i.val < 959 then (136, 114) else (if i.val < 960 then (133, 18) else (95, 4))) else (if i.val < 963 then (if i.val < 962 then (15, 0) else (122, 152)) else (if i.val < 964 then (5, 190) else (111, 58)))) else (if i.val < 968 then (if i.val < 966 then (15, 117) else (if i.val < 967 then (119, 170) else (111, 180))) else (if i.val < 970 then (if i.val < 969 then (86, 19) else (141, 239)) else (if i.val < 971 then (58, 99) else (89, 56)))))))) else (if i.val < 1026 then (if i.val < 999 then (if i.val < 985 then (if i.val < 978 then (if i.val < 975 then (if i.val < 973 then (108, 65) else (if i.val < 974 then (4, 247) else (108, 104))) else (if i.val < 976 then (38, 131) else (if i.val < 977 then (83, 62) else (52, 156)))) else (if i.val < 981 then (if i.val < 979 then (95, 244) else (if i.val < 980 then (111, 129) else (51, 207))) else (if i.val < 983 then (if i.val < 982 then (131, 160) else (107, 184)) else (if i.val < 984 then (58, 193) else (2, 242))))) else (if i.val < 992 then (if i.val < 988 then (if i.val < 986 then (77, 217) else (if i.val < 987 then (5, 98) else (73, 162))) else (if i.val < 990 then (if i.val < 989 then (82, 249) else (111, 29)) else (if i.val < 991 then (15, 170) else (132, 9)))) else (if i.val < 995 then (if i.val < 993 then (133, 184) else (if i.val < 994 then (74, 177) else (141, 6))) else (if i.val < 997 then (if i.val < 996 then (101, 51) else (86, 113)) else (if i.val < 998 then (2, 15) else (129, 104)))))) else (if i.val < 1012 then (if i.val < 1005 then (if i.val < 1002 then (if i.val < 1000 then (134, 193) else (if i.val < 1001 then (112, 99) else (141, 115))) else (if i.val < 1003 then (106, 241) else (if i.val < 1004 then (95, 64) else (75, 67)))) else (if i.val < 1008 then (if i.val < 1006 then (102, 216) else (if i.val < 1007 then (67, 172) else (1, 168))) else (if i.val < 1010 then (if i.val < 1009 then (137, 69) else (141, 138)) else (if i.val < 1011 then (28, 255) else (99, 7))))) else (if i.val < 1019 then (if i.val < 1015 then (if i.val < 1013 then (116, 164) else (if i.val < 1014 then (142, 204) else (107, 57))) else (if i.val < 1017 then (if i.val < 1016 then (124, 74) else (64, 94)) else (if i.val < 1018 then (121, 58) else (23, 157)))) else (if i.val < 1022 then (if i.val < 1020 then (121, 91) else (if i.val < 1021 then (47, 113) else (69, 166))) else (if i.val < 1024 then (if i.val < 1023 then (123, 32) else (19, 168)) else (if i.val < 1025 then (101, 154) else (111, 194))))))) else (if i.val < 1053 then (if i.val < 1039 then (if i.val < 1032 then (if i.val < 1029 then (if i.val < 1027 then (81, 132) else (if i.val < 1028 then (124, 135) else (24, 12))) else (if i.val < 1030 then (0, 177) else (if i.val < 1031 then (48, 82) else (132, 69)))) else (if i.val < 1035 then (if i.val < 1033 then (74, 73) else (if i.val < 1034 then (109, 34) else (113, 214))) else (if i.val < 1037 then (if i.val < 1036 then (104, 54) else (111, 30)) else (if i.val < 1038 then (134, 75) else (90, 146))))) else (if i.val < 1046 then (if i.val < 1042 then (if i.val < 1040 then (61, 101) else (if i.val < 1041 then (98, 196) else (108, 5))) else (if i.val < 1044 then (if i.val < 1043 then (131, 174) else (100, 94)) else (if i.val < 1045 then (45, 252) else (20, 187)))) else (if i.val < 1049 then (if i.val < 1047 then (140, 188) else (if i.val < 1048 then (46, 121) else (133, 43))) else (if i.val < 1051 then (if i.val < 1050 then (75, 212) else (92, 74)) else (if i.val < 1052 then (21, 115) else (58, 75)))))) else (if i.val < 1066 then (if i.val < 1059 then (if i.val < 1056 then (if i.val < 1054 then (103, 77) else (if i.val < 1055 then (108, 126) else (140, 64))) else (if i.val < 1057 then (109, 211) else (if i.val < 1058 then (138, 133) else (139, 161)))) else (if i.val < 1062 then (if i.val < 1060 then (0, 160) else (if i.val < 1061 then (83, 101) else (75, 23))) else (if i.val < 1064 then (if i.val < 1063 then (128, 71) else (53, 200)) else (if i.val < 1065 then (6, 5) else (1, 172))))) else (if i.val < 1073 then (if i.val < 1069 then (if i.val < 1067 then (106, 3) else (if i.val < 1068 then (8, 76) else (106, 171))) else (if i.val < 1071 then (if i.val < 1070 then (46, 253) else (9, 60)) else (if i.val < 1072 then (64, 236) else (56, 20)))) else (if i.val < 1076 then (if i.val < 1074 then (134, 233) else (if i.val < 1075 then (75, 112) else (65, 84))) else (if i.val < 1078 then (if i.val < 1077 then (124, 54) else (105, 72)) else (if i.val < 1079 then (96, 214) else (111, 124))))))))) else (if i.val < 1188 then (if i.val < 1134 then (if i.val < 1107 then (if i.val < 1093 then (if i.val < 1086 then (if i.val < 1083 then (if i.val < 1081 then (56, 99) else (if i.val < 1082 then (131, 161) else (142, 28))) else (if i.val < 1084 then (113, 177) else (if i.val < 1085 then (140, 73) else (41, 126)))) else (if i.val < 1089 then (if i.val < 1087 then (102, 105) else (if i.val < 1088 then (77, 243) else (36, 231))) else (if i.val < 1091 then (if i.val < 1090 then (44, 83) else (112, 152)) else (if i.val < 1092 then (35, 57) else (121, 233))))) else (if i.val < 1100 then (if i.val < 1096 then (if i.val < 1094 then (123, 141) else (if i.val < 1095 then (140, 74) else (140, 238))) else (if i.val < 1098 then (if i.val < 1097 then (114, 109) else (84, 193)) else (if i.val < 1099 then (124, 252) else (50, 186)))) else (if i.val < 1103 then (if i.val < 1101 then (123, 42) else (if i.val < 1102 then (105, 30) else (18, 250))) else (if i.val < 1105 then (if i.val < 1104 then (98, 13) else (75, 178)) else (if i.val < 1106 then (88, 91) else (116, 32)))))) else (if i.val < 1120 then (if i.val < 1113 then (if i.val < 1110 then (if i.val < 1108 then (139, 65) else (if i.val < 1109 then (116, 37) else (39, 226))) else (if i.val < 1111 then (101, 60) else (if i.val < 1112 then (16, 197) else (118, 219)))) else (if i.val < 1116 then (if i.val < 1114 then (71, 172) else (if i.val < 1115 then (115, 14) else (35, 204))) else (if i.val < 1118 then (if i.val < 1117 then (54, 46) else (44, 42)) else (if i.val < 1119 then (23, 141) else (78, 63))))) else (if i.val < 1127 then (if i.val < 1123 then (if i.val < 1121 then (117, 146) else (if i.val < 1122 then (98, 61) else (21, 106))) else (if i.val < 1125 then (if i.val < 1124 then (51, 40) else (72, 180)) else (if i.val < 1126 then (77, 103) else (93, 38)))) else (if i.val < 1130 then (if i.val < 1128 then (87, 25) else (if i.val < 1129 then (101, 186) else (29, 72))) else (if i.val < 1132 then (if i.val < 1131 then (58, 102) else (45, 90)) else (if i.val < 1133 then (60, 175) else (119, 252))))))) else (if i.val < 1161 then (if i.val < 1147 then (if i.val < 1140 then (if i.val < 1137 then (if i.val < 1135 then (2, 16) else (if i.val < 1136 then (135, 207) else (73, 27))) else (if i.val < 1138 then (131, 191) else (if i.val < 1139 then (48, 120) else (93, 202)))) else (if i.val < 1143 then (if i.val < 1141 then (107, 49) else (if i.val < 1142 then (75, 179) else (34, 196))) else (if i.val < 1145 then (if i.val < 1144 then (105, 154) else (81, 86)) else (if i.val < 1146 then (25, 70) else (77, 230))))) else (if i.val < 1154 then (if i.val < 1150 then (if i.val < 1148 then (134, 125) else (if i.val < 1149 then (91, 232) else (129, 232))) else (if i.val < 1152 then (if i.val < 1151 then (122, 208) else (63, 68)) else (if i.val < 1153 then (52, 18) else (25, 135)))) else (if i.val < 1157 then (if i.val < 1155 then (63, 23) else (if i.val < 1156 then (133, 237) else (85, 219))) else (if i.val < 1159 then (if i.val < 1158 then (41, 38) else (97, 232)) else (if i.val < 1160 then (116, 135) else (117, 120)))))) else (if i.val < 1174 then (if i.val < 1167 then (if i.val < 1164 then (if i.val < 1162 then (50, 152) else (if i.val < 1163 then (132, 56) else (25, 207))) else (if i.val < 1165 then (138, 195) else (if i.val < 1166 then (91, 36) else (89, 97)))) else (if i.val < 1170 then (if i.val < 1168 then (92, 24) else (if i.val < 1169 then (100, 174) else (89, 209))) else (if i.val < 1172 then (if i.val < 1171 then (125, 235) else (137, 123)) else (if i.val < 1173 then (120, 48) else (106, 36))))) else (if i.val < 1181 then (if i.val < 1177 then (if i.val < 1175 then (94, 227) else (if i.val < 1176 then (90, 120) else (138, 125))) else (if i.val < 1179 then (if i.val < 1178 then (77, 91) else (57, 97)) else (if i.val < 1180 then (56, 224) else (28, 111)))) else (if i.val < 1184 then (if i.val < 1182 then (60, 144) else (if i.val < 1183 then (109, 109) else (129, 147))) else (if i.val < 1186 then (if i.val < 1185 then (24, 155) else (114, 4)) else (if i.val < 1187 then (92, 31) else (97, 22)))))))) else (if i.val < 1242 then (if i.val < 1215 then (if i.val < 1201 then (if i.val < 1194 then (if i.val < 1191 then (if i.val < 1189 then (99, 143) else (if i.val < 1190 then (75, 52) else (79, 102))) else (if i.val < 1192 then (33, 44) else (if i.val < 1193 then (131, 189) else (140, 199)))) else (if i.val < 1197 then (if i.val < 1195 then (0, 34) else (if i.val < 1196 then (135, 153) else (144, 126))) else (if i.val < 1199 then (if i.val < 1198 then (16, 38) else (24, 131)) else (if i.val < 1200 then (129, 209) else (77, 162))))) else (if i.val < 1208 then (if i.val < 1204 then (if i.val < 1202 then (107, 241) else (if i.val < 1203 then (56, 166) else (58, 93))) else (if i.val < 1206 then (if i.val < 1205 then (4, 49) else (38, 44)) else (if i.val < 1207 then (135, 181) else (84, 176)))) else (if i.val < 1211 then (if i.val < 1209 then (15, 227) else (if i.val < 1210 then (137, 113) else (47, 242))) else (if i.val < 1213 then (if i.val < 1212 then (72, 76) else (143, 71)) else (if i.val < 1214 then (127, 6) else (85, 142)))))) else (if i.val < 1228 then (if i.val < 1221 then (if i.val < 1218 then (if i.val < 1216 then (50, 254) else (if i.val < 1217 then (92, 234) else (120, 240))) else (if i.val < 1219 then (47, 102) else (if i.val < 1220 then (127, 43) else (60, 160)))) else (if i.val < 1224 then (if i.val < 1222 then (6, 200) else (if i.val < 1223 then (87, 152) else (80, 77))) else (if i.val < 1226 then (if i.val < 1225 then (138, 109) else (126, 71)) else (if i.val < 1227 then (94, 4) else (122, 199))))) else (if i.val < 1235 then (if i.val < 1231 then (if i.val < 1229 then (119, 132) else (if i.val < 1230 then (62, 88) else (121, 133))) else (if i.val < 1233 then (if i.val < 1232 then (79, 66) else (58, 70)) else (if i.val < 1234 then (60, 128) else (96, 87)))) else (if i.val < 1238 then (if i.val < 1236 then (99, 188) else (if i.val < 1237 then (85, 116) else (102, 51))) else (if i.val < 1240 then (if i.val < 1239 then (28, 122) else (16, 235)) else (if i.val < 1241 then (127, 22) else (143, 40))))))) else (if i.val < 1269 then (if i.val < 1255 then (if i.val < 1248 then (if i.val < 1245 then (if i.val < 1243 then (116, 213) else (if i.val < 1244 then (67, 123) else (85, 214))) else (if i.val < 1246 then (67, 169) else (if i.val < 1247 then (110, 124) else (127, 85)))) else (if i.val < 1251 then (if i.val < 1249 then (132, 71) else (if i.val < 1250 then (142, 81) else (114, 230))) else (if i.val < 1253 then (if i.val < 1252 then (98, 113) else (132, 51)) else (if i.val < 1254 then (106, 129) else (144, 134))))) else (if i.val < 1262 then (if i.val < 1258 then (if i.val < 1256 then (42, 132) else (if i.val < 1257 then (124, 1) else (139, 191))) else (if i.val < 1260 then (if i.val < 1259 then (117, 83) else (8, 3)) else (if i.val < 1261 then (87, 229) else (90, 154)))) else (if i.val < 1265 then (if i.val < 1263 then (130, 86) else (if i.val < 1264 then (17, 99) else (39, 14))) else (if i.val < 1267 then (if i.val < 1266 then (99, 177) else (141, 135)) else (if i.val < 1268 then (55, 14) else (106, 139)))))) else (if i.val < 1282 then (if i.val < 1275 then (if i.val < 1272 then (if i.val < 1270 then (86, 34) else (if i.val < 1271 then (133, 98) else (72, 32))) else (if i.val < 1273 then (138, 213) else (if i.val < 1274 then (140, 115) else (115, 144)))) else (if i.val < 1278 then (if i.val < 1276 then (41, 198) else (if i.val < 1277 then (113, 204) else (96, 201))) else (if i.val < 1280 then (if i.val < 1279 then (124, 174) else (141, 236)) else (if i.val < 1281 then (137, 247) else (130, 230))))) else (if i.val < 1289 then (if i.val < 1285 then (if i.val < 1283 then (66, 96) else (if i.val < 1284 then (89, 178) else (39, 84))) else (if i.val < 1287 then (if i.val < 1286 then (115, 169) else (8, 27)) else (if i.val < 1288 then (127, 44) else (41, 207)))) else (if i.val < 1292 then (if i.val < 1290 then (93, 176) else (if i.val < 1291 then (122, 164) else (115, 9))) else (if i.val < 1294 then (if i.val < 1293 then (33, 165) else (127, 74)) else (if i.val < 1295 then (109, 251) else (122, 156)))))))))) else (if i.val < 1512 then (if i.val < 1404 then (if i.val < 1350 then (if i.val < 1323 then (if i.val < 1309 then (if i.val < 1302 then (if i.val < 1299 then (if i.val < 1297 then (141, 252) else (if i.val < 1298 then (77, 183) else (8, 54))) else (if i.val < 1300 then (119, 89) else (if i.val < 1301 then (113, 121) else (112, 250)))) else (if i.val < 1305 then (if i.val < 1303 then (121, 102) else (if i.val < 1304 then (56, 225) else (50, 127))) else (if i.val < 1307 then (if i.val < 1306 then (127, 115) else (136, 210)) else (if i.val < 1308 then (110, 33) else (90, 67))))) else (if i.val < 1316 then (if i.val < 1312 then (if i.val < 1310 then (98, 57) else (if i.val < 1311 then (133, 153) else (81, 158))) else (if i.val < 1314 then (if i.val < 1313 then (24, 210) else (142, 195)) else (if i.val < 1315 then (114, 86) else (131, 151)))) else (if i.val < 1319 then (if i.val < 1317 then (131, 144) else (if i.val < 1318 then (63, 246) else (105, 69))) else (if i.val < 1321 then (if i.val < 1320 then (29, 185) else (24, 28)) else (if i.val < 1322 then (115, 220) else (5, 49)))))) else (if i.val < 1336 then (if i.val < 1329 then (if i.val < 1326 then (if i.val < 1324 then (66, 227) else (if i.val < 1325 then (86, 122) else (124, 130))) else (if i.val < 1327 then (5, 66) else (if i.val < 1328 then (106, 250) else (135, 167)))) else (if i.val < 1332 then (if i.val < 1330 then (132, 117) else (if i.val < 1331 then (138, 219) else (135, 49))) else (if i.val < 1334 then (if i.val < 1333 then (87, 153) else (140, 42)) else (if i.val < 1335 then (119, 183) else (69, 155))))) else (if i.val < 1343 then (if i.val < 1339 then (if i.val < 1337 then (47, 192) else (if i.val < 1338 then (19, 252) else (94, 15))) else (if i.val < 1341 then (if i.val < 1340 then (137, 208) else (49, 87)) else (if i.val < 1342 then (121, 96) else (95, 1)))) else (if i.val < 1346 then (if i.val < 1344 then (82, 158) else (if i.val < 1345 then (11, 164) else (116, 31))) else (if i.val < 1348 then (if i.val < 1347 then (36, 250) else (66, 114)) else (if i.val < 1349 then (121, 43) else (37, 19))))))) else (if i.val < 1377 then (if i.val < 1363 then (if i.val < 1356 then (if i.val < 1353 then (if i.val < 1351 then (87, 133) else (if i.val < 1352 then (33, 73) else (58, 100))) else (if i.val < 1354 then (139, 212) else (if i.val < 1355 then (140, 151) else (136, 129)))) else (if i.val < 1359 then (if i.val < 1357 then (27, 35) else (if i.val < 1358 then (80, 234) else (93, 156))) else (if i.val < 1361 then (if i.val < 1360 then (29, 158) else (74, 13)) else (if i.val < 1362 then (133, 195) else (131, 21))))) else (if i.val < 1370 then (if i.val < 1366 then (if i.val < 1364 then (111, 188) else (if i.val < 1365 then (141, 196) else (80, 54))) else (if i.val < 1368 then (if i.val < 1367 then (16, 106) else (51, 26)) else (if i.val < 1369 then (118, 78) else (72, 238)))) else (if i.val < 1373 then (if i.val < 1371 then (138, 249) else (if i.val < 1372 then (38, 79) else (120, 8))) else (if i.val < 1375 then (if i.val < 1374 then (3, 181) else (113, 71)) else (if i.val < 1376 then (117, 204) else (98, 70)))))) else (if i.val < 1390 then (if i.val < 1383 then (if i.val < 1380 then (if i.val < 1378 then (134, 80) else (if i.val < 1379 then (118, 190) else (134, 46))) else (if i.val < 1381 then (29, 125) else (if i.val < 1382 then (65, 147) else (72, 86)))) else (if i.val < 1386 then (if i.val < 1384 then (75, 153) else (if i.val < 1385 then (99, 59) else (90, 215))) else (if i.val < 1388 then (if i.val < 1387 then (92, 221) else (85, 145)) else (if i.val < 1389 then (115, 123) else (39, 193))))) else (if i.val < 1397 then (if i.val < 1393 then (if i.val < 1391 then (101, 171) else (if i.val < 1392 then (76, 231) else (88, 252))) else (if i.val < 1395 then (if i.val < 1394 then (108, 106) else (122, 198)) else (if i.val < 1396 then (88, 239) else (120, 160)))) else (if i.val < 1400 then (if i.val < 1398 then (81, 147) else (if i.val < 1399 then (90, 183) else (123, 172))) else (if i.val < 1402 then (if i.val < 1401 then (36, 151) else (51, 28)) else (if i.val < 1403 then (134, 78) else (29, 180)))))))) else (if i.val < 1458 then (if i.val < 1431 then (if i.val < 1417 then (if i.val < 1410 then (if i.val < 1407 then (if i.val < 1405 then (72, 34) else (if i.val < 1406 then (60, 68) else (133, 66))) else (if i.val < 1408 then (135, 24) else (if i.val < 1409 then (92, 109) else (56, 38)))) else (if i.val < 1413 then (if i.val < 1411 then (119, 119) else (if i.val < 1412 then (10, 175) else (88, 61))) else (if i.val < 1415 then (if i.val < 1414 then (144, 50) else (37, 102)) else (if i.val < 1416 then (109, 66) else (142, 246))))) else (if i.val < 1424 then (if i.val < 1420 then (if i.val < 1418 then (110, 115) else (if i.val < 1419 then (133, 185) else (65, 10))) else (if i.val < 1422 then (if i.val < 1421 then (11, 156) else (102, 127)) else (if i.val < 1423 then (99, 93) else (56, 17)))) else (if i.val < 1427 then (if i.val < 1425 then (117, 236) else (if i.val < 1426 then (135, 214) else (134, 49))) else (if i.val < 1429 then (if i.val < 1428 then (136, 37) else (118, 138)) else (if i.val < 1430 then (95, 85) else (102, 130)))))) else (if i.val < 1444 then (if i.val < 1437 then (if i.val < 1434 then (if i.val < 1432 then (58, 129) else (if i.val < 1433 then (38, 183) else (122, 224))) else (if i.val < 1435 then (42, 39) else (if i.val < 1436 then (88, 147) else (60, 146)))) else (if i.val < 1440 then (if i.val < 1438 then (118, 209) else (if i.val < 1439 then (131, 225) else (44, 232))) else (if i.val < 1442 then (if i.val < 1441 then (135, 166) else (85, 216)) else (if i.val < 1443 then (118, 62) else (133, 246))))) else (if i.val < 1451 then (if i.val < 1447 then (if i.val < 1445 then (122, 146) else (if i.val < 1446 then (35, 217) else (91, 209))) else (if i.val < 1449 then (if i.val < 1448 then (135, 12) else (137, 169)) else (if i.val < 1450 then (49, 113) else (127, 87)))) else (if i.val < 1454 then (if i.val < 1452 then (130, 33) else (if i.val < 1453 then (48, 20) else (19, 27))) else (if i.val < 1456 then (if i.val < 1455 then (11, 155) else (20, 122)) else (if i.val < 1457 then (117, 54) else (62, 181))))))) else (if i.val < 1485 then (if i.val < 1471 then (if i.val < 1464 then (if i.val < 1461 then (if i.val < 1459 then (65, 190) else (if i.val < 1460 then (58, 239) else (96, 50))) else (if i.val < 1462 then (38, 66) else (if i.val < 1463 then (118, 242) else (87, 115)))) else (if i.val < 1467 then (if i.val < 1465 then (9, 66) else (if i.val < 1466 then (53, 229) else (110, 43))) else (if i.val < 1469 then (if i.val < 1468 then (23, 6) else (89, 39)) else (if i.val < 1470 then (80, 148) else (76, 171))))) else (if i.val < 1478 then (if i.val < 1474 then (if i.val < 1472 then (31, 113) else (if i.val < 1473 then (119, 91) else (131, 17))) else (if i.val < 1476 then (if i.val < 1475 then (16, 11) else (31, 106)) else (if i.val < 1477 then (135, 100) else (128, 75)))) else (if i.val < 1481 then (if i.val < 1479 then (71, 93) else (if i.val < 1480 then (133, 202) else (117, 110))) else (if i.val < 1483 then (if i.val < 1482 then (20, 245) else (108, 155)) else (if i.val < 1484 then (81, 239) else (129, 212)))))) else (if i.val < 1498 then (if i.val < 1491 then (if i.val < 1488 then (if i.val < 1486 then (93, 73) else (if i.val < 1487 then (132, 116) else (72, 47))) else (if i.val < 1489 then (85, 44) else (if i.val < 1490 then (108, 202) else (143, 101)))) else (if i.val < 1494 then (if i.val < 1492 then (122, 230) else (if i.val < 1493 then (135, 240) else (61, 252))) else (if i.val < 1496 then (if i.val < 1495 then (122, 98) else (49, 59)) else (if i.val < 1497 then (67, 97) else (137, 64))))) else (if i.val < 1505 then (if i.val < 1501 then (if i.val < 1499 then (104, 88) else (if i.val < 1500 then (115, 174) else (97, 154))) else (if i.val < 1503 then (if i.val < 1502 then (142, 168) else (88, 150)) else (if i.val < 1504 then (9, 121) else (21, 144)))) else (if i.val < 1508 then (if i.val < 1506 then (111, 14) else (if i.val < 1507 then (84, 25) else (31, 123))) else (if i.val < 1510 then (if i.val < 1509 then (62, 191) else (114, 174)) else (if i.val < 1511 then (81, 156) else (133, 127))))))))) else (if i.val < 1620 then (if i.val < 1566 then (if i.val < 1539 then (if i.val < 1525 then (if i.val < 1518 then (if i.val < 1515 then (if i.val < 1513 then (132, 108) else (if i.val < 1514 then (130, 188) else (131, 240))) else (if i.val < 1516 then (73, 174) else (if i.val < 1517 then (123, 161) else (41, 147)))) else (if i.val < 1521 then (if i.val < 1519 then (142, 137) else (if i.val < 1520 then (64, 144) else (94, 216))) else (if i.val < 1523 then (if i.val < 1522 then (47, 2) else (133, 84)) else (if i.val < 1524 then (92, 164) else (142, 86))))) else (if i.val < 1532 then (if i.val < 1528 then (if i.val < 1526 then (133, 203) else (if i.val < 1527 then (92, 23) else (134, 24))) else (if i.val < 1530 then (if i.val < 1529 then (138, 142) else (138, 248)) else (if i.val < 1531 then (141, 60) else (74, 205)))) else (if i.val < 1535 then (if i.val < 1533 then (60, 120) else (if i.val < 1534 then (106, 42) else (31, 156))) else (if i.val < 1537 then (if i.val < 1536 then (126, 39) else (10, 93)) else (if i.val < 1538 then (34, 240) else (65, 6)))))) else (if i.val < 1552 then (if i.val < 1545 then (if i.val < 1542 then (if i.val < 1540 then (115, 150) else (if i.val < 1541 then (107, 157) else (122, 87))) else (if i.val < 1543 then (93, 186) else (if i.val < 1544 then (87, 109) else (60, 238)))) else (if i.val < 1548 then (if i.val < 1546 then (24, 190) else (if i.val < 1547 then (49, 10) else (102, 138))) else (if i.val < 1550 then (if i.val < 1549 then (65, 4) else (61, 176)) else (if i.val < 1551 then (1, 236) else (60, 28))))) else (if i.val < 1559 then (if i.val < 1555 then (if i.val < 1553 then (68, 2) else (if i.val < 1554 then (91, 204) else (5, 195))) else (if i.val < 1557 then (if i.val < 1556 then (69, 162) else (134, 188)) else (if i.val < 1558 then (34, 178) else (129, 197)))) else (if i.val < 1562 then (if i.val < 1560 then (109, 218) else (if i.val < 1561 then (126, 33) else (65, 236))) else (if i.val < 1564 then (if i.val < 1563 then (5, 192) else (43, 74)) else (if i.val < 1565 then (58, 231) else (132, 144))))))) else (if i.val < 1593 then (if i.val < 1579 then (if i.val < 1572 then (if i.val < 1569 then (if i.val < 1567 then (64, 185) else (if i.val < 1568 then (98, 29) else (34, 212))) else (if i.val < 1570 then (98, 172) else (if i.val < 1571 then (129, 188) else (123, 34)))) else (if i.val < 1575 then (if i.val < 1573 then (90, 38) else (if i.val < 1574 then (1, 167) else (124, 186))) else (if i.val < 1577 then (if i.val < 1576 then (80, 81) else (135, 89)) else (if i.val < 1578 then (60, 34) else (14, 244))))) else (if i.val < 1586 then (if i.val < 1582 then (if i.val < 1580 then (136, 138) else (if i.val < 1581 then (4, 69) else (100, 53))) else (if i.val < 1584 then (if i.val < 1583 then (89, 53) else (73, 244)) else (if i.val < 1585 then (112, 70) else (60, 141)))) else (if i.val < 1589 then (if i.val < 1587 then (140, 86) else (if i.val < 1588 then (140, 32) else (85, 226))) else (if i.val < 1591 then (if i.val < 1590 then (4, 120) else (105, 196)) else (if i.val < 1592 then (19, 121) else (53, 238)))))) else (if i.val < 1606 then (if i.val < 1599 then (if i.val < 1596 then (if i.val < 1594 then (138, 53) else (if i.val < 1595 then (113, 21) else (139, 251))) else (if i.val < 1597 then (109, 148) else (if i.val < 1598 then (73, 209) else (127, 182)))) else (if i.val < 1602 then (if i.val < 1600 then (123, 177) else (if i.val < 1601 then (104, 116) else (135, 209))) else (if i.val < 1604 then (if i.val < 1603 then (47, 130) else (127, 177)) else (if i.val < 1605 then (132, 85) else (35, 93))))) else (if i.val < 1613 then (if i.val < 1609 then (if i.val < 1607 then (118, 4) else (if i.val < 1608 then (136, 226) else (126, 134))) else (if i.val < 1611 then (if i.val < 1610 then (103, 57) else (129, 180)) else (if i.val < 1612 then (122, 180) else (76, 114)))) else (if i.val < 1616 then (if i.val < 1614 then (72, 3) else (if i.val < 1615 then (8, 160) else (127, 58))) else (if i.val < 1618 then (if i.val < 1617 then (112, 254) else (60, 25)) else (if i.val < 1619 then (78, 135) else (140, 141)))))))) else (if i.val < 1674 then (if i.val < 1647 then (if i.val < 1633 then (if i.val < 1626 then (if i.val < 1623 then (if i.val < 1621 then (126, 237) else (if i.val < 1622 then (100, 218) else (139, 125))) else (if i.val < 1624 then (89, 211) else (if i.val < 1625 then (95, 228) else (102, 35)))) else (if i.val < 1629 then (if i.val < 1627 then (116, 11) else (if i.val < 1628 then (56, 247) else (4, 83))) else (if i.val < 1631 then (if i.val < 1630 then (74, 28) else (136, 200)) else (if i.val < 1632 then (105, 93) else (35, 236))))) else (if i.val < 1640 then (if i.val < 1636 then (if i.val < 1634 then (55, 211) else (if i.val < 1635 then (126, 230) else (118, 249))) else (if i.val < 1638 then (if i.val < 1637 then (112, 211) else (55, 198)) else (if i.val < 1639 then (119, 1) else (123, 154)))) else (if i.val < 1643 then (if i.val < 1641 then (139, 104) else (if i.val < 1642 then (45, 14) else (11, 228))) else (if i.val < 1645 then (if i.val < 1644 then (105, 48) else (143, 113)) else (if i.val < 1646 then (140, 171) else (7, 171)))))) else (if i.val < 1660 then (if i.val < 1653 then (if i.val < 1650 then (if i.val < 1648 then (91, 64) else (if i.val < 1649 then (61, 66) else (119, 81))) else (if i.val < 1651 then (133, 133) else (if i.val < 1652 then (106, 111) else (102, 224)))) else (if i.val < 1656 then (if i.val < 1654 then (119, 133) else (if i.val < 1655 then (47, 166) else (88, 210))) else (if i.val < 1658 then (if i.val < 1657 then (127, 221) else (140, 63)) else (if i.val < 1659 then (118, 246) else (69, 144))))) else (if i.val < 1667 then (if i.val < 1663 then (if i.val < 1661 then (49, 124) else (if i.val < 1662 then (51, 99) else (0, 153))) else (if i.val < 1665 then (if i.val < 1664 then (37, 147) else (105, 235)) else (if i.val < 1666 then (60, 204) else (107, 145)))) else (if i.val < 1670 then (if i.val < 1668 then (55, 37) else (if i.val < 1669 then (140, 81) else (109, 86))) else (if i.val < 1672 then (if i.val < 1671 then (133, 107) else (92, 35)) else (if i.val < 1673 then (83, 225) else (125, 188))))))) else (if i.val < 1701 then (if i.val < 1687 then (if i.val < 1680 then (if i.val < 1677 then (if i.val < 1675 then (90, 61) else (if i.val < 1676 then (28, 5) else (13, 244))) else (if i.val < 1678 then (133, 36) else (if i.val < 1679 then (11, 55) else (113, 133)))) else (if i.val < 1683 then (if i.val < 1681 then (60, 77) else (if i.val < 1682 then (116, 245) else (108, 66))) else (if i.val < 1685 then (if i.val < 1684 then (117, 33) else (45, 139)) else (if i.val < 1686 then (108, 48) else (70, 26))))) else (if i.val < 1694 then (if i.val < 1690 then (if i.val < 1688 then (136, 174) else (if i.val < 1689 then (87, 178) else (51, 188))) else (if i.val < 1692 then (if i.val < 1691 then (41, 33) else (60, 200)) else (if i.val < 1693 then (140, 242) else (94, 17)))) else (if i.val < 1697 then (if i.val < 1695 then (12, 4) else (if i.val < 1696 then (19, 84) else (93, 184))) else (if i.val < 1699 then (if i.val < 1698 then (67, 109) else (62, 217)) else (if i.val < 1700 then (143, 24) else (100, 195)))))) else (if i.val < 1714 then (if i.val < 1707 then (if i.val < 1704 then (if i.val < 1702 then (23, 63) else (if i.val < 1703 then (73, 194) else (138, 136))) else (if i.val < 1705 then (11, 242) else (if i.val < 1706 then (115, 168) else (101, 254)))) else (if i.val < 1710 then (if i.val < 1708 then (133, 190) else (if i.val < 1709 then (67, 9) else (130, 196))) else (if i.val < 1712 then (if i.val < 1711 then (137, 191) else (89, 241)) else (if i.val < 1713 then (116, 15) else (66, 119))))) else (if i.val < 1721 then (if i.val < 1717 then (if i.val < 1715 then (45, 71) else (if i.val < 1716 then (102, 229) else (136, 244))) else (if i.val < 1719 then (if i.val < 1718 then (106, 40) else (7, 49)) else (if i.val < 1720 then (88, 69) else (129, 240)))) else (if i.val < 1724 then (if i.val < 1722 then (116, 94) else (if i.val < 1723 then (44, 166) else (19, 5))) else (if i.val < 1726 then (if i.val < 1725 then (88, 72) else (47, 85)) else (if i.val < 1727 then (4, 107) else (113, 194)))))))))))) else (if i.val < 2592 then (if i.val < 2160 then (if i.val < 1944 then (if i.val < 1836 then (if i.val < 1782 then (if i.val < 1755 then (if i.val < 1741 then (if i.val < 1734 then (if i.val < 1731 then (if i.val < 1729 then (78, 144) else (if i.val < 1730 then (26, 81) else (139, 162))) else (if i.val < 1732 then (95, 13) else (if i.val < 1733 then (142, 160) else (66, 93)))) else (if i.val < 1737 then (if i.val < 1735 then (140, 36) else (if i.val < 1736 then (108, 56) else (26, 103))) else (if i.val < 1739 then (if i.val < 1738 then (29, 0) else (109, 54)) else (if i.val < 1740 then (138, 124) else (139, 183))))) else (if i.val < 1748 then (if i.val < 1744 then (if i.val < 1742 then (137, 151) else (if i.val < 1743 then (118, 179) else (77, 149))) else (if i.val < 1746 then (if i.val < 1745 then (128, 150) else (68, 92)) else (if i.val < 1747 then (101, 187) else (134, 36)))) else (if i.val < 1751 then (if i.val < 1749 then (93, 5) else (if i.val < 1750 then (122, 246) else (71, 105))) else (if i.val < 1753 then (if i.val < 1752 then (114, 147) else (23, 189)) else (if i.val < 1754 then (100, 162) else (24, 84)))))) else (if i.val < 1768 then (if i.val < 1761 then (if i.val < 1758 then (if i.val < 1756 then (12, 179) else (if i.val < 1757 then (53, 133) else (111, 2))) else (if i.val < 1759 then (90, 249) else (if i.val < 1760 then (67, 236) else (79, 97)))) else (if i.val < 1764 then (if i.val < 1762 then (133, 23) else (if i.val < 1763 then (96, 131) else (1, 76))) else (if i.val < 1766 then (if i.val < 1765 then (97, 150) else (131, 9)) else (if i.val < 1767 then (38, 171) else (80, 76))))) else (if i.val < 1775 then (if i.val < 1771 then (if i.val < 1769 then (34, 116) else (if i.val < 1770 then (14, 7) else (84, 118))) else (if i.val < 1773 then (if i.val < 1772 then (134, 132) else (62, 69)) else (if i.val < 1774 then (90, 211) else (104, 6)))) else (if i.val < 1778 then (if i.val < 1776 then (105, 179) else (if i.val < 1777 then (80, 6) else (96, 92))) else (if i.val < 1780 then (if i.val < 1779 then (85, 68) else (37, 98)) else (if i.val < 1781 then (136, 70) else (121, 209))))))) else (if i.val < 1809 then (if i.val < 1795 then (if i.val < 1788 then (if i.val < 1785 then (if i.val < 1783 then (38, 42) else (if i.val < 1784 then (117, 180) else (4, 225))) else (if i.val < 1786 then (79, 251) else (if i.val < 1787 then (110, 86) else (34, 37)))) else (if i.val < 1791 then (if i.val < 1789 then (25, 145) else (if i.val < 1790 then (114, 172) else (99, 113))) else (if i.val < 1793 then (if i.val < 1792 then (4, 219) else (19, 95)) else (if i.val < 1794 then (105, 160) else (137, 203))))) else (if i.val < 1802 then (if i.val < 1798 then (if i.val < 1796 then (89, 69) else (if i.val < 1797 then (59, 86) else (64, 76))) else (if i.val < 1800 then (if i.val < 1799 then (119, 0) else (91, 44)) else (if i.val < 1801 then (136, 119) else (119, 116)))) else (if i.val < 1805 then (if i.val < 1803 then (117, 140) else (if i.val < 1804 then (87, 38) else (77, 151))) else (if i.val < 1807 then (if i.val < 1806 then (60, 82) else (125, 186)) else (if i.val < 1808 then (85, 194) else (117, 196)))))) else (if i.val < 1822 then (if i.val < 1815 then (if i.val < 1812 then (if i.val < 1810 then (62, 62) else (if i.val < 1811 then (117, 151) else (73, 24))) else (if i.val < 1813 then (60, 151) else (if i.val < 1814 then (139, 154) else (110, 1)))) else (if i.val < 1818 then (if i.val < 1816 then (142, 215) else (if i.val < 1817 then (25, 44) else (5, 106))) else (if i.val < 1820 then (if i.val < 1819 then (84, 160) else (134, 116)) else (if i.val < 1821 then (108, 146) else (127, 131))))) else (if i.val < 1829 then (if i.val < 1825 then (if i.val < 1823 then (141, 246) else (if i.val < 1824 then (128, 110) else (136, 194))) else (if i.val < 1827 then (if i.val < 1826 then (144, 223) else (87, 145)) else (if i.val < 1828 then (114, 242) else (128, 158)))) else (if i.val < 1832 then (if i.val < 1830 then (36, 102) else (if i.val < 1831 then (53, 58) else (110, 101))) else (if i.val < 1834 then (if i.val < 1833 then (91, 93) else (89, 181)) else (if i.val < 1835 then (141, 58) else (141, 97)))))))) else (if i.val < 1890 then (if i.val < 1863 then (if i.val < 1849 then (if i.val < 1842 then (if i.val < 1839 then (if i.val < 1837 then (133, 188) else (if i.val < 1838 then (119, 40) else (132, 8))) else (if i.val < 1840 then (133, 81) else (if i.val < 1841 then (114, 58) else (104, 254)))) else (if i.val < 1845 then (if i.val < 1843 then (105, 209) else (if i.val < 1844 then (127, 135) else (129, 137))) else (if i.val < 1847 then (if i.val < 1846 then (124, 48) else (115, 61)) else (if i.val < 1848 then (50, 227) else (107, 171))))) else (if i.val < 1856 then (if i.val < 1852 then (if i.val < 1850 then (118, 109) else (if i.val < 1851 then (79, 71) else (129, 79))) else (if i.val < 1854 then (if i.val < 1853 then (66, 61) else (28, 77)) else (if i.val < 1855 then (92, 227) else (112, 12)))) else (if i.val < 1859 then (if i.val < 1857 then (50, 154) else (if i.val < 1858 then (53, 198) else (123, 113))) else (if i.val < 1861 then (if i.val < 1860 then (88, 213) else (138, 61)) else (if i.val < 1862 then (57, 52) else (144, 147)))))) else (if i.val < 1876 then (if i.val < 1869 then (if i.val < 1866 then (if i.val < 1864 then (0, 21) else (if i.val < 1865 then (77, 194) else (120, 174))) else (if i.val < 1867 then (16, 4) else (if i.val < 1868 then (19, 164) else (55, 214)))) else (if i.val < 1872 then (if i.val < 1870 then (13, 148) else (if i.val < 1871 then (54, 79) else (34, 52))) else (if i.val < 1874 then (if i.val < 1873 then (89, 115) else (139, 126)) else (if i.val < 1875 then (121, 89) else (91, 85))))) else (if i.val < 1883 then (if i.val < 1879 then (if i.val < 1877 then (5, 141) else (if i.val < 1878 then (144, 199) else (100, 34))) else (if i.val < 1881 then (if i.val < 1880 then (112, 77) else (36, 146)) else (if i.val < 1882 then (122, 100) else (126, 216)))) else (if i.val < 1886 then (if i.val < 1884 then (75, 227) else (if i.val < 1885 then (12, 110) else (18, 177))) else (if i.val < 1888 then (if i.val < 1887 then (137, 57) else (79, 207)) else (if i.val < 1889 then (141, 210) else (79, 12))))))) else (if i.val < 1917 then (if i.val < 1903 then (if i.val < 1896 then (if i.val < 1893 then (if i.val < 1891 then (108, 234) else (if i.val < 1892 then (100, 225) else (5, 137))) else (if i.val < 1894 then (62, 167) else (if i.val < 1895 then (16, 32) else (113, 23)))) else (if i.val < 1899 then (if i.val < 1897 then (139, 234) else (if i.val < 1898 then (133, 30) else (125, 158))) else (if i.val < 1901 then (if i.val < 1900 then (61, 204) else (0, 223)) else (if i.val < 1902 then (87, 0) else (136, 101))))) else (if i.val < 1910 then (if i.val < 1906 then (if i.val < 1904 then (9, 134) else (if i.val < 1905 then (141, 82) else (92, 75))) else (if i.val < 1908 then (if i.val < 1907 then (30, 152) else (30, 69)) else (if i.val < 1909 then (65, 83) else (105, 185)))) else (if i.val < 1913 then (if i.val < 1911 then (122, 81) else (if i.val < 1912 then (20, 212) else (120, 111))) else (if i.val < 1915 then (if i.val < 1914 then (111, 110) else (102, 76)) else (if i.val < 1916 then (61, 191) else (43, 83)))))) else (if i.val < 1930 then (if i.val < 1923 then (if i.val < 1920 then (if i.val < 1918 then (110, 130) else (if i.val < 1919 then (26, 97) else (115, 119))) else (if i.val < 1921 then (105, 103) else (if i.val < 1922 then (136, 48) else (143, 19)))) else (if i.val < 1926 then (if i.val < 1924 then (113, 46) else (if i.val < 1925 then (127, 36) else (59, 72))) else (if i.val < 1928 then (if i.val < 1927 then (89, 51) else (14, 242)) else (if i.val < 1929 then (115, 228) else (133, 200))))) else (if i.val < 1937 then (if i.val < 1933 then (if i.val < 1931 then (94, 194) else (if i.val < 1932 then (44, 247) else (5, 151))) else (if i.val < 1935 then (if i.val < 1934 then (72, 79) else (90, 13)) else (if i.val < 1936 then (50, 215) else (108, 119)))) else (if i.val < 1940 then (if i.val < 1938 then (5, 205) else (if i.val < 1939 then (57, 16) else (131, 192))) else (if i.val < 1942 then (if i.val < 1941 then (93, 153) else (109, 254)) else (if i.val < 1943 then (142, 255) else (140, 247))))))))) else (if i.val < 2052 then (if i.val < 1998 then (if i.val < 1971 then (if i.val < 1957 then (if i.val < 1950 then (if i.val < 1947 then (if i.val < 1945 then (68, 241) else (if i.val < 1946 then (128, 42) else (142, 183))) else (if i.val < 1948 then (111, 90) else (if i.val < 1949 then (79, 134) else (90, 231)))) else (if i.val < 1953 then (if i.val < 1951 then (126, 186) else (if i.val < 1952 then (29, 147) else (5, 59))) else (if i.val < 1955 then (if i.val < 1954 then (82, 152) else (85, 107)) else (if i.val < 1956 then (100, 198) else (116, 43))))) else (if i.val < 1964 then (if i.val < 1960 then (if i.val < 1958 then (120, 107) else (if i.val < 1959 then (93, 57) else (140, 185))) else (if i.val < 1962 then (if i.val < 1961 then (93, 124) else (129, 16)) else (if i.val < 1963 then (84, 30) else (90, 101)))) else (if i.val < 1967 then (if i.val < 1965 then (119, 11) else (if i.val < 1966 then (122, 248) else (108, 129))) else (if i.val < 1969 then (if i.val < 1968 then (88, 101) else (134, 109)) else (if i.val < 1970 then (143, 49) else (65, 67)))))) else (if i.val < 1984 then (if i.val < 1977 then (if i.val < 1974 then (if i.val < 1972 then (120, 181) else (if i.val < 1973 then (6, 58) else (132, 44))) else (if i.val < 1975 then (79, 145) else (if i.val < 1976 then (117, 182) else (25, 140)))) else (if i.val < 1980 then (if i.val < 1978 then (63, 106) else (if i.val < 1979 then (70, 151) else (107, 166))) else (if i.val < 1982 then (if i.val < 1981 then (60, 52) else (64, 10)) else (if i.val < 1983 then (107, 29) else (112, 35))))) else (if i.val < 1991 then (if i.val < 1987 then (if i.val < 1985 then (144, 200) else (if i.val < 1986 then (109, 67) else (133, 206))) else (if i.val < 1989 then (if i.val < 1988 then (29, 157) else (40, 149)) else (if i.val < 1990 then (141, 4) else (112, 164)))) else (if i.val < 1994 then (if i.val < 1992 then (113, 155) else (if i.val < 1993 then (103, 152) else (133, 121))) else (if i.val < 1996 then (if i.val < 1995 then (35, 28) else (52, 21)) else (if i.val < 1997 then (53, 31) else (117, 142))))))) else (if i.val < 2025 then (if i.val < 2011 then (if i.val < 2004 then (if i.val < 2001 then (if i.val < 1999 then (121, 119) else (if i.val < 2000 then (128, 249) else (90, 150))) else (if i.val < 2002 then (40, 18) else (if i.val < 2003 then (125, 136) else (79, 222)))) else (if i.val < 2007 then (if i.val < 2005 then (6, 236) else (if i.val < 2006 then (128, 208) else (132, 107))) else (if i.val < 2009 then (if i.val < 2008 then (33, 207) else (69, 252)) else (if i.val < 2010 then (94, 219) else (105, 192))))) else (if i.val < 2018 then (if i.val < 2014 then (if i.val < 2012 then (94, 185) else (if i.val < 2013 then (100, 29) else (110, 13))) else (if i.val < 2016 then (if i.val < 2015 then (73, 142) else (122, 69)) else (if i.val < 2017 then (97, 248) else (31, 115)))) else (if i.val < 2021 then (if i.val < 2019 then (108, 152) else (if i.val < 2020 then (88, 47) else (74, 5))) else (if i.val < 2023 then (if i.val < 2022 then (91, 12) else (115, 203)) else (if i.val < 2024 then (119, 107) else (74, 106)))))) else (if i.val < 2038 then (if i.val < 2031 then (if i.val < 2028 then (if i.val < 2026 then (138, 156) else (if i.val < 2027 then (48, 247) else (134, 187))) else (if i.val < 2029 then (124, 55) else (if i.val < 2030 then (50, 255) else (123, 181)))) else (if i.val < 2034 then (if i.val < 2032 then (75, 155) else (if i.val < 2033 then (26, 179) else (116, 175))) else (if i.val < 2036 then (if i.val < 2035 then (73, 0) else (136, 125)) else (if i.val < 2037 then (26, 216) else (108, 85))))) else (if i.val < 2045 then (if i.val < 2041 then (if i.val < 2039 then (110, 91) else (if i.val < 2040 then (125, 204) else (129, 196))) else (if i.val < 2043 then (if i.val < 2042 then (61, 93) else (125, 67)) else (if i.val < 2044 then (113, 100) else (102, 239)))) else (if i.val < 2048 then (if i.val < 2046 then (38, 92) else (if i.val < 2047 then (5, 22) else (41, 7))) else (if i.val < 2050 then (if i.val < 2049 then (97, 177) else (68, 20)) else (if i.val < 2051 then (124, 155) else (144, 4)))))))) else (if i.val < 2106 then (if i.val < 2079 then (if i.val < 2065 then (if i.val < 2058 then (if i.val < 2055 then (if i.val < 2053 then (115, 130) else (if i.val < 2054 then (12, 120) else (10, 151))) else (if i.val < 2056 then (113, 154) else (if i.val < 2057 then (20, 76) else (82, 26)))) else (if i.val < 2061 then (if i.val < 2059 then (87, 27) else (if i.val < 2060 then (20, 94) else (87, 46))) else (if i.val < 2063 then (if i.val < 2062 then (104, 71) else (20, 183)) else (if i.val < 2064 then (54, 126) else (74, 151))))) else (if i.val < 2072 then (if i.val < 2068 then (if i.val < 2066 then (143, 3) else (if i.val < 2067 then (124, 91) else (129, 14))) else (if i.val < 2070 then (if i.val < 2069 then (97, 108) else (50, 174)) else (if i.val < 2071 then (81, 190) else (114, 83)))) else (if i.val < 2075 then (if i.val < 2073 then (91, 169) else (if i.val < 2074 then (143, 48) else (126, 46))) else (if i.val < 2077 then (if i.val < 2076 then (143, 151) else (140, 109)) else (if i.val < 2078 then (12, 84) else (86, 254)))))) else (if i.val < 2092 then (if i.val < 2085 then (if i.val < 2082 then (if i.val < 2080 then (103, 111) else (if i.val < 2081 then (53, 197) else (71, 128))) else (if i.val < 2083 then (89, 25) else (if i.val < 2084 then (102, 171) else (108, 69)))) else (if i.val < 2088 then (if i.val < 2086 then (8, 37) else (if i.val < 2087 then (7, 214) else (3, 210))) else (if i.val < 2090 then (if i.val < 2089 then (9, 124) else (86, 76)) else (if i.val < 2091 then (132, 168) else (9, 93))))) else (if i.val < 2099 then (if i.val < 2095 then (if i.val < 2093 then (53, 123) else (if i.val < 2094 then (122, 54) else (21, 197))) else (if i.val < 2097 then (if i.val < 2096 then (69, 157) else (115, 215)) else (if i.val < 2098 then (116, 204) else (124, 113)))) else (if i.val < 2102 then (if i.val < 2100 then (103, 233) else (if i.val < 2101 then (132, 145) else (95, 214))) else (if i.val < 2104 then (if i.val < 2103 then (7, 199) else (16, 144)) else (if i.val < 2105 then (76, 135) else (140, 226))))))) else (if i.val < 2133 then (if i.val < 2119 then (if i.val < 2112 then (if i.val < 2109 then (if i.val < 2107 then (132, 200) else (if i.val < 2108 then (91, 134) else (92, 252))) else (if i.val < 2110 then (123, 65) else (if i.val < 2111 then (128, 165) else (114, 90)))) else (if i.val < 2115 then (if i.val < 2113 then (134, 102) else (if i.val < 2114 then (73, 20) else (114, 49))) else (if i.val < 2117 then (if i.val < 2116 then (90, 239) else (142, 94)) else (if i.val < 2118 then (52, 135) else (134, 118))))) else (if i.val < 2126 then (if i.val < 2122 then (if i.val < 2120 then (121, 9) else (if i.val < 2121 then (131, 213) else (130, 81))) else (if i.val < 2124 then (if i.val < 2123 then (83, 208) else (103, 116)) else (if i.val < 2125 then (139, 113) else (125, 209)))) else (if i.val < 2129 then (if i.val < 2127 then (113, 15) else (if i.val < 2128 then (27, 15) else (45, 143))) else (if i.val < 2131 then (if i.val < 2130 then (85, 53) else (140, 6)) else (if i.val < 2132 then (22, 153) else (97, 103)))))) else (if i.val < 2146 then (if i.val < 2139 then (if i.val < 2136 then (if i.val < 2134 then (19, 159) else (if i.val < 2135 then (71, 97) else (76, 97))) else (if i.val < 2137 then (102, 248) else (if i.val < 2138 then (127, 231) else (68, 32)))) else (if i.val < 2142 then (if i.val < 2140 then (41, 133) else (if i.val < 2141 then (71, 79) else (104, 45))) else (if i.val < 2144 then (if i.val < 2143 then (139, 14) else (96, 206)) else (if i.val < 2145 then (126, 160) else (129, 128))))) else (if i.val < 2153 then (if i.val < 2149 then (if i.val < 2147 then (139, 38) else (if i.val < 2148 then (128, 78) else (23, 88))) else (if i.val < 2151 then (if i.val < 2150 then (73, 159) else (129, 183)) else (if i.val < 2152 then (84, 29) else (82, 59)))) else (if i.val < 2156 then (if i.val < 2154 then (86, 97) else (if i.val < 2155 then (45, 231) else (97, 183))) else (if i.val < 2158 then (if i.val < 2157 then (97, 221) else (89, 246)) else (if i.val < 2159 then (128, 234) else (117, 29)))))))))) else (if i.val < 2376 then (if i.val < 2268 then (if i.val < 2214 then (if i.val < 2187 then (if i.val < 2173 then (if i.val < 2166 then (if i.val < 2163 then (if i.val < 2161 then (128, 72) else (if i.val < 2162 then (130, 22) else (116, 216))) else (if i.val < 2164 then (142, 139) else (if i.val < 2165 then (129, 143) else (122, 212)))) else (if i.val < 2169 then (if i.val < 2167 then (49, 162) else (if i.val < 2168 then (99, 55) else (124, 160))) else (if i.val < 2171 then (if i.val < 2170 then (138, 121) else (131, 136)) else (if i.val < 2172 then (90, 48) else (113, 244))))) else (if i.val < 2180 then (if i.val < 2176 then (if i.val < 2174 then (112, 45) else (if i.val < 2175 then (69, 20) else (141, 160))) else (if i.val < 2178 then (if i.val < 2177 then (127, 234) else (131, 242)) else (if i.val < 2179 then (112, 119) else (28, 26)))) else (if i.val < 2183 then (if i.val < 2181 then (79, 73) else (if i.val < 2182 then (33, 144) else (99, 96))) else (if i.val < 2185 then (if i.val < 2184 then (82, 71) else (14, 157)) else (if i.val < 2186 then (56, 39) else (85, 113)))))) else (if i.val < 2200 then (if i.val < 2193 then (if i.val < 2190 then (if i.val < 2188 then (83, 85) else (if i.val < 2189 then (142, 62) else (113, 226))) else (if i.val < 2191 then (126, 123) else (if i.val < 2192 then (83, 89) else (83, 53)))) else (if i.val < 2196 then (if i.val < 2194 then (131, 49) else (if i.val < 2195 then (141, 36) else (138, 33))) else (if i.val < 2198 then (if i.val < 2197 then (125, 203) else (78, 241)) else (if i.val < 2199 then (21, 167) else (77, 45))))) else (if i.val < 2207 then (if i.val < 2203 then (if i.val < 2201 then (113, 135) else (if i.val < 2202 then (30, 171) else (137, 237))) else (if i.val < 2205 then (if i.val < 2204 then (38, 209) else (74, 61)) else (if i.val < 2206 then (61, 99) else (57, 164)))) else (if i.val < 2210 then (if i.val < 2208 then (54, 177) else (if i.val < 2209 then (115, 84) else (133, 5))) else (if i.val < 2212 then (if i.val < 2211 then (54, 204) else (141, 3)) else (if i.val < 2213 then (123, 146) else (76, 152))))))) else (if i.val < 2241 then (if i.val < 2227 then (if i.val < 2220 then (if i.val < 2217 then (if i.val < 2215 then (37, 110) else (if i.val < 2216 then (95, 233) else (114, 0))) else (if i.val < 2218 then (126, 227) else (if i.val < 2219 then (125, 215) else (54, 87)))) else (if i.val < 2223 then (if i.val < 2221 then (54, 178) else (if i.val < 2222 then (91, 43) else (57, 115))) else (if i.val < 2225 then (if i.val < 2224 then (136, 250) else (47, 146)) else (if i.val < 2226 then (57, 70) else (68, 5))))) else (if i.val < 2234 then (if i.val < 2230 then (if i.val < 2228 then (137, 196) else (if i.val < 2229 then (130, 4) else (34, 180))) else (if i.val < 2232 then (if i.val < 2231 then (85, 186) else (76, 112)) else (if i.val < 2233 then (32, 214) else (90, 26)))) else (if i.val < 2237 then (if i.val < 2235 then (82, 234) else (if i.val < 2236 then (56, 8) else (106, 100))) else (if i.val < 2239 then (if i.val < 2238 then (131, 247) else (104, 3)) else (if i.val < 2240 then (129, 30) else (53, 146)))))) else (if i.val < 2254 then (if i.val < 2247 then (if i.val < 2244 then (if i.val < 2242 then (29, 235) else (if i.val < 2243 then (129, 200) else (5, 71))) else (if i.val < 2245 then (124, 37) else (if i.val < 2246 then (110, 52) else (81, 247)))) else (if i.val < 2250 then (if i.val < 2248 then (128, 225) else (if i.val < 2249 then (142, 91) else (132, 103))) else (if i.val < 2252 then (if i.val < 2251 then (126, 159) else (48, 215)) else (if i.val < 2253 then (141, 31) else (137, 189))))) else (if i.val < 2261 then (if i.val < 2257 then (if i.val < 2255 then (37, 13) else (if i.val < 2256 then (64, 99) else (144, 176))) else (if i.val < 2259 then (if i.val < 2258 then (143, 242) else (113, 0)) else (if i.val < 2260 then (63, 43) else (76, 205)))) else (if i.val < 2264 then (if i.val < 2262 then (86, 5) else (if i.val < 2263 then (80, 196) else (17, 160))) else (if i.val < 2266 then (if i.val < 2265 then (142, 65) else (27, 187)) else (if i.val < 2267 then (136, 116) else (132, 153)))))))) else (if i.val < 2322 then (if i.val < 2295 then (if i.val < 2281 then (if i.val < 2274 then (if i.val < 2271 then (if i.val < 2269 then (133, 151) else (if i.val < 2270 then (93, 46) else (134, 5))) else (if i.val < 2272 then (97, 12) else (if i.val < 2273 then (141, 53) else (131, 82)))) else (if i.val < 2277 then (if i.val < 2275 then (88, 54) else (if i.val < 2276 then (69, 213) else (4, 17))) else (if i.val < 2279 then (if i.val < 2278 then (116, 255) else (53, 68)) else (if i.val < 2280 then (116, 118) else (55, 65))))) else (if i.val < 2288 then (if i.val < 2284 then (if i.val < 2282 then (91, 149) else (if i.val < 2283 then (117, 251) else (32, 174))) else (if i.val < 2286 then (if i.val < 2285 then (90, 64) else (138, 161)) else (if i.val < 2287 then (2, 129) else (34, 248)))) else (if i.val < 2291 then (if i.val < 2289 then (131, 239) else (if i.val < 2290 then (116, 54) else (57, 136))) else (if i.val < 2293 then (if i.val < 2292 then (124, 145) else (82, 230)) else (if i.val < 2294 then (112, 131) else (17, 251)))))) else (if i.val < 2308 then (if i.val < 2301 then (if i.val < 2298 then (if i.val < 2296 then (105, 121) else (if i.val < 2297 then (135, 228) else (61, 156))) else (if i.val < 2299 then (86, 206) else (if i.val < 2300 then (122, 77) else (117, 114)))) else (if i.val < 2304 then (if i.val < 2302 then (101, 16) else (if i.val < 2303 then (134, 48) else (70, 162))) else (if i.val < 2306 then (if i.val < 2305 then (69, 87) else (35, 6)) else (if i.val < 2307 then (77, 150) else (11, 16))))) else (if i.val < 2315 then (if i.val < 2311 then (if i.val < 2309 then (69, 109) else (if i.val < 2310 then (79, 181) else (4, 108))) else (if i.val < 2313 then (if i.val < 2312 then (14, 95) else (66, 161)) else (if i.val < 2314 then (101, 179) else (131, 13)))) else (if i.val < 2318 then (if i.val < 2316 then (14, 93) else (if i.val < 2317 then (124, 122) else (136, 203))) else (if i.val < 2320 then (if i.val < 2319 then (138, 140) else (73, 250)) else (if i.val < 2321 then (115, 201) else (85, 78))))))) else (if i.val < 2349 then (if i.val < 2335 then (if i.val < 2328 then (if i.val < 2325 then (if i.val < 2323 then (58, 115) else (if i.val < 2324 then (6, 155) else (141, 183))) else (if i.val < 2326 then (80, 23) else (if i.val < 2327 then (33, 15) else (143, 119)))) else (if i.val < 2331 then (if i.val < 2329 then (3, 239) else (if i.val < 2330 then (103, 50) else (43, 34))) else (if i.val < 2333 then (if i.val < 2332 then (116, 53) else (41, 5)) else (if i.val < 2334 then (130, 98) else (134, 136))))) else (if i.val < 2342 then (if i.val < 2338 then (if i.val < 2336 then (33, 43) else (if i.val < 2337 then (124, 159) else (128, 20))) else (if i.val < 2340 then (if i.val < 2339 then (116, 73) else (136, 145)) else (if i.val < 2341 then (33, 52) else (58, 199)))) else (if i.val < 2345 then (if i.val < 2343 then (138, 181) else (if i.val < 2344 then (141, 213) else (133, 8))) else (if i.val < 2347 then (if i.val < 2346 then (77, 130) else (40, 169)) else (if i.val < 2348 then (72, 57) else (118, 79)))))) else (if i.val < 2362 then (if i.val < 2355 then (if i.val < 2352 then (if i.val < 2350 then (71, 58) else (if i.val < 2351 then (125, 129) else (14, 97))) else (if i.val < 2353 then (102, 103) else (if i.val < 2354 then (37, 99) else (120, 236)))) else (if i.val < 2358 then (if i.val < 2356 then (144, 206) else (if i.val < 2357 then (25, 0) else (126, 120))) else (if i.val < 2360 then (if i.val < 2359 then (74, 105) else (109, 42)) else (if i.val < 2361 then (131, 195) else (33, 111))))) else (if i.val < 2369 then (if i.val < 2365 then (if i.val < 2363 then (59, 1) else (if i.val < 2364 then (14, 88) else (47, 47))) else (if i.val < 2367 then (if i.val < 2366 then (56, 110) else (54, 175)) else (if i.val < 2368 then (87, 6) else (141, 166)))) else (if i.val < 2372 then (if i.val < 2370 then (139, 97) else (if i.val < 2371 then (81, 198) else (71, 98))) else (if i.val < 2374 then (if i.val < 2373 then (108, 67) else (69, 18)) else (if i.val < 2375 then (92, 163) else (92, 45))))))))) else (if i.val < 2484 then (if i.val < 2430 then (if i.val < 2403 then (if i.val < 2389 then (if i.val < 2382 then (if i.val < 2379 then (if i.val < 2377 then (110, 218) else (if i.val < 2378 then (144, 185) else (116, 18))) else (if i.val < 2380 then (104, 98) else (if i.val < 2381 then (47, 160) else (124, 101)))) else (if i.val < 2385 then (if i.val < 2383 then (76, 6) else (if i.val < 2384 then (130, 53) else (76, 75))) else (if i.val < 2387 then (if i.val < 2386 then (56, 124) else (131, 27)) else (if i.val < 2388 then (49, 143) else (109, 233))))) else (if i.val < 2396 then (if i.val < 2392 then (if i.val < 2390 then (108, 211) else (if i.val < 2391 then (15, 23) else (80, 106))) else (if i.val < 2394 then (if i.val < 2393 then (93, 240) else (132, 245)) else (if i.val < 2395 then (92, 233) else (5, 194)))) else (if i.val < 2399 then (if i.val < 2397 then (127, 148) else (if i.val < 2398 then (9, 235) else (113, 208))) else (if i.val < 2401 then (if i.val < 2400 then (144, 172) else (53, 65)) else (if i.val < 2402 then (41, 187) else (31, 201)))))) else (if i.val < 2416 then (if i.val < 2409 then (if i.val < 2406 then (if i.val < 2404 then (98, 137) else (if i.val < 2405 then (6, 186) else (113, 248))) else (if i.val < 2407 then (10, 50) else (if i.val < 2408 then (126, 201) else (109, 228)))) else (if i.val < 2412 then (if i.val < 2410 then (78, 136) else (if i.val < 2411 then (48, 252) else (53, 19))) else (if i.val < 2414 then (if i.val < 2413 then (34, 98) else (105, 138)) else (if i.val < 2415 then (37, 186) else (52, 40))))) else (if i.val < 2423 then (if i.val < 2419 then (if i.val < 2417 then (48, 255) else (if i.val < 2418 then (126, 4) else (94, 207))) else (if i.val < 2421 then (if i.val < 2420 then (103, 126) else (42, 92)) else (if i.val < 2422 then (127, 240) else (43, 175)))) else (if i.val < 2426 then (if i.val < 2424 then (53, 78) else (if i.val < 2425 then (114, 24) else (92, 79))) else (if i.val < 2428 then (if i.val < 2427 then (113, 243) else (102, 246)) else (if i.val < 2429 then (111, 8) else (141, 205))))))) else (if i.val < 2457 then (if i.val < 2443 then (if i.val < 2436 then (if i.val < 2433 then (if i.val < 2431 then (112, 143) else (if i.val < 2432 then (105, 231) else (30, 169))) else (if i.val < 2434 then (47, 64) else (if i.val < 2435 then (54, 212) else (35, 194)))) else (if i.val < 2439 then (if i.val < 2437 then (109, 113) else (if i.val < 2438 then (70, 81) else (80, 179))) else (if i.val < 2441 then (if i.val < 2440 then (135, 169) else (93, 15)) else (if i.val < 2442 then (59, 185) else (20, 87))))) else (if i.val < 2450 then (if i.val < 2446 then (if i.val < 2444 then (136, 76) else (if i.val < 2445 then (56, 136) else (109, 221))) else (if i.val < 2448 then (if i.val < 2447 then (5, 196) else (9, 253)) else (if i.val < 2449 then (52, 131) else (31, 202)))) else (if i.val < 2453 then (if i.val < 2451 then (107, 96) else (if i.val < 2452 then (6, 203) else (3, 8))) else (if i.val < 2455 then (if i.val < 2454 then (108, 194) else (115, 127)) else (if i.val < 2456 then (89, 105) else (12, 243)))))) else (if i.val < 2470 then (if i.val < 2463 then (if i.val < 2460 then (if i.val < 2458 then (63, 226) else (if i.val < 2459 then (37, 154) else (30, 130))) else (if i.val < 2461 then (117, 233) else (if i.val < 2462 then (37, 63) else (89, 222)))) else (if i.val < 2466 then (if i.val < 2464 then (14, 138) else (if i.val < 2465 then (12, 242) else (42, 123))) else (if i.val < 2468 then (if i.val < 2467 then (113, 120) else (91, 46)) else (if i.val < 2469 then (37, 188) else (64, 241))))) else (if i.val < 2477 then (if i.val < 2473 then (if i.val < 2471 then (38, 191) else (if i.val < 2472 then (122, 232) else (80, 34))) else (if i.val < 2475 then (if i.val < 2474 then (28, 221) else (112, 168)) else (if i.val < 2476 then (18, 198) else (116, 221)))) else (if i.val < 2480 then (if i.val < 2478 then (137, 18) else (if i.val < 2479 then (104, 41) else (14, 206))) else (if i.val < 2482 then (if i.val < 2481 then (26, 34) else (105, 152)) else (if i.val < 2483 then (92, 239) else (29, 3)))))))) else (if i.val < 2538 then (if i.val < 2511 then (if i.val < 2497 then (if i.val < 2490 then (if i.val < 2487 then (if i.val < 2485 then (105, 66) else (if i.val < 2486 then (16, 29) else (6, 195))) else (if i.val < 2488 then (104, 7) else (if i.val < 2489 then (68, 130) else (5, 58)))) else (if i.val < 2493 then (if i.val < 2491 then (11, 19) else (if i.val < 2492 then (103, 24) else (130, 206))) else (if i.val < 2495 then (if i.val < 2494 then (79, 9) else (30, 211)) else (if i.val < 2496 then (1, 85) else (112, 23))))) else (if i.val < 2504 then (if i.val < 2500 then (if i.val < 2498 then (127, 178) else (if i.val < 2499 then (124, 229) else (87, 43))) else (if i.val < 2502 then (if i.val < 2501 then (107, 198) else (90, 55)) else (if i.val < 2503 then (54, 35) else (5, 158)))) else (if i.val < 2507 then (if i.val < 2505 then (77, 78) else (if i.val < 2506 then (41, 60) else (111, 236))) else (if i.val < 2509 then (if i.val < 2508 then (105, 15) else (127, 194)) else (if i.val < 2510 then (111, 244) else (103, 28)))))) else (if i.val < 2524 then (if i.val < 2517 then (if i.val < 2514 then (if i.val < 2512 then (55, 4) else (if i.val < 2513 then (76, 20) else (66, 190))) else (if i.val < 2515 then (62, 43) else (if i.val < 2516 then (135, 129) else (91, 241)))) else (if i.val < 2520 then (if i.val < 2518 then (94, 5) else (if i.val < 2519 then (109, 52) else (139, 157))) else (if i.val < 2522 then (if i.val < 2521 then (107, 68) else (141, 145)) else (if i.val < 2523 then (90, 128) else (56, 132))))) else (if i.val < 2531 then (if i.val < 2527 then (if i.val < 2525 then (50, 170) else (if i.val < 2526 then (82, 187) else (69, 33))) else (if i.val < 2529 then (if i.val < 2528 then (98, 232) else (50, 76)) else (if i.val < 2530 then (106, 175) else (38, 204)))) else (if i.val < 2534 then (if i.val < 2532 then (83, 19) else (if i.val < 2533 then (79, 166) else (83, 74))) else (if i.val < 2536 then (if i.val < 2535 then (45, 36) else (115, 23)) else (if i.val < 2537 then (28, 58) else (33, 53))))))) else (if i.val < 2565 then (if i.val < 2551 then (if i.val < 2544 then (if i.val < 2541 then (if i.val < 2539 then (129, 61) else (if i.val < 2540 then (81, 228) else (83, 132))) else (if i.val < 2542 then (43, 227) else (if i.val < 2543 then (90, 83) else (116, 174)))) else (if i.val < 2547 then (if i.val < 2545 then (120, 7) else (if i.val < 2546 then (13, 141) else (15, 61))) else (if i.val < 2549 then (if i.val < 2548 then (106, 211) else (64, 193)) else (if i.val < 2550 then (129, 98) else (144, 101))))) else (if i.val < 2558 then (if i.val < 2554 then (if i.val < 2552 then (65, 124) else (if i.val < 2553 then (39, 93) else (59, 218))) else (if i.val < 2556 then (if i.val < 2555 then (61, 192) else (129, 249)) else (if i.val < 2557 then (83, 175) else (117, 121)))) else (if i.val < 2561 then (if i.val < 2559 then (7, 165) else (if i.val < 2560 then (48, 193) else (135, 151))) else (if i.val < 2563 then (if i.val < 2562 then (134, 196) else (107, 242)) else (if i.val < 2564 then (58, 62) else (19, 92)))))) else (if i.val < 2578 then (if i.val < 2571 then (if i.val < 2568 then (if i.val < 2566 then (141, 87) else (if i.val < 2567 then (98, 233) else (141, 176))) else (if i.val < 2569 then (142, 227) else (if i.val < 2570 then (88, 0) else (64, 88)))) else (if i.val < 2574 then (if i.val < 2572 then (9, 215) else (if i.val < 2573 then (53, 118) else (5, 79))) else (if i.val < 2576 then (if i.val < 2575 then (93, 109) else (14, 172)) else (if i.val < 2577 then (37, 156) else (112, 139))))) else (if i.val < 2585 then (if i.val < 2581 then (if i.val < 2579 then (21, 158) else (if i.val < 2580 then (72, 176) else (34, 8))) else (if i.val < 2583 then (if i.val < 2582 then (32, 72) else (10, 91)) else (if i.val < 2584 then (47, 247) else (87, 55)))) else (if i.val < 2588 then (if i.val < 2586 then (11, 241) else (if i.val < 2587 then (106, 83) else (86, 115))) else (if i.val < 2590 then (if i.val < 2589 then (73, 157) else (106, 90)) else (if i.val < 2591 then (65, 183) else (45, 239))))))))))) else (if i.val < 3024 then (if i.val < 2808 then (if i.val < 2700 then (if i.val < 2646 then (if i.val < 2619 then (if i.val < 2605 then (if i.val < 2598 then (if i.val < 2595 then (if i.val < 2593 then (105, 23) else (if i.val < 2594 then (49, 15) else (112, 20))) else (if i.val < 2596 then (115, 218) else (if i.val < 2597 then (20, 208) else (90, 131)))) else (if i.val < 2601 then (if i.val < 2599 then (109, 49) else (if i.val < 2600 then (5, 33) else (40, 67))) else (if i.val < 2603 then (if i.val < 2602 then (45, 179) else (57, 38)) else (if i.val < 2604 then (4, 67) else (138, 93))))) else (if i.val < 2612 then (if i.val < 2608 then (if i.val < 2606 then (139, 172) else (if i.val < 2607 then (60, 32) else (80, 69))) else (if i.val < 2610 then (if i.val < 2609 then (36, 157) else (130, 31)) else (if i.val < 2611 then (136, 26) else (73, 99)))) else (if i.val < 2615 then (if i.val < 2613 then (88, 105) else (if i.val < 2614 then (36, 74) else (129, 142))) else (if i.val < 2617 then (if i.val < 2616 then (110, 245) else (8, 125)) else (if i.val < 2618 then (92, 58) else (106, 186)))))) else (if i.val < 2632 then (if i.val < 2625 then (if i.val < 2622 then (if i.val < 2620 then (94, 67) else (if i.val < 2621 then (144, 188) else (142, 1))) else (if i.val < 2623 then (132, 150) else (if i.val < 2624 then (89, 208) else (125, 187)))) else (if i.val < 2628 then (if i.val < 2626 then (29, 49) else (if i.val < 2627 then (15, 91) else (141, 1))) else (if i.val < 2630 then (if i.val < 2629 then (21, 73) else (44, 117)) else (if i.val < 2631 then (70, 192) else (125, 212))))) else (if i.val < 2639 then (if i.val < 2635 then (if i.val < 2633 then (45, 163) else (if i.val < 2634 then (10, 62) else (48, 52))) else (if i.val < 2637 then (if i.val < 2636 then (32, 78) else (83, 77)) else (if i.val < 2638 then (84, 190) else (95, 123)))) else (if i.val < 2642 then (if i.val < 2640 then (135, 6) else (if i.val < 2641 then (71, 32) else (4, 33))) else (if i.val < 2644 then (if i.val < 2643 then (8, 99) else (89, 250)) else (if i.val < 2645 then (126, 185) else (94, 88))))))) else (if i.val < 2673 then (if i.val < 2659 then (if i.val < 2652 then (if i.val < 2649 then (if i.val < 2647 then (114, 246) else (if i.val < 2648 then (121, 174) else (102, 155))) else (if i.val < 2650 then (77, 214) else (if i.val < 2651 then (57, 243) else (34, 247)))) else (if i.val < 2655 then (if i.val < 2653 then (39, 152) else (if i.val < 2654 then (17, 115) else (87, 198))) else (if i.val < 2657 then (if i.val < 2656 then (79, 149) else (23, 13)) else (if i.val < 2658 then (130, 60) else (63, 174))))) else (if i.val < 2666 then (if i.val < 2662 then (if i.val < 2660 then (87, 221) else (if i.val < 2661 then (106, 4) else (109, 235))) else (if i.val < 2664 then (if i.val < 2663 then (32, 243) else (134, 195)) else (if i.val < 2665 then (130, 36) else (28, 188)))) else (if i.val < 2669 then (if i.val < 2667 then (89, 93) else (if i.val < 2668 then (133, 44) else (127, 245))) else (if i.val < 2671 then (if i.val < 2670 then (70, 164) else (111, 99)) else (if i.val < 2672 then (68, 71) else (34, 124)))))) else (if i.val < 2686 then (if i.val < 2679 then (if i.val < 2676 then (if i.val < 2674 then (104, 110) else (if i.val < 2675 then (133, 45) else (106, 142))) else (if i.val < 2677 then (116, 39) else (if i.val < 2678 then (67, 33) else (100, 9)))) else (if i.val < 2682 then (if i.val < 2680 then (80, 104) else (if i.val < 2681 then (38, 163) else (130, 45))) else (if i.val < 2684 then (if i.val < 2683 then (130, 82) else (65, 240)) else (if i.val < 2685 then (130, 64) else (109, 193))))) else (if i.val < 2693 then (if i.val < 2689 then (if i.val < 2687 then (33, 49) else (if i.val < 2688 then (103, 117) else (20, 126))) else (if i.val < 2691 then (if i.val < 2690 then (117, 49) else (132, 123)) else (if i.val < 2692 then (61, 25) else (33, 47)))) else (if i.val < 2696 then (if i.val < 2694 then (118, 100) else (if i.val < 2695 then (84, 32) else (135, 9))) else (if i.val < 2698 then (if i.val < 2697 then (28, 166) else (139, 158)) else (if i.val < 2699 then (117, 237) else (32, 234)))))))) else (if i.val < 2754 then (if i.val < 2727 then (if i.val < 2713 then (if i.val < 2706 then (if i.val < 2703 then (if i.val < 2701 then (132, 244) else (if i.val < 2702 then (141, 47) else (46, 154))) else (if i.val < 2704 then (103, 89) else (if i.val < 2705 then (64, 127) else (79, 67)))) else (if i.val < 2709 then (if i.val < 2707 then (92, 22) else (if i.val < 2708 then (54, 239) else (57, 206))) else (if i.val < 2711 then (if i.val < 2710 then (46, 41) else (140, 71)) else (if i.val < 2712 then (96, 104) else (141, 33))))) else (if i.val < 2720 then (if i.val < 2716 then (if i.val < 2714 then (3, 109) else (if i.val < 2715 then (58, 52) else (7, 212))) else (if i.val < 2718 then (if i.val < 2717 then (65, 180) else (140, 49)) else (if i.val < 2719 then (132, 48) else (94, 121)))) else (if i.val < 2723 then (if i.val < 2721 then (144, 202) else (if i.val < 2722 then (102, 33) else (116, 211))) else (if i.val < 2725 then (if i.val < 2724 then (64, 170) else (62, 173)) else (if i.val < 2726 then (86, 69) else (117, 205)))))) else (if i.val < 2740 then (if i.val < 2733 then (if i.val < 2730 then (if i.val < 2728 then (72, 146) else (if i.val < 2729 then (20, 172) else (113, 130))) else (if i.val < 2731 then (108, 7) else (if i.val < 2732 then (83, 191) else (143, 133)))) else (if i.val < 2736 then (if i.val < 2734 then (86, 247) else (if i.val < 2735 then (100, 166) else (84, 196))) else (if i.val < 2738 then (if i.val < 2737 then (93, 135) else (68, 56)) else (if i.val < 2739 then (92, 232) else (129, 244))))) else (if i.val < 2747 then (if i.val < 2743 then (if i.val < 2741 then (143, 55) else (if i.val < 2742 then (98, 157) else (117, 176))) else (if i.val < 2745 then (if i.val < 2744 then (140, 96) else (141, 46)) else (if i.val < 2746 then (89, 41) else (19, 81)))) else (if i.val < 2750 then (if i.val < 2748 then (23, 208) else (if i.val < 2749 then (123, 165) else (107, 65))) else (if i.val < 2752 then (if i.val < 2751 then (25, 115) else (117, 65)) else (if i.val < 2753 then (105, 248) else (45, 186))))))) else (if i.val < 2781 then (if i.val < 2767 then (if i.val < 2760 then (if i.val < 2757 then (if i.val < 2755 then (138, 152) else (if i.val < 2756 then (65, 230) else (54, 72))) else (if i.val < 2758 then (129, 1) else (if i.val < 2759 then (95, 135) else (140, 155)))) else (if i.val < 2763 then (if i.val < 2761 then (126, 64) else (if i.val < 2762 then (64, 135) else (106, 69))) else (if i.val < 2765 then (if i.val < 2764 then (97, 181) else (33, 21)) else (if i.val < 2766 then (32, 102) else (57, 134))))) else (if i.val < 2774 then (if i.val < 2770 then (if i.val < 2768 then (33, 193) else (if i.val < 2769 then (103, 15) else (19, 16))) else (if i.val < 2772 then (if i.val < 2771 then (64, 83) else (114, 77)) else (if i.val < 2773 then (129, 177) else (56, 143)))) else (if i.val < 2777 then (if i.val < 2775 then (65, 2) else (if i.val < 2776 then (95, 122) else (122, 209))) else (if i.val < 2779 then (if i.val < 2778 then (116, 48) else (95, 170)) else (if i.val < 2780 then (95, 252) else (40, 66)))))) else (if i.val < 2794 then (if i.val < 2787 then (if i.val < 2784 then (if i.val < 2782 then (24, 86) else (if i.val < 2783 then (141, 39) else (134, 173))) else (if i.val < 2785 then (142, 245) else (if i.val < 2786 then (140, 127) else (53, 20)))) else (if i.val < 2790 then (if i.val < 2788 then (74, 162) else (if i.val < 2789 then (33, 18) else (34, 165))) else (if i.val < 2792 then (if i.val < 2791 then (105, 39) else (117, 93)) else (if i.val < 2793 then (142, 22) else (94, 96))))) else (if i.val < 2801 then (if i.val < 2797 then (if i.val < 2795 then (102, 50) else (if i.val < 2796 then (98, 119) else (114, 152))) else (if i.val < 2799 then (if i.val < 2798 then (73, 119) else (123, 136)) else (if i.val < 2800 then (141, 56) else (86, 143)))) else (if i.val < 2804 then (if i.val < 2802 then (112, 242) else (if i.val < 2803 then (122, 220) else (130, 180))) else (if i.val < 2806 then (if i.val < 2805 then (105, 14) else (144, 132)) else (if i.val < 2807 then (97, 6) else (141, 21))))))))) else (if i.val < 2916 then (if i.val < 2862 then (if i.val < 2835 then (if i.val < 2821 then (if i.val < 2814 then (if i.val < 2811 then (if i.val < 2809 then (88, 43) else (if i.val < 2810 then (134, 168) else (139, 47))) else (if i.val < 2812 then (98, 251) else (if i.val < 2813 then (116, 125) else (122, 18)))) else (if i.val < 2817 then (if i.val < 2815 then (109, 157) else (if i.val < 2816 then (82, 233) else (88, 135))) else (if i.val < 2819 then (if i.val < 2818 then (123, 243) else (118, 181)) else (if i.val < 2820 then (84, 194) else (118, 129))))) else (if i.val < 2828 then (if i.val < 2824 then (if i.val < 2822 then (95, 114) else (if i.val < 2823 then (133, 55) else (42, 227))) else (if i.val < 2826 then (if i.val < 2825 then (72, 83) else (134, 124)) else (if i.val < 2827 then (141, 11) else (144, 128)))) else (if i.val < 2831 then (if i.val < 2829 then (118, 250) else (if i.val < 2830 then (135, 97) else (111, 27))) else (if i.val < 2833 then (if i.val < 2832 then (87, 108) else (89, 170)) else (if i.val < 2834 then (55, 220) else (59, 197)))))) else (if i.val < 2848 then (if i.val < 2841 then (if i.val < 2838 then (if i.val < 2836 then (136, 253) else (if i.val < 2837 then (144, 164) else (2, 19))) else (if i.val < 2839 then (121, 57) else (if i.val < 2840 then (88, 163) else (56, 5)))) else (if i.val < 2844 then (if i.val < 2842 then (121, 214) else (if i.val < 2843 then (136, 58) else (92, 118))) else (if i.val < 2846 then (if i.val < 2845 then (132, 239) else (123, 17)) else (if i.val < 2847 then (111, 221) else (141, 204))))) else (if i.val < 2855 then (if i.val < 2851 then (if i.val < 2849 then (111, 185) else (if i.val < 2850 then (33, 106) else (62, 34))) else (if i.val < 2853 then (if i.val < 2852 then (16, 12) else (60, 24)) else (if i.val < 2854 then (131, 126) else (90, 59)))) else (if i.val < 2858 then (if i.val < 2856 then (120, 56) else (if i.val < 2857 then (140, 132) else (122, 1))) else (if i.val < 2860 then (if i.val < 2859 then (60, 227) else (144, 173)) else (if i.val < 2861 then (135, 19) else (15, 128))))))) else (if i.val < 2889 then (if i.val < 2875 then (if i.val < 2868 then (if i.val < 2865 then (if i.val < 2863 then (112, 199) else (if i.val < 2864 then (75, 217) else (52, 213))) else (if i.val < 2866 then (32, 43) else (if i.val < 2867 then (119, 237) else (128, 185)))) else (if i.val < 2871 then (if i.val < 2869 then (35, 125) else (if i.val < 2870 then (57, 26) else (144, 2))) else (if i.val < 2873 then (if i.val < 2872 then (68, 39) else (114, 232)) else (if i.val < 2874 then (117, 173) else (93, 139))))) else (if i.val < 2882 then (if i.val < 2878 then (if i.val < 2876 then (88, 171) else (if i.val < 2877 then (19, 248) else (64, 126))) else (if i.val < 2880 then (if i.val < 2879 then (44, 15) else (76, 16)) else (if i.val < 2881 then (101, 144) else (97, 49)))) else (if i.val < 2885 then (if i.val < 2883 then (133, 34) else (if i.val < 2884 then (39, 19) else (35, 113))) else (if i.val < 2887 then (if i.val < 2886 then (52, 44) else (59, 118)) else (if i.val < 2888 then (131, 216) else (131, 206)))))) else (if i.val < 2902 then (if i.val < 2895 then (if i.val < 2892 then (if i.val < 2890 then (56, 252) else (if i.val < 2891 then (9, 248) else (135, 150))) else (if i.val < 2893 then (15, 118) else (if i.val < 2894 then (128, 86) else (136, 96)))) else (if i.val < 2898 then (if i.val < 2896 then (63, 78) else (if i.val < 2897 then (122, 221) else (50, 141))) else (if i.val < 2900 then (if i.val < 2899 then (110, 46) else (131, 102)) else (if i.val < 2901 then (63, 183) else (81, 152))))) else (if i.val < 2909 then (if i.val < 2905 then (if i.val < 2903 then (140, 160) else (if i.val < 2904 then (132, 176) else (114, 153))) else (if i.val < 2907 then (if i.val < 2906 then (81, 44) else (138, 59)) else (if i.val < 2908 then (142, 209) else (98, 44)))) else (if i.val < 2912 then (if i.val < 2910 then (134, 20) else (if i.val < 2911 then (135, 124) else (120, 182))) else (if i.val < 2914 then (if i.val < 2913 then (20, 168) else (130, 183)) else (if i.val < 2915 then (63, 93) else (69, 186)))))))) else (if i.val < 2970 then (if i.val < 2943 then (if i.val < 2929 then (if i.val < 2922 then (if i.val < 2919 then (if i.val < 2917 then (65, 225) else (if i.val < 2918 then (100, 121) else (116, 2))) else (if i.val < 2920 then (35, 141) else (if i.val < 2921 then (81, 63) else (140, 85)))) else (if i.val < 2925 then (if i.val < 2923 then (99, 40) else (if i.val < 2924 then (117, 179) else (142, 202))) else (if i.val < 2927 then (if i.val < 2926 then (141, 190) else (52, 253)) else (if i.val < 2928 then (114, 244) else (75, 120))))) else (if i.val < 2936 then (if i.val < 2932 then (if i.val < 2930 then (139, 52) else (if i.val < 2931 then (92, 80) else (130, 222))) else (if i.val < 2934 then (if i.val < 2933 then (28, 96) else (69, 28)) else (if i.val < 2935 then (136, 81) else (63, 240)))) else (if i.val < 2939 then (if i.val < 2937 then (11, 2) else (if i.val < 2938 then (86, 184) else (90, 63))) else (if i.val < 2941 then (if i.val < 2940 then (54, 23) else (117, 78)) else (if i.val < 2942 then (143, 137) else (68, 42)))))) else (if i.val < 2956 then (if i.val < 2949 then (if i.val < 2946 then (if i.val < 2944 then (117, 47) else (if i.val < 2945 then (9, 205) else (123, 250))) else (if i.val < 2947 then (28, 13) else (if i.val < 2948 then (131, 72) else (63, 1)))) else (if i.val < 2952 then (if i.val < 2950 then (19, 62) else (if i.val < 2951 then (63, 25) else (136, 25))) else (if i.val < 2954 then (if i.val < 2953 then (136, 105) else (85, 66)) else (if i.val < 2955 then (119, 202) else (135, 245))))) else (if i.val < 2963 then (if i.val < 2959 then (if i.val < 2957 then (91, 160) else (if i.val < 2958 then (42, 210) else (42, 149))) else (if i.val < 2961 then (if i.val < 2960 then (88, 218) else (85, 117)) else (if i.val < 2962 then (27, 122) else (48, 254)))) else (if i.val < 2966 then (if i.val < 2964 then (82, 102) else (if i.val < 2965 then (11, 211) else (100, 178))) else (if i.val < 2968 then (if i.val < 2967 then (51, 202) else (81, 188)) else (if i.val < 2969 then (67, 165) else (144, 104))))))) else (if i.val < 2997 then (if i.val < 2983 then (if i.val < 2976 then (if i.val < 2973 then (if i.val < 2971 then (83, 222) else (if i.val < 2972 then (97, 104) else (136, 22))) else (if i.val < 2974 then (132, 79) else (if i.val < 2975 then (75, 86) else (84, 181)))) else (if i.val < 2979 then (if i.val < 2977 then (135, 107) else (if i.val < 2978 then (73, 221) else (47, 109))) else (if i.val < 2981 then (if i.val < 2980 then (94, 42) else (129, 22)) else (if i.val < 2982 then (41, 94) else (34, 0))))) else (if i.val < 2990 then (if i.val < 2986 then (if i.val < 2984 then (49, 236) else (if i.val < 2985 then (84, 161) else (113, 97))) else (if i.val < 2988 then (if i.val < 2987 then (51, 247) else (121, 70)) else (if i.val < 2989 then (131, 87) else (112, 22)))) else (if i.val < 2993 then (if i.val < 2991 then (141, 168) else (if i.val < 2992 then (132, 183) else (140, 170))) else (if i.val < 2995 then (if i.val < 2994 then (132, 203) else (135, 84)) else (if i.val < 2996 then (109, 117) else (142, 205)))))) else (if i.val < 3010 then (if i.val < 3003 then (if i.val < 3000 then (if i.val < 2998 then (52, 154) else (if i.val < 2999 then (126, 45) else (28, 244))) else (if i.val < 3001 then (144, 125) else (if i.val < 3002 then (144, 162) else (78, 208)))) else (if i.val < 3006 then (if i.val < 3004 then (10, 194) else (if i.val < 3005 then (58, 22) else (57, 3))) else (if i.val < 3008 then (if i.val < 3007 then (57, 148) else (104, 133)) else (if i.val < 3009 then (114, 31) else (45, 84))))) else (if i.val < 3017 then (if i.val < 3013 then (if i.val < 3011 then (105, 225) else (if i.val < 3012 then (134, 56) else (72, 48))) else (if i.val < 3015 then (if i.val < 3014 then (45, 248) else (102, 65)) else (if i.val < 3016 then (115, 39) else (132, 81)))) else (if i.val < 3020 then (if i.val < 3018 then (26, 128) else (if i.val < 3019 then (62, 230) else (118, 95))) else (if i.val < 3022 then (if i.val < 3021 then (74, 137) else (128, 242)) else (if i.val < 3023 then (100, 161) else (75, 110)))))))))) else (if i.val < 3240 then (if i.val < 3132 then (if i.val < 3078 then (if i.val < 3051 then (if i.val < 3037 then (if i.val < 3030 then (if i.val < 3027 then (if i.val < 3025 then (59, 187) else (if i.val < 3026 then (131, 61) else (44, 140))) else (if i.val < 3028 then (26, 182) else (if i.val < 3029 then (29, 133) else (74, 26)))) else (if i.val < 3033 then (if i.val < 3031 then (98, 89) else (if i.val < 3032 then (124, 127) else (86, 139))) else (if i.val < 3035 then (if i.val < 3034 then (143, 180) else (43, 181)) else (if i.val < 3036 then (134, 19) else (142, 155))))) else (if i.val < 3044 then (if i.val < 3040 then (if i.val < 3038 then (45, 2) else (if i.val < 3039 then (139, 143) else (101, 141))) else (if i.val < 3042 then (if i.val < 3041 then (124, 195) else (66, 150)) else (if i.val < 3043 then (10, 252) else (44, 61)))) else (if i.val < 3047 then (if i.val < 3045 then (120, 209) else (if i.val < 3046 then (24, 192) else (71, 5))) else (if i.val < 3049 then (if i.val < 3048 then (115, 128) else (141, 104)) else (if i.val < 3050 then (38, 91) else (142, 11)))))) else (if i.val < 3064 then (if i.val < 3057 then (if i.val < 3054 then (if i.val < 3052 then (12, 34) else (if i.val < 3053 then (126, 112) else (134, 31))) else (if i.val < 3055 then (25, 30) else (if i.val < 3056 then (12, 75) else (27, 39)))) else (if i.val < 3060 then (if i.val < 3058 then (125, 34) else (if i.val < 3059 then (116, 200) else (144, 36))) else (if i.val < 3062 then (if i.val < 3061 then (142, 115) else (102, 177)) else (if i.val < 3063 then (91, 107) else (7, 208))))) else (if i.val < 3071 then (if i.val < 3067 then (if i.val < 3065 then (87, 70) else (if i.val < 3066 then (11, 232) else (108, 235))) else (if i.val < 3069 then (if i.val < 3068 then (12, 92) else (88, 11)) else (if i.val < 3070 then (113, 51) else (139, 106)))) else (if i.val < 3074 then (if i.val < 3072 then (132, 99) else (if i.val < 3073 then (89, 21) else (44, 126))) else (if i.val < 3076 then (if i.val < 3075 then (134, 100) else (51, 110)) else (if i.val < 3077 then (39, 47) else (25, 32))))))) else (if i.val < 3105 then (if i.val < 3091 then (if i.val < 3084 then (if i.val < 3081 then (if i.val < 3079 then (103, 59) else (if i.val < 3080 then (118, 102) else (126, 254))) else (if i.val < 3082 then (121, 66) else (if i.val < 3083 then (91, 73) else (135, 205)))) else (if i.val < 3087 then (if i.val < 3085 then (125, 54) else (if i.val < 3086 then (96, 177) else (7, 205))) else (if i.val < 3089 then (if i.val < 3088 then (114, 240) else (71, 89)) else (if i.val < 3090 then (111, 158) else (43, 93))))) else (if i.val < 3098 then (if i.val < 3094 then (if i.val < 3092 then (35, 13) else (if i.val < 3093 then (101, 221) else (20, 240))) else (if i.val < 3096 then (if i.val < 3095 then (71, 166) else (51, 132)) else (if i.val < 3097 then (135, 79) else (75, 123)))) else (if i.val < 3101 then (if i.val < 3099 then (4, 128) else (if i.val < 3100 then (51, 138) else (67, 54))) else (if i.val < 3103 then (if i.val < 3102 then (59, 7) else (70, 108)) else (if i.val < 3104 then (136, 86) else (142, 23)))))) else (if i.val < 3118 then (if i.val < 3111 then (if i.val < 3108 then (if i.val < 3106 then (120, 70) else (if i.val < 3107 then (134, 179) else (43, 61))) else (if i.val < 3109 then (138, 29) else (if i.val < 3110 then (28, 205) else (90, 1)))) else (if i.val < 3114 then (if i.val < 3112 then (68, 198) else (if i.val < 3113 then (111, 187) else (35, 16))) else (if i.val < 3116 then (if i.val < 3115 then (84, 52) else (102, 38)) else (if i.val < 3117 then (77, 22) else (72, 195))))) else (if i.val < 3125 then (if i.val < 3121 then (if i.val < 3119 then (47, 73) else (if i.val < 3120 then (58, 235) else (98, 68))) else (if i.val < 3123 then (if i.val < 3122 then (47, 17) else (133, 82)) else (if i.val < 3124 then (90, 89) else (104, 142)))) else (if i.val < 3128 then (if i.val < 3126 then (143, 102) else (if i.val < 3127 then (49, 225) else (55, 63))) else (if i.val < 3130 then (if i.val < 3129 then (125, 169) else (143, 17)) else (if i.val < 3131 then (87, 49) else (14, 184)))))))) else (if i.val < 3186 then (if i.val < 3159 then (if i.val < 3145 then (if i.val < 3138 then (if i.val < 3135 then (if i.val < 3133 then (89, 243) else (if i.val < 3134 then (87, 195) else (5, 18))) else (if i.val < 3136 then (13, 5) else (if i.val < 3137 then (114, 164) else (14, 237)))) else (if i.val < 3141 then (if i.val < 3139 then (144, 149) else (if i.val < 3140 then (47, 219) else (22, 83))) else (if i.val < 3143 then (if i.val < 3142 then (141, 162) else (113, 94)) else (if i.val < 3144 then (49, 144) else (111, 96))))) else (if i.val < 3152 then (if i.val < 3148 then (if i.val < 3146 then (104, 200) else (if i.val < 3147 then (112, 204) else (132, 90))) else (if i.val < 3150 then (if i.val < 3149 then (64, 246) else (121, 82)) else (if i.val < 3151 then (128, 68) else (95, 83)))) else (if i.val < 3155 then (if i.val < 3153 then (116, 61) else (if i.val < 3154 then (118, 12) else (3, 99))) else (if i.val < 3157 then (if i.val < 3156 then (111, 118) else (14, 215)) else (if i.val < 3158 then (14, 190) else (5, 27)))))) else (if i.val < 3172 then (if i.val < 3165 then (if i.val < 3162 then (if i.val < 3160 then (1, 131) else (if i.val < 3161 then (73, 95) else (62, 92))) else (if i.val < 3163 then (43, 68) else (if i.val < 3164 then (82, 41) else (55, 54)))) else (if i.val < 3168 then (if i.val < 3166 then (5, 43) else (if i.val < 3167 then (27, 16) else (111, 108))) else (if i.val < 3170 then (if i.val < 3169 then (113, 172) else (114, 222)) else (if i.val < 3171 then (119, 224) else (61, 225))))) else (if i.val < 3179 then (if i.val < 3175 then (if i.val < 3173 then (21, 207) else (if i.val < 3174 then (132, 3) else (40, 25))) else (if i.val < 3177 then (if i.val < 3176 then (129, 13) else (113, 185)) else (if i.val < 3178 then (109, 104) else (121, 128)))) else (if i.val < 3182 then (if i.val < 3180 then (81, 48) else (if i.val < 3181 then (73, 238) else (32, 235))) else (if i.val < 3184 then (if i.val < 3183 then (105, 54) else (50, 65)) else (if i.val < 3185 then (102, 64) else (83, 177))))))) else (if i.val < 3213 then (if i.val < 3199 then (if i.val < 3192 then (if i.val < 3189 then (if i.val < 3187 then (107, 194) else (if i.val < 3188 then (55, 78) else (55, 73))) else (if i.val < 3190 then (125, 97) else (if i.val < 3191 then (41, 209) else (118, 176)))) else (if i.val < 3195 then (if i.val < 3193 then (30, 213) else (if i.val < 3194 then (134, 22) else (41, 27))) else (if i.val < 3197 then (if i.val < 3196 then (83, 54) else (48, 69)) else (if i.val < 3198 then (66, 146) else (116, 193))))) else (if i.val < 3206 then (if i.val < 3202 then (if i.val < 3200 then (10, 137) else (if i.val < 3201 then (34, 169) else (74, 204))) else (if i.val < 3204 then (if i.val < 3203 then (87, 170) else (87, 179)) else (if i.val < 3205 then (59, 69) else (1, 99)))) else (if i.val < 3209 then (if i.val < 3207 then (60, 119) else (if i.val < 3208 then (88, 173) else (20, 249))) else (if i.val < 3211 then (if i.val < 3210 then (121, 150) else (124, 206)) else (if i.val < 3212 then (144, 7) else (126, 52)))))) else (if i.val < 3226 then (if i.val < 3219 then (if i.val < 3216 then (if i.val < 3214 then (124, 2) else (if i.val < 3215 then (124, 96) else (130, 223))) else (if i.val < 3217 then (89, 206) else (if i.val < 3218 then (76, 34) else (59, 84)))) else (if i.val < 3222 then (if i.val < 3220 then (105, 178) else (if i.val < 3221 then (101, 72) else (35, 119))) else (if i.val < 3224 then (if i.val < 3223 then (127, 251) else (90, 163)) else (if i.val < 3225 then (120, 126) else (111, 36))))) else (if i.val < 3233 then (if i.val < 3229 then (if i.val < 3227 then (80, 151) else (if i.val < 3228 then (128, 70) else (5, 116))) else (if i.val < 3231 then (if i.val < 3230 then (28, 35) else (55, 174)) else (if i.val < 3232 then (134, 101) else (27, 173)))) else (if i.val < 3236 then (if i.val < 3234 then (100, 149) else (if i.val < 3235 then (127, 164) else (124, 139))) else (if i.val < 3238 then (if i.val < 3237 then (80, 131) else (2, 190)) else (if i.val < 3239 then (121, 136) else (114, 96))))))))) else (if i.val < 3348 then (if i.val < 3294 then (if i.val < 3267 then (if i.val < 3253 then (if i.val < 3246 then (if i.val < 3243 then (if i.val < 3241 then (52, 76) else (if i.val < 3242 then (2, 218) else (97, 247))) else (if i.val < 3244 then (104, 87) else (if i.val < 3245 then (111, 101) else (124, 8)))) else (if i.val < 3249 then (if i.val < 3247 then (98, 227) else (if i.val < 3248 then (124, 245) else (40, 125))) else (if i.val < 3251 then (if i.val < 3250 then (111, 208) else (117, 175)) else (if i.val < 3252 then (105, 215) else (79, 170))))) else (if i.val < 3260 then (if i.val < 3256 then (if i.val < 3254 then (61, 231) else (if i.val < 3255 then (139, 80) else (65, 139))) else (if i.val < 3258 then (if i.val < 3257 then (111, 173) else (121, 215)) else (if i.val < 3259 then (51, 173) else (39, 204)))) else (if i.val < 3263 then (if i.val < 3261 then (75, 138) else (if i.val < 3262 then (52, 163) else (86, 150))) else (if i.val < 3265 then (if i.val < 3264 then (23, 173) else (91, 177)) else (if i.val < 3266 then (142, 190) else (94, 78)))))) else (if i.val < 3280 then (if i.val < 3273 then (if i.val < 3270 then (if i.val < 3268 then (117, 61) else (if i.val < 3269 then (26, 104) else (83, 27))) else (if i.val < 3271 then (60, 13) else (if i.val < 3272 then (50, 46) else (49, 202)))) else (if i.val < 3276 then (if i.val < 3274 then (31, 105) else (if i.val < 3275 then (26, 125) else (142, 73))) else (if i.val < 3278 then (if i.val < 3277 then (143, 174) else (138, 10)) else (if i.val < 3279 then (36, 110) else (112, 196))))) else (if i.val < 3287 then (if i.val < 3283 then (if i.val < 3281 then (65, 54) else (if i.val < 3282 then (131, 41) else (81, 61))) else (if i.val < 3285 then (if i.val < 3284 then (36, 145) else (52, 229)) else (if i.val < 3286 then (111, 186) else (125, 4)))) else (if i.val < 3290 then (if i.val < 3288 then (59, 208) else (if i.val < 3289 then (84, 171) else (124, 67))) else (if i.val < 3292 then (if i.val < 3291 then (124, 65) else (34, 167)) else (if i.val < 3293 then (45, 228) else (138, 126))))))) else (if i.val < 3321 then (if i.val < 3307 then (if i.val < 3300 then (if i.val < 3297 then (if i.val < 3295 then (75, 181) else (if i.val < 3296 then (138, 42) else (144, 28))) else (if i.val < 3298 then (124, 149) else (if i.val < 3299 then (111, 7) else (116, 50)))) else (if i.val < 3303 then (if i.val < 3301 then (125, 222) else (if i.val < 3302 then (4, 163) else (122, 134))) else (if i.val < 3305 then (if i.val < 3304 then (101, 22) else (26, 139)) else (if i.val < 3306 then (138, 171) else (114, 188))))) else (if i.val < 3314 then (if i.val < 3310 then (if i.val < 3308 then (75, 240) else (if i.val < 3309 then (111, 12) else (103, 238))) else (if i.val < 3312 then (if i.val < 3311 then (138, 56) else (69, 250)) else (if i.val < 3313 then (118, 166) else (16, 210)))) else (if i.val < 3317 then (if i.val < 3315 then (115, 216) else (if i.val < 3316 then (104, 0) else (94, 239))) else (if i.val < 3319 then (if i.val < 3318 then (9, 137) else (100, 194)) else (if i.val < 3320 then (130, 130) else (47, 42)))))) else (if i.val < 3334 then (if i.val < 3327 then (if i.val < 3324 then (if i.val < 3322 then (139, 39) else (if i.val < 3323 then (89, 154) else (140, 29))) else (if i.val < 3325 then (116, 192) else (if i.val < 3326 then (134, 88) else (104, 115)))) else (if i.val < 3330 then (if i.val < 3328 then (73, 233) else (if i.val < 3329 then (121, 125) else (103, 147))) else (if i.val < 3332 then (if i.val < 3331 then (126, 65) else (144, 44)) else (if i.val < 3333 then (114, 168) else (132, 97))))) else (if i.val < 3341 then (if i.val < 3337 then (if i.val < 3335 then (101, 7) else (if i.val < 3336 then (127, 201) else (83, 164))) else (if i.val < 3339 then (if i.val < 3338 then (33, 39) else (120, 212)) else (if i.val < 3340 then (144, 211) else (33, 121)))) else (if i.val < 3344 then (if i.val < 3342 then (138, 69) else (if i.val < 3343 then (75, 81) else (49, 75))) else (if i.val < 3346 then (if i.val < 3345 then (32, 180) else (97, 238)) else (if i.val < 3347 then (136, 209) else (32, 146)))))))) else (if i.val < 3402 then (if i.val < 3375 then (if i.val < 3361 then (if i.val < 3354 then (if i.val < 3351 then (if i.val < 3349 then (123, 166) else (if i.val < 3350 then (120, 229) else (118, 30))) else (if i.val < 3352 then (9, 232) else (if i.val < 3353 then (44, 176) else (110, 167)))) else (if i.val < 3357 then (if i.val < 3355 then (14, 211) else (if i.val < 3356 then (137, 238) else (121, 176))) else (if i.val < 3359 then (if i.val < 3358 then (101, 74) else (141, 114)) else (if i.val < 3360 then (23, 220) else (140, 203))))) else (if i.val < 3368 then (if i.val < 3364 then (if i.val < 3362 then (10, 36) else (if i.val < 3363 then (139, 64) else (14, 214))) else (if i.val < 3366 then (if i.val < 3365 then (96, 20) else (136, 191)) else (if i.val < 3367 then (143, 157) else (73, 58)))) else (if i.val < 3371 then (if i.val < 3369 then (137, 44) else (if i.val < 3370 then (118, 51) else (33, 188))) else (if i.val < 3373 then (if i.val < 3372 then (33, 59) else (35, 56)) else (if i.val < 3374 then (79, 188) else (124, 171)))))) else (if i.val < 3388 then (if i.val < 3381 then (if i.val < 3378 then (if i.val < 3376 then (33, 115) else (if i.val < 3377 then (104, 20) else (115, 106))) else (if i.val < 3379 then (48, 228) else (if i.val < 3380 then (116, 176) else (137, 33)))) else (if i.val < 3384 then (if i.val < 3382 then (88, 119) else (if i.val < 3383 then (86, 85) else (54, 156))) else (if i.val < 3386 then (if i.val < 3385 then (120, 194) else (121, 251)) else (if i.val < 3387 then (75, 117) else (14, 235))))) else (if i.val < 3395 then (if i.val < 3391 then (if i.val < 3389 then (106, 223) else (if i.val < 3390 then (54, 207) else (144, 198))) else (if i.val < 3393 then (if i.val < 3392 then (97, 239) else (121, 232)) else (if i.val < 3394 then (86, 200) else (33, 175)))) else (if i.val < 3398 then (if i.val < 3396 then (74, 69) else (if i.val < 3397 then (56, 15) else (32, 131))) else (if i.val < 3400 then (if i.val < 3399 then (32, 103) else (14, 197)) else (if i.val < 3401 then (51, 236) else (35, 255))))))) else (if i.val < 3429 then (if i.val < 3415 then (if i.val < 3408 then (if i.val < 3405 then (if i.val < 3403 then (35, 201) else (if i.val < 3404 then (5, 65) else (56, 25))) else (if i.val < 3406 then (62, 140) else (if i.val < 3407 then (52, 59) else (6, 91)))) else (if i.val < 3411 then (if i.val < 3409 then (130, 236) else (if i.val < 3410 then (98, 59) else (56, 88))) else (if i.val < 3413 then (if i.val < 3412 then (63, 164) else (52, 57)) else (if i.val < 3414 then (6, 75) else (141, 149))))) else (if i.val < 3422 then (if i.val < 3418 then (if i.val < 3416 then (116, 87) else (if i.val < 3417 then (118, 85) else (135, 203))) else (if i.val < 3420 then (if i.val < 3419 then (121, 231) else (88, 142)) else (if i.val < 3421 then (114, 119) else (92, 36)))) else (if i.val < 3425 then (if i.val < 3423 then (83, 178) else (if i.val < 3424 then (14, 94) else (111, 79))) else (if i.val < 3427 then (if i.val < 3426 then (124, 133) else (97, 19)) else (if i.val < 3428 then (130, 192) else (121, 237)))))) else (if i.val < 3442 then (if i.val < 3435 then (if i.val < 3432 then (if i.val < 3430 then (141, 161) else (if i.val < 3431 then (143, 69) else (135, 171))) else (if i.val < 3433 then (82, 109) else (if i.val < 3434 then (30, 105) else (14, 11)))) else (if i.val < 3438 then (if i.val < 3436 then (30, 63) else (if i.val < 3437 then (120, 167) else (10, 54))) else (if i.val < 3440 then (if i.val < 3439 then (13, 187) else (67, 187)) else (if i.val < 3441 then (94, 180) else (67, 96))))) else (if i.val < 3449 then (if i.val < 3445 then (if i.val < 3443 then (96, 46) else (if i.val < 3444 then (135, 59) else (68, 179))) else (if i.val < 3447 then (if i.val < 3446 then (95, 29) else (108, 141)) else (if i.val < 3448 then (143, 81) else (120, 102)))) else (if i.val < 3452 then (if i.val < 3450 then (93, 98) else (if i.val < 3451 then (136, 136) else (82, 66))) else (if i.val < 3454 then (if i.val < 3453 then (93, 200) else (120, 19)) else (if i.val < 3455 then (120, 113) else (81, 154)))))))))))))

def g32p_supplierGroup00_classify : Fin 3456 → Fin 102 :=
  fun i => (if i.val < 1728 then (if i.val < 864 then (if i.val < 432 then (if i.val < 216 then (if i.val < 108 then (if i.val < 54 then (if i.val < 27 then (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 69 else 101)) else (if i.val < 4 then 11 else (if i.val < 5 then 35 else 18))) else (if i.val < 9 then (if i.val < 7 then 99 else (if i.val < 8 then 34 else 25)) else (if i.val < 11 then (if i.val < 10 then 32 else 18) else (if i.val < 12 then 96 else 78)))) else (if i.val < 20 then (if i.val < 16 then (if i.val < 14 then 45 else (if i.val < 15 then 65 else 25)) else (if i.val < 18 then (if i.val < 17 then 4 else 67) else (if i.val < 19 then 50 else 32))) else (if i.val < 23 then (if i.val < 21 then 45 else (if i.val < 22 then 65 else 18)) else (if i.val < 25 then (if i.val < 24 then 65 else 69) else (if i.val < 26 then 37 else 56))))) else (if i.val < 40 then (if i.val < 33 then (if i.val < 30 then (if i.val < 28 then 32 else (if i.val < 29 then 18 else 13)) else (if i.val < 31 then 74 else (if i.val < 32 then 84 else 65))) else (if i.val < 36 then (if i.val < 34 then 56 else (if i.val < 35 then 29 else 7)) else (if i.val < 38 then (if i.val < 37 then 46 else 32) else (if i.val < 39 then 45 else 57)))) else (if i.val < 47 then (if i.val < 43 then (if i.val < 41 then 57 else (if i.val < 42 then 4 else 6)) else (if i.val < 45 then (if i.val < 44 then 82 else 74) else (if i.val < 46 then 11 else 2))) else (if i.val < 50 then (if i.val < 48 then 43 else (if i.val < 49 then 84 else 6)) else (if i.val < 52 then (if i.val < 51 then 82 else 65) else (if i.val < 53 then 82 else 29)))))) else (if i.val < 81 then (if i.val < 67 then (if i.val < 60 then (if i.val < 57 then (if i.val < 55 then 7 else (if i.val < 56 then 46 else 29)) else (if i.val < 58 then 1 else (if i.val < 59 then 59 else 7))) else (if i.val < 63 then (if i.val < 61 then 2 else (if i.val < 62 then 43 else 46)) else (if i.val < 65 then (if i.val < 64 then 43 else 7) else (if i.val < 66 then 45 else 57)))) else (if i.val < 74 then (if i.val < 70 then (if i.val < 68 then 45 else (if i.val < 69 then 57 else 46)) else (if i.val < 72 then (if i.val < 71 then 57 else 57) else (if i.val < 73 then 35 else 34))) else (if i.val < 77 then (if i.val < 75 then 25 else (if i.val < 76 then 35 else 97)) else (if i.val < 79 then (if i.val < 78 then 24 else 84) else (if i.val < 80 then 65 else 25))))) else (if i.val < 94 then (if i.val < 87 then (if i.val < 84 then (if i.val < 82 then 92 else (if i.val < 83 then 95 else 50)) else (if i.val < 85 then 35 else (if i.val < 86 then 84 else 65))) else (if i.val < 90 then (if i.val < 88 then 65 else (if i.val < 89 then 59 else 75)) else (if i.val < 92 then (if i.val < 91 then 82 else 24) else (if i.val < 93 then 50 else 58)))) else (if i.val < 101 then (if i.val < 97 then (if i.val < 95 then 21 else (if i.val < 96 then 84 else 6)) else (if i.val < 99 then (if i.val < 98 then 49 else 49) else (if i.val < 100 then 4 else 7))) else (if i.val < 104 then (if i.val < 102 then 50 else (if i.val < 103 then 92 else 48)) else (if i.val < 106 then (if i.val < 105 then 30 else 95) else (if i.val < 107 then 63 else 43))))))) else (if i.val < 162 then (if i.val < 135 then (if i.val < 121 then (if i.val < 114 then (if i.val < 111 then (if i.val < 109 then 50 else (if i.val < 110 then 43 else 7)) else (if i.val < 112 then 65 else (if i.val < 113 then 84 else 65))) else (if i.val < 117 then (if i.val < 115 then 65 else (if i.val < 116 then 35 else 59)) else (if i.val < 119 then (if i.val < 118 then 78 else 100) else (if i.val < 120 then 29 else 75)))) else (if i.val < 128 then (if i.val < 124 then (if i.val < 122 then 18 else (if i.val < 123 then 82 else 18)) else (if i.val < 126 then (if i.val < 125 then 50 else 58) else (if i.val < 127 then 21 else 50))) else (if i.val < 131 then (if i.val < 129 then 76 else (if i.val < 130 then 25 else 58)) else (if i.val < 133 then (if i.val < 132 then 100 else 29) else (if i.val < 134 then 21 else 29))))) else (if i.val < 148 then (if i.val < 141 then (if i.val < 138 then (if i.val < 136 then 58 else (if i.val < 137 then 6 else 49)) else (if i.val < 139 then 6 else (if i.val < 140 then 49 else 21))) else (if i.val < 144 then (if i.val < 142 then 49 else (if i.val < 143 then 49 else 4)) else (if i.val < 146 then (if i.val < 145 then 69 else 48) else (if i.val < 147 then 30 else 7)))) else (if i.val < 155 then (if i.val < 151 then (if i.val < 149 then 63 else (if i.val < 150 then 43 else 43)) else (if i.val < 153 then (if i.val < 152 then 69 else 48) else (if i.val < 154 then 30 else 48))) else (if i.val < 158 then (if i.val < 156 then 76 else (if i.val < 157 then 25 else 30)) else (if i.val < 160 then (if i.val < 159 then 25 else 48) else (if i.val < 161 then 63 else 43)))))) else (if i.val < 189 then (if i.val < 175 then (if i.val < 168 then (if i.val < 165 then (if i.val < 163 then 63 else (if i.val < 164 then 43 else 30)) else (if i.val < 166 then 43 else (if i.val < 167 then 43 else 67))) else (if i.val < 171 then (if i.val < 169 then 7 else (if i.val < 170 then 48 else 63)) else (if i.val < 173 then (if i.val < 172 then 43 else 69) else (if i.val < 174 then 82 else 49)))) else (if i.val < 182 then (if i.val < 178 then (if i.val < 176 then 63 else (if i.val < 177 then 69 else 49)) else (if i.val < 180 then (if i.val < 179 then 43 else 49) else (if i.val < 181 then 30 else 43))) else (if i.val < 185 then (if i.val < 183 then 65 else (if i.val < 184 then 49 else 32)) else (if i.val < 187 then (if i.val < 186 then 43 else 82) else (if i.val < 188 then 32 else 35))))) else (if i.val < 202 then (if i.val < 195 then (if i.val < 192 then (if i.val < 190 then 13 else (if i.val < 191 then 74 else 45)) else (if i.val < 193 then 11 else (if i.val < 194 then 29 else 72))) else (if i.val < 198 then (if i.val < 196 then 35 else (if i.val < 197 then 84 else 57)) else (if i.val < 200 then (if i.val < 199 then 92 else 75) else (if i.val < 201 then 82 else 74)))) else (if i.val < 209 then (if i.val < 205 then (if i.val < 203 then 56 else (if i.val < 204 then 93 else 43)) else (if i.val < 207 then (if i.val < 206 then 45 else 75) else (if i.val < 208 then 82 else 82))) else (if i.val < 212 then (if i.val < 210 then 29 else (if i.val < 211 then 72 else 29)) else (if i.val < 214 then (if i.val < 213 then 98 else 59) else (if i.val < 215 then 72 else 93)))))))) else (if i.val < 324 then (if i.val < 270 then (if i.val < 243 then (if i.val < 229 then (if i.val < 222 then (if i.val < 219 then (if i.val < 217 then 43 else (if i.val < 218 then 43 else 72)) else (if i.val < 220 then 84 else (if i.val < 221 then 57 else 32))) else (if i.val < 225 then (if i.val < 223 then 92 else (if i.val < 224 then 43 else 55)) else (if i.val < 227 then (if i.val < 226 then 30 else 75) else (if i.val < 228 then 38 else 38)))) else (if i.val < 236 then (if i.val < 232 then (if i.val < 230 then 11 else (if i.val < 231 then 58 else 43)) else (if i.val < 234 then (if i.val < 233 then 56 else 20) else (if i.val < 235 then 46 else 93))) else (if i.val < 239 then (if i.val < 237 then 27 else (if i.val < 238 then 29 else 43)) else (if i.val < 241 then (if i.val < 240 then 29 else 58) else (if i.val < 242 then 82 else 75))))) else (if i.val < 256 then (if i.val < 249 then (if i.val < 246 then (if i.val < 244 then 29 else (if i.val < 245 then 69 else 80)) else (if i.val < 247 then 59 else (if i.val < 248 then 72 else 58))) else (if i.val < 252 then (if i.val < 250 then 21 else (if i.val < 251 then 21 else 69)) else (if i.val < 254 then (if i.val < 253 then 48 else 59) else (if i.val < 255 then 98 else 41)))) else (if i.val < 263 then (if i.val < 259 then (if i.val < 257 then 25 else (if i.val < 258 then 59 else 25)) else (if i.val < 261 then (if i.val < 260 then 80 else 63) else (if i.val < 262 then 43 else 93))) else (if i.val < 266 then (if i.val < 264 then 43 else (if i.val < 265 then 59 else 21)) else (if i.val < 268 then (if i.val < 267 then 43 else 72) else (if i.val < 269 then 72 else 48)))))) else (if i.val < 297 then (if i.val < 283 then (if i.val < 276 then (if i.val < 273 then (if i.val < 271 then 21 else (if i.val < 272 then 49 else 58)) else (if i.val < 274 then 69 else (if i.val < 275 then 82 else 21))) else (if i.val < 279 then (if i.val < 277 then 49 else (if i.val < 278 then 21 else 35)) else (if i.val < 281 then (if i.val < 280 then 32 else 43) else (if i.val < 282 then 55 else 30)))) else (if i.val < 290 then (if i.val < 286 then (if i.val < 284 then 43 else (if i.val < 285 then 87 else 74)) else (if i.val < 288 then (if i.val < 287 then 55 else 50) else (if i.val < 289 then 30 else 50))) else (if i.val < 293 then (if i.val < 291 then 55 else (if i.val < 292 then 38 else 38)) else (if i.val < 295 then (if i.val < 294 then 30 else 38) else (if i.val < 296 then 38 else 11))))) else (if i.val < 310 then (if i.val < 303 then (if i.val < 300 then (if i.val < 298 then 34 else (if i.val < 299 then 20 else 46)) else (if i.val < 301 then 58 else (if i.val < 302 then 27 else 29))) else (if i.val < 306 then (if i.val < 304 then 29 else (if i.val < 305 then 34 else 20)) else (if i.val < 308 then (if i.val < 307 then 46 else 20) else (if i.val < 309 then 87 else 74)))) else (if i.val < 317 then (if i.val < 313 then (if i.val < 311 then 46 else (if i.val < 312 then 74 else 20)) else (if i.val < 315 then (if i.val < 314 then 27 else 29) else (if i.val < 316 then 27 else 29))) else (if i.val < 320 then (if i.val < 318 then 46 else (if i.val < 319 then 29 else 29)) else (if i.val < 322 then (if i.val < 321 then 58 else 20) else (if i.val < 323 then 27 else 29))))))) else (if i.val < 378 then (if i.val < 351 then (if i.val < 337 then (if i.val < 330 then (if i.val < 327 then (if i.val < 325 then 34 else (if i.val < 326 then 18 else 38)) else (if i.val < 328 then 27 else (if i.val < 329 then 34 else 38))) else (if i.val < 333 then (if i.val < 331 then 29 else (if i.val < 332 then 38 else 46)) else (if i.val < 335 then (if i.val < 334 then 29 else 38) else (if i.val < 336 then 29 else 18)))) else (if i.val < 344 then (if i.val < 340 then (if i.val < 338 then 69 else (if i.val < 339 then 80 else 59)) else (if i.val < 342 then (if i.val < 341 then 69 else 32) else (if i.val < 343 then 18 else 80))) else (if i.val < 347 then (if i.val < 345 then 41 else (if i.val < 346 then 25 else 59)) else (if i.val < 349 then (if i.val < 348 then 25 else 48) else (if i.val < 350 then 21 else 58))))) else (if i.val < 364 then (if i.val < 357 then (if i.val < 354 then (if i.val < 352 then 21 else (if i.val < 353 then 21 else 72)) else (if i.val < 355 then 69 else (if i.val < 356 then 25 else 32))) else (if i.val < 360 then (if i.val < 358 then 18 else (if i.val < 359 then 48 else 41)) else (if i.val < 362 then (if i.val < 361 then 25 else 25) else (if i.val < 363 then 32 else 41)))) else (if i.val < 371 then (if i.val < 367 then (if i.val < 365 then 25 else (if i.val < 366 then 41 else 25)) else (if i.val < 369 then (if i.val < 368 then 18 else 25) else (if i.val < 370 then 25 else 1))) else (if i.val < 374 then (if i.val < 372 then 80 else (if i.val < 373 then 32 else 41)) else (if i.val < 376 then (if i.val < 375 then 25 else 25) else (if i.val < 377 then 30 else 29)))))) else (if i.val < 405 then (if i.val < 391 then (if i.val < 384 then (if i.val < 381 then (if i.val < 379 then 41 else (if i.val < 380 then 25 else 29)) else (if i.val < 382 then 25 else (if i.val < 383 then 29 else 18))) else (if i.val < 387 then (if i.val < 385 then 25 else (if i.val < 386 then 21 else 29)) else (if i.val < 389 then (if i.val < 388 then 7 else 25) else (if i.val < 390 then 30 else 7)))) else (if i.val < 398 then (if i.val < 394 then (if i.val < 392 then 72 else (if i.val < 393 then 80 else 58)) else (if i.val < 396 then (if i.val < 395 then 21 else 48) else (if i.val < 397 then 41 else 25))) else (if i.val < 401 then (if i.val < 399 then 63 else (if i.val < 400 then 25 else 30)) else (if i.val < 403 then (if i.val < 402 then 21 else 29) else (if i.val < 404 then 69 else 13))))) else (if i.val < 418 then (if i.val < 411 then (if i.val < 408 then (if i.val < 406 then 58 else (if i.val < 407 then 41 else 25)) else (if i.val < 409 then 29 else (if i.val < 410 then 38 else 18))) else (if i.val < 414 then (if i.val < 412 then 25 else (if i.val < 413 then 29 else 18)) else (if i.val < 416 then (if i.val < 415 then 13 else 25) else (if i.val < 417 then 43 else 29)))) else (if i.val < 425 then (if i.val < 421 then (if i.val < 419 then 7 else (if i.val < 420 then 21 else 21)) else (if i.val < 423 then (if i.val < 422 then 25 else 30) else (if i.val < 424 then 7 else 38))) else (if i.val < 428 then (if i.val < 426 then 45 else (if i.val < 427 then 13 else 72)) else (if i.val < 430 then (if i.val < 429 then 13 else 59) else (if i.val < 431 then 6 else 78))))))))) else (if i.val < 648 then (if i.val < 540 then (if i.val < 486 then (if i.val < 459 then (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then (if i.val < 433 then 50 else (if i.val < 434 then 63 else 75)) else (if i.val < 436 then 92 else (if i.val < 437 then 72 else 4))) else (if i.val < 441 then (if i.val < 439 then 80 else (if i.val < 440 then 67 else 58)) else (if i.val < 443 then (if i.val < 442 then 43 else 72) else (if i.val < 444 then 59 else 24)))) else (if i.val < 452 then (if i.val < 448 then (if i.val < 446 then 28 else (if i.val < 447 then 29 else 6)) else (if i.val < 450 then (if i.val < 449 then 18 else 18) else (if i.val < 451 then 50 else 63))) else (if i.val < 455 then (if i.val < 453 then 50 else (if i.val < 454 then 44 else 25)) else (if i.val < 457 then (if i.val < 456 then 63 else 28) else (if i.val < 458 then 29 else 29))))) else (if i.val < 472 then (if i.val < 465 then (if i.val < 462 then (if i.val < 460 then 63 else (if i.val < 461 then 75 else 92)) else (if i.val < 463 then 69 else (if i.val < 464 then 80 else 72))) else (if i.val < 468 then (if i.val < 466 then 58 else (if i.val < 467 then 43 else 69)) else (if i.val < 470 then (if i.val < 469 then 80 else 80) else (if i.val < 471 then 44 else 25)))) else (if i.val < 479 then (if i.val < 475 then (if i.val < 473 then 25 else (if i.val < 474 then 80 else 58)) else (if i.val < 477 then (if i.val < 476 then 43 else 95) else (if i.val < 478 then 72 else 80))) else (if i.val < 482 then (if i.val < 480 then 58 else (if i.val < 481 then 43 else 78)) else (if i.val < 484 then (if i.val < 483 then 55 else 29) else (if i.val < 485 then 24 else 61)))))) else (if i.val < 513 then (if i.val < 499 then (if i.val < 492 then (if i.val < 489 then (if i.val < 487 then 21 else (if i.val < 488 then 28 else 50)) else (if i.val < 490 then 29 else (if i.val < 491 then 50 else 55))) else (if i.val < 495 then (if i.val < 493 then 50 else (if i.val < 494 then 34 else 41)) else (if i.val < 497 then (if i.val < 496 then 25 else 63) else (if i.val < 498 then 55 else 30)))) else (if i.val < 506 then (if i.val < 502 then (if i.val < 500 then 30 else (if i.val < 501 then 34 else 20)) else (if i.val < 504 then (if i.val < 503 then 25 else 44) else (if i.val < 505 then 17 else 74))) else (if i.val < 509 then (if i.val < 507 then 25 else (if i.val < 508 then 74 else 41)) else (if i.val < 511 then (if i.val < 510 then 27 else 29) else (if i.val < 512 then 28 else 29))))) else (if i.val < 526 then (if i.val < 519 then (if i.val < 516 then (if i.val < 514 then 25 else (if i.val < 515 then 30 else 29)) else (if i.val < 517 then 63 else (if i.val < 518 then 20 else 30))) else (if i.val < 522 then (if i.val < 520 then 55 else (if i.val < 521 then 34 else 18)) else (if i.val < 524 then (if i.val < 523 then 81 else 30) else (if i.val < 525 then 66 else 69)))) else (if i.val < 533 then (if i.val < 529 then (if i.val < 527 then 80 else (if i.val < 528 then 41 else 46)) else (if i.val < 531 then (if i.val < 530 then 30 else 46) else (if i.val < 532 then 81 else 43))) else (if i.val < 536 then (if i.val < 534 then 58 else (if i.val < 535 then 43 else 43)) else (if i.val < 538 then (if i.val < 537 then 7 else 11) else (if i.val < 539 then 15 else 69))))))) else (if i.val < 594 then (if i.val < 567 then (if i.val < 553 then (if i.val < 546 then (if i.val < 543 then (if i.val < 541 then 80 else (if i.val < 542 then 20 else 46)) else (if i.val < 544 then 46 else (if i.val < 545 then 66 else 41))) else (if i.val < 549 then (if i.val < 547 then 25 else (if i.val < 548 then 44 else 25)) else (if i.val < 551 then (if i.val < 550 then 69 else 46) else (if i.val < 552 then 25 else 80)))) else (if i.val < 560 then (if i.val < 556 then (if i.val < 554 then 80 else (if i.val < 555 then 15 else 19)) else (if i.val < 558 then (if i.val < 557 then 46 else 25) else (if i.val < 559 then 29 else 29))) else (if i.val < 563 then (if i.val < 561 then 41 else (if i.val < 562 then 25 else 29)) else (if i.val < 565 then (if i.val < 564 then 46 else 29) else (if i.val < 566 then 69 else 46))))) else (if i.val < 580 then (if i.val < 573 then (if i.val < 570 then (if i.val < 568 then 43 else (if i.val < 569 then 30 else 72)) else (if i.val < 571 then 46 else (if i.val < 572 then 29 else 67))) else (if i.val < 576 then (if i.val < 574 then 95 else (if i.val < 575 then 81 else 93)) else (if i.val < 578 then (if i.val < 577 then 43 else 80) else (if i.val < 579 then 46 else 43)))) else (if i.val < 587 then (if i.val < 583 then (if i.val < 581 then 29 else (if i.val < 582 then 58 else 20)) else (if i.val < 585 then (if i.val < 584 then 25 else 30) else (if i.val < 586 then 46 else 29))) else (if i.val < 590 then (if i.val < 588 then 43 else (if i.val < 589 then 46 else 72)) else (if i.val < 592 then (if i.val < 591 then 7 else 78) else (if i.val < 593 then 13 else 61)))))) else (if i.val < 621 then (if i.val < 607 then (if i.val < 600 then (if i.val < 597 then (if i.val < 595 then 21 else (if i.val < 596 then 55 else 50)) else (if i.val < 598 then 50 else (if i.val < 599 then 13 else 61))) else (if i.val < 603 then (if i.val < 601 then 21 else (if i.val < 602 then 61 else 59)) else (if i.val < 605 then (if i.val < 604 then 21 else 59) else (if i.val < 606 then 61 else 72)))) else (if i.val < 614 then (if i.val < 610 then (if i.val < 608 then 50 else (if i.val < 609 then 50 else 21)) else (if i.val < 612 then (if i.val < 611 then 50 else 50) else (if i.val < 613 then 55 else 61))) else (if i.val < 617 then (if i.val < 615 then 50 else (if i.val < 616 then 57 else 50)) else (if i.val < 619 then (if i.val < 618 then 57 else 21) else (if i.val < 620 then 50 else 50))))) else (if i.val < 634 then (if i.val < 627 then (if i.val < 624 then (if i.val < 622 then 34 else (if i.val < 623 then 41 else 25)) else (if i.val < 625 then 34 else (if i.val < 626 then 84 else 65))) else (if i.val < 630 then (if i.val < 628 then 41 else (if i.val < 629 then 17 else 74)) else (if i.val < 632 then (if i.val < 631 then 25 else 74) else (if i.val < 633 then 20 else 30)))) else (if i.val < 641 then (if i.val < 637 then (if i.val < 635 then 55 else (if i.val < 636 then 34 else 74)) else (if i.val < 639 then (if i.val < 638 then 84 else 65) else (if i.val < 640 then 20 else 17))) else (if i.val < 644 then (if i.val < 642 then 74 else (if i.val < 643 then 74 else 84)) else (if i.val < 646 then (if i.val < 645 then 17 else 74) else (if i.val < 647 then 17 else 74)))))))) else (if i.val < 756 then (if i.val < 702 then (if i.val < 675 then (if i.val < 661 then (if i.val < 654 then (if i.val < 651 then (if i.val < 649 then 65 else (if i.val < 650 then 74 else 74)) else (if i.val < 652 then 41 else (if i.val < 653 then 84 else 17))) else (if i.val < 657 then (if i.val < 655 then 74 else (if i.val < 656 then 74 else 46)) else (if i.val < 659 then (if i.val < 658 then 50 else 17) else (if i.val < 660 then 74 else 50)))) else (if i.val < 668 then (if i.val < 664 then (if i.val < 662 then 74 else (if i.val < 663 then 50 else 65)) else (if i.val < 666 then (if i.val < 665 then 74 else 30) else (if i.val < 667 then 50 else 74))) else (if i.val < 671 then (if i.val < 669 then 46 else (if i.val < 670 then 41 else 55)) else (if i.val < 673 then (if i.val < 672 then 30 else 20) else (if i.val < 674 then 17 else 74))))) else (if i.val < 688 then (if i.val < 681 then (if i.val < 678 then (if i.val < 676 then 27 else (if i.val < 677 then 74 else 46)) else (if i.val < 679 then 30 else (if i.val < 680 then 50 else 34))) else (if i.val < 684 then (if i.val < 682 then 55 else (if i.val < 683 then 17 else 74)) else (if i.val < 686 then (if i.val < 685 then 50 else 57) else (if i.val < 687 then 74 else 50)))) else (if i.val < 695 then (if i.val < 691 then (if i.val < 689 then 74 else (if i.val < 690 then 50 else 30)) else (if i.val < 693 then (if i.val < 692 then 74 else 46) else (if i.val < 694 then 57 else 6))) else (if i.val < 698 then (if i.val < 696 then 56 else (if i.val < 697 then 66 else 69)) else (if i.val < 700 then (if i.val < 699 then 41 else 46) else (if i.val < 701 then 46 else 15)))))) else (if i.val < 729 then (if i.val < 715 then (if i.val < 708 then (if i.val < 705 then (if i.val < 703 then 66 else (if i.val < 704 then 45 else 57)) else (if i.val < 706 then 57 else (if i.val < 707 then 15 else 19))) else (if i.val < 711 then (if i.val < 709 then 46 else (if i.val < 710 then 41 else 46)) else (if i.val < 713 then (if i.val < 712 then 69 else 46) else (if i.val < 714 then 46 else 80)))) else (if i.val < 722 then (if i.val < 718 then (if i.val < 716 then 81 else (if i.val < 717 then 32 else 46)) else (if i.val < 720 then (if i.val < 719 then 29 else 20) else (if i.val < 721 then 25 else 46))) else (if i.val < 725 then (if i.val < 723 then 29 else (if i.val < 724 then 46 else 7)) else (if i.val < 727 then (if i.val < 726 then 56 else 66) else (if i.val < 728 then 11 else 7))))) else (if i.val < 742 then (if i.val < 735 then (if i.val < 732 then (if i.val < 730 then 46 else (if i.val < 731 then 15 else 45)) else (if i.val < 733 then 57 else (if i.val < 734 then 57 else 32))) else (if i.val < 738 then (if i.val < 736 then 46 else (if i.val < 737 then 20 else 46)) else (if i.val < 740 then (if i.val < 739 then 46 else 80) else (if i.val < 741 then 66 else 7)))) else (if i.val < 749 then (if i.val < 745 then (if i.val < 743 then 45 else (if i.val < 744 then 57 else 29)) else (if i.val < 747 then (if i.val < 746 then 21 else 74) else (if i.val < 748 then 45 else 29))) else (if i.val < 752 then (if i.val < 750 then 74 else (if i.val < 751 then 57 else 74)) else (if i.val < 754 then (if i.val < 753 then 46 else 57) else (if i.val < 755 then 46 else 74))))))) else (if i.val < 810 then (if i.val < 783 then (if i.val < 769 then (if i.val < 762 then (if i.val < 759 then (if i.val < 757 then 48 else (if i.val < 758 then 57 else 21)) else (if i.val < 760 then 48 else (if i.val < 761 then 80 else 66))) else (if i.val < 765 then (if i.val < 763 then 41 else (if i.val < 764 then 46 else 15)) else (if i.val < 767 then (if i.val < 766 then 45 else 57) else (if i.val < 768 then 19 else 29)))) else (if i.val < 776 then (if i.val < 772 then (if i.val < 770 then 21 else (if i.val < 771 then 46 else 74)) else (if i.val < 774 then (if i.val < 773 then 25 else 59) else (if i.val < 775 then 41 else 45))) else (if i.val < 779 then (if i.val < 777 then 29 else (if i.val < 778 then 74 else 50)) else (if i.val < 781 then (if i.val < 780 then 46 else 57) else (if i.val < 782 then 74 else 46))))) else (if i.val < 796 then (if i.val < 789 then (if i.val < 786 then (if i.val < 784 then 59 else (if i.val < 785 then 57 else 46)) else (if i.val < 787 then 74 else (if i.val < 788 then 48 else 46))) else (if i.val < 792 then (if i.val < 790 then 46 else (if i.val < 791 then 57 else 21)) else (if i.val < 794 then (if i.val < 793 then 48 else 50) else (if i.val < 795 then 63 else 59)))) else (if i.val < 803 then (if i.val < 799 then (if i.val < 797 then 80 else (if i.val < 798 then 59 else 66)) else (if i.val < 801 then (if i.val < 800 then 41 else 46) else (if i.val < 802 then 93 else 56))) else (if i.val < 806 then (if i.val < 804 then 29 else (if i.val < 805 then 30 else 15)) else (if i.val < 808 then (if i.val < 807 then 20 else 46) else (if i.val < 809 then 41 else 29)))))) else (if i.val < 837 then (if i.val < 823 then (if i.val < 816 then (if i.val < 813 then (if i.val < 811 then 21 else (if i.val < 812 then 46 else 74)) else (if i.val < 814 then 25 else (if i.val < 815 then 29 else 25))) else (if i.val < 819 then (if i.val < 817 then 29 else (if i.val < 818 then 46 else 30)) else (if i.val < 821 then (if i.val < 820 then 29 else 59) else (if i.val < 822 then 25 else 41)))) else (if i.val < 830 then (if i.val < 826 then (if i.val < 824 then 56 else (if i.val < 825 then 20 else 29)) else (if i.val < 828 then (if i.val < 827 then 74 else 25) else (if i.val < 829 then 50 else 30))) else (if i.val < 833 then (if i.val < 831 then 46 else (if i.val < 832 then 74 else 29)) else (if i.val < 835 then (if i.val < 834 then 46 else 59) else (if i.val < 836 then 25 else 74))))) else (if i.val < 850 then (if i.val < 843 then (if i.val < 840 then (if i.val < 838 then 48 else (if i.val < 839 then 46 else 29)) else (if i.val < 841 then 43 else (if i.val < 842 then 46 else 46))) else (if i.val < 846 then (if i.val < 844 then 29 else (if i.val < 845 then 7 else 46)) else (if i.val < 848 then (if i.val < 847 then 21 else 48) else (if i.val < 849 then 29 else 50)))) else (if i.val < 857 then (if i.val < 853 then (if i.val < 851 then 63 else (if i.val < 852 then 72 else 59)) else (if i.val < 855 then (if i.val < 854 then 80 else 59) else (if i.val < 856 then 4 else 43))) else (if i.val < 860 then (if i.val < 858 then 27 else (if i.val < 859 then 56 else 63)) else (if i.val < 862 then (if i.val < 861 then 11 else 41) else (if i.val < 863 then 2 else 55)))))))))) else (if i.val < 1296 then (if i.val < 1080 then (if i.val < 972 then (if i.val < 918 then (if i.val < 891 then (if i.val < 877 then (if i.val < 870 then (if i.val < 867 then (if i.val < 865 then 29 else (if i.val < 866 then 48 else 7)) else (if i.val < 868 then 63 else (if i.val < 869 then 21 else 80))) else (if i.val < 873 then (if i.val < 871 then 1 else (if i.val < 872 then 20 else 25)) else (if i.val < 875 then (if i.val < 874 then 48 else 2) else (if i.val < 876 then 7 else 80)))) else (if i.val < 884 then (if i.val < 880 then (if i.val < 878 then 43 else (if i.val < 879 then 27 else 43)) else (if i.val < 882 then (if i.val < 881 then 88 else 74) else (if i.val < 883 then 27 else 50))) else (if i.val < 887 then (if i.val < 885 then 50 else (if i.val < 886 then 27 else 56)) else (if i.val < 889 then (if i.val < 888 then 34 else 41) else (if i.val < 890 then 55 else 34))))) else (if i.val < 904 then (if i.val < 897 then (if i.val < 894 then (if i.val < 892 then 41 else (if i.val < 893 then 41 else 88)) else (if i.val < 895 then 74 else (if i.val < 896 then 74 else 41))) else (if i.val < 900 then (if i.val < 898 then 55 else (if i.val < 899 then 63 else 41)) else (if i.val < 902 then (if i.val < 901 then 55 else 69) else (if i.val < 903 then 48 else 35)))) else (if i.val < 911 then (if i.val < 907 then (if i.val < 905 then 48 else (if i.val < 906 then 20 else 25)) else (if i.val < 909 then (if i.val < 908 then 80 else 25) else (if i.val < 910 then 35 else 80))) else (if i.val < 914 then (if i.val < 912 then 20 else (if i.val < 913 then 25 else 35)) else (if i.val < 916 then (if i.val < 915 then 20 else 25) else (if i.val < 917 then 98 else 48)))))) else (if i.val < 945 then (if i.val < 931 then (if i.val < 924 then (if i.val < 921 then (if i.val < 919 then 35 else (if i.val < 920 then 20 else 25)) else (if i.val < 922 then 48 else (if i.val < 923 then 63 else 80))) else (if i.val < 927 then (if i.val < 925 then 63 else (if i.val < 926 then 20 else 21)) else (if i.val < 929 then (if i.val < 928 then 25 else 43) else (if i.val < 930 then 13 else 17)))) else (if i.val < 938 then (if i.val < 934 then (if i.val < 932 then 74 else (if i.val < 933 then 27 else 46)) else (if i.val < 936 then (if i.val < 935 then 46 else 13) else (if i.val < 937 then 61 else 74))) else (if i.val < 941 then (if i.val < 939 then 88 else (if i.val < 940 then 59 else 74)) else (if i.val < 943 then (if i.val < 942 then 59 else 17) else (if i.val < 944 then 72 else 50))))) else (if i.val < 958 then (if i.val < 951 then (if i.val < 948 then (if i.val < 946 then 50 else (if i.val < 947 then 74 else 46)) else (if i.val < 949 then 50 else (if i.val < 950 then 27 else 61))) else (if i.val < 954 then (if i.val < 952 then 65 else (if i.val < 953 then 19 else 46)) else (if i.val < 956 then (if i.val < 955 then 10 else 34) else (if i.val < 957 then 41 else 17)))) else (if i.val < 965 then (if i.val < 961 then (if i.val < 959 then 21 else (if i.val < 960 then 46 else 21)) else (if i.val < 963 then (if i.val < 962 then 19 else 55) else (if i.val < 964 then 78 else 86))) else (if i.val < 968 then (if i.val < 966 then 34 else (if i.val < 967 then 41 else 61)) else (if i.val < 970 then (if i.val < 969 then 21 else 21) else (if i.val < 971 then 10 else 17))))))) else (if i.val < 1026 then (if i.val < 999 then (if i.val < 985 then (if i.val < 978 then (if i.val < 975 then (if i.val < 973 then 74 else (if i.val < 974 then 88 else 74)) else (if i.val < 976 then 34 else (if i.val < 977 then 21 else 74))) else (if i.val < 981 then (if i.val < 979 then 41 else (if i.val < 980 then 86 else 91)) else (if i.val < 983 then (if i.val < 982 then 21 else 74) else (if i.val < 984 then 50 else 50)))) else (if i.val < 992 then (if i.val < 988 then (if i.val < 986 then 17 else (if i.val < 987 then 74 else 50)) else (if i.val < 990 then (if i.val < 989 then 21 else 50) else (if i.val < 991 then 34 else 21))) else (if i.val < 995 then (if i.val < 993 then 29 else (if i.val < 994 then 46 else 21)) else (if i.val < 997 then (if i.val < 996 then 50 else 19) else (if i.val < 998 then 28 else 41))))) else (if i.val < 1012 then (if i.val < 1005 then (if i.val < 1002 then (if i.val < 1000 then 21 else (if i.val < 1001 then 29 else 55)) else (if i.val < 1003 then 61 else (if i.val < 1004 then 74 else 25))) else (if i.val < 1008 then (if i.val < 1006 then 66 else (if i.val < 1007 then 69 else 77)) else (if i.val < 1010 then (if i.val < 1009 then 46 else 46) else (if i.val < 1011 then 35 else 10)))) else (if i.val < 1019 then (if i.val < 1015 then (if i.val < 1013 then 57 else (if i.val < 1014 then 57 else 66)) else (if i.val < 1017 then (if i.val < 1016 then 25 else 20) else (if i.val < 1018 then 25 else 69))) else (if i.val < 1022 then (if i.val < 1020 then 46 else (if i.val < 1021 then 25 else 80)) else (if i.val < 1024 then (if i.val < 1023 then 80 else 32) else (if i.val < 1025 then 46 else 29)))))) else (if i.val < 1053 then (if i.val < 1039 then (if i.val < 1032 then (if i.val < 1029 then (if i.val < 1027 then 77 else (if i.val < 1028 then 25 else 46)) else (if i.val < 1030 then 29 else (if i.val < 1031 then 46 else 7))) else (if i.val < 1035 then (if i.val < 1033 then 25 else (if i.val < 1034 then 72 else 50)) else (if i.val < 1037 then (if i.val < 1036 then 35 else 86) else (if i.val < 1038 then 57 else 57)))) else (if i.val < 1046 then (if i.val < 1042 then (if i.val < 1040 then 32 else (if i.val < 1041 then 25 else 20)) else (if i.val < 1044 then (if i.val < 1043 then 25 else 25) else (if i.val < 1045 then 48 else 35))) else (if i.val < 1049 then (if i.val < 1047 then 72 else (if i.val < 1048 then 84 else 57)) else (if i.val < 1051 then (if i.val < 1050 then 29 else 74) else (if i.val < 1052 then 74 else 10))))) else (if i.val < 1066 then (if i.val < 1059 then (if i.val < 1056 then (if i.val < 1054 then 29 else (if i.val < 1055 then 74 else 57)) else (if i.val < 1057 then 74 else (if i.val < 1058 then 50 else 57))) else (if i.val < 1062 then (if i.val < 1060 then 25 else (if i.val < 1061 then 21 else 80)) else (if i.val < 1064 then (if i.val < 1063 then 57 else 74) else (if i.val < 1065 then 1 else 98)))) else (if i.val < 1073 then (if i.val < 1069 then (if i.val < 1067 then 66 else (if i.val < 1068 then 25 else 35)) else (if i.val < 1071 then (if i.val < 1070 then 84 else 57) else (if i.val < 1072 then 20 else 92))) else (if i.val < 1076 then (if i.val < 1074 then 21 else (if i.val < 1075 then 25 else 21)) else (if i.val < 1078 then (if i.val < 1077 then 25 else 59) else (if i.val < 1079 then 20 else 86)))))))) else (if i.val < 1188 then (if i.val < 1134 then (if i.val < 1107 then (if i.val < 1093 then (if i.val < 1086 then (if i.val < 1083 then (if i.val < 1081 then 92 else (if i.val < 1082 then 21 else 50)) else (if i.val < 1084 then 50 else (if i.val < 1085 then 57 else 21))) else (if i.val < 1089 then (if i.val < 1087 then 50 else (if i.val < 1088 then 59 else 57)) else (if i.val < 1091 then (if i.val < 1090 then 25 else 21) else (if i.val < 1092 then 48 else 46)))) else (if i.val < 1100 then (if i.val < 1096 then (if i.val < 1094 then 25 else (if i.val < 1095 then 57 else 21)) else (if i.val < 1098 then (if i.val < 1097 then 48 else 50) else (if i.val < 1099 then 58 else 59))) else (if i.val < 1103 then (if i.val < 1101 then 80 else (if i.val < 1102 then 59 else 32)) else (if i.val < 1105 then (if i.val < 1104 then 46 else 63) else (if i.val < 1106 then 25 else 29))))) else (if i.val < 1120 then (if i.val < 1113 then (if i.val < 1110 then (if i.val < 1108 then 29 else (if i.val < 1109 then 32 else 44)) else (if i.val < 1111 then 25 else (if i.val < 1112 then 25 else 74))) else (if i.val < 1116 then (if i.val < 1114 then 46 else (if i.val < 1115 then 29 else 29)) else (if i.val < 1118 then (if i.val < 1117 then 77 else 25) else (if i.val < 1119 then 20 else 29)))) else (if i.val < 1127 then (if i.val < 1123 then (if i.val < 1121 then 21 else (if i.val < 1122 then 25 else 74)) else (if i.val < 1125 then (if i.val < 1124 then 29 else 46) else (if i.val < 1126 then 29 else 7))) else (if i.val < 1130 then (if i.val < 1128 then 25 else (if i.val < 1129 then 80 else 72)) else (if i.val < 1132 then (if i.val < 1131 then 48 else 13) else (if i.val < 1133 then 17 else 74)))))) else (if i.val < 1161 then (if i.val < 1147 then (if i.val < 1140 then (if i.val < 1137 then (if i.val < 1135 then 13 else (if i.val < 1136 then 75 else 82)) else (if i.val < 1138 then 17 else (if i.val < 1139 then 59 else 74))) else (if i.val < 1143 then (if i.val < 1141 then 59 else (if i.val < 1142 then 61 else 13)) else (if i.val < 1145 then (if i.val < 1144 then 59 else 75) else (if i.val < 1146 then 82 else 61)))) else (if i.val < 1154 then (if i.val < 1150 then (if i.val < 1148 then 59 else (if i.val < 1149 then 59 else 75)) else (if i.val < 1152 then (if i.val < 1151 then 80 else 59) else (if i.val < 1153 then 59 else 82))) else (if i.val < 1157 then (if i.val < 1155 then 59 else (if i.val < 1156 then 59 else 17)) else (if i.val < 1159 then (if i.val < 1158 then 75 else 80) else (if i.val < 1160 then 59 else 43))))) else (if i.val < 1174 then (if i.val < 1167 then (if i.val < 1164 then (if i.val < 1162 then 59 else (if i.val < 1163 then 43 else 82)) else (if i.val < 1165 then 59 else (if i.val < 1166 then 59 else 17))) else (if i.val < 1170 then (if i.val < 1168 then 7 else (if i.val < 1169 then 46 else 61)) else (if i.val < 1172 then (if i.val < 1171 then 59 else 46) else (if i.val < 1173 then 43 else 59)))) else (if i.val < 1181 then (if i.val < 1177 then (if i.val < 1175 then 43 else (if i.val < 1176 then 59 else 46)) else (if i.val < 1179 then (if i.val < 1178 then 59 else 24) else (if i.val < 1180 then 10 else 34))) else (if i.val < 1184 then (if i.val < 1182 then 17 else (if i.val < 1183 then 21 else 21)) else (if i.val < 1186 then (if i.val < 1185 then 86 else 10) else (if i.val < 1187 then 6 else 49))))))) else (if i.val < 1242 then (if i.val < 1215 then (if i.val < 1201 then (if i.val < 1194 then (if i.val < 1191 then (if i.val < 1189 then 49 else (if i.val < 1190 then 86 else 91)) else (if i.val < 1192 then 21 else (if i.val < 1193 then 17 else 21))) else (if i.val < 1197 then (if i.val < 1195 then 34 else (if i.val < 1196 then 21 else 21)) else (if i.val < 1199 then (if i.val < 1198 then 19 else 84) else (if i.val < 1200 then 21 else 61)))) else (if i.val < 1208 then (if i.val < 1204 then (if i.val < 1202 then 74 else (if i.val < 1203 then 24 else 10)) else (if i.val < 1206 then (if i.val < 1205 then 78 else 58) else (if i.val < 1207 then 21 else 86))) else (if i.val < 1211 then (if i.val < 1209 then 6 else (if i.val < 1210 then 49 else 49)) else (if i.val < 1213 then (if i.val < 1212 then 84 else 21) else (if i.val < 1214 then 61 else 10))))) else (if i.val < 1228 then (if i.val < 1221 then (if i.val < 1218 then (if i.val < 1216 then 58 else (if i.val < 1217 then 6 else 49)) else (if i.val < 1219 then 50 else (if i.val < 1220 then 30 else 59))) else (if i.val < 1224 then (if i.val < 1222 then 6 else (if i.val < 1223 then 50 else 59)) else (if i.val < 1226 then (if i.val < 1225 then 49 else 59) else (if i.val < 1227 then 21 else 49)))) else (if i.val < 1235 then (if i.val < 1231 then (if i.val < 1229 then 21 else (if i.val < 1230 then 59 else 49)) else (if i.val < 1233 then (if i.val < 1232 then 30 else 10) else (if i.val < 1234 then 17 else 21))) else (if i.val < 1238 then (if i.val < 1236 then 86 else (if i.val < 1237 then 6 else 49)) else (if i.val < 1240 then (if i.val < 1239 then 91 else 50) else (if i.val < 1241 then 30 else 21)))))) else (if i.val < 1269 then (if i.val < 1255 then (if i.val < 1248 then (if i.val < 1245 then (if i.val < 1243 then 59 else (if i.val < 1244 then 74 else 17)) else (if i.val < 1246 then 6 else (if i.val < 1247 then 50 else 59))) else (if i.val < 1251 then (if i.val < 1249 then 43 else (if i.val < 1250 then 49 else 59)) else (if i.val < 1253 then (if i.val < 1252 then 49 else 21) else (if i.val < 1254 then 59 else 21)))) else (if i.val < 1262 then (if i.val < 1258 then (if i.val < 1256 then 21 else (if i.val < 1257 then 49 else 30)) else (if i.val < 1260 then (if i.val < 1259 then 43 else 27) else (if i.val < 1261 then 10 else 17))) else (if i.val < 1265 then (if i.val < 1263 then 21 else (if i.val < 1264 then 28 else 24)) else (if i.val < 1267 then (if i.val < 1266 then 50 else 46) else (if i.val < 1268 then 86 else 61))))) else (if i.val < 1282 then (if i.val < 1275 then (if i.val < 1272 then (if i.val < 1270 then 21 else (if i.val < 1271 then 17 else 50)) else (if i.val < 1273 then 30 else (if i.val < 1274 then 21 else 59))) else (if i.val < 1278 then (if i.val < 1276 then 74 else (if i.val < 1277 then 50 else 74)) else (if i.val < 1280 then (if i.val < 1279 then 50 else 21) else (if i.val < 1281 then 46 else 50)))) else (if i.val < 1289 then (if i.val < 1285 then (if i.val < 1283 then 74 else (if i.val < 1284 then 17 else 24)) else (if i.val < 1287 then (if i.val < 1286 then 61 else 50) else (if i.val < 1288 then 59 else 74))) else (if i.val < 1292 then (if i.val < 1290 then 43 else (if i.val < 1291 then 46 else 59)) else (if i.val < 1294 then (if i.val < 1293 then 50 else 59) else (if i.val < 1295 then 21 else 50))))))))) else (if i.val < 1512 then (if i.val < 1404 then (if i.val < 1350 then (if i.val < 1323 then (if i.val < 1309 then (if i.val < 1302 then (if i.val < 1299 then (if i.val < 1297 then 21 else (if i.val < 1298 then 30 else 50)) else (if i.val < 1300 then 43 else (if i.val < 1301 then 27 else 7))) else (if i.val < 1305 then (if i.val < 1303 then 50 else (if i.val < 1304 then 10 else 57)) else (if i.val < 1307 then (if i.val < 1306 then 57 else 46) else (if i.val < 1308 then 80 else 32)))) else (if i.val < 1316 then (if i.val < 1312 then (if i.val < 1310 then 86 else (if i.val < 1311 then 57 else 72)) else (if i.val < 1314 then (if i.val < 1313 then 84 else 57) else (if i.val < 1315 then 10 else 57))) else (if i.val < 1319 then (if i.val < 1317 then 57 else (if i.val < 1318 then 35 else 66)) else (if i.val < 1321 then (if i.val < 1320 then 95 else 84) else (if i.val < 1322 then 57 else 92))))) else (if i.val < 1336 then (if i.val < 1329 then (if i.val < 1326 then (if i.val < 1324 then 21 else (if i.val < 1325 then 21 else 86)) else (if i.val < 1327 then 92 else (if i.val < 1328 then 57 else 21))) else (if i.val < 1332 then (if i.val < 1330 then 50 else (if i.val < 1331 then 57 else 21)) else (if i.val < 1334 then (if i.val < 1333 then 48 else 57) else (if i.val < 1335 then 21 else 48)))) else (if i.val < 1343 then (if i.val < 1339 then (if i.val < 1337 then 80 else (if i.val < 1338 then 32 else 41)) else (if i.val < 1341 then (if i.val < 1340 then 46 else 65) else (if i.val < 1342 then 46 else 74))) else (if i.val < 1346 then (if i.val < 1344 then 77 else (if i.val < 1345 then 84 else 29)) else (if i.val < 1348 then (if i.val < 1347 then 65 else 74) else (if i.val < 1349 then 46 else 65)))))) else (if i.val < 1377 then (if i.val < 1363 then (if i.val < 1356 then (if i.val < 1353 then (if i.val < 1351 then 48 else (if i.val < 1352 then 7 else 10)) else (if i.val < 1354 then 57 else (if i.val < 1355 then 72 else 72))) else (if i.val < 1359 then (if i.val < 1357 then 63 else (if i.val < 1358 then 43 else 43)) else (if i.val < 1361 then (if i.val < 1360 then 95 else 84) else (if i.val < 1362 then 57 else 86)))) else (if i.val < 1370 then (if i.val < 1366 then (if i.val < 1364 then 57 else (if i.val < 1365 then 57 else 35)) else (if i.val < 1368 then (if i.val < 1367 then 7 else 65) else (if i.val < 1369 then 74 else 84))) else (if i.val < 1373 then (if i.val < 1371 then 29 else (if i.val < 1372 then 65 else 74)) else (if i.val < 1375 then (if i.val < 1374 then 65 else 48) else (if i.val < 1376 then 7 else 10))))) else (if i.val < 1390 then (if i.val < 1383 then (if i.val < 1380 then (if i.val < 1378 then 57 else (if i.val < 1379 then 72 else 63)) else (if i.val < 1381 then 43 else (if i.val < 1382 then 69 else 82))) else (if i.val < 1386 then (if i.val < 1384 then 57 else (if i.val < 1385 then 49 else 29)) else (if i.val < 1388 then (if i.val < 1387 then 43 else 10) else (if i.val < 1389 then 63 else 69)))) else (if i.val < 1397 then (if i.val < 1393 then (if i.val < 1391 then 49 else (if i.val < 1392 then 59 else 30)) else (if i.val < 1395 then (if i.val < 1394 then 43 else 49) else (if i.val < 1396 then 30 else 43))) else (if i.val < 1400 then (if i.val < 1398 then 43 else (if i.val < 1399 then 57 else 49)) else (if i.val < 1402 then (if i.val < 1401 then 32 else 65) else (if i.val < 1403 then 57 else 43))))))) else (if i.val < 1458 then (if i.val < 1431 then (if i.val < 1417 then (if i.val < 1410 then (if i.val < 1407 then (if i.val < 1405 then 82 else (if i.val < 1406 then 32 else 59)) else (if i.val < 1408 then 41 else (if i.val < 1409 then 43 else 35))) else (if i.val < 1413 then (if i.val < 1411 then 43 else (if i.val < 1412 then 7 else 10)) else (if i.val < 1415 then (if i.val < 1414 then 57 else 4) else (if i.val < 1416 then 74 else 21)))) else (if i.val < 1424 then (if i.val < 1420 then (if i.val < 1418 then 86 else (if i.val < 1419 then 57 else 69)) else (if i.val < 1422 then (if i.val < 1421 then 82 else 57) else (if i.val < 1423 then 49 else 92))) else (if i.val < 1427 then (if i.val < 1425 then 21 else (if i.val < 1426 then 21 else 57)) else (if i.val < 1429 then (if i.val < 1428 then 21 else 21) else (if i.val < 1430 then 43 else 29))))) else (if i.val < 1444 then (if i.val < 1437 then (if i.val < 1434 then (if i.val < 1432 then 10 else (if i.val < 1433 then 4 else 86)) else (if i.val < 1435 then 69 else (if i.val < 1436 then 49 else 59))) else (if i.val < 1440 then (if i.val < 1438 then 21 else (if i.val < 1439 then 30 else 49)) else (if i.val < 1442 then (if i.val < 1441 then 21 else 30) else (if i.val < 1443 then 43 else 57)))) else (if i.val < 1451 then (if i.val < 1447 then (if i.val < 1445 then 49 else (if i.val < 1446 then 32 else 57)) else (if i.val < 1449 then (if i.val < 1448 then 21 else 46) else (if i.val < 1450 then 65 else 57))) else (if i.val < 1454 then (if i.val < 1452 then 74 else (if i.val < 1453 then 80 else 57)) else (if i.val < 1456 then (if i.val < 1455 then 82 else 32) else (if i.val < 1457 then 21 else 59)))))) else (if i.val < 1485 then (if i.val < 1471 then (if i.val < 1464 then (if i.val < 1461 then (if i.val < 1459 then 41 else (if i.val < 1460 then 48 else 43)) else (if i.val < 1462 then 35 else (if i.val < 1463 then 43 else 10))) else (if i.val < 1467 then (if i.val < 1465 then 4 else (if i.val < 1466 then 74 else 46)) else (if i.val < 1469 then (if i.val < 1468 then 21 else 29) else (if i.val < 1470 then 29 else 29)))) else (if i.val < 1478 then (if i.val < 1474 then (if i.val < 1472 then 92 else (if i.val < 1473 then 72 else 86)) else (if i.val < 1476 then (if i.val < 1475 then 44 else 92) else (if i.val < 1477 then 74 else 21))) else (if i.val < 1481 then (if i.val < 1479 then 84 else (if i.val < 1480 then 29 else 74)) else (if i.val < 1483 then (if i.val < 1482 then 29 else 74) else (if i.val < 1484 then 21 else 74))))) else (if i.val < 1498 then (if i.val < 1491 then (if i.val < 1488 then (if i.val < 1486 then 43 else (if i.val < 1487 then 50 else 50)) else (if i.val < 1489 then 92 else (if i.val < 1490 then 72 else 21))) else (if i.val < 1494 then (if i.val < 1492 then 50 else (if i.val < 1493 then 21 else 29)) else (if i.val < 1496 then (if i.val < 1495 then 50 else 4) else (if i.val < 1497 then 21 else 50)))) else (if i.val < 1505 then (if i.val < 1501 then (if i.val < 1499 then 59 else (if i.val < 1500 then 59 else 25)) else (if i.val < 1503 then (if i.val < 1502 then 29 else 10) else (if i.val < 1504 then 4 else 7))) else (if i.val < 1508 then (if i.val < 1506 then 46 else (if i.val < 1507 then 86 else 92)) else (if i.val < 1510 then (if i.val < 1509 then 29 else 59) else (if i.val < 1511 then 21 else 30)))))))) else (if i.val < 1620 then (if i.val < 1566 then (if i.val < 1539 then (if i.val < 1525 then (if i.val < 1518 then (if i.val < 1515 then (if i.val < 1513 then 50 else (if i.val < 1514 then 50 else 21)) else (if i.val < 1516 then 50 else (if i.val < 1517 then 50 else 74))) else (if i.val < 1521 then (if i.val < 1519 then 30 else (if i.val < 1520 then 43 else 21)) else (if i.val < 1523 then (if i.val < 1522 then 50 else 57) else (if i.val < 1524 then 74 else 25)))) else (if i.val < 1532 then (if i.val < 1528 then (if i.val < 1526 then 57 else (if i.val < 1527 then 21 else 29)) else (if i.val < 1530 then (if i.val < 1529 then 25 else 57) else (if i.val < 1531 then 74 else 80))) else (if i.val < 1535 then (if i.val < 1533 then 29 else (if i.val < 1534 then 58 else 92)) else (if i.val < 1537 then (if i.val < 1536 then 57 else 74) else (if i.val < 1538 then 48 else 74))))) else (if i.val < 1552 then (if i.val < 1545 then (if i.val < 1542 then (if i.val < 1540 then 59 else (if i.val < 1541 then 41 else 80)) else (if i.val < 1543 then 43 else (if i.val < 1544 then 50 else 58))) else (if i.val < 1548 then (if i.val < 1546 then 48 else (if i.val < 1547 then 4 else 59)) else (if i.val < 1550 then (if i.val < 1549 then 43 else 59) else (if i.val < 1551 then 24 else 27)))) else (if i.val < 1559 then (if i.val < 1555 then (if i.val < 1553 then 78 else (if i.val < 1554 then 17 else 100)) else (if i.val < 1557 then (if i.val < 1556 then 50 else 20) else (if i.val < 1558 then 27 else 41))) else (if i.val < 1562 then (if i.val < 1560 then 76 else (if i.val < 1561 then 61 else 20)) else (if i.val < 1564 then (if i.val < 1563 then 100 else 18) else (if i.val < 1565 then 8 else 48)))))) else (if i.val < 1593 then (if i.val < 1579 then (if i.val < 1572 then (if i.val < 1569 then (if i.val < 1567 then 20 else (if i.val < 1568 then 46 else 8)) else (if i.val < 1570 then 48 else (if i.val < 1571 then 41 else 46))) else (if i.val < 1575 then (if i.val < 1573 then 15 else (if i.val < 1574 then 76 else 48)) else (if i.val < 1577 then (if i.val < 1576 then 66 else 20) else (if i.val < 1578 then 8 else 2)))) else (if i.val < 1586 then (if i.val < 1582 then (if i.val < 1580 then 48 else (if i.val < 1581 then 24 else 13)) else (if i.val < 1584 then (if i.val < 1583 then 17 else 13) else (if i.val < 1585 then 17 else 17))) else (if i.val < 1589 then (if i.val < 1587 then 59 else (if i.val < 1588 then 59 else 17)) else (if i.val < 1591 then (if i.val < 1590 then 27 else 17) else (if i.val < 1592 then 34 else 20))))) else (if i.val < 1606 then (if i.val < 1599 then (if i.val < 1596 then (if i.val < 1594 then 45 else (if i.val < 1595 then 20 else 61)) else (if i.val < 1597 then 74 else (if i.val < 1598 then 45 else 61))) else (if i.val < 1602 then (if i.val < 1600 then 45 else (if i.val < 1601 then 61 else 20)) else (if i.val < 1604 then (if i.val < 1603 then 45 else 61) else (if i.val < 1605 then 20 else 27)))) else (if i.val < 1613 then (if i.val < 1609 then (if i.val < 1607 then 41 else (if i.val < 1608 then 27 else 61)) else (if i.val < 1611 then (if i.val < 1610 then 15 else 20) else (if i.val < 1612 then 46 else 15))) else (if i.val < 1616 then (if i.val < 1614 then 84 else (if i.val < 1615 then 57 else 66)) else (if i.val < 1618 then (if i.val < 1617 then 20 else 8) else (if i.val < 1619 then 35 else 72))))))) else (if i.val < 1674 then (if i.val < 1647 then (if i.val < 1633 then (if i.val < 1626 then (if i.val < 1623 then (if i.val < 1621 then 66 else (if i.val < 1622 then 84 else 57)) else (if i.val < 1624 then 35 else (if i.val < 1625 then 72 else 84))) else (if i.val < 1629 then (if i.val < 1627 then 57 else (if i.val < 1628 then 15 else 20)) else (if i.val < 1631 then (if i.val < 1630 then 84 else 46) else (if i.val < 1632 then 57 else 2)))) else (if i.val < 1640 then (if i.val < 1636 then (if i.val < 1634 then 11 else (if i.val < 1635 then 29 else 41)) else (if i.val < 1638 then (if i.val < 1637 then 20 else 11) else (if i.val < 1639 then 41 else 46))) else (if i.val < 1643 then (if i.val < 1641 then 29 else (if i.val < 1642 then 46 else 82)) else (if i.val < 1645 then (if i.val < 1644 then 91 else 21) else (if i.val < 1646 then 71 else 13))))) else (if i.val < 1660 then (if i.val < 1653 then (if i.val < 1650 then (if i.val < 1648 then 17 else (if i.val < 1649 then 30 else 21)) else (if i.val < 1651 then 30 else (if i.val < 1652 then 91 else 4))) else (if i.val < 1656 then (if i.val < 1654 then 40 else (if i.val < 1655 then 13 else 17)) else (if i.val < 1658 then (if i.val < 1657 then 30 else 30) else (if i.val < 1659 then 71 else 80)))) else (if i.val < 1667 then (if i.val < 1663 then (if i.val < 1661 then 59 else (if i.val < 1662 then 59 else 13)) else (if i.val < 1665 then (if i.val < 1664 then 30 else 59) else (if i.val < 1666 then 17 else 40))) else (if i.val < 1670 then (if i.val < 1668 then 81 else (if i.val < 1669 then 30 else 43)) else (if i.val < 1672 then (if i.val < 1671 then 30 else 43) else (if i.val < 1673 then 13 else 30)))))) else (if i.val < 1701 then (if i.val < 1687 then (if i.val < 1680 then (if i.val < 1677 then (if i.val < 1675 then 30 else (if i.val < 1676 then 91 else 95)) else (if i.val < 1678 then 17 else (if i.val < 1679 then 74 else 10))) else (if i.val < 1683 then (if i.val < 1681 then 34 else (if i.val < 1682 then 64 else 21)) else (if i.val < 1685 then (if i.val < 1684 then 21 else 45) else (if i.val < 1686 then 71 else 49)))) else (if i.val < 1694 then (if i.val < 1690 then (if i.val < 1688 then 49 else (if i.val < 1689 then 10 else 61)) else (if i.val < 1692 then (if i.val < 1691 then 74 else 34) else (if i.val < 1693 then 21 else 41))) else (if i.val < 1697 then (if i.val < 1695 then 84 else (if i.val < 1696 then 64 else 74)) else (if i.val < 1699 then (if i.val < 1698 then 74 else 63) else (if i.val < 1700 then 43 else 45))))) else (if i.val < 1714 then (if i.val < 1707 then (if i.val < 1704 then (if i.val < 1702 then 40 else (if i.val < 1703 then 49 else 49)) else (if i.val < 1705 then 84 else (if i.val < 1706 then 61 else 45))) else (if i.val < 1710 then (if i.val < 1708 then 63 else (if i.val < 1709 then 75 else 49)) else (if i.val < 1712 then (if i.val < 1711 then 50 else 59) else (if i.val < 1713 then 59 else 71)))) else (if i.val < 1721 then (if i.val < 1717 then (if i.val < 1715 then 50 else (if i.val < 1716 then 59 else 49)) else (if i.val < 1719 then (if i.val < 1718 then 59 else 43) else (if i.val < 1720 then 49 else 74))) else (if i.val < 1724 then (if i.val < 1722 then 30 else (if i.val < 1723 then 49 else 59)) else (if i.val < 1726 then (if i.val < 1725 then 10 else 45) else (if i.val < 1727 then 75 else 49))))))))))) else (if i.val < 2592 then (if i.val < 2160 then (if i.val < 1944 then (if i.val < 1836 then (if i.val < 1782 then (if i.val < 1755 then (if i.val < 1741 then (if i.val < 1734 then (if i.val < 1731 then (if i.val < 1729 then 61 else (if i.val < 1730 then 56 else 30)) else (if i.val < 1732 then 74 else (if i.val < 1733 then 30 else 74))) else (if i.val < 1737 then (if i.val < 1735 then 61 else (if i.val < 1736 then 40 else 56)) else (if i.val < 1739 then (if i.val < 1738 then 30 else 43) else (if i.val < 1740 then 49 else 30)))) else (if i.val < 1748 then (if i.val < 1744 then (if i.val < 1742 then 49 else (if i.val < 1743 then 74 else 30)) else (if i.val < 1746 then (if i.val < 1745 then 21 else 74) else (if i.val < 1747 then 49 else 30))) else (if i.val < 1751 then (if i.val < 1749 then 43 else (if i.val < 1750 then 55 else 84)) else (if i.val < 1753 then (if i.val < 1752 then 27 else 74) else (if i.val < 1754 then 50 else 84))))) else (if i.val < 1768 then (if i.val < 1761 then (if i.val < 1758 then (if i.val < 1756 then 88 else (if i.val < 1757 then 74 else 50)) else (if i.val < 1759 then 64 else (if i.val < 1760 then 74 else 61))) else (if i.val < 1764 then (if i.val < 1762 then 50 else (if i.val < 1763 then 74 else 79)) else (if i.val < 1766 then (if i.val < 1765 then 46 else 86) else (if i.val < 1767 then 34 else 34)))) else (if i.val < 1775 then (if i.val < 1771 then (if i.val < 1769 then 8 else (if i.val < 1770 then 79 else 86)) else (if i.val < 1773 then (if i.val < 1772 then 57 else 57) else (if i.val < 1774 then 57 else 66))) else (if i.val < 1778 then (if i.val < 1776 then 66 else (if i.val < 1777 then 34 else 21)) else (if i.val < 1780 then (if i.val < 1779 then 92 else 34) else (if i.val < 1781 then 21 else 46)))))) else (if i.val < 1809 then (if i.val < 1795 then (if i.val < 1788 then (if i.val < 1785 then (if i.val < 1783 then 34 else (if i.val < 1784 then 21 else 81)) else (if i.val < 1786 then 34 else (if i.val < 1787 then 80 else 48))) else (if i.val < 1791 then (if i.val < 1789 then 46 else (if i.val < 1790 then 57 else 46)) else (if i.val < 1793 then (if i.val < 1792 then 45 else 4) else (if i.val < 1794 then 57 else 46)))) else (if i.val < 1802 then (if i.val < 1798 then (if i.val < 1796 then 57 else (if i.val < 1797 then 8 else 23)) else (if i.val < 1800 then (if i.val < 1799 then 72 else 63) else (if i.val < 1801 then 21 else 21))) else (if i.val < 1805 then (if i.val < 1803 then 7 else (if i.val < 1804 then 10 else 57)) else (if i.val < 1807 then (if i.val < 1806 then 57 else 57) else (if i.val < 1808 then 15 else 23))))) else (if i.val < 1822 then (if i.val < 1815 then (if i.val < 1812 then (if i.val < 1810 then 57 else (if i.val < 1811 then 74 else 45)) else (if i.val < 1813 then 29 else (if i.val < 1814 then 57 else 74))) else (if i.val < 1818 then (if i.val < 1816 then 57 else (if i.val < 1817 then 48 else 79)) else (if i.val < 1820 then (if i.val < 1819 then 86 else 57) else (if i.val < 1821 then 72 else 89)))) else (if i.val < 1829 then (if i.val < 1825 then (if i.val < 1823 then 21 else (if i.val < 1824 then 94 else 49)) else (if i.val < 1827 then (if i.val < 1826 then 57 else 49) else (if i.val < 1828 then 29 else 43))) else (if i.val < 1832 then (if i.val < 1830 then 63 else (if i.val < 1831 then 94 else 49)) else (if i.val < 1834 then (if i.val < 1833 then 59 else 59) else (if i.val < 1835 then 21 else 49))))))) else (if i.val < 1890 then (if i.val < 1863 then (if i.val < 1849 then (if i.val < 1842 then (if i.val < 1839 then (if i.val < 1837 then 59 else (if i.val < 1838 then 43 else 21)) else (if i.val < 1840 then 57 else (if i.val < 1841 then 49 else 66))) else (if i.val < 1845 then (if i.val < 1843 then 57 else (if i.val < 1844 then 57 else 21)) else (if i.val < 1847 then (if i.val < 1846 then 49 else 15) else (if i.val < 1848 then 59 else 20)))) else (if i.val < 1856 then (if i.val < 1852 then (if i.val < 1850 then 43 else (if i.val < 1851 then 66 else 43)) else (if i.val < 1854 then (if i.val < 1853 then 7 else 34) else (if i.val < 1855 then 21 else 10))) else (if i.val < 1859 then (if i.val < 1857 then 57 else (if i.val < 1858 then 94 else 49)) else (if i.val < 1861 then (if i.val < 1860 then 57 else 49) else (if i.val < 1862 then 4 else 21))))) else (if i.val < 1876 then (if i.val < 1869 then (if i.val < 1866 then (if i.val < 1864 then 21 else (if i.val < 1865 then 34 else 21)) else (if i.val < 1867 then 24 else (if i.val < 1868 then 4 else 86))) else (if i.val < 1872 then (if i.val < 1870 then 92 else (if i.val < 1871 then 94 else 49)) else (if i.val < 1874 then (if i.val < 1873 then 30 else 30) else (if i.val < 1875 then 49 else 30)))) else (if i.val < 1883 then (if i.val < 1879 then (if i.val < 1877 then 78 else (if i.val < 1878 then 57 else 49)) else (if i.val < 1881 then (if i.val < 1880 then 15 else 34) else (if i.val < 1882 then 46 else 57))) else (if i.val < 1886 then (if i.val < 1884 then 34 else (if i.val < 1885 then 48 else 57)) else (if i.val < 1888 then (if i.val < 1887 then 49 else 66) else (if i.val < 1889 then 21 else 30)))))) else (if i.val < 1917 then (if i.val < 1903 then (if i.val < 1896 then (if i.val < 1893 then (if i.val < 1891 then 77 else (if i.val < 1892 then 80 else 78)) else (if i.val < 1894 then 15 else (if i.val < 1895 then 24 else 21))) else (if i.val < 1899 then (if i.val < 1897 then 29 else (if i.val < 1898 then 29 else 30)) else (if i.val < 1901 then (if i.val < 1900 then 59 else 23) else (if i.val < 1902 then 10 else 41)))) else (if i.val < 1910 then (if i.val < 1906 then (if i.val < 1904 then 29 else (if i.val < 1905 then 74 else 74)) else (if i.val < 1908 then (if i.val < 1907 then 74 else 74) else (if i.val < 1909 then 21 else 30))) else (if i.val < 1913 then (if i.val < 1911 then 50 else (if i.val < 1912 then 59 else 21)) else (if i.val < 1915 then (if i.val < 1914 then 50 else 45) else (if i.val < 1916 then 4 else 67))))) else (if i.val < 1930 then (if i.val < 1923 then (if i.val < 1920 then (if i.val < 1918 then 50 else (if i.val < 1919 then 45 else 29)) else (if i.val < 1921 then 29 else (if i.val < 1922 then 74 else 21))) else (if i.val < 1926 then (if i.val < 1924 then 50 else (if i.val < 1925 then 57 else 8)) else (if i.val < 1928 then (if i.val < 1927 then 29 else 2) else (if i.val < 1929 then 59 else 57)))) else (if i.val < 1937 then (if i.val < 1933 then (if i.val < 1931 then 74 else (if i.val < 1932 then 48 else 80)) else (if i.val < 1935 then (if i.val < 1934 then 81 else 59) else (if i.val < 1936 then 92 else 71))) else (if i.val < 1940 then (if i.val < 1938 then 13 else (if i.val < 1939 then 30 else 30)) else (if i.val < 1942 then (if i.val < 1941 then 40 else 71) else (if i.val < 1943 then 38 else 38)))))))) else (if i.val < 2052 then (if i.val < 1998 then (if i.val < 1971 then (if i.val < 1957 then (if i.val < 1950 then (if i.val < 1947 then (if i.val < 1945 then 40 else (if i.val < 1946 then 30 else 30)) else (if i.val < 1948 then 13 else (if i.val < 1949 then 30 else 30))) else (if i.val < 1953 then (if i.val < 1951 then 91 else (if i.val < 1952 then 75 else 92)) else (if i.val < 1955 then (if i.val < 1954 then 71 else 4) else (if i.val < 1956 then 55 else 30)))) else (if i.val < 1964 then (if i.val < 1960 then (if i.val < 1958 then 40 else (if i.val < 1959 then 38 else 38)) else (if i.val < 1962 then (if i.val < 1961 then 75 else 71) else (if i.val < 1963 then 55 else 35))) else (if i.val < 1967 then (if i.val < 1965 then 38 else (if i.val < 1966 then 25 else 38)) else (if i.val < 1969 then (if i.val < 1968 then 25 else 30) else (if i.val < 1970 then 38 else 38))))) else (if i.val < 1984 then (if i.val < 1977 then (if i.val < 1974 then (if i.val < 1972 then 71 else (if i.val < 1973 then 30 else 40)) else (if i.val < 1975 then 35 else (if i.val < 1976 then 38 else 81))) else (if i.val < 1980 then (if i.val < 1978 then 30 else (if i.val < 1979 then 25 else 38)) else (if i.val < 1982 then (if i.val < 1981 then 25 else 38) else (if i.val < 1983 then 30 else 30)))) else (if i.val < 1991 then (if i.val < 1987 then (if i.val < 1985 then 38 else (if i.val < 1986 then 71 else 30)) else (if i.val < 1989 then (if i.val < 1988 then 95 else 43) else (if i.val < 1990 then 21 else 40))) else (if i.val < 1994 then (if i.val < 1992 then 48 else (if i.val < 1993 then 30 else 30)) else (if i.val < 1996 then (if i.val < 1995 then 25 else 30) else (if i.val < 1997 then 21 else 43)))))) else (if i.val < 2025 then (if i.val < 2011 then (if i.val < 2004 then (if i.val < 2001 then (if i.val < 1999 then 25 else (if i.val < 2000 then 43 else 30)) else (if i.val < 2002 then 43 else (if i.val < 2003 then 30 else 58))) else (if i.val < 2007 then (if i.val < 2005 then 43 else (if i.val < 2006 then 71 else 49)) else (if i.val < 2009 then (if i.val < 2008 then 49 else 84) else (if i.val < 2010 then 40 else 63)))) else (if i.val < 2018 then (if i.val < 2014 then (if i.val < 2012 then 75 else (if i.val < 2013 then 49 else 71)) else (if i.val < 2016 then (if i.val < 2015 then 49 else 49) else (if i.val < 2017 then 10 else 93))) else (if i.val < 2021 then (if i.val < 2019 then 75 else (if i.val < 2020 then 49 else 56)) else (if i.val < 2023 then (if i.val < 2022 then 30 else 30) else (if i.val < 2024 then 40 else 56))))) else (if i.val < 2038 then (if i.val < 2031 then (if i.val < 2028 then (if i.val < 2026 then 49 else (if i.val < 2027 then 30 else 43)) else (if i.val < 2029 then 49 else (if i.val < 2030 then 30 else 49))) else (if i.val < 2034 then (if i.val < 2032 then 30 else (if i.val < 2033 then 84 else 17)) else (if i.val < 2036 then (if i.val < 2035 then 82 else 21) else (if i.val < 2037 then 64 else 75)))) else (if i.val < 2045 then (if i.val < 2041 then (if i.val < 2039 then 50 else (if i.val < 2040 then 58 else 71)) else (if i.val < 2043 then (if i.val < 2042 then 63 else 63) else (if i.val < 2044 then 27 else 29))) else (if i.val < 2048 then (if i.val < 2046 then 29 else (if i.val < 2047 then 93 else 75)) else (if i.val < 2050 then (if i.val < 2049 then 49 else 40) else (if i.val < 2051 then 49 else 49))))))) else (if i.val < 2106 then (if i.val < 2079 then (if i.val < 2065 then (if i.val < 2058 then (if i.val < 2055 then (if i.val < 2053 then 58 else (if i.val < 2054 then 82 else 75)) else (if i.val < 2056 then 50 else (if i.val < 2057 then 58 else 71))) else (if i.val < 2061 then (if i.val < 2059 then 49 else (if i.val < 2060 then 63 else 27)) else (if i.val < 2063 then (if i.val < 2062 then 29 else 34) else (if i.val < 2064 then 18 else 49)))) else (if i.val < 2072 then (if i.val < 2068 then (if i.val < 2066 then 38 else (if i.val < 2067 then 50 else 71)) else (if i.val < 2070 then (if i.val < 2069 then 27 else 34) else (if i.val < 2071 then 38 else 25))) else (if i.val < 2075 then (if i.val < 2073 then 29 else (if i.val < 2074 then 38 else 29)) else (if i.val < 2077 then (if i.val < 2076 then 49 else 38) else (if i.val < 2078 then 82 else 49))))) else (if i.val < 2092 then (if i.val < 2085 then (if i.val < 2082 then (if i.val < 2080 then 29 else (if i.val < 2081 then 18 else 25)) else (if i.val < 2083 then 17 else (if i.val < 2084 then 58 else 71))) else (if i.val < 2088 then (if i.val < 2086 then 49 else (if i.val < 2087 then 11 else 59)) else (if i.val < 2090 then (if i.val < 2089 then 30 else 40) else (if i.val < 2091 then 49 else 34)))) else (if i.val < 2099 then (if i.val < 2095 then (if i.val < 2093 then 18 else (if i.val < 2094 then 49 else 38)) else (if i.val < 2097 then (if i.val < 2096 then 56 else 30) else (if i.val < 2098 then 30 else 49))) else (if i.val < 2102 then (if i.val < 2100 then 30 else (if i.val < 2101 then 50 else 71)) else (if i.val < 2104 then (if i.val < 2103 then 11 else 40) else (if i.val < 2105 then 34 else 38)))))) else (if i.val < 2133 then (if i.val < 2119 then (if i.val < 2112 then (if i.val < 2109 then (if i.val < 2107 then 25 else (if i.val < 2108 then 30 else 38)) else (if i.val < 2110 then 49 else (if i.val < 2111 then 38 else 49))) else (if i.val < 2115 then (if i.val < 2113 then 30 else (if i.val < 2114 then 82 else 49)) else (if i.val < 2117 then (if i.val < 2116 then 59 else 49) else (if i.val < 2118 then 18 else 30)))) else (if i.val < 2126 then (if i.val < 2122 then (if i.val < 2120 then 25 else (if i.val < 2121 then 17 else 71)) else (if i.val < 2124 then (if i.val < 2123 then 11 else 59) else (if i.val < 2125 then 30 else 63))) else (if i.val < 2129 then (if i.val < 2127 then 40 else (if i.val < 2128 then 88 else 56)) else (if i.val < 2131 then (if i.val < 2130 then 59 else 30) else (if i.val < 2132 then 75 else 50))))) else (if i.val < 2146 then (if i.val < 2139 then (if i.val < 2136 then (if i.val < 2134 then 59 else (if i.val < 2135 then 50 else 59)) else (if i.val < 2137 then 30 else (if i.val < 2138 then 59 else 43))) else (if i.val < 2142 then (if i.val < 2140 then 43 else (if i.val < 2141 then 56 else 63)) else (if i.val < 2144 then (if i.val < 2143 then 30 else 43) else (if i.val < 2145 then 30 else 43)))) else (if i.val < 2153 then (if i.val < 2149 then (if i.val < 2147 then 30 else (if i.val < 2148 then 43 else 74)) else (if i.val < 2151 then (if i.val < 2150 then 50 else 71) else (if i.val < 2152 then 11 else 21))) else (if i.val < 2156 then (if i.val < 2154 then 40 else (if i.val < 2155 then 56 else 50)) else (if i.val < 2158 then (if i.val < 2157 then 25 else 30) else (if i.val < 2159 then 43 else 43))))))))) else (if i.val < 2376 then (if i.val < 2268 then (if i.val < 2214 then (if i.val < 2187 then (if i.val < 2173 then (if i.val < 2166 then (if i.val < 2163 then (if i.val < 2161 then 30 else (if i.val < 2162 then 43 else 59)) else (if i.val < 2164 then 30 else (if i.val < 2165 then 43 else 49))) else (if i.val < 2169 then (if i.val < 2167 then 59 else (if i.val < 2168 then 50 else 55)) else (if i.val < 2171 then (if i.val < 2170 then 49 else 59) else (if i.val < 2172 then 59 else 25)))) else (if i.val < 2180 then (if i.val < 2176 then (if i.val < 2174 then 17 else (if i.val < 2175 then 43 else 55)) else (if i.val < 2178 then (if i.val < 2177 then 58 else 21) else (if i.val < 2179 then 21 else 34))) else (if i.val < 2183 then (if i.val < 2181 then 66 else (if i.val < 2182 then 23 else 45)) else (if i.val < 2185 then (if i.val < 2184 then 79 else 98) else (if i.val < 2186 then 89 else 21))))) else (if i.val < 2200 then (if i.val < 2193 then (if i.val < 2190 then (if i.val < 2188 then 94 else (if i.val < 2189 then 49 else 49)) else (if i.val < 2191 then 63 else (if i.val < 2192 then 94 else 21))) else (if i.val < 2196 then (if i.val < 2194 then 49 else (if i.val < 2195 then 21 else 49)) else (if i.val < 2198 then (if i.val < 2197 then 15 else 66) else (if i.val < 2199 then 7 else 34)))) else (if i.val < 2207 then (if i.val < 2203 then (if i.val < 2201 then 10 else (if i.val < 2202 then 94 else 49)) else (if i.val < 2205 then (if i.val < 2204 then 34 else 49) else (if i.val < 2206 then 4 else 24))) else (if i.val < 2210 then (if i.val < 2208 then 94 else (if i.val < 2209 then 30 else 49)) else (if i.val < 2212 then (if i.val < 2211 then 78 else 21) else (if i.val < 2213 then 49 else 15)))))) else (if i.val < 2241 then (if i.val < 2227 then (if i.val < 2220 then (if i.val < 2217 then (if i.val < 2215 then 34 else (if i.val < 2216 then 43 else 49)) else (if i.val < 2218 then 66 else (if i.val < 2219 then 30 else 77))) else (if i.val < 2223 then (if i.val < 2221 then 78 else (if i.val < 2222 then 15 else 24)) else (if i.val < 2225 then (if i.val < 2224 then 49 else 45) else (if i.val < 2226 then 4 else 69)))) else (if i.val < 2234 then (if i.val < 2230 then (if i.val < 2228 then 49 else (if i.val < 2229 then 21 else 8)) else (if i.val < 2232 then (if i.val < 2231 then 32 else 58) else (if i.val < 2233 then 21 else 63))) else (if i.val < 2237 then (if i.val < 2235 then 21 else (if i.val < 2236 then 98 else 89)) else (if i.val < 2239 then (if i.val < 2238 then 21 else 63) else (if i.val < 2240 then 21 else 21))))) else (if i.val < 2254 then (if i.val < 2247 then (if i.val < 2244 then (if i.val < 2242 then 72 else (if i.val < 2243 then 43 else 94)) else (if i.val < 2245 then 49 else (if i.val < 2246 then 49 else 94))) else (if i.val < 2250 then (if i.val < 2248 then 43 else (if i.val < 2249 then 49 else 49)) else (if i.val < 2252 then (if i.val < 2251 then 66 else 15) else (if i.val < 2253 then 21 else 49)))) else (if i.val < 2261 then (if i.val < 2257 then (if i.val < 2255 then 58 else (if i.val < 2256 then 69 else 21)) else (if i.val < 2259 then (if i.val < 2258 then 49 else 21) else (if i.val < 2260 then 32 else 58))) else (if i.val < 2264 then (if i.val < 2262 then 21 else (if i.val < 2263 then 69 else 13)) else (if i.val < 2266 then (if i.val < 2265 then 49 else 63) else (if i.val < 2267 then 21 else 25))))))) else (if i.val < 2322 then (if i.val < 2295 then (if i.val < 2281 then (if i.val < 2274 then (if i.val < 2271 then (if i.val < 2269 then 30 else (if i.val < 2270 then 21 else 29)) else (if i.val < 2272 then 49 else (if i.val < 2273 then 21 else 49))) else (if i.val < 2277 then (if i.val < 2275 then 49 else (if i.val < 2276 then 13 else 69)) else (if i.val < 2279 then (if i.val < 2278 then 58 else 69) else (if i.val < 2280 then 63 else 25)))) else (if i.val < 2288 then (if i.val < 2284 then (if i.val < 2282 then 29 else (if i.val < 2283 then 38 else 18)) else (if i.val < 2286 then (if i.val < 2285 then 29 else 49) else (if i.val < 2287 then 18 else 13))) else (if i.val < 2291 then (if i.val < 2289 then 21 else (if i.val < 2290 then 29 else 7)) else (if i.val < 2293 then (if i.val < 2292 then 49 else 21) else (if i.val < 2294 then 21 else 13))))) else (if i.val < 2308 then (if i.val < 2301 then (if i.val < 2298 then (if i.val < 2296 then 66 else (if i.val < 2297 then 21 else 30)) else (if i.val < 2299 then 7 else (if i.val < 2300 then 49 else 38))) else (if i.val < 2304 then (if i.val < 2302 then 45 else (if i.val < 2303 then 15 else 13)) else (if i.val < 2306 then (if i.val < 2305 then 72 else 13) else (if i.val < 2307 then 58 else 69)))) else (if i.val < 2315 then (if i.val < 2311 then (if i.val < 2309 then 13 else (if i.val < 2310 then 34 else 49)) else (if i.val < 2313 then (if i.val < 2312 then 78 else 69) else (if i.val < 2314 then 13 else 49))) else (if i.val < 2318 then (if i.val < 2316 then 94 else (if i.val < 2317 then 49 else 49)) else (if i.val < 2320 then (if i.val < 2319 then 49 else 13) else (if i.val < 2321 then 30 else 30)))))) else (if i.val < 2349 then (if i.val < 2335 then (if i.val < 2328 then (if i.val < 2325 then (if i.val < 2323 then 49 else (if i.val < 2324 then 30 else 49)) else (if i.val < 2326 then 59 else (if i.val < 2327 then 24 else 49))) else (if i.val < 2331 then (if i.val < 2329 then 69 else (if i.val < 2330 then 58 else 69)) else (if i.val < 2333 then (if i.val < 2332 then 30 else 69) else (if i.val < 2334 then 94 else 38)))) else (if i.val < 2342 then (if i.val < 2338 then (if i.val < 2336 then 18 else (if i.val < 2337 then 49 else 59)) else (if i.val < 2340 then (if i.val < 2339 then 30 else 49) else (if i.val < 2341 then 18 else 13))) else (if i.val < 2345 then (if i.val < 2343 then 49 else (if i.val < 2344 then 21 else 49)) else (if i.val < 2347 then (if i.val < 2346 then 34 else 43) else (if i.val < 2348 then 49 else 21))))) else (if i.val < 2362 then (if i.val < 2355 then (if i.val < 2352 then (if i.val < 2350 then 13 else (if i.val < 2351 then 66 else 78)) else (if i.val < 2353 then 13 else (if i.val < 2354 then 15 else 49))) else (if i.val < 2358 then (if i.val < 2356 then 38 else (if i.val < 2357 then 45 else 66)) else (if i.val < 2360 then (if i.val < 2359 then 13 else 77) else (if i.val < 2361 then 15 else 24)))) else (if i.val < 2369 then (if i.val < 2365 then (if i.val < 2363 then 13 else (if i.val < 2364 then 69 else 13)) else (if i.val < 2367 then (if i.val < 2366 then 92 else 78) else (if i.val < 2368 then 50 else 50))) else (if i.val < 2372 then (if i.val < 2370 then 63 else (if i.val < 2371 then 69 else 13)) else (if i.val < 2374 then (if i.val < 2373 then 74 else 74) else (if i.val < 2375 then 74 else 24)))))))) else (if i.val < 2484 then (if i.val < 2430 then (if i.val < 2403 then (if i.val < 2389 then (if i.val < 2382 then (if i.val < 2379 then (if i.val < 2377 then 86 else (if i.val < 2378 then 49 else 59)) else (if i.val < 2380 then 59 else (if i.val < 2381 then 80 else 49))) else (if i.val < 2385 then (if i.val < 2383 then 59 else (if i.val < 2384 then 74 else 59)) else (if i.val < 2387 then (if i.val < 2386 then 78 else 49) else (if i.val < 2388 then 59 else 43)))) else (if i.val < 2396 then (if i.val < 2392 then (if i.val < 2390 then 43 else (if i.val < 2391 then 28 else 92)) else (if i.val < 2394 then (if i.val < 2393 then 43 else 49) else (if i.val < 2395 then 43 else 100))) else (if i.val < 2399 then (if i.val < 2397 then 59 else (if i.val < 2398 then 24 else 49)) else (if i.val < 2401 then (if i.val < 2400 then 30 else 78) else (if i.val < 2402 then 43 else 100))))) else (if i.val < 2416 then (if i.val < 2409 then (if i.val < 2406 then (if i.val < 2404 then 55 else (if i.val < 2405 then 24 else 27)) else (if i.val < 2407 then 67 else (if i.val < 2408 then 29 else 69))) else (if i.val < 2412 then (if i.val < 2410 then 30 else (if i.val < 2411 then 63 else 69)) else (if i.val < 2414 then (if i.val < 2413 then 48 else 30) else (if i.val < 2415 then 59 else 59)))) else (if i.val < 2423 then (if i.val < 2419 then (if i.val < 2417 then 59 else (if i.val < 2418 then 59 else 43)) else (if i.val < 2421 then (if i.val < 2420 then 30 else 43) else (if i.val < 2422 then 59 else 50))) else (if i.val < 2426 then (if i.val < 2424 then 21 else (if i.val < 2425 then 27 else 43)) else (if i.val < 2428 then (if i.val < 2427 then 49 else 59) else (if i.val < 2429 then 49 else 30)))))) else (if i.val < 2457 then (if i.val < 2443 then (if i.val < 2436 then (if i.val < 2433 then (if i.val < 2431 then 21 else (if i.val < 2432 then 29 else 74)) else (if i.val < 2434 then 13 else (if i.val < 2435 then 78 else 2))) else (if i.val < 2439 then (if i.val < 2437 then 21 else (if i.val < 2438 then 13 else 74)) else (if i.val < 2441 then (if i.val < 2440 then 20 else 24) else (if i.val < 2442 then 49 else 59)))) else (if i.val < 2450 then (if i.val < 2446 then (if i.val < 2444 then 20 else (if i.val < 2445 then 78 else 43)) else (if i.val < 2448 then (if i.val < 2447 then 100 else 24) else (if i.val < 2449 then 78 else 100))) else (if i.val < 2453 then (if i.val < 2451 then 43 else (if i.val < 2452 then 24 else 28)) else (if i.val < 2455 then (if i.val < 2454 then 43 else 61) else (if i.val < 2456 then 17 else 87))))) else (if i.val < 2470 then (if i.val < 2463 then (if i.val < 2460 then (if i.val < 2458 then 61 else (if i.val < 2459 then 65 else 77)) else (if i.val < 2461 then 20 else (if i.val < 2462 then 61 else 17))) else (if i.val < 2466 then (if i.val < 2464 then 86 else (if i.val < 2465 then 87 else 20)) else (if i.val < 2468 then (if i.val < 2467 then 10 else 61) else (if i.val < 2469 then 15 else 19)))) else (if i.val < 2477 then (if i.val < 2473 then (if i.val < 2471 then 15 else (if i.val < 2472 then 48 else 35)) else (if i.val < 2475 then (if i.val < 2474 then 35 else 7) else (if i.val < 2476 then 15 else 58))) else (if i.val < 2480 then (if i.val < 2478 then 25 else (if i.val < 2479 then 29 else 76)) else (if i.val < 2482 then (if i.val < 2481 then 13 else 61) else (if i.val < 2483 then 6 else 61))))))) else (if i.val < 2538 then (if i.val < 2511 then (if i.val < 2497 then (if i.val < 2490 then (if i.val < 2487 then (if i.val < 2485 then 59 else (if i.val < 2486 then 6 else 6)) else (if i.val < 2488 then 61 else (if i.val < 2489 then 6 else 61))) else (if i.val < 2493 then (if i.val < 2491 then 72 else (if i.val < 2492 then 17 else 86)) else (if i.val < 2495 then (if i.val < 2494 then 61 else 86) else (if i.val < 2496 then 75 else 10)))) else (if i.val < 2504 then (if i.val < 2500 then (if i.val < 2498 then 61 else (if i.val < 2499 then 63 else 10)) else (if i.val < 2502 then (if i.val < 2501 then 75 else 63) else (if i.val < 2503 then 75 else 86))) else (if i.val < 2507 then (if i.val < 2505 then 61 else (if i.val < 2506 then 75 else 78)) else (if i.val < 2509 then (if i.val < 2508 then 17 else 61) else (if i.val < 2510 then 78 else 17))))) else (if i.val < 2524 then (if i.val < 2517 then (if i.val < 2514 then (if i.val < 2512 then 86 else (if i.val < 2513 then 57 else 7)) else (if i.val < 2515 then 15 else (if i.val < 2516 then 7 else 58))) else (if i.val < 2520 then (if i.val < 2518 then 43 else (if i.val < 2519 then 72 else 58)) else (if i.val < 2522 then (if i.val < 2521 then 43 else 86) else (if i.val < 2523 then 57 else 76)))) else (if i.val < 2531 then (if i.val < 2527 then (if i.val < 2525 then 4 else (if i.val < 2526 then 74 else 72)) else (if i.val < 2529 then (if i.val < 2528 then 46 else 4) else (if i.val < 2530 then 29 else 63))) else (if i.val < 2534 then (if i.val < 2532 then 74 else (if i.val < 2533 then 59 else 71)) else (if i.val < 2536 then (if i.val < 2535 then 13 else 30) else (if i.val < 2537 then 30 else 6)))))) else (if i.val < 2565 then (if i.val < 2551 then (if i.val < 2544 then (if i.val < 2541 then (if i.val < 2539 then 38 else (if i.val < 2540 then 38 else 71)) else (if i.val < 2542 then 13 else (if i.val < 2543 then 30 else 17))) else (if i.val < 2547 then (if i.val < 2545 then 75 else (if i.val < 2546 then 59 else 27)) else (if i.val < 2549 then (if i.val < 2548 then 29 else 6) else (if i.val < 2550 then 38 else 38)))) else (if i.val < 2558 then (if i.val < 2554 then (if i.val < 2552 then 75 else (if i.val < 2553 then 6 else 27)) else (if i.val < 2556 then (if i.val < 2555 then 32 else 38) else (if i.val < 2557 then 25 else 38))) else (if i.val < 2561 then (if i.val < 2559 then 25 else (if i.val < 2560 then 29 else 38)) else (if i.val < 2563 then (if i.val < 2562 then 38 else 71) else (if i.val < 2564 then 6 else 32))))) else (if i.val < 2578 then (if i.val < 2571 then (if i.val < 2568 then (if i.val < 2566 then 38 else (if i.val < 2567 then 48 else 46)) else (if i.val < 2569 then 38 else (if i.val < 2570 then 46 else 38))) else (if i.val < 2574 then (if i.val < 2572 then 38 else (if i.val < 2573 then 75 else 72)) else (if i.val < 2576 then (if i.val < 2575 then 75 else 98) else (if i.val < 2577 then 3 else 21)))) else (if i.val < 2585 then (if i.val < 2581 then (if i.val < 2579 then 40 else (if i.val < 2580 then 13 else 13)) else (if i.val < 2583 then (if i.val < 2582 then 3 else 40) else (if i.val < 2584 then 49 else 10))) else (if i.val < 2588 then (if i.val < 2586 then 56 else (if i.val < 2587 then 30 else 21)) else (if i.val < 2590 then (if i.val < 2589 then 13 else 30) else (if i.val < 2591 then 6 else 11)))))))))) else (if i.val < 3024 then (if i.val < 2808 then (if i.val < 2700 then (if i.val < 2646 then (if i.val < 2619 then (if i.val < 2605 then (if i.val < 2598 then (if i.val < 2595 then (if i.val < 2593 then 89 else (if i.val < 2594 then 63 else 27)) else (if i.val < 2596 then 30 else (if i.val < 2597 then 30 else 58))) else (if i.val < 2601 then (if i.val < 2599 then 71 else (if i.val < 2600 then 89 else 6)) else (if i.val < 2603 then (if i.val < 2602 then 50 else 3) else (if i.val < 2604 then 40 else 49)))) else (if i.val < 2612 then (if i.val < 2608 then (if i.val < 2606 then 63 else (if i.val < 2607 then 51 else 30)) else (if i.val < 2610 then (if i.val < 2609 then 31 else 38) else (if i.val < 2611 then 38 else 50))) else (if i.val < 2615 then (if i.val < 2613 then 27 else (if i.val < 2614 then 31 else 38)) else (if i.val < 2617 then (if i.val < 2616 then 25 else 30) else (if i.val < 2618 then 38 else 30))))) else (if i.val < 2632 then (if i.val < 2625 then (if i.val < 2622 then (if i.val < 2620 then 38 else (if i.val < 2621 then 30 else 38)) else (if i.val < 2623 then 25 else (if i.val < 2624 then 61 else 58))) else (if i.val < 2628 then (if i.val < 2626 then 71 else (if i.val < 2627 then 31 else 38)) else (if i.val < 2630 then (if i.val < 2629 then 38 else 11) else (if i.val < 2631 then 13 else 30)))) else (if i.val < 2639 then (if i.val < 2635 then (if i.val < 2633 then 11 else (if i.val < 2634 then 40 else 56)) else (if i.val < 2637 then (if i.val < 2636 then 31 else 38) else (if i.val < 2638 then 46 else 38))) else (if i.val < 2642 then (if i.val < 2640 then 38 else (if i.val < 2641 then 13 else 38)) else (if i.val < 2644 then (if i.val < 2643 then 46 else 64) else (if i.val < 2645 then 89 else 71)))))) else (if i.val < 2673 then (if i.val < 2659 then (if i.val < 2652 then (if i.val < 2649 then (if i.val < 2647 then 17 else (if i.val < 2648 then 50 else 59)) else (if i.val < 2650 then 59 else (if i.val < 2651 then 6 else 11))) else (if i.val < 2655 then (if i.val < 2653 then 6 else (if i.val < 2654 then 50 else 50)) else (if i.val < 2657 then (if i.val < 2656 then 89 else 21) else (if i.val < 2658 then 21 else 15)))) else (if i.val < 2666 then (if i.val < 2662 then (if i.val < 2660 then 48 else (if i.val < 2661 then 58 else 21)) else (if i.val < 2664 then (if i.val < 2663 then 5 else 21) else (if i.val < 2665 then 21 else 35))) else (if i.val < 2669 then (if i.val < 2667 then 32 else (if i.val < 2668 then 57 else 57)) else (if i.val < 2671 then (if i.val < 2670 then 49 else 49) else (if i.val < 2672 then 21 else 13))))) else (if i.val < 2686 then (if i.val < 2679 then (if i.val < 2676 then (if i.val < 2674 then 66 else (if i.val < 2675 then 57 else 66)) else (if i.val < 2677 then 15 else (if i.val < 2678 then 5 else 80))) else (if i.val < 2682 then (if i.val < 2680 then 35 else (if i.val < 2681 then 3 else 21)) else (if i.val < 2684 then (if i.val < 2683 then 43 else 43) else (if i.val < 2685 then 43 else 72)))) else (if i.val < 2693 then (if i.val < 2689 then (if i.val < 2687 then 5 else (if i.val < 2688 then 35 else 32)) else (if i.val < 2691 then (if i.val < 2690 then 21 else 49) else (if i.val < 2692 then 3 else 5))) else (if i.val < 2696 then (if i.val < 2694 then 21 else (if i.val < 2695 then 49 else 21)) else (if i.val < 2698 then (if i.val < 2697 then 35 else 58) else (if i.val < 2699 then 21 else 5))))))) else (if i.val < 2754 then (if i.val < 2727 then (if i.val < 2713 then (if i.val < 2706 then (if i.val < 2703 then (if i.val < 2701 then 49 else (if i.val < 2702 then 43 else 56)) else (if i.val < 2704 then 30 else (if i.val < 2705 then 43 else 30))) else (if i.val < 2709 then (if i.val < 2707 then 21 else (if i.val < 2708 then 83 else 5)) else (if i.val < 2711 then (if i.val < 2710 then 56 else 30) else (if i.val < 2712 then 38 else 38)))) else (if i.val < 2720 then (if i.val < 2716 then (if i.val < 2714 then 30 else (if i.val < 2715 then 38 else 52)) else (if i.val < 2718 then (if i.val < 2717 then 43 else 30) else (if i.val < 2719 then 7 else 21))) else (if i.val < 2723 then (if i.val < 2721 then 21 else (if i.val < 2722 then 49 else 32)) else (if i.val < 2725 then (if i.val < 2724 then 43 else 30) else (if i.val < 2726 then 7 else 38))))) else (if i.val < 2740 then (if i.val < 2733 then (if i.val < 2730 then (if i.val < 2728 then 45 else (if i.val < 2729 then 35 else 52)) else (if i.val < 2731 then 72 else (if i.val < 2732 then 83 else 49))) else (if i.val < 2736 then (if i.val < 2734 then 5 else (if i.val < 2735 then 83 else 49)) else (if i.val < 2738 then (if i.val < 2737 then 5 else 69) else (if i.val < 2739 then 38 else 38)))) else (if i.val < 2747 then (if i.val < 2743 then (if i.val < 2741 then 38 else (if i.val < 2742 then 52 else 21)) else (if i.val < 2745 then (if i.val < 2744 then 57 else 43) else (if i.val < 2746 then 15 else 32))) else (if i.val < 2750 then (if i.val < 2748 then 38 else (if i.val < 2749 then 45 else 35)) else (if i.val < 2752 then (if i.val < 2751 then 52 else 20) else (if i.val < 2753 then 66 else 83)))))) else (if i.val < 2781 then (if i.val < 2767 then (if i.val < 2760 then (if i.val < 2757 then (if i.val < 2755 then 49 else (if i.val < 2756 then 74 else 74)) else (if i.val < 2758 then 21 else (if i.val < 2759 then 43 else 21))) else (if i.val < 2763 then (if i.val < 2761 then 59 else (if i.val < 2762 then 43 else 59)) else (if i.val < 2765 then (if i.val < 2764 then 55 else 5) else (if i.val < 2766 then 3 else 5)))) else (if i.val < 2774 then (if i.val < 2770 then (if i.val < 2768 then 1 else (if i.val < 2769 then 59 else 59)) else (if i.val < 2772 then (if i.val < 2771 then 21 else 49) else (if i.val < 2773 then 74 else 76))) else (if i.val < 2777 then (if i.val < 2775 then 43 else (if i.val < 2776 then 43 else 55)) else (if i.val < 2779 then (if i.val < 2778 then 29 else 38) else (if i.val < 2780 then 38 else 75))))) else (if i.val < 2794 then (if i.val < 2787 then (if i.val < 2784 then (if i.val < 2782 then 27 else (if i.val < 2783 then 38 else 38)) else (if i.val < 2785 then 38 else (if i.val < 2786 then 71 else 38))) else (if i.val < 2790 then (if i.val < 2788 then 46 else (if i.val < 2789 then 38 else 46)) else (if i.val < 2792 then (if i.val < 2791 then 29 else 38) else (if i.val < 2793 then 38 else 75)))) else (if i.val < 2801 then (if i.val < 2797 then (if i.val < 2795 then 55 else (if i.val < 2796 then 27 else 27)) else (if i.val < 2799 then (if i.val < 2798 then 50 else 50) else (if i.val < 2800 then 38 else 38))) else (if i.val < 2804 then (if i.val < 2802 then 38 else (if i.val < 2803 then 55 else 55)) else (if i.val < 2806 then (if i.val < 2805 then 66 else 38) else (if i.val < 2807 then 27 else 72)))))))) else (if i.val < 2916 then (if i.val < 2862 then (if i.val < 2835 then (if i.val < 2821 then (if i.val < 2814 then (if i.val < 2811 then (if i.val < 2809 then 50 else (if i.val < 2810 then 38 else 57)) else (if i.val < 2812 then 50 else (if i.val < 2813 then 57 else 50))) else (if i.val < 2817 then (if i.val < 2815 then 38 else (if i.val < 2816 then 38 else 50)) else (if i.val < 2819 then (if i.val < 2818 then 55 else 38) else (if i.val < 2820 then 46 else 38)))) else (if i.val < 2828 then (if i.val < 2824 then (if i.val < 2822 then 38 else (if i.val < 2823 then 57 else 38)) else (if i.val < 2826 then (if i.val < 2825 then 46 else 57) else (if i.val < 2827 then 38 else 38))) else (if i.val < 2831 then (if i.val < 2829 then 38 else (if i.val < 2830 then 38 else 46)) else (if i.val < 2833 then (if i.val < 2832 then 27 else 15) else (if i.val < 2834 then 98 else 25))))) else (if i.val < 2848 then (if i.val < 2841 then (if i.val < 2838 then (if i.val < 2836 then 46 else (if i.val < 2837 then 46 else 25)) else (if i.val < 2839 then 46 else (if i.val < 2840 then 46 else 25))) else (if i.val < 2844 then (if i.val < 2842 then 46 else (if i.val < 2843 then 38 else 38)) else (if i.val < 2846 then (if i.val < 2845 then 25 else 55) else (if i.val < 2847 then 30 else 30)))) else (if i.val < 2855 then (if i.val < 2851 then (if i.val < 2849 then 89 else (if i.val < 2850 then 6 else 3)) else (if i.val < 2853 then (if i.val < 2852 then 44 else 51) else (if i.val < 2854 then 30 else 31))) else (if i.val < 2858 then (if i.val < 2856 then 38 else (if i.val < 2857 then 38 else 27)) else (if i.val < 2860 then (if i.val < 2859 then 31 else 30) else (if i.val < 2861 then 38 else 30)))))) else (if i.val < 2889 then (if i.val < 2875 then (if i.val < 2868 then (if i.val < 2865 then (if i.val < 2863 then 38 else (if i.val < 2864 then 58 else 71)) else (if i.val < 2866 then 31 else (if i.val < 2867 then 38 else 38))) else (if i.val < 2871 then (if i.val < 2869 then 11 else (if i.val < 2870 then 31 else 46)) else (if i.val < 2873 then (if i.val < 2872 then 38 else 30) else (if i.val < 2874 then 38 else 38)))) else (if i.val < 2882 then (if i.val < 2878 then (if i.val < 2876 then 46 else (if i.val < 2877 then 64 else 6)) else (if i.val < 2880 then (if i.val < 2879 then 11 else 34) else (if i.val < 2881 then 55 else 27))) else (if i.val < 2885 then (if i.val < 2883 then 30 else (if i.val < 2884 then 44 else 51)) else (if i.val < 2887 then (if i.val < 2886 then 30 else 27) else (if i.val < 2888 then 30 else 30))))) else (if i.val < 2902 then (if i.val < 2895 then (if i.val < 2892 then (if i.val < 2890 then 31 else (if i.val < 2891 then 38 else 38)) else (if i.val < 2893 then 31 else (if i.val < 2894 then 38 else 38))) else (if i.val < 2898 then (if i.val < 2896 then 30 else (if i.val < 2897 then 55 else 34)) else (if i.val < 2900 then (if i.val < 2899 then 55 else 30) else (if i.val < 2901 then 34 else 69)))) else (if i.val < 2909 then (if i.val < 2905 then (if i.val < 2903 then 38 else (if i.val < 2904 then 27 else 30)) else (if i.val < 2907 then (if i.val < 2906 then 74 else 46) else (if i.val < 2908 then 30 else 50))) else (if i.val < 2912 then (if i.val < 2910 then 30 else (if i.val < 2911 then 38 else 38)) else (if i.val < 2914 then (if i.val < 2913 then 34 else 55) else (if i.val < 2915 then 34 else 27))))))) else (if i.val < 2970 then (if i.val < 2943 then (if i.val < 2929 then (if i.val < 2922 then (if i.val < 2919 then (if i.val < 2917 then 74 else (if i.val < 2918 then 50 else 57)) else (if i.val < 2920 then 50 else (if i.val < 2921 then 38 else 30))) else (if i.val < 2925 then (if i.val < 2923 then 50 else (if i.val < 2924 then 38 else 30)) else (if i.val < 2927 then (if i.val < 2926 then 30 else 69) else (if i.val < 2928 then 30 else 46)))) else (if i.val < 2936 then (if i.val < 2932 then (if i.val < 2930 then 57 else (if i.val < 2931 then 6 else 55)) else (if i.val < 2934 then (if i.val < 2933 then 34 else 69) else (if i.val < 2935 then 38 else 34))) else (if i.val < 2939 then (if i.val < 2937 then 69 else (if i.val < 2938 then 38 else 31)) else (if i.val < 2941 then (if i.val < 2940 then 38 else 38) else (if i.val < 2942 then 46 else 38))))) else (if i.val < 2956 then (if i.val < 2949 then (if i.val < 2946 then (if i.val < 2944 then 38 else (if i.val < 2945 then 34 else 55)) else (if i.val < 2947 then 34 else (if i.val < 2948 then 46 else 34))) else (if i.val < 2952 then (if i.val < 2950 then 31 else (if i.val < 2951 then 57 else 38)) else (if i.val < 2954 then (if i.val < 2953 then 38 else 30) else (if i.val < 2955 then 38 else 38)))) else (if i.val < 2963 then (if i.val < 2959 then (if i.val < 2957 then 30 else (if i.val < 2958 then 69 else 69)) else (if i.val < 2961 then (if i.val < 2960 then 57 else 6) else (if i.val < 2962 then 64 else 34))) else (if i.val < 2966 then (if i.val < 2964 then 69 else (if i.val < 2965 then 56 else 27)) else (if i.val < 2968 then (if i.val < 2967 then 34 else 69) else (if i.val < 2969 then 40 else 38)))))) else (if i.val < 2997 then (if i.val < 2983 then (if i.val < 2976 then (if i.val < 2973 then (if i.val < 2971 then 25 else (if i.val < 2972 then 25 else 41)) else (if i.val < 2974 then 38 else (if i.val < 2975 then 25 else 25))) else (if i.val < 2979 then (if i.val < 2977 then 38 else (if i.val < 2978 then 25 else 56)) else (if i.val < 2981 then (if i.val < 2980 then 38 else 38) else (if i.val < 2982 then 67 else 50)))) else (if i.val < 2990 then (if i.val < 2986 then (if i.val < 2984 then 34 else (if i.val < 2985 then 46 else 27)) else (if i.val < 2988 then (if i.val < 2987 then 34 else 46) else (if i.val < 2989 then 25 else 25))) else (if i.val < 2993 then (if i.val < 2991 then 25 else (if i.val < 2992 then 46 else 38)) else (if i.val < 2995 then (if i.val < 2994 then 25 else 38) else (if i.val < 2996 then 69 else 30))))) else (if i.val < 3010 then (if i.val < 3003 then (if i.val < 3000 then (if i.val < 2998 then 69 else (if i.val < 2999 then 59 else 61)) else (if i.val < 3001 then 38 else (if i.val < 3002 then 25 else 61))) else (if i.val < 3006 then (if i.val < 3004 then 67 else (if i.val < 3005 then 7 else 3)) else (if i.val < 3008 then (if i.val < 3007 then 5 else 58) else (if i.val < 3009 then 25 else 56)))) else (if i.val < 3017 then (if i.val < 3013 then (if i.val < 3011 then 30 else (if i.val < 3012 then 30 else 83)) else (if i.val < 3015 then (if i.val < 3014 then 56 else 25) else (if i.val < 3016 then 30 else 38))) else (if i.val < 3020 then (if i.val < 3018 then 52 else (if i.val < 3019 then 30 else 7)) else (if i.val < 3022 then (if i.val < 3021 then 52 else 72) else (if i.val < 3023 then 83 else 80))))))))) else (if i.val < 3240 then (if i.val < 3132 then (if i.val < 3078 then (if i.val < 3051 then (if i.val < 3037 then (if i.val < 3030 then (if i.val < 3027 then (if i.val < 3025 then 49 else (if i.val < 3026 then 49 else 83)) else (if i.val < 3028 then 52 else (if i.val < 3029 then 72 else 52))) else (if i.val < 3033 then (if i.val < 3031 then 83 else (if i.val < 3032 then 49 else 5)) else (if i.val < 3035 then (if i.val < 3034 then 49 else 56) else (if i.val < 3036 then 30 else 30)))) else (if i.val < 3044 then (if i.val < 3040 then (if i.val < 3038 then 56 else (if i.val < 3039 then 30 else 25)) else (if i.val < 3042 then (if i.val < 3041 then 30 else 7) else (if i.val < 3043 then 72 else 83))) else (if i.val < 3047 then (if i.val < 3045 then 52 else (if i.val < 3046 then 52 else 83)) else (if i.val < 3049 then (if i.val < 3048 then 29 else 25) else (if i.val < 3050 then 29 else 7))))) else (if i.val < 3064 then (if i.val < 3057 then (if i.val < 3054 then (if i.val < 3052 then 56 else (if i.val < 3053 then 29 else 30)) else (if i.val < 3055 then 13 else (if i.val < 3056 then 11 else 29))) else (if i.val < 3060 then (if i.val < 3058 then 30 else (if i.val < 3059 then 30 else 30)) else (if i.val < 3062 then (if i.val < 3061 then 30 else 59) else (if i.val < 3063 then 30 else 13)))) else (if i.val < 3071 then (if i.val < 3067 then (if i.val < 3065 then 25 else (if i.val < 3066 then 56 else 38)) else (if i.val < 3069 then (if i.val < 3068 then 11 else 50) else (if i.val < 3070 then 46 else 30))) else (if i.val < 3074 then (if i.val < 3072 then 46 else (if i.val < 3073 then 59 else 25)) else (if i.val < 3076 then (if i.val < 3075 then 30 else 29) else (if i.val < 3077 then 7 else 13)))))) else (if i.val < 3105 then (if i.val < 3091 then (if i.val < 3084 then (if i.val < 3081 then (if i.val < 3079 then 29 else (if i.val < 3080 then 72 else 30)) else (if i.val < 3082 then 50 else (if i.val < 3083 then 63 else 7))) else (if i.val < 3087 then (if i.val < 3085 then 59 else (if i.val < 3086 then 72 else 13)) else (if i.val < 3089 then (if i.val < 3088 then 59 else 56) else (if i.val < 3090 then 29 else 69)))) else (if i.val < 3098 then (if i.val < 3094 then (if i.val < 3092 then 13 else (if i.val < 3093 then 13 else 30)) else (if i.val < 3096 then (if i.val < 3095 then 13 else 30) else (if i.val < 3097 then 38 else 52))) else (if i.val < 3101 then (if i.val < 3099 then 83 else (if i.val < 3100 then 61 else 69)) else (if i.val < 3103 then (if i.val < 3102 then 13 else 56) else (if i.val < 3104 then 38 else 38))))) else (if i.val < 3118 then (if i.val < 3111 then (if i.val < 3108 then (if i.val < 3106 then 38 else (if i.val < 3107 then 38 else 69)) else (if i.val < 3109 then 46 else (if i.val < 3110 then 61 else 30))) else (if i.val < 3114 then (if i.val < 3112 then 38 else (if i.val < 3113 then 29 else 13)) else (if i.val < 3116 then (if i.val < 3115 then 86 else 13) else (if i.val < 3117 then 30 else 13)))) else (if i.val < 3125 then (if i.val < 3121 then (if i.val < 3119 then 52 else (if i.val < 3120 then 13 else 83)) else (if i.val < 3123 then (if i.val < 3122 then 11 else 29) else (if i.val < 3124 then 59 else 59))) else (if i.val < 3128 then (if i.val < 3126 then 38 else (if i.val < 3127 then 88 else 25)) else (if i.val < 3130 then (if i.val < 3129 then 30 else 38) else (if i.val < 3131 then 25 else 87))))))) else (if i.val < 3186 then (if i.val < 3159 then (if i.val < 3145 then (if i.val < 3138 then (if i.val < 3135 then (if i.val < 3133 then 30 else (if i.val < 3134 then 25 else 87)) else (if i.val < 3136 then 61 else (if i.val < 3137 then 17 else 1))) else (if i.val < 3141 then (if i.val < 3139 then 38 else (if i.val < 3140 then 11 else 38)) else (if i.val < 3143 then (if i.val < 3142 then 25 else 25) else (if i.val < 3144 then 59 else 46)))) else (if i.val < 3152 then (if i.val < 3148 then (if i.val < 3146 then 17 else (if i.val < 3147 then 38 else 25)) else (if i.val < 3150 then (if i.val < 3149 then 7 else 46) else (if i.val < 3151 then 61 else 74))) else (if i.val < 3155 then (if i.val < 3153 then 30 else (if i.val < 3154 then 74 else 29)) else (if i.val < 3157 then (if i.val < 3156 then 86 else 76) else (if i.val < 3158 then 87 else 87))))) else (if i.val < 3172 then (if i.val < 3165 then (if i.val < 3162 then (if i.val < 3160 then 88 else (if i.val < 3161 then 82 else 64)) else (if i.val < 3163 then 40 else (if i.val < 3164 then 71 else 86))) else (if i.val < 3168 then (if i.val < 3166 then 91 else (if i.val < 3167 then 58 else 86)) else (if i.val < 3170 then (if i.val < 3169 then 10 else 15) else (if i.val < 3171 then 20 else 29)))) else (if i.val < 3179 then (if i.val < 3175 then (if i.val < 3173 then 74 else (if i.val < 3174 then 40 else 40)) else (if i.val < 3177 then (if i.val < 3176 then 71 else 27) else (if i.val < 3178 then 71 else 27))) else (if i.val < 3182 then (if i.val < 3180 then 40 else (if i.val < 3181 then 80 else 40)) else (if i.val < 3184 then (if i.val < 3183 then 58 else 58) else (if i.val < 3185 then 55 else 55)))))) else (if i.val < 3213 then (if i.val < 3199 then (if i.val < 3192 then (if i.val < 3189 then (if i.val < 3187 then 40 else (if i.val < 3188 then 11 else 11)) else (if i.val < 3190 then 30 else (if i.val < 3191 then 74 else 41))) else (if i.val < 3195 then (if i.val < 3193 then 85 else (if i.val < 3194 then 30 else 69)) else (if i.val < 3197 then (if i.val < 3196 then 69 else 85) else (if i.val < 3198 then 71 else 30)))) else (if i.val < 3206 then (if i.val < 3202 then (if i.val < 3200 then 69 else (if i.val < 3201 then 51 else 27)) else (if i.val < 3204 then (if i.val < 3203 then 46 else 46) else (if i.val < 3205 then 51 else 85))) else (if i.val < 3209 then (if i.val < 3207 then 15 else (if i.val < 3208 then 27 else 23)) else (if i.val < 3211 then (if i.val < 3210 then 46 else 57) else (if i.val < 3212 then 46 else 57))))) else (if i.val < 3226 then (if i.val < 3219 then (if i.val < 3216 then (if i.val < 3214 then 46 else (if i.val < 3215 then 46 else 55)) else (if i.val < 3217 then 57 else (if i.val < 3218 then 57 else 51))) else (if i.val < 3222 then (if i.val < 3220 then 66 else (if i.val < 3221 then 80 else 51)) else (if i.val < 3224 then (if i.val < 3223 then 30 else 30) else (if i.val < 3225 then 20 else 55)))) else (if i.val < 3233 then (if i.val < 3229 then (if i.val < 3227 then 90 else (if i.val < 3228 then 30 else 69)) else (if i.val < 3231 then (if i.val < 3230 then 90 else 85) else (if i.val < 3232 then 30 else 90))) else (if i.val < 3236 then (if i.val < 3234 then 85 else (if i.val < 3235 then 90 else 55)) else (if i.val < 3238 then (if i.val < 3237 then 90 else 24) else (if i.val < 3239 then 46 else 46)))))))) else (if i.val < 3348 then (if i.val < 3294 then (if i.val < 3267 then (if i.val < 3253 then (if i.val < 3246 then (if i.val < 3243 then (if i.val < 3241 then 90 else (if i.val < 3242 then 24 else 46)) else (if i.val < 3244 then 57 else (if i.val < 3245 then 46 else 46))) else (if i.val < 3249 then (if i.val < 3247 then 46 else (if i.val < 3248 then 57 else 6)) else (if i.val < 3251 then (if i.val < 3250 then 90 else 38) else (if i.val < 3252 then 90 else 34)))) else (if i.val < 3260 then (if i.val < 3256 then (if i.val < 3254 then 57 else (if i.val < 3255 then 57 else 6)) else (if i.val < 3258 then (if i.val < 3257 then 90 else 85) else (if i.val < 3259 then 90 else 23))) else (if i.val < 3263 then (if i.val < 3261 then 11 else (if i.val < 3262 then 79 else 23)) else (if i.val < 3265 then (if i.val < 3264 then 79 else 30) else (if i.val < 3266 then 30 else 72))))) else (if i.val < 3280 then (if i.val < 3273 then (if i.val < 3270 then (if i.val < 3268 then 7 else (if i.val < 3269 then 11 else 79)) else (if i.val < 3271 then 11 else (if i.val < 3272 then 30 else 30))) else (if i.val < 3276 then (if i.val < 3274 then 92 else (if i.val < 3275 then 11 else 46)) else (if i.val < 3278 then (if i.val < 3277 then 46 else 46) else (if i.val < 3279 then 4 else 23)))) else (if i.val < 3287 then (if i.val < 3283 then (if i.val < 3281 then 7 else (if i.val < 3282 then 46 else 72)) else (if i.val < 3285 then (if i.val < 3284 then 4 else 79) else (if i.val < 3286 then 92 else 61))) else (if i.val < 3290 then (if i.val < 3288 then 11 else (if i.val < 3289 then 86 else 46)) else (if i.val < 3292 then (if i.val < 3291 then 46 else 51) else (if i.val < 3293 then 85 else 46)))))) else (if i.val < 3321 then (if i.val < 3307 then (if i.val < 3300 then (if i.val < 3297 then (if i.val < 3295 then 57 else (if i.val < 3296 then 46 else 57)) else (if i.val < 3298 then 46 else (if i.val < 3299 then 55 else 57))) else (if i.val < 3303 then (if i.val < 3301 then 57 else (if i.val < 3302 then 46 else 46)) else (if i.val < 3305 then (if i.val < 3304 then 46 else 46) else (if i.val < 3306 then 46 else 57)))) else (if i.val < 3314 then (if i.val < 3310 then (if i.val < 3308 then 57 else (if i.val < 3309 then 46 else 57)) else (if i.val < 3312 then (if i.val < 3311 then 46 else 46) else (if i.val < 3313 then 43 else 46))) else (if i.val < 3317 then (if i.val < 3315 then 57 else (if i.val < 3316 then 57 else 43)) else (if i.val < 3319 then (if i.val < 3318 then 57 else 46) else (if i.val < 3320 then 46 else 46))))) else (if i.val < 3334 then (if i.val < 3327 then (if i.val < 3324 then (if i.val < 3322 then 57 else (if i.val < 3323 then 57 else 57)) else (if i.val < 3325 then 57 else (if i.val < 3326 then 57 else 57))) else (if i.val < 3330 then (if i.val < 3328 then 46 else (if i.val < 3329 then 46 else 57)) else (if i.val < 3332 then (if i.val < 3331 then 57 else 57) else (if i.val < 3333 then 57 else 46)))) else (if i.val < 3341 then (if i.val < 3337 then (if i.val < 3335 then 85 else (if i.val < 3336 then 90 else 55)) else (if i.val < 3339 then (if i.val < 3338 then 24 else 46) else (if i.val < 3340 then 46 else 24))) else (if i.val < 3344 then (if i.val < 3342 then 46 else (if i.val < 3343 then 46 else 90)) else (if i.val < 3346 then (if i.val < 3345 then 24 else 46) else (if i.val < 3347 then 46 else 24))))))) else (if i.val < 3402 then (if i.val < 3375 then (if i.val < 3361 then (if i.val < 3354 then (if i.val < 3351 then (if i.val < 3349 then 46 else (if i.val < 3350 then 46 else 74)) else (if i.val < 3352 then 24 else (if i.val < 3353 then 50 else 46))) else (if i.val < 3357 then (if i.val < 3355 then 78 else (if i.val < 3356 then 50 else 46)) else (if i.val < 3359 then (if i.val < 3358 then 46 else 46) else (if i.val < 3360 then 46 else 74)))) else (if i.val < 3368 then (if i.val < 3364 then (if i.val < 3362 then 24 else (if i.val < 3363 then 57 else 78)) else (if i.val < 3366 then (if i.val < 3365 then 43 else 46) else (if i.val < 3367 then 50 else 50))) else (if i.val < 3371 then (if i.val < 3369 then 46 else (if i.val < 3370 then 43 else 27)) else (if i.val < 3373 then (if i.val < 3372 then 24 else 50) else (if i.val < 3374 then 34 else 46))))) else (if i.val < 3388 then (if i.val < 3381 then (if i.val < 3378 then (if i.val < 3376 then 24 else (if i.val < 3377 then 57 else 57)) else (if i.val < 3379 then 57 else (if i.val < 3380 then 57 else 46))) else (if i.val < 3384 then (if i.val < 3382 then 50 else (if i.val < 3383 then 40 else 78)) else (if i.val < 3386 then (if i.val < 3385 then 50 else 46) else (if i.val < 3387 then 46 else 1)))) else (if i.val < 3395 then (if i.val < 3391 then (if i.val < 3389 then 57 else (if i.val < 3390 then 78 else 57)) else (if i.val < 3393 then (if i.val < 3392 then 46 else 50) else (if i.val < 3394 then 40 else 1))) else (if i.val < 3398 then (if i.val < 3396 then 11 else (if i.val < 3397 then 92 else 4)) else (if i.val < 3400 then (if i.val < 3399 then 4 else 92) else (if i.val < 3401 then 92 else 4)))))) else (if i.val < 3429 then (if i.val < 3415 then (if i.val < 3408 then (if i.val < 3405 then (if i.val < 3403 then 4 else (if i.val < 3404 then 92 else 92)) else (if i.val < 3406 then 4 else (if i.val < 3407 then 92 else 4))) else (if i.val < 3411 then (if i.val < 3409 then 46 else (if i.val < 3410 then 46 else 92)) else (if i.val < 3413 then (if i.val < 3412 then 4 else 92) else (if i.val < 3414 then 4 else 46)))) else (if i.val < 3422 then (if i.val < 3418 then (if i.val < 3416 then 57 else (if i.val < 3417 then 40 else 40)) else (if i.val < 3420 then (if i.val < 3419 then 46 else 48) else (if i.val < 3421 then 50 else 40))) else (if i.val < 3425 then (if i.val < 3423 then 55 else (if i.val < 3424 then 71 else 55)) else (if i.val < 3427 then (if i.val < 3426 then 55 else 46) else (if i.val < 3428 then 46 else 46))))) else (if i.val < 3442 then (if i.val < 3435 then (if i.val < 3432 then (if i.val < 3430 then 46 else (if i.val < 3431 then 21 else 21)) else (if i.val < 3433 then 78 else (if i.val < 3434 then 78 else 78))) else (if i.val < 3438 then (if i.val < 3436 then 78 else (if i.val < 3437 then 21 else 21)) else (if i.val < 3440 then (if i.val < 3439 then 78 else 21) else (if i.val < 3441 then 21 else 21)))) else (if i.val < 3449 then (if i.val < 3445 then (if i.val < 3443 then 21 else (if i.val < 3444 then 21 else 21)) else (if i.val < 3447 then (if i.val < 3446 then 21 else 21) else (if i.val < 3448 then 21 else 21))) else (if i.val < 3452 then (if i.val < 3450 then 21 else (if i.val < 3451 then 21 else 78)) else (if i.val < 3454 then (if i.val < 3453 then 21 else 21) else (if i.val < 3455 then 21 else 21))))))))))))

def g32p_supplierGroup00_support : Finset (Fin 102) :=
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 15, 17, 18, 19, 20, 21, 23, 24, 25, 27, 28, 29, 30, 31, 32, 34, 35, 37, 38, 40, 41, 43, 44, 45, 46, 48, 49, 50, 51, 52, 55, 56, 57, 58, 59, 61, 63, 64, 65, 66, 67, 69, 71, 72, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup00_matrix_000 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 0 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 0 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 0 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 0 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 0 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

theorem g32p_supplierGroup00_matrix_001 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 1 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 1 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 1 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 1 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 1 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

theorem g32p_supplierGroup00_matrix_002 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 2 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 2 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 2 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 2 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 2 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

theorem g32p_supplierGroup00_matrix_003 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 3 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 3 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 3 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 3 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 3 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

theorem g32p_supplierGroup00_matrix_004 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 4 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 4 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 4 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 4 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 4 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

theorem g32p_supplierGroup00_matrix_005 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 5 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 5 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 5 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 5 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 5 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

theorem g32p_supplierGroup00_matrix_006 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 6 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 6 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 6 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 6 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 6 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

theorem g32p_supplierGroup00_matrix_007 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 7 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 7 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 7 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 7 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 7 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

theorem g32p_supplierGroup00_matrix_008 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 8 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 8 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 8 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 8 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 8 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

theorem g32p_supplierGroup00_matrix_009 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 9 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 9 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 9 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_009 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 9 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 9 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 9 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_009 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 9 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

theorem g32p_supplierGroup00_matrix_010 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 10 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 10 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 10 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_010 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 10 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 10 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 10 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_010 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 10 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

theorem g32p_supplierGroup00_matrix_011 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 11 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 11 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 11 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_011 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 11 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 11 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 11 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_011 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 11 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

theorem g32p_supplierGroup00_matrix_012 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 12 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 12 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 12 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_012 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 12 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 12 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 12 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_012 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 12 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

theorem g32p_supplierGroup00_matrix_013 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 13 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 13 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 13 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_013 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 13 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 13 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 13 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_013 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 13 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

theorem g32p_supplierGroup00_matrix_014 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 14 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 14 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 14 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_014 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 14 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 14 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 14 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_014 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 14 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

theorem g32p_supplierGroup00_matrix_015 : ∀ r : Fin 16,
    g32p_row02_groupNodes (g32p_finBlockIndex 3456 15 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 15 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 15 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup00_class_015 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 15 r)).1 (g32p_supplierGroup00_source (g32p_finBlockIndex 3456 15 r)).2 =
      g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 15 r) := by
  decide +kernel

theorem g32p_supplierGroup00_support_015 : ∀ r : Fin 16,
    g32p_supplierGroup00_classify (g32p_finBlockIndex 3456 15 r) ∈ g32p_supplierGroup00_support := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
