import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0241
import HodgeLean.Foundations.Program.G32PropFourSixPacked0242
import HodgeLean.Foundations.Program.G32PropFourSixPacked0247
import HodgeLean.Foundations.Program.G32PropFourSixPacked0248
import HodgeLean.Foundations.Program.G32PropFourSixPacked0249
import HodgeLean.Foundations.Program.G32PropFourSixPacked0250
import HodgeLean.Foundations.Program.G32PropFourSixPacked0251
import HodgeLean.Foundations.Program.G32PropFourSixPacked0255
import HodgeLean.Foundations.Program.G32PropFourSixPacked0256

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_088909 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088909 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088909 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016487 := by
  decide +kernel

theorem g32p_supplierForest_actual_088909 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088909) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_088909
    g32p_supplierForest_actual_016487

def g32p_supplierForest_node_088922 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_088922 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088922 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_084998 := by
  decide +kernel

theorem g32p_supplierForest_actual_088922 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088922) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_088922
    g32p_supplierForest_actual_084998

def g32p_supplierForest_node_088959 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_088959 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088959 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_099702 := by
  decide +kernel

theorem g32p_supplierForest_actual_088959 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088959) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 1 g32p_supplierForest_edge_088959
    g32p_supplierForest_actual_099702

def g32p_supplierForest_node_088974 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_088974 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088974 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_099376 := by
  decide +kernel

theorem g32p_supplierForest_actual_088974 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088974) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 0 g32p_supplierForest_edge_088974
    g32p_supplierForest_actual_099376

def g32p_supplierForest_node_088978 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_088978 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088978 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015331 := by
  decide +kernel

theorem g32p_supplierForest_actual_088978 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088978) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_088978
    g32p_supplierForest_actual_015331

def g32p_supplierForest_node_089046 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_089046 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089046 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_090383 := by
  decide +kernel

theorem g32p_supplierForest_actual_089046 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089046) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 1 g32p_supplierForest_edge_089046
    g32p_supplierForest_actual_090383

def g32p_supplierForest_node_089054 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089054 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089054 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074583 := by
  decide +kernel

theorem g32p_supplierForest_actual_089054 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089054) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_089054
    g32p_supplierForest_actual_074583

def g32p_supplierForest_node_089056 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_089056 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089056 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_099445 := by
  decide +kernel

theorem g32p_supplierForest_actual_089056 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089056) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_089056
    g32p_supplierForest_actual_099445

def g32p_supplierForest_node_089096 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089096 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089096 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085677 := by
  decide +kernel

theorem g32p_supplierForest_actual_089096 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089096) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_089096
    g32p_supplierForest_actual_085677

def g32p_supplierForest_node_089112 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_089112 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089112 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085706 := by
  decide +kernel

theorem g32p_supplierForest_actual_089112 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089112) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_089112
    g32p_supplierForest_actual_085706

def g32p_supplierForest_node_089133 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_089133 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089133 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_081444 := by
  decide +kernel

theorem g32p_supplierForest_actual_089133 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089133) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_089133
    g32p_supplierForest_actual_081444

def g32p_supplierForest_node_089142 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_089142 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089142 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100725 := by
  decide +kernel

theorem g32p_supplierForest_actual_089142 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089142) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_089142
    g32p_supplierForest_actual_100725

def g32p_supplierForest_node_089199 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_089199 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089199 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_147541 := by
  decide +kernel

theorem g32p_supplierForest_actual_089199 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089199) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_089199
    g32p_supplierForest_actual_147541

def g32p_supplierForest_node_089206 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089206 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089206 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073632 := by
  decide +kernel

theorem g32p_supplierForest_actual_089206 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089206) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_089206
    g32p_supplierForest_actual_073632

def g32p_supplierForest_node_089241 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_089241 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089241 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_149440 := by
  decide +kernel

theorem g32p_supplierForest_actual_089241 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089241) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_089241
    g32p_supplierForest_actual_149440

def g32p_supplierForest_node_089254 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089254 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089254 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_099617 := by
  decide +kernel

theorem g32p_supplierForest_actual_089254 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089254) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_089254
    g32p_supplierForest_actual_099617

def g32p_supplierForest_node_089318 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_089318 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089318 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_145818 := by
  decide +kernel

theorem g32p_supplierForest_actual_089318 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089318) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_089318
    g32p_supplierForest_actual_145818

def g32p_supplierForest_node_089336 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_089336 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089336 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076847 := by
  decide +kernel

theorem g32p_supplierForest_actual_089336 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089336) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 1 g32p_supplierForest_edge_089336
    g32p_supplierForest_actual_076847

def g32p_supplierForest_node_089379 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_089379 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089379 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_087038 := by
  decide +kernel

theorem g32p_supplierForest_actual_089379 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089379) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 1 g32p_supplierForest_edge_089379
    g32p_supplierForest_actual_087038

def g32p_supplierForest_node_089392 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_089392 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089392 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087972 := by
  decide +kernel

theorem g32p_supplierForest_actual_089392 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089392) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_089392
    g32p_supplierForest_actual_087972

def g32p_supplierForest_node_089399 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_089399 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089399 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_080529 := by
  decide +kernel

theorem g32p_supplierForest_actual_089399 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089399) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_089399
    g32p_supplierForest_actual_080529

def g32p_supplierForest_node_089422 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089422 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089422 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_018802 := by
  decide +kernel

theorem g32p_supplierForest_actual_089422 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089422) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_089422
    g32p_supplierForest_actual_018802

def g32p_supplierForest_node_089450 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_089450 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089450 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091973 := by
  decide +kernel

theorem g32p_supplierForest_actual_089450 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089450) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_089450
    g32p_supplierForest_actual_091973

def g32p_supplierForest_node_089474 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_089474 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089474 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_080143 := by
  decide +kernel

theorem g32p_supplierForest_actual_089474 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089474) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_089474
    g32p_supplierForest_actual_080143

def g32p_supplierForest_node_089502 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_089502 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089502 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083770 := by
  decide +kernel

theorem g32p_supplierForest_actual_089502 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089502) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_089502
    g32p_supplierForest_actual_083770

def g32p_supplierForest_node_089516 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089516 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089516 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_145606 := by
  decide +kernel

theorem g32p_supplierForest_actual_089516 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089516) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_089516
    g32p_supplierForest_actual_145606

def g32p_supplierForest_node_089577 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_089577 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089577 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083313 := by
  decide +kernel

theorem g32p_supplierForest_actual_089577 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089577) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_089577
    g32p_supplierForest_actual_083313

def g32p_supplierForest_node_089607 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_089607 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089607 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_078644 := by
  decide +kernel

theorem g32p_supplierForest_actual_089607 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089607) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_089607
    g32p_supplierForest_actual_078644

def g32p_supplierForest_node_089642 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089642 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089642 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_072378 := by
  decide +kernel

theorem g32p_supplierForest_actual_089642 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089642) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_089642
    g32p_supplierForest_actual_072378

def g32p_supplierForest_node_089664 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089664 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089664 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_016454 := by
  decide +kernel

theorem g32p_supplierForest_actual_089664 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089664) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_089664
    g32p_supplierForest_actual_016454

def g32p_supplierForest_node_089714 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_089714 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089714 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083787 := by
  decide +kernel

theorem g32p_supplierForest_actual_089714 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089714) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_089714
    g32p_supplierForest_actual_083787

def g32p_supplierForest_node_089718 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089718 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089718 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082588 := by
  decide +kernel

theorem g32p_supplierForest_actual_089718 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089718) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_089718
    g32p_supplierForest_actual_082588

def g32p_supplierForest_node_089762 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_089762 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089762 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_150327 := by
  decide +kernel

theorem g32p_supplierForest_actual_089762 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089762) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_089762
    g32p_supplierForest_actual_150327

def g32p_supplierForest_node_089774 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089774 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089774 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_100101 := by
  decide +kernel

theorem g32p_supplierForest_actual_089774 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089774) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_089774
    g32p_supplierForest_actual_100101

def g32p_supplierForest_node_089780 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_089780 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089780 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_022608 := by
  decide +kernel

theorem g32p_supplierForest_actual_089780 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089780) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_089780
    g32p_supplierForest_actual_022608

def g32p_supplierForest_node_089781 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089781 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089781 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_148801 := by
  decide +kernel

theorem g32p_supplierForest_actual_089781 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089781) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_089781
    g32p_supplierForest_actual_148801

def g32p_supplierForest_node_089795 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_089795 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089795 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016840 := by
  decide +kernel

theorem g32p_supplierForest_actual_089795 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089795) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_089795
    g32p_supplierForest_actual_016840

def g32p_supplierForest_node_089855 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089855 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089855 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_089363 := by
  decide +kernel

theorem g32p_supplierForest_actual_089855 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089855) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_089855
    g32p_supplierForest_actual_089363

def g32p_supplierForest_node_089933 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_089933 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089933 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_022660 := by
  decide +kernel

theorem g32p_supplierForest_actual_089933 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089933) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_089933
    g32p_supplierForest_actual_022660

def g32p_supplierForest_node_089972 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_089972 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089972 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076754 := by
  decide +kernel

theorem g32p_supplierForest_actual_089972 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089972) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_089972
    g32p_supplierForest_actual_076754

def g32p_supplierForest_node_089990 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_089990 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089990 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_022693 := by
  decide +kernel

theorem g32p_supplierForest_actual_089990 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089990) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_089990
    g32p_supplierForest_actual_022693

def g32p_supplierForest_node_090000 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090000 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090000 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_079418 := by
  decide +kernel

theorem g32p_supplierForest_actual_090000 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090000) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_090000
    g32p_supplierForest_actual_079418

def g32p_supplierForest_node_090021 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_090021 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090021 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_087738 := by
  decide +kernel

theorem g32p_supplierForest_actual_090021 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090021) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_090021
    g32p_supplierForest_actual_087738

def g32p_supplierForest_node_090043 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090043 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090043 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_090505 := by
  decide +kernel

theorem g32p_supplierForest_actual_090043 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090043) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_090043
    g32p_supplierForest_actual_090505

def g32p_supplierForest_node_090067 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090067 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090067 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_146513 := by
  decide +kernel

theorem g32p_supplierForest_actual_090067 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090067) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_090067
    g32p_supplierForest_actual_146513

def g32p_supplierForest_node_090090 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_090090 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090090 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_079562 := by
  decide +kernel

theorem g32p_supplierForest_actual_090090 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090090) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 3 g32p_supplierForest_edge_090090
    g32p_supplierForest_actual_079562

def g32p_supplierForest_node_090097 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_090097 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090097 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_024202 := by
  decide +kernel

theorem g32p_supplierForest_actual_090097 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090097) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_090097
    g32p_supplierForest_actual_024202

def g32p_supplierForest_node_090110 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_090110 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090110 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083326 := by
  decide +kernel

theorem g32p_supplierForest_actual_090110 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090110) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_090110
    g32p_supplierForest_actual_083326

def g32p_supplierForest_node_090123 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_090123 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090123 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_088741 := by
  decide +kernel

theorem g32p_supplierForest_actual_090123 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090123) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_090123
    g32p_supplierForest_actual_088741

def g32p_supplierForest_node_090127 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090127 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090127 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094742 := by
  decide +kernel

theorem g32p_supplierForest_actual_090127 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090127) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_090127
    g32p_supplierForest_actual_094742

def g32p_supplierForest_node_090178 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_090178 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090178 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_090775 := by
  decide +kernel

theorem g32p_supplierForest_actual_090178 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090178) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_090178
    g32p_supplierForest_actual_090775

def g32p_supplierForest_node_090185 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_090185 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090185 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_074019 := by
  decide +kernel

theorem g32p_supplierForest_actual_090185 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090185) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_090185
    g32p_supplierForest_actual_074019

def g32p_supplierForest_node_090187 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_090187 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090187 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_089124 := by
  decide +kernel

theorem g32p_supplierForest_actual_090187 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090187) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_090187
    g32p_supplierForest_actual_089124

def g32p_supplierForest_node_090217 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090217 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090217 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_089997 := by
  decide +kernel

theorem g32p_supplierForest_actual_090217 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090217) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_090217
    g32p_supplierForest_actual_089997

def g32p_supplierForest_node_090231 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090231 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090231 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_090807 := by
  decide +kernel

theorem g32p_supplierForest_actual_090231 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090231) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_090231
    g32p_supplierForest_actual_090807

def g32p_supplierForest_node_090234 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_090234 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090234 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_079913 := by
  decide +kernel

theorem g32p_supplierForest_actual_090234 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090234) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_090234
    g32p_supplierForest_actual_079913

def g32p_supplierForest_node_090278 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_090278 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090278 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_081324 := by
  decide +kernel

theorem g32p_supplierForest_actual_090278 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090278) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_090278
    g32p_supplierForest_actual_081324

def g32p_supplierForest_node_090279 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_090279 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090279 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_087628 := by
  decide +kernel

theorem g32p_supplierForest_actual_090279 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090279) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_090279
    g32p_supplierForest_actual_087628

def g32p_supplierForest_node_090297 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_090297 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090297 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_090559 := by
  decide +kernel

theorem g32p_supplierForest_actual_090297 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090297) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_090297
    g32p_supplierForest_actual_090559

def g32p_supplierForest_node_090319 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_090319 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090319 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091232 := by
  decide +kernel

theorem g32p_supplierForest_actual_090319 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090319) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_090319
    g32p_supplierForest_actual_091232

def g32p_supplierForest_node_090397 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_090397 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090397 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_080020 := by
  decide +kernel

theorem g32p_supplierForest_actual_090397 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090397) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 1 g32p_supplierForest_edge_090397
    g32p_supplierForest_actual_080020

def g32p_supplierForest_node_090401 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_090401 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090401 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_089067 := by
  decide +kernel

theorem g32p_supplierForest_actual_090401 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090401) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_090401
    g32p_supplierForest_actual_089067

def g32p_supplierForest_node_090427 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_090427 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090427 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091379 := by
  decide +kernel

theorem g32p_supplierForest_actual_090427 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090427) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_090427
    g32p_supplierForest_actual_091379

def g32p_supplierForest_node_090443 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_090443 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090443 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_098461 := by
  decide +kernel

theorem g32p_supplierForest_actual_090443 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090443) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_090443
    g32p_supplierForest_actual_098461

def g32p_supplierForest_node_090447 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_090447 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090447 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_100441 := by
  decide +kernel

theorem g32p_supplierForest_actual_090447 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090447) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_090447
    g32p_supplierForest_actual_100441

def g32p_supplierForest_node_090452 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_090452 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090452 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_090901 := by
  decide +kernel

theorem g32p_supplierForest_actual_090452 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090452) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_090452
    g32p_supplierForest_actual_090901

def g32p_supplierForest_node_090465 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_090465 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090465 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076338 := by
  decide +kernel

theorem g32p_supplierForest_actual_090465 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090465) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_090465
    g32p_supplierForest_actual_076338

def g32p_supplierForest_node_090488 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_090488 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090488 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_088987 := by
  decide +kernel

theorem g32p_supplierForest_actual_090488 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090488) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_090488
    g32p_supplierForest_actual_088987

def g32p_supplierForest_node_090508 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_090508 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090508 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_090477 := by
  decide +kernel

theorem g32p_supplierForest_actual_090508 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090508) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_090508
    g32p_supplierForest_actual_090477

def g32p_supplierForest_node_090521 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_090521 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090521 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_080057 := by
  decide +kernel

theorem g32p_supplierForest_actual_090521 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090521) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_090521
    g32p_supplierForest_actual_080057

def g32p_supplierForest_node_090573 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_090573 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090573 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_077246 := by
  decide +kernel

theorem g32p_supplierForest_actual_090573 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090573) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_090573
    g32p_supplierForest_actual_077246

def g32p_supplierForest_node_090585 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_090585 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090585 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091713 := by
  decide +kernel

theorem g32p_supplierForest_actual_090585 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090585) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_090585
    g32p_supplierForest_actual_091713

def g32p_supplierForest_node_090600 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090600 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090600 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097583 := by
  decide +kernel

theorem g32p_supplierForest_actual_090600 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090600) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_090600
    g32p_supplierForest_actual_097583

def g32p_supplierForest_node_090660 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_090660 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090660 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100298 := by
  decide +kernel

theorem g32p_supplierForest_actual_090660 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090660) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_090660
    g32p_supplierForest_actual_100298

def g32p_supplierForest_node_090677 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_090677 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090677 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_098472 := by
  decide +kernel

theorem g32p_supplierForest_actual_090677 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090677) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_090677
    g32p_supplierForest_actual_098472

def g32p_supplierForest_node_090716 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090716 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090716 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_099669 := by
  decide +kernel

theorem g32p_supplierForest_actual_090716 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090716) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_090716
    g32p_supplierForest_actual_099669

def g32p_supplierForest_node_090751 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_090751 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090751 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_019087 := by
  decide +kernel

theorem g32p_supplierForest_actual_090751 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090751) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_090751
    g32p_supplierForest_actual_019087

def g32p_supplierForest_node_090781 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090781 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090781 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023271 := by
  decide +kernel

theorem g32p_supplierForest_actual_090781 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090781) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_090781
    g32p_supplierForest_actual_023271

def g32p_supplierForest_node_090864 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090864 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090864 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_100758 := by
  decide +kernel

theorem g32p_supplierForest_actual_090864 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090864) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 0 g32p_supplierForest_edge_090864
    g32p_supplierForest_actual_100758

def g32p_supplierForest_node_090887 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090887 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090887 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_079481 := by
  decide +kernel

theorem g32p_supplierForest_actual_090887 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090887) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_090887
    g32p_supplierForest_actual_079481

def g32p_supplierForest_node_090914 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_090914 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090914 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_087529 := by
  decide +kernel

theorem g32p_supplierForest_actual_090914 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090914) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_090914
    g32p_supplierForest_actual_087529

def g32p_supplierForest_node_090941 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_090941 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090941 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_018801 := by
  decide +kernel

theorem g32p_supplierForest_actual_090941 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090941) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_090941
    g32p_supplierForest_actual_018801

def g32p_supplierForest_node_090952 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_090952 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090952 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_079858 := by
  decide +kernel

theorem g32p_supplierForest_actual_090952 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090952) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_090952
    g32p_supplierForest_actual_079858

def g32p_supplierForest_node_090964 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_090964 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090964 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_100838 := by
  decide +kernel

theorem g32p_supplierForest_actual_090964 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090964) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_090964
    g32p_supplierForest_actual_100838

def g32p_supplierForest_node_090996 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_090996 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090996 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_017326 := by
  decide +kernel

theorem g32p_supplierForest_actual_090996 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090996) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_090996
    g32p_supplierForest_actual_017326

def g32p_supplierForest_node_091018 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_091018 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091018 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_074711 := by
  decide +kernel

theorem g32p_supplierForest_actual_091018 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091018) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_091018
    g32p_supplierForest_actual_074711

def g32p_supplierForest_node_091138 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091138 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091138 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_021505 := by
  decide +kernel

theorem g32p_supplierForest_actual_091138 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091138) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_091138
    g32p_supplierForest_actual_021505

def g32p_supplierForest_node_091144 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_091144 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091144 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_096809 := by
  decide +kernel

theorem g32p_supplierForest_actual_091144 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091144) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_091144
    g32p_supplierForest_actual_096809

def g32p_supplierForest_node_091156 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091156 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091156 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_072256 := by
  decide +kernel

theorem g32p_supplierForest_actual_091156 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091156) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_091156
    g32p_supplierForest_actual_072256

def g32p_supplierForest_node_091180 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_091180 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091180 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094131 := by
  decide +kernel

theorem g32p_supplierForest_actual_091180 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091180) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_091180
    g32p_supplierForest_actual_094131

def g32p_supplierForest_node_091186 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_091186 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091186 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_091181 := by
  decide +kernel

theorem g32p_supplierForest_actual_091186 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091186) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_091186
    g32p_supplierForest_actual_091181

def g32p_supplierForest_node_091209 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_091209 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091209 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096084 := by
  decide +kernel

theorem g32p_supplierForest_actual_091209 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091209) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_091209
    g32p_supplierForest_actual_096084

def g32p_supplierForest_node_091211 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091211 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091211 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075023 := by
  decide +kernel

theorem g32p_supplierForest_actual_091211 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091211) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_091211
    g32p_supplierForest_actual_075023

def g32p_supplierForest_node_091281 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091281 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091281 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075798 := by
  decide +kernel

theorem g32p_supplierForest_actual_091281 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091281) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_091281
    g32p_supplierForest_actual_075798

def g32p_supplierForest_node_091287 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091287 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091287 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_090023 := by
  decide +kernel

theorem g32p_supplierForest_actual_091287 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091287) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_091287
    g32p_supplierForest_actual_090023

def g32p_supplierForest_node_091318 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091318 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091318 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_100981 := by
  decide +kernel

theorem g32p_supplierForest_actual_091318 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091318) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 0 g32p_supplierForest_edge_091318
    g32p_supplierForest_actual_100981

def g32p_supplierForest_node_091319 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_091319 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091319 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013072 := by
  decide +kernel

theorem g32p_supplierForest_actual_091319 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091319) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_091319
    g32p_supplierForest_actual_013072

def g32p_supplierForest_node_091328 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_091328 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091328 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_098593 := by
  decide +kernel

theorem g32p_supplierForest_actual_091328 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091328) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_091328
    g32p_supplierForest_actual_098593

def g32p_supplierForest_node_091340 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_091340 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091340 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100227 := by
  decide +kernel

theorem g32p_supplierForest_actual_091340 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091340) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_091340
    g32p_supplierForest_actual_100227

def g32p_supplierForest_node_091355 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_091355 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091355 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022070 := by
  decide +kernel

theorem g32p_supplierForest_actual_091355 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091355) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_091355
    g32p_supplierForest_actual_022070

def g32p_supplierForest_node_091363 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_091363 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091363 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100260 := by
  decide +kernel

theorem g32p_supplierForest_actual_091363 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091363) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_091363
    g32p_supplierForest_actual_100260

def g32p_supplierForest_node_091368 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_091368 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091368 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019442 := by
  decide +kernel

theorem g32p_supplierForest_actual_091368 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091368) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 2 g32p_supplierForest_edge_091368
    g32p_supplierForest_actual_019442

def g32p_supplierForest_node_091381 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_091381 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091381 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_084066 := by
  decide +kernel

theorem g32p_supplierForest_actual_091381 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091381) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_091381
    g32p_supplierForest_actual_084066

def g32p_supplierForest_node_091397 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091397 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091397 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015673 := by
  decide +kernel

theorem g32p_supplierForest_actual_091397 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091397) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_091397
    g32p_supplierForest_actual_015673

def g32p_supplierForest_node_091422 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_091422 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091422 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_085565 := by
  decide +kernel

theorem g32p_supplierForest_actual_091422 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091422) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_091422
    g32p_supplierForest_actual_085565

def g32p_supplierForest_node_091440 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_091440 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091440 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_082225 := by
  decide +kernel

theorem g32p_supplierForest_actual_091440 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091440) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_091440
    g32p_supplierForest_actual_082225

def g32p_supplierForest_node_091447 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_091447 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091447 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_080171 := by
  decide +kernel

theorem g32p_supplierForest_actual_091447 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091447) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_091447
    g32p_supplierForest_actual_080171

def g32p_supplierForest_node_091455 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_091455 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091455 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_094696 := by
  decide +kernel

theorem g32p_supplierForest_actual_091455 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091455) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_091455
    g32p_supplierForest_actual_094696

def g32p_supplierForest_node_091468 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091468 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091468 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_091486 := by
  decide +kernel

theorem g32p_supplierForest_actual_091468 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091468) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_091468
    g32p_supplierForest_actual_091486

def g32p_supplierForest_node_091477 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091477 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091477 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_096462 := by
  decide +kernel

theorem g32p_supplierForest_actual_091477 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091477) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_091477
    g32p_supplierForest_actual_096462

def g32p_supplierForest_node_091494 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_091494 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091494 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100681 := by
  decide +kernel

theorem g32p_supplierForest_actual_091494 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091494) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_091494
    g32p_supplierForest_actual_100681

def g32p_supplierForest_node_091504 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091504 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091504 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073198 := by
  decide +kernel

theorem g32p_supplierForest_actual_091504 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091504) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_091504
    g32p_supplierForest_actual_073198

def g32p_supplierForest_node_091512 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091512 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091512 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_080024 := by
  decide +kernel

theorem g32p_supplierForest_actual_091512 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091512) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_091512
    g32p_supplierForest_actual_080024

def g32p_supplierForest_node_091516 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091516 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091516 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_149879 := by
  decide +kernel

theorem g32p_supplierForest_actual_091516 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091516) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_091516
    g32p_supplierForest_actual_149879

def g32p_supplierForest_node_091521 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091521 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091521 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097082 := by
  decide +kernel

theorem g32p_supplierForest_actual_091521 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091521) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_091521
    g32p_supplierForest_actual_097082

def g32p_supplierForest_node_091528 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091528 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091528 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_082773 := by
  decide +kernel

theorem g32p_supplierForest_actual_091528 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091528) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_091528
    g32p_supplierForest_actual_082773

def g32p_supplierForest_node_091540 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091540 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091540 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_023253 := by
  decide +kernel

theorem g32p_supplierForest_actual_091540 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091540) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_091540
    g32p_supplierForest_actual_023253

def g32p_supplierForest_node_091548 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091548 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091548 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_087927 := by
  decide +kernel

theorem g32p_supplierForest_actual_091548 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091548) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_091548
    g32p_supplierForest_actual_087927

def g32p_supplierForest_node_091653 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_091653 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091653 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_094999 := by
  decide +kernel

theorem g32p_supplierForest_actual_091653 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091653) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_091653
    g32p_supplierForest_actual_094999

def g32p_supplierForest_node_091663 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_091663 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091663 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_072917 := by
  decide +kernel

theorem g32p_supplierForest_actual_091663 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091663) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_091663
    g32p_supplierForest_actual_072917

def g32p_supplierForest_node_091674 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091674 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091674 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092001 := by
  decide +kernel

theorem g32p_supplierForest_actual_091674 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091674) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_091674
    g32p_supplierForest_actual_092001

def g32p_supplierForest_node_091677 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091677 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091677 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073833 := by
  decide +kernel

theorem g32p_supplierForest_actual_091677 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091677) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_091677
    g32p_supplierForest_actual_073833

def g32p_supplierForest_node_091710 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091710 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091710 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_151902 := by
  decide +kernel

theorem g32p_supplierForest_actual_091710 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091710) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_091710
    g32p_supplierForest_actual_151902

def g32p_supplierForest_node_091728 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_091728 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091728 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_086906 := by
  decide +kernel

theorem g32p_supplierForest_actual_091728 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091728) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_091728
    g32p_supplierForest_actual_086906

def g32p_supplierForest_node_091732 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091732 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091732 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074245 := by
  decide +kernel

theorem g32p_supplierForest_actual_091732 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091732) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_091732
    g32p_supplierForest_actual_074245

def g32p_supplierForest_node_091739 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091739 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091739 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_088866 := by
  decide +kernel

theorem g32p_supplierForest_actual_091739 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091739) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_091739
    g32p_supplierForest_actual_088866

def g32p_supplierForest_node_091748 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091748 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091748 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_084903 := by
  decide +kernel

theorem g32p_supplierForest_actual_091748 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091748) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_091748
    g32p_supplierForest_actual_084903

def g32p_supplierForest_node_091833 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_091833 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091833 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091888 := by
  decide +kernel

theorem g32p_supplierForest_actual_091833 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091833) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_091833
    g32p_supplierForest_actual_091888

def g32p_supplierForest_node_091837 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091837 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091837 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023984 := by
  decide +kernel

theorem g32p_supplierForest_actual_091837 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091837) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_091837
    g32p_supplierForest_actual_023984

def g32p_supplierForest_node_091844 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091844 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091844 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078691 := by
  decide +kernel

theorem g32p_supplierForest_actual_091844 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091844) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_091844
    g32p_supplierForest_actual_078691

def g32p_supplierForest_node_091853 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091853 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091853 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_097620 := by
  decide +kernel

theorem g32p_supplierForest_actual_091853 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091853) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 0 g32p_supplierForest_edge_091853
    g32p_supplierForest_actual_097620

def g32p_supplierForest_node_091855 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091855 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091855 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100980 := by
  decide +kernel

theorem g32p_supplierForest_actual_091855 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091855) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_091855
    g32p_supplierForest_actual_100980

def g32p_supplierForest_node_091868 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_091868 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091868 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_080722 := by
  decide +kernel

theorem g32p_supplierForest_actual_091868 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091868) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_091868
    g32p_supplierForest_actual_080722

def g32p_supplierForest_node_091899 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091899 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091899 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073355 := by
  decide +kernel

theorem g32p_supplierForest_actual_091899 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091899) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_091899
    g32p_supplierForest_actual_073355

def g32p_supplierForest_node_091911 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_091911 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091911 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_074847 := by
  decide +kernel

theorem g32p_supplierForest_actual_091911 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091911) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_091911
    g32p_supplierForest_actual_074847

def g32p_supplierForest_node_091940 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091940 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091940 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_098889 := by
  decide +kernel

theorem g32p_supplierForest_actual_091940 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091940) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 0 g32p_supplierForest_edge_091940
    g32p_supplierForest_actual_098889

def g32p_supplierForest_node_091945 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_091945 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091945 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_076582 := by
  decide +kernel

theorem g32p_supplierForest_actual_091945 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091945) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_091945
    g32p_supplierForest_actual_076582

def g32p_supplierForest_node_091965 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_091965 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091965 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_087500 := by
  decide +kernel

theorem g32p_supplierForest_actual_091965 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091965) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_091965
    g32p_supplierForest_actual_087500

def g32p_supplierForest_node_091985 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_091985 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091985 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_148130 := by
  decide +kernel

theorem g32p_supplierForest_actual_091985 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091985) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_091985
    g32p_supplierForest_actual_148130

def g32p_supplierForest_node_092015 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092015 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092015 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_079963 := by
  decide +kernel

theorem g32p_supplierForest_actual_092015 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092015) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_092015
    g32p_supplierForest_actual_079963

def g32p_supplierForest_node_092020 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_092020 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092020 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_148287 := by
  decide +kernel

theorem g32p_supplierForest_actual_092020 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092020) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 3 g32p_supplierForest_edge_092020
    g32p_supplierForest_actual_148287

def g32p_supplierForest_node_092024 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_092024 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092024 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_084204 := by
  decide +kernel

theorem g32p_supplierForest_actual_092024 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092024) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 2 g32p_supplierForest_edge_092024
    g32p_supplierForest_actual_084204

def g32p_supplierForest_node_092027 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_092027 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092027 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_089708 := by
  decide +kernel

theorem g32p_supplierForest_actual_092027 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092027) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_092027
    g32p_supplierForest_actual_089708

def g32p_supplierForest_node_092057 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092057 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092057 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_146426 := by
  decide +kernel

theorem g32p_supplierForest_actual_092057 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092057) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_092057
    g32p_supplierForest_actual_146426

def g32p_supplierForest_node_092095 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092095 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092095 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_024057 := by
  decide +kernel

theorem g32p_supplierForest_actual_092095 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092095) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_092095
    g32p_supplierForest_actual_024057

def g32p_supplierForest_node_092113 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_092113 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092113 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_095447 := by
  decide +kernel

theorem g32p_supplierForest_actual_092113 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092113) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_092113
    g32p_supplierForest_actual_095447

def g32p_supplierForest_node_092116 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_092116 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092116 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_097754 := by
  decide +kernel

theorem g32p_supplierForest_actual_092116 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092116) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_092116
    g32p_supplierForest_actual_097754

def g32p_supplierForest_node_092121 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092121 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092121 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_090578 := by
  decide +kernel

theorem g32p_supplierForest_actual_092121 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092121) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_092121
    g32p_supplierForest_actual_090578

def g32p_supplierForest_node_092131 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_092131 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092131 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_072758 := by
  decide +kernel

theorem g32p_supplierForest_actual_092131 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092131) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_092131
    g32p_supplierForest_actual_072758

def g32p_supplierForest_node_092133 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092133 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092133 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_098608 := by
  decide +kernel

theorem g32p_supplierForest_actual_092133 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092133) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 3 g32p_supplierForest_edge_092133
    g32p_supplierForest_actual_098608

def g32p_supplierForest_node_092166 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092166 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092166 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_090457 := by
  decide +kernel

theorem g32p_supplierForest_actual_092166 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092166) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_092166
    g32p_supplierForest_actual_090457

def g32p_supplierForest_node_092177 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_092177 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092177 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_090238 := by
  decide +kernel

theorem g32p_supplierForest_actual_092177 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092177) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_092177
    g32p_supplierForest_actual_090238

def g32p_supplierForest_node_092192 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_092192 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092192 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_093727 := by
  decide +kernel

theorem g32p_supplierForest_actual_092192 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092192) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_092192
    g32p_supplierForest_actual_093727

def g32p_supplierForest_node_092197 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092197 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092197 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_086874 := by
  decide +kernel

theorem g32p_supplierForest_actual_092197 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092197) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_092197
    g32p_supplierForest_actual_086874

def g32p_supplierForest_node_092206 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092206 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092206 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082465 := by
  decide +kernel

theorem g32p_supplierForest_actual_092206 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092206) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_092206
    g32p_supplierForest_actual_082465

def g32p_supplierForest_node_092213 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092213 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092213 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_099516 := by
  decide +kernel

theorem g32p_supplierForest_actual_092213 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092213) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_092213
    g32p_supplierForest_actual_099516

def g32p_supplierForest_node_092216 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_092216 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092216 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096830 := by
  decide +kernel

theorem g32p_supplierForest_actual_092216 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092216) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_092216
    g32p_supplierForest_actual_096830

def g32p_supplierForest_node_092225 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092225 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092225 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_072600 := by
  decide +kernel

theorem g32p_supplierForest_actual_092225 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092225) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_092225
    g32p_supplierForest_actual_072600

def g32p_supplierForest_node_092228 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_092228 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092228 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022392 := by
  decide +kernel

theorem g32p_supplierForest_actual_092228 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092228) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_092228
    g32p_supplierForest_actual_022392

def g32p_supplierForest_node_092246 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092246 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092246 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098575 := by
  decide +kernel

theorem g32p_supplierForest_actual_092246 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092246) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_092246
    g32p_supplierForest_actual_098575

def g32p_supplierForest_node_092268 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092268 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092268 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_087868 := by
  decide +kernel

theorem g32p_supplierForest_actual_092268 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092268) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_092268
    g32p_supplierForest_actual_087868

def g32p_supplierForest_node_092304 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092304 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092304 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_090190 := by
  decide +kernel

theorem g32p_supplierForest_actual_092304 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092304) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 2 g32p_supplierForest_edge_092304
    g32p_supplierForest_actual_090190

def g32p_supplierForest_node_092309 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_092309 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092309 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076145 := by
  decide +kernel

theorem g32p_supplierForest_actual_092309 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092309) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_092309
    g32p_supplierForest_actual_076145

def g32p_supplierForest_node_092342 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_092342 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092342 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_075988 := by
  decide +kernel

theorem g32p_supplierForest_actual_092342 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092342) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 2 g32p_supplierForest_edge_092342
    g32p_supplierForest_actual_075988

def g32p_supplierForest_node_092356 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_092356 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092356 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078836 := by
  decide +kernel

theorem g32p_supplierForest_actual_092356 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092356) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_092356
    g32p_supplierForest_actual_078836

def g32p_supplierForest_node_092358 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092358 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092358 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_082839 := by
  decide +kernel

theorem g32p_supplierForest_actual_092358 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092358) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_092358
    g32p_supplierForest_actual_082839

def g32p_supplierForest_node_092388 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092388 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092388 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_151866 := by
  decide +kernel

theorem g32p_supplierForest_actual_092388 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092388) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 1 g32p_supplierForest_edge_092388
    g32p_supplierForest_actual_151866

def g32p_supplierForest_node_092392 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092392 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092392 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_094257 := by
  decide +kernel

theorem g32p_supplierForest_actual_092392 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092392) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_092392
    g32p_supplierForest_actual_094257

def g32p_supplierForest_node_092436 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092436 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092436 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_019139 := by
  decide +kernel

theorem g32p_supplierForest_actual_092436 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092436) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_092436
    g32p_supplierForest_actual_019139

def g32p_supplierForest_node_092466 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_092466 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092466 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_150028 := by
  decide +kernel

theorem g32p_supplierForest_actual_092466 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092466) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 1 g32p_supplierForest_edge_092466
    g32p_supplierForest_actual_150028

def g32p_supplierForest_node_092522 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_092522 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092522 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_147144 := by
  decide +kernel

theorem g32p_supplierForest_actual_092522 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092522) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_092522
    g32p_supplierForest_actual_147144

def g32p_supplierForest_node_092585 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_092585 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092585 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_094022 := by
  decide +kernel

theorem g32p_supplierForest_actual_092585 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092585) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_092585
    g32p_supplierForest_actual_094022

def g32p_supplierForest_node_092594 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092594 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092594 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_093042 := by
  decide +kernel

theorem g32p_supplierForest_actual_092594 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092594) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_092594
    g32p_supplierForest_actual_093042

def g32p_supplierForest_node_092612 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_092612 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092612 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092618 := by
  decide +kernel

theorem g32p_supplierForest_actual_092612 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092612) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_092612
    g32p_supplierForest_actual_092618

def g32p_supplierForest_node_092614 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_092614 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092614 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075916 := by
  decide +kernel

theorem g32p_supplierForest_actual_092614 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092614) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_092614
    g32p_supplierForest_actual_075916

def g32p_supplierForest_node_092635 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_092635 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092635 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075760 := by
  decide +kernel

theorem g32p_supplierForest_actual_092635 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092635) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 1 g32p_supplierForest_edge_092635
    g32p_supplierForest_actual_075760

def g32p_supplierForest_node_092637 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_092637 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092637 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_018172 := by
  decide +kernel

theorem g32p_supplierForest_actual_092637 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092637) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_092637
    g32p_supplierForest_actual_018172

def g32p_supplierForest_node_092654 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_092654 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092654 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095904 := by
  decide +kernel

theorem g32p_supplierForest_actual_092654 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092654) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_092654
    g32p_supplierForest_actual_095904

def g32p_supplierForest_node_092687 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092687 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092687 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085167 := by
  decide +kernel

theorem g32p_supplierForest_actual_092687 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092687) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_092687
    g32p_supplierForest_actual_085167

def g32p_supplierForest_node_092724 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_092724 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092724 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018045 := by
  decide +kernel

theorem g32p_supplierForest_actual_092724 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092724) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_092724
    g32p_supplierForest_actual_018045

def g32p_supplierForest_node_092734 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_092734 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092734 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_144764 := by
  decide +kernel

theorem g32p_supplierForest_actual_092734 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092734) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_092734
    g32p_supplierForest_actual_144764

def g32p_supplierForest_node_092801 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_092801 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092801 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097998 := by
  decide +kernel

theorem g32p_supplierForest_actual_092801 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092801) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_092801
    g32p_supplierForest_actual_097998

def g32p_supplierForest_node_092803 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092803 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092803 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_076481 := by
  decide +kernel

theorem g32p_supplierForest_actual_092803 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092803) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_092803
    g32p_supplierForest_actual_076481

def g32p_supplierForest_node_092844 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092844 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092844 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_095027 := by
  decide +kernel

theorem g32p_supplierForest_actual_092844 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092844) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_092844
    g32p_supplierForest_actual_095027

def g32p_supplierForest_node_092856 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_092856 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092856 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093637 := by
  decide +kernel

theorem g32p_supplierForest_actual_092856 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092856) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_092856
    g32p_supplierForest_actual_093637

def g32p_supplierForest_node_092868 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_092868 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092868 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_148801 := by
  decide +kernel

theorem g32p_supplierForest_actual_092868 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092868) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_092868
    g32p_supplierForest_actual_148801

def g32p_supplierForest_node_092900 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_092900 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092900 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093423 := by
  decide +kernel

theorem g32p_supplierForest_actual_092900 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092900) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_092900
    g32p_supplierForest_actual_093423

def g32p_supplierForest_node_092903 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092903 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092903 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_150533 := by
  decide +kernel

theorem g32p_supplierForest_actual_092903 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092903) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_092903
    g32p_supplierForest_actual_150533

def g32p_supplierForest_node_092940 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_092940 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092940 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_094909 := by
  decide +kernel

theorem g32p_supplierForest_actual_092940 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092940) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_092940
    g32p_supplierForest_actual_094909

def g32p_supplierForest_node_092970 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092970 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092970 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_144949 := by
  decide +kernel

theorem g32p_supplierForest_actual_092970 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092970) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_092970
    g32p_supplierForest_actual_144949

def g32p_supplierForest_node_092991 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_092991 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092991 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083231 := by
  decide +kernel

theorem g32p_supplierForest_actual_092991 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092991) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_092991
    g32p_supplierForest_actual_083231

def g32p_supplierForest_node_093003 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093003 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093003 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018982 := by
  decide +kernel

theorem g32p_supplierForest_actual_093003 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093003) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_093003
    g32p_supplierForest_actual_018982

def g32p_supplierForest_node_093023 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093023 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093023 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_081747 := by
  decide +kernel

theorem g32p_supplierForest_actual_093023 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093023) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_093023
    g32p_supplierForest_actual_081747

def g32p_supplierForest_node_093059 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093059 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093059 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_093040 := by
  decide +kernel

theorem g32p_supplierForest_actual_093059 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093059) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_093059
    g32p_supplierForest_actual_093040

def g32p_supplierForest_node_093090 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_093090 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093090 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021159 := by
  decide +kernel

theorem g32p_supplierForest_actual_093090 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093090) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_093090
    g32p_supplierForest_actual_021159

def g32p_supplierForest_node_093100 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093100 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093100 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073466 := by
  decide +kernel

theorem g32p_supplierForest_actual_093100 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093100) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_093100
    g32p_supplierForest_actual_073466

def g32p_supplierForest_node_093111 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_093111 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093111 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_084650 := by
  decide +kernel

theorem g32p_supplierForest_actual_093111 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093111) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_093111
    g32p_supplierForest_actual_084650

def g32p_supplierForest_node_093127 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093127 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093127 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_078006 := by
  decide +kernel

theorem g32p_supplierForest_actual_093127 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093127) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_093127
    g32p_supplierForest_actual_078006

def g32p_supplierForest_node_093155 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_093155 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093155 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_145081 := by
  decide +kernel

theorem g32p_supplierForest_actual_093155 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093155) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 0 g32p_supplierForest_edge_093155
    g32p_supplierForest_actual_145081

def g32p_supplierForest_node_093182 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093182 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093182 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085898 := by
  decide +kernel

theorem g32p_supplierForest_actual_093182 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093182) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_093182
    g32p_supplierForest_actual_085898

def g32p_supplierForest_node_093210 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093210 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093210 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_072760 := by
  decide +kernel

theorem g32p_supplierForest_actual_093210 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093210) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_093210
    g32p_supplierForest_actual_072760

def g32p_supplierForest_node_093213 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093213 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093213 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_078498 := by
  decide +kernel

theorem g32p_supplierForest_actual_093213 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093213) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_093213
    g32p_supplierForest_actual_078498

def g32p_supplierForest_node_093228 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_093228 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093228 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092559 := by
  decide +kernel

theorem g32p_supplierForest_actual_093228 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093228) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_093228
    g32p_supplierForest_actual_092559

def g32p_supplierForest_node_093235 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093235 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093235 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_072208 := by
  decide +kernel

theorem g32p_supplierForest_actual_093235 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093235) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_093235
    g32p_supplierForest_actual_072208

def g32p_supplierForest_node_093257 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093257 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093257 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_078059 := by
  decide +kernel

theorem g32p_supplierForest_actual_093257 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093257) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_093257
    g32p_supplierForest_actual_078059

def g32p_supplierForest_node_093260 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093260 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093260 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092475 := by
  decide +kernel

theorem g32p_supplierForest_actual_093260 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093260) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_093260
    g32p_supplierForest_actual_092475

def g32p_supplierForest_node_093267 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093267 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093267 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_148583 := by
  decide +kernel

theorem g32p_supplierForest_actual_093267 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093267) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 2 g32p_supplierForest_edge_093267
    g32p_supplierForest_actual_148583

def g32p_supplierForest_node_093271 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093271 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093271 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076421 := by
  decide +kernel

theorem g32p_supplierForest_actual_093271 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093271) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_093271
    g32p_supplierForest_actual_076421

def g32p_supplierForest_node_093285 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093285 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093285 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_094299 := by
  decide +kernel

theorem g32p_supplierForest_actual_093285 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093285) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_093285
    g32p_supplierForest_actual_094299

def g32p_supplierForest_node_093290 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_093290 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093290 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_151640 := by
  decide +kernel

theorem g32p_supplierForest_actual_093290 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093290) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 3 g32p_supplierForest_edge_093290
    g32p_supplierForest_actual_151640

def g32p_supplierForest_node_093295 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093295 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093295 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_099397 := by
  decide +kernel

theorem g32p_supplierForest_actual_093295 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093295) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_093295
    g32p_supplierForest_actual_099397

def g32p_supplierForest_node_093338 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093338 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093338 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_078924 := by
  decide +kernel

theorem g32p_supplierForest_actual_093338 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093338) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_093338
    g32p_supplierForest_actual_078924

def g32p_supplierForest_node_093357 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_093357 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093357 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091028 := by
  decide +kernel

theorem g32p_supplierForest_actual_093357 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093357) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_093357
    g32p_supplierForest_actual_091028

def g32p_supplierForest_node_093378 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093378 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093378 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082467 := by
  decide +kernel

theorem g32p_supplierForest_actual_093378 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093378) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_093378
    g32p_supplierForest_actual_082467

def g32p_supplierForest_node_093380 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093380 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093380 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_077941 := by
  decide +kernel

theorem g32p_supplierForest_actual_093380 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093380) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_093380
    g32p_supplierForest_actual_077941

def g32p_supplierForest_node_093382 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093382 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093382 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_079329 := by
  decide +kernel

theorem g32p_supplierForest_actual_093382 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093382) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_093382
    g32p_supplierForest_actual_079329

def g32p_supplierForest_node_093390 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093390 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093390 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_094373 := by
  decide +kernel

theorem g32p_supplierForest_actual_093390 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093390) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_093390
    g32p_supplierForest_actual_094373

def g32p_supplierForest_node_093395 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093395 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093395 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_149772 := by
  decide +kernel

theorem g32p_supplierForest_actual_093395 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093395) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_093395
    g32p_supplierForest_actual_149772

def g32p_supplierForest_node_093456 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093456 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093456 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_094823 := by
  decide +kernel

theorem g32p_supplierForest_actual_093456 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093456) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_093456
    g32p_supplierForest_actual_094823

def g32p_supplierForest_node_093465 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093465 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093465 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_019071 := by
  decide +kernel

theorem g32p_supplierForest_actual_093465 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093465) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_093465
    g32p_supplierForest_actual_019071

def g32p_supplierForest_node_093483 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093483 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093483 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_145337 := by
  decide +kernel

theorem g32p_supplierForest_actual_093483 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093483) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_093483
    g32p_supplierForest_actual_145337

def g32p_supplierForest_node_093497 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093497 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093497 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_079858 := by
  decide +kernel

theorem g32p_supplierForest_actual_093497 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093497) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_093497
    g32p_supplierForest_actual_079858

def g32p_supplierForest_node_093538 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_093538 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093538 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091125 := by
  decide +kernel

theorem g32p_supplierForest_actual_093538 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093538) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_093538
    g32p_supplierForest_actual_091125

def g32p_supplierForest_node_093571 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093571 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093571 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_092488 := by
  decide +kernel

theorem g32p_supplierForest_actual_093571 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093571) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_093571
    g32p_supplierForest_actual_092488

def g32p_supplierForest_node_093592 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093592 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093592 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_080304 := by
  decide +kernel

theorem g32p_supplierForest_actual_093592 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093592) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_093592
    g32p_supplierForest_actual_080304

def g32p_supplierForest_node_093627 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_093627 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093627 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088846 := by
  decide +kernel

theorem g32p_supplierForest_actual_093627 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093627) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_093627
    g32p_supplierForest_actual_088846

def g32p_supplierForest_node_093652 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093652 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093652 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_151656 := by
  decide +kernel

theorem g32p_supplierForest_actual_093652 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093652) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_093652
    g32p_supplierForest_actual_151656

def g32p_supplierForest_node_093658 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_093658 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093658 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_149769 := by
  decide +kernel

theorem g32p_supplierForest_actual_093658 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093658) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_093658
    g32p_supplierForest_actual_149769

def g32p_supplierForest_node_093660 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_093660 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093660 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_078761 := by
  decide +kernel

theorem g32p_supplierForest_actual_093660 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093660) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_093660
    g32p_supplierForest_actual_078761

def g32p_supplierForest_node_093685 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_093685 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093685 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076613 := by
  decide +kernel

theorem g32p_supplierForest_actual_093685 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093685) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_093685
    g32p_supplierForest_actual_076613

def g32p_supplierForest_node_093686 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_093686 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093686 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_101041 := by
  decide +kernel

theorem g32p_supplierForest_actual_093686 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093686) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_093686
    g32p_supplierForest_actual_101041

def g32p_supplierForest_node_093720 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093720 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093720 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098721 := by
  decide +kernel

theorem g32p_supplierForest_actual_093720 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093720) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_093720
    g32p_supplierForest_actual_098721

def g32p_supplierForest_node_093723 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_093723 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093723 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_082556 := by
  decide +kernel

theorem g32p_supplierForest_actual_093723 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093723) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_093723
    g32p_supplierForest_actual_082556

def g32p_supplierForest_node_093741 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093741 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093741 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_081418 := by
  decide +kernel

theorem g32p_supplierForest_actual_093741 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093741) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_093741
    g32p_supplierForest_actual_081418

def g32p_supplierForest_node_093745 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093745 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093745 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_093894 := by
  decide +kernel

theorem g32p_supplierForest_actual_093745 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093745) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_093745
    g32p_supplierForest_actual_093894

def g32p_supplierForest_node_093792 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_093792 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093792 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075454 := by
  decide +kernel

theorem g32p_supplierForest_actual_093792 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093792) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_093792
    g32p_supplierForest_actual_075454

def g32p_supplierForest_node_093801 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093801 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093801 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_072639 := by
  decide +kernel

theorem g32p_supplierForest_actual_093801 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093801) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_093801
    g32p_supplierForest_actual_072639

def g32p_supplierForest_node_093805 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093805 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093805 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096753 := by
  decide +kernel

theorem g32p_supplierForest_actual_093805 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093805) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_093805
    g32p_supplierForest_actual_096753

def g32p_supplierForest_node_093814 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_093814 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093814 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_146979 := by
  decide +kernel

theorem g32p_supplierForest_actual_093814 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093814) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_093814
    g32p_supplierForest_actual_146979

def g32p_supplierForest_node_093815 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_093815 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093815 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021612 := by
  decide +kernel

theorem g32p_supplierForest_actual_093815 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093815) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_093815
    g32p_supplierForest_actual_021612

def g32p_supplierForest_node_093820 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093820 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093820 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_094664 := by
  decide +kernel

theorem g32p_supplierForest_actual_093820 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093820) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_093820
    g32p_supplierForest_actual_094664

def g32p_supplierForest_node_093919 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093919 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093919 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088292 := by
  decide +kernel

theorem g32p_supplierForest_actual_093919 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093919) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_093919
    g32p_supplierForest_actual_088292

def g32p_supplierForest_node_093933 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093933 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093933 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078631 := by
  decide +kernel

theorem g32p_supplierForest_actual_093933 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093933) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_093933
    g32p_supplierForest_actual_078631

def g32p_supplierForest_node_093935 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093935 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093935 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_079332 := by
  decide +kernel

theorem g32p_supplierForest_actual_093935 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093935) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_093935
    g32p_supplierForest_actual_079332

def g32p_supplierForest_node_093978 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093978 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093978 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_145628 := by
  decide +kernel

theorem g32p_supplierForest_actual_093978 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093978) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_093978
    g32p_supplierForest_actual_145628

def g32p_supplierForest_node_093999 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_093999 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093999 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_086376 := by
  decide +kernel

theorem g32p_supplierForest_actual_093999 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093999) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_093999
    g32p_supplierForest_actual_086376

def g32p_supplierForest_node_094031 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_094031 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094031 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_089929 := by
  decide +kernel

theorem g32p_supplierForest_actual_094031 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094031) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_094031
    g32p_supplierForest_actual_089929

def g32p_supplierForest_node_094037 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094037 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094037 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_089985 := by
  decide +kernel

theorem g32p_supplierForest_actual_094037 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094037) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_094037
    g32p_supplierForest_actual_089985

def g32p_supplierForest_node_094043 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094043 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094043 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_099015 := by
  decide +kernel

theorem g32p_supplierForest_actual_094043 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094043) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_094043
    g32p_supplierForest_actual_099015

def g32p_supplierForest_node_094081 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094081 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094081 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_093927 := by
  decide +kernel

theorem g32p_supplierForest_actual_094081 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094081) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_094081
    g32p_supplierForest_actual_093927

def g32p_supplierForest_node_094099 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_094099 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094099 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100990 := by
  decide +kernel

theorem g32p_supplierForest_actual_094099 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094099) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_094099
    g32p_supplierForest_actual_100990

def g32p_supplierForest_node_094104 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094104 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094104 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_072929 := by
  decide +kernel

theorem g32p_supplierForest_actual_094104 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094104) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_094104
    g32p_supplierForest_actual_072929

def g32p_supplierForest_node_094119 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094119 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094119 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075324 := by
  decide +kernel

theorem g32p_supplierForest_actual_094119 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094119) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_094119
    g32p_supplierForest_actual_075324

def g32p_supplierForest_node_094145 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_094145 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094145 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073231 := by
  decide +kernel

theorem g32p_supplierForest_actual_094145 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094145) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_094145
    g32p_supplierForest_actual_073231

def g32p_supplierForest_node_094164 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_094164 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094164 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_090493 := by
  decide +kernel

theorem g32p_supplierForest_actual_094164 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094164) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_094164
    g32p_supplierForest_actual_090493

def g32p_supplierForest_node_094187 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_094187 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094187 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_093225 := by
  decide +kernel

theorem g32p_supplierForest_actual_094187 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094187) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_094187
    g32p_supplierForest_actual_093225

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_094191 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_094191 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094191 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_093517 := by
  decide +kernel

theorem g32p_supplierForest_actual_094191 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094191) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_094191
    g32p_supplierForest_actual_093517

def g32p_supplierForest_node_094204 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_094204 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094204 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_072997 := by
  decide +kernel

theorem g32p_supplierForest_actual_094204 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094204) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_094204
    g32p_supplierForest_actual_072997

def g32p_supplierForest_node_094232 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_094232 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094232 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096272 := by
  decide +kernel

theorem g32p_supplierForest_actual_094232 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094232) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_094232
    g32p_supplierForest_actual_096272

def g32p_supplierForest_node_094243 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_094243 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094243 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081662 := by
  decide +kernel

theorem g32p_supplierForest_actual_094243 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094243) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_094243
    g32p_supplierForest_actual_081662

def g32p_supplierForest_node_094287 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_094287 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094287 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097478 := by
  decide +kernel

theorem g32p_supplierForest_actual_094287 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094287) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_094287
    g32p_supplierForest_actual_097478

def g32p_supplierForest_node_094295 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_094295 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094295 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081695 := by
  decide +kernel

theorem g32p_supplierForest_actual_094295 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094295) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 0 g32p_supplierForest_edge_094295
    g32p_supplierForest_actual_081695

def g32p_supplierForest_node_094302 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_094302 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094302 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088046 := by
  decide +kernel

theorem g32p_supplierForest_actual_094302 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094302) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 2 g32p_supplierForest_edge_094302
    g32p_supplierForest_actual_088046

def g32p_supplierForest_node_094311 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094311 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094311 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_090884 := by
  decide +kernel

theorem g32p_supplierForest_actual_094311 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094311) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 1 g32p_supplierForest_edge_094311
    g32p_supplierForest_actual_090884

def g32p_supplierForest_node_094341 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_094341 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094341 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101890 := by
  decide +kernel

theorem g32p_supplierForest_actual_094341 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094341) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_094341
    g32p_supplierForest_actual_101890

def g32p_supplierForest_node_094360 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_094360 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094360 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100980 := by
  decide +kernel

theorem g32p_supplierForest_actual_094360 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094360) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_094360
    g32p_supplierForest_actual_100980

def g32p_supplierForest_node_094371 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_094371 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094371 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_091027 := by
  decide +kernel

theorem g32p_supplierForest_actual_094371 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094371) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_094371
    g32p_supplierForest_actual_091027

def g32p_supplierForest_node_094382 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_094382 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094382 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_092199 := by
  decide +kernel

theorem g32p_supplierForest_actual_094382 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094382) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_094382
    g32p_supplierForest_actual_092199

def g32p_supplierForest_node_094402 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_094402 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094402 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_091021 := by
  decide +kernel

theorem g32p_supplierForest_actual_094402 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094402) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_094402
    g32p_supplierForest_actual_091021

def g32p_supplierForest_node_094404 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_094404 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094404 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_091157 := by
  decide +kernel

theorem g32p_supplierForest_actual_094404 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094404) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_094404
    g32p_supplierForest_actual_091157

def g32p_supplierForest_node_094405 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_094405 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094405 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_089721 := by
  decide +kernel

theorem g32p_supplierForest_actual_094405 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094405) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_094405
    g32p_supplierForest_actual_089721

def g32p_supplierForest_node_094421 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_094421 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094421 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097037 := by
  decide +kernel

theorem g32p_supplierForest_actual_094421 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094421) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_094421
    g32p_supplierForest_actual_097037

def g32p_supplierForest_node_094436 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094436 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094436 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075074 := by
  decide +kernel

theorem g32p_supplierForest_actual_094436 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094436) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_094436
    g32p_supplierForest_actual_075074

def g32p_supplierForest_node_094439 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094439 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094439 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088485 := by
  decide +kernel

theorem g32p_supplierForest_actual_094439 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094439) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_094439
    g32p_supplierForest_actual_088485

def g32p_supplierForest_node_094445 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_094445 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094445 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085650 := by
  decide +kernel

theorem g32p_supplierForest_actual_094445 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094445) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_094445
    g32p_supplierForest_actual_085650

def g32p_supplierForest_node_094464 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_094464 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094464 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073225 := by
  decide +kernel

theorem g32p_supplierForest_actual_094464 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094464) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_094464
    g32p_supplierForest_actual_073225

def g32p_supplierForest_node_094483 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_094483 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094483 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073544 := by
  decide +kernel

theorem g32p_supplierForest_actual_094483 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094483) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_094483
    g32p_supplierForest_actual_073544

def g32p_supplierForest_node_094510 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094510 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094510 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_076667 := by
  decide +kernel

theorem g32p_supplierForest_actual_094510 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094510) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_094510
    g32p_supplierForest_actual_076667

def g32p_supplierForest_node_094521 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_094521 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094521 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078416 := by
  decide +kernel

theorem g32p_supplierForest_actual_094521 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094521) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_094521
    g32p_supplierForest_actual_078416

def g32p_supplierForest_node_094523 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_094523 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094523 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_082798 := by
  decide +kernel

theorem g32p_supplierForest_actual_094523 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094523) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_094523
    g32p_supplierForest_actual_082798

def g32p_supplierForest_node_094528 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_094528 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094528 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_076578 := by
  decide +kernel

theorem g32p_supplierForest_actual_094528 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094528) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_094528
    g32p_supplierForest_actual_076578

def g32p_supplierForest_node_094563 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_094563 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094563 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077337 := by
  decide +kernel

theorem g32p_supplierForest_actual_094563 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094563) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_094563
    g32p_supplierForest_actual_077337

def g32p_supplierForest_node_094581 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_094581 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094581 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073718 := by
  decide +kernel

theorem g32p_supplierForest_actual_094581 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094581) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_094581
    g32p_supplierForest_actual_073718

def g32p_supplierForest_node_094591 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_094591 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094591 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085176 := by
  decide +kernel

theorem g32p_supplierForest_actual_094591 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094591) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 0 g32p_supplierForest_edge_094591
    g32p_supplierForest_actual_085176

def g32p_supplierForest_node_094593 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094593 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094593 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_094480 := by
  decide +kernel

theorem g32p_supplierForest_actual_094593 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094593) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_094593
    g32p_supplierForest_actual_094480

def g32p_supplierForest_node_094617 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_094617 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094617 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076936 := by
  decide +kernel

theorem g32p_supplierForest_actual_094617 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094617) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_094617
    g32p_supplierForest_actual_076936

def g32p_supplierForest_node_094662 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_094662 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094662 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097858 := by
  decide +kernel

theorem g32p_supplierForest_actual_094662 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094662) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_094662
    g32p_supplierForest_actual_097858

def g32p_supplierForest_node_094673 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_094673 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094673 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_017858 := by
  decide +kernel

theorem g32p_supplierForest_actual_094673 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094673) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_094673
    g32p_supplierForest_actual_017858

def g32p_supplierForest_node_094697 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094697 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094697 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_092890 := by
  decide +kernel

theorem g32p_supplierForest_actual_094697 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094697) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_094697
    g32p_supplierForest_actual_092890

def g32p_supplierForest_node_094745 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_094745 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094745 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_018587 := by
  decide +kernel

theorem g32p_supplierForest_actual_094745 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094745) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_094745
    g32p_supplierForest_actual_018587

def g32p_supplierForest_node_094747 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094747 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094747 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_100601 := by
  decide +kernel

theorem g32p_supplierForest_actual_094747 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094747) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_094747
    g32p_supplierForest_actual_100601

def g32p_supplierForest_node_094748 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_094748 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094748 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083571 := by
  decide +kernel

theorem g32p_supplierForest_actual_094748 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094748) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_094748
    g32p_supplierForest_actual_083571

def g32p_supplierForest_node_094809 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094809 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094809 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_020566 := by
  decide +kernel

theorem g32p_supplierForest_actual_094809 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094809) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_094809
    g32p_supplierForest_actual_020566

def g32p_supplierForest_node_094842 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_094842 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094842 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073115 := by
  decide +kernel

theorem g32p_supplierForest_actual_094842 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094842) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_094842
    g32p_supplierForest_actual_073115

def g32p_supplierForest_node_094850 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094850 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094850 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098306 := by
  decide +kernel

theorem g32p_supplierForest_actual_094850 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094850) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_094850
    g32p_supplierForest_actual_098306

def g32p_supplierForest_node_094863 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_094863 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094863 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096297 := by
  decide +kernel

theorem g32p_supplierForest_actual_094863 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094863) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_094863
    g32p_supplierForest_actual_096297

def g32p_supplierForest_node_094875 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_094875 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094875 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_092815 := by
  decide +kernel

theorem g32p_supplierForest_actual_094875 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094875) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_094875
    g32p_supplierForest_actual_092815

def g32p_supplierForest_node_094885 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_094885 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094885 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_080097 := by
  decide +kernel

theorem g32p_supplierForest_actual_094885 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094885) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_094885
    g32p_supplierForest_actual_080097

def g32p_supplierForest_node_094900 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_094900 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094900 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091346 := by
  decide +kernel

theorem g32p_supplierForest_actual_094900 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094900) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_094900
    g32p_supplierForest_actual_091346

def g32p_supplierForest_node_094947 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_094947 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094947 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016888 := by
  decide +kernel

theorem g32p_supplierForest_actual_094947 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094947) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_094947
    g32p_supplierForest_actual_016888

def g32p_supplierForest_node_094948 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_094948 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_094948 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_088636 := by
  decide +kernel

theorem g32p_supplierForest_actual_094948 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_094948) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_094948
    g32p_supplierForest_actual_088636

def g32p_supplierForest_node_095016 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095016 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095016 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_099247 := by
  decide +kernel

theorem g32p_supplierForest_actual_095016 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095016) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_095016
    g32p_supplierForest_actual_099247

def g32p_supplierForest_node_095018 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_095018 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095018 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019912 := by
  decide +kernel

theorem g32p_supplierForest_actual_095018 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095018) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_095018
    g32p_supplierForest_actual_019912

def g32p_supplierForest_node_095102 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095102 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095102 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098119 := by
  decide +kernel

theorem g32p_supplierForest_actual_095102 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095102) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_095102
    g32p_supplierForest_actual_098119

def g32p_supplierForest_node_095112 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_095112 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095112 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082621 := by
  decide +kernel

theorem g32p_supplierForest_actual_095112 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095112) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_095112
    g32p_supplierForest_actual_082621

def g32p_supplierForest_node_095130 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_095130 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095130 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_020186 := by
  decide +kernel

theorem g32p_supplierForest_actual_095130 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095130) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 2 g32p_supplierForest_edge_095130
    g32p_supplierForest_actual_020186

def g32p_supplierForest_node_095164 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095164 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095164 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_091571 := by
  decide +kernel

theorem g32p_supplierForest_actual_095164 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095164) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_095164
    g32p_supplierForest_actual_091571

def g32p_supplierForest_node_095180 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_095180 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095180 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_093918 := by
  decide +kernel

theorem g32p_supplierForest_actual_095180 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095180) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_095180
    g32p_supplierForest_actual_093918

def g32p_supplierForest_node_095226 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_095226 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095226 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095210 := by
  decide +kernel

theorem g32p_supplierForest_actual_095226 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095226) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 2 g32p_supplierForest_edge_095226
    g32p_supplierForest_actual_095210

def g32p_supplierForest_node_095228 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095228 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095228 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_145606 := by
  decide +kernel

theorem g32p_supplierForest_actual_095228 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095228) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_095228
    g32p_supplierForest_actual_145606

def g32p_supplierForest_node_095229 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_095229 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095229 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146469 := by
  decide +kernel

theorem g32p_supplierForest_actual_095229 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095229) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_095229
    g32p_supplierForest_actual_146469

def g32p_supplierForest_node_095232 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095232 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095232 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_093884 := by
  decide +kernel

theorem g32p_supplierForest_actual_095232 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095232) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_095232
    g32p_supplierForest_actual_093884

def g32p_supplierForest_node_095237 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_095237 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095237 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073478 := by
  decide +kernel

theorem g32p_supplierForest_actual_095237 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095237) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_095237
    g32p_supplierForest_actual_073478

def g32p_supplierForest_node_095249 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095249 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095249 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146480 := by
  decide +kernel

theorem g32p_supplierForest_actual_095249 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095249) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_095249
    g32p_supplierForest_actual_146480

def g32p_supplierForest_node_095265 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095265 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095265 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_093972 := by
  decide +kernel

theorem g32p_supplierForest_actual_095265 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095265) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_095265
    g32p_supplierForest_actual_093972

def g32p_supplierForest_node_095275 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_095275 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095275 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_099507 := by
  decide +kernel

theorem g32p_supplierForest_actual_095275 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095275) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_095275
    g32p_supplierForest_actual_099507

def g32p_supplierForest_node_095279 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_095279 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095279 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082709 := by
  decide +kernel

theorem g32p_supplierForest_actual_095279 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095279) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_095279
    g32p_supplierForest_actual_082709

def g32p_supplierForest_node_095303 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095303 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095303 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_074019 := by
  decide +kernel

theorem g32p_supplierForest_actual_095303 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095303) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_095303
    g32p_supplierForest_actual_074019

def g32p_supplierForest_node_095316 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095316 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095316 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094116 := by
  decide +kernel

theorem g32p_supplierForest_actual_095316 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095316) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 1 g32p_supplierForest_edge_095316
    g32p_supplierForest_actual_094116

def g32p_supplierForest_node_095350 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_095350 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095350 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_079251 := by
  decide +kernel

theorem g32p_supplierForest_actual_095350 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095350) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_095350
    g32p_supplierForest_actual_079251

def g32p_supplierForest_node_095416 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_095416 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095416 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_074083 := by
  decide +kernel

theorem g32p_supplierForest_actual_095416 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095416) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_095416
    g32p_supplierForest_actual_074083

def g32p_supplierForest_node_095426 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_095426 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095426 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_094511 := by
  decide +kernel

theorem g32p_supplierForest_actual_095426 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095426) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_095426
    g32p_supplierForest_actual_094511

def g32p_supplierForest_node_095435 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_095435 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095435 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076578 := by
  decide +kernel

theorem g32p_supplierForest_actual_095435 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095435) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_095435
    g32p_supplierForest_actual_076578

def g32p_supplierForest_node_095469 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095469 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095469 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098418 := by
  decide +kernel

theorem g32p_supplierForest_actual_095469 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095469) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_095469
    g32p_supplierForest_actual_098418

def g32p_supplierForest_node_095515 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095515 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095515 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096527 := by
  decide +kernel

theorem g32p_supplierForest_actual_095515 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095515) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_095515
    g32p_supplierForest_actual_096527

def g32p_supplierForest_node_095517 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_095517 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095517 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_098444 := by
  decide +kernel

theorem g32p_supplierForest_actual_095517 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095517) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_095517
    g32p_supplierForest_actual_098444

def g32p_supplierForest_node_095529 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095529 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095529 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096125 := by
  decide +kernel

theorem g32p_supplierForest_actual_095529 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095529) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_095529
    g32p_supplierForest_actual_096125

def g32p_supplierForest_node_095616 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095616 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095616 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_078241 := by
  decide +kernel

theorem g32p_supplierForest_actual_095616 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095616) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_095616
    g32p_supplierForest_actual_078241

def g32p_supplierForest_node_095623 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_095623 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095623 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_078432 := by
  decide +kernel

theorem g32p_supplierForest_actual_095623 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095623) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 1 g32p_supplierForest_edge_095623
    g32p_supplierForest_actual_078432

def g32p_supplierForest_node_095632 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095632 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095632 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093952 := by
  decide +kernel

theorem g32p_supplierForest_actual_095632 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095632) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_095632
    g32p_supplierForest_actual_093952

def g32p_supplierForest_node_095643 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095643 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095643 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085546 := by
  decide +kernel

theorem g32p_supplierForest_actual_095643 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095643) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_095643
    g32p_supplierForest_actual_085546

def g32p_supplierForest_node_095684 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095684 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095684 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_096887 := by
  decide +kernel

theorem g32p_supplierForest_actual_095684 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095684) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_095684
    g32p_supplierForest_actual_096887

def g32p_supplierForest_node_095709 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095709 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095709 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086696 := by
  decide +kernel

theorem g32p_supplierForest_actual_095709 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095709) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_095709
    g32p_supplierForest_actual_086696

def g32p_supplierForest_node_095734 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_095734 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095734 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073980 := by
  decide +kernel

theorem g32p_supplierForest_actual_095734 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095734) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_095734
    g32p_supplierForest_actual_073980

def g32p_supplierForest_node_095748 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_095748 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095748 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_020403 := by
  decide +kernel

theorem g32p_supplierForest_actual_095748 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095748) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_095748
    g32p_supplierForest_actual_020403

def g32p_supplierForest_node_095756 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_095756 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095756 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095472 := by
  decide +kernel

theorem g32p_supplierForest_actual_095756 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095756) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 2 g32p_supplierForest_edge_095756
    g32p_supplierForest_actual_095472

def g32p_supplierForest_node_095839 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095839 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095839 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_094053 := by
  decide +kernel

theorem g32p_supplierForest_actual_095839 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095839) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_095839
    g32p_supplierForest_actual_094053

def g32p_supplierForest_node_095854 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095854 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095854 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_084905 := by
  decide +kernel

theorem g32p_supplierForest_actual_095854 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095854) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_095854
    g32p_supplierForest_actual_084905

def g32p_supplierForest_node_095858 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_095858 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095858 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075798 := by
  decide +kernel

theorem g32p_supplierForest_actual_095858 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095858) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_095858
    g32p_supplierForest_actual_075798

def g32p_supplierForest_node_095882 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_095882 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095882 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092694 := by
  decide +kernel

theorem g32p_supplierForest_actual_095882 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095882) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_095882
    g32p_supplierForest_actual_092694

def g32p_supplierForest_node_095897 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095897 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095897 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097375 := by
  decide +kernel

theorem g32p_supplierForest_actual_095897 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095897) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_095897
    g32p_supplierForest_actual_097375

def g32p_supplierForest_node_095924 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095924 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095924 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_094556 := by
  decide +kernel

theorem g32p_supplierForest_actual_095924 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095924) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_095924
    g32p_supplierForest_actual_094556

def g32p_supplierForest_node_095955 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_095955 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095955 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095973 := by
  decide +kernel

theorem g32p_supplierForest_actual_095955 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095955) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_095955
    g32p_supplierForest_actual_095973

def g32p_supplierForest_node_095961 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095961 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095961 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083575 := by
  decide +kernel

theorem g32p_supplierForest_actual_095961 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095961) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_095961
    g32p_supplierForest_actual_083575

def g32p_supplierForest_node_095996 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_095996 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_095996 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_082938 := by
  decide +kernel

theorem g32p_supplierForest_actual_095996 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_095996) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_095996
    g32p_supplierForest_actual_082938

def g32p_supplierForest_node_096006 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096006 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096006 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146935 := by
  decide +kernel

theorem g32p_supplierForest_actual_096006 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096006) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_096006
    g32p_supplierForest_actual_146935

def g32p_supplierForest_node_096017 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_096017 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096017 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019848 := by
  decide +kernel

theorem g32p_supplierForest_actual_096017 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096017) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_096017
    g32p_supplierForest_actual_019848

def g32p_supplierForest_node_096024 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096024 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096024 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_074104 := by
  decide +kernel

theorem g32p_supplierForest_actual_096024 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096024) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_096024
    g32p_supplierForest_actual_074104

def g32p_supplierForest_node_096029 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_096029 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096029 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_023812 := by
  decide +kernel

theorem g32p_supplierForest_actual_096029 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096029) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_096029
    g32p_supplierForest_actual_023812

def g32p_supplierForest_node_096045 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096045 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096045 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146965 := by
  decide +kernel

theorem g32p_supplierForest_actual_096045 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096045) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_096045
    g32p_supplierForest_actual_146965

def g32p_supplierForest_node_096083 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_096083 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096083 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097797 := by
  decide +kernel

theorem g32p_supplierForest_actual_096083 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096083) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_096083
    g32p_supplierForest_actual_097797

def g32p_supplierForest_node_096093 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096093 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096093 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096526 := by
  decide +kernel

theorem g32p_supplierForest_actual_096093 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096093) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_096093
    g32p_supplierForest_actual_096526

def g32p_supplierForest_node_096109 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_096109 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096109 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_084632 := by
  decide +kernel

theorem g32p_supplierForest_actual_096109 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096109) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_096109
    g32p_supplierForest_actual_084632

def g32p_supplierForest_node_096112 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096112 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096112 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_151385 := by
  decide +kernel

theorem g32p_supplierForest_actual_096112 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096112) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_096112
    g32p_supplierForest_actual_151385

def g32p_supplierForest_node_096219 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096219 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096219 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146774 := by
  decide +kernel

theorem g32p_supplierForest_actual_096219 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096219) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_096219
    g32p_supplierForest_actual_146774

def g32p_supplierForest_node_096223 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_096223 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096223 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_084545 := by
  decide +kernel

theorem g32p_supplierForest_actual_096223 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096223) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 3 g32p_supplierForest_edge_096223
    g32p_supplierForest_actual_084545

def g32p_supplierForest_node_096255 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096255 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096255 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_098092 := by
  decide +kernel

theorem g32p_supplierForest_actual_096255 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096255) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_096255
    g32p_supplierForest_actual_098092

def g32p_supplierForest_node_096258 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096258 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096258 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_147098 := by
  decide +kernel

theorem g32p_supplierForest_actual_096258 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096258) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_096258
    g32p_supplierForest_actual_147098

def g32p_supplierForest_node_096266 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096266 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096266 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078983 := by
  decide +kernel

theorem g32p_supplierForest_actual_096266 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096266) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_096266
    g32p_supplierForest_actual_078983

def g32p_supplierForest_node_096273 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096273 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096273 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097496 := by
  decide +kernel

theorem g32p_supplierForest_actual_096273 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096273) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_096273
    g32p_supplierForest_actual_097496

def g32p_supplierForest_node_096296 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_096296 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096296 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_092789 := by
  decide +kernel

theorem g32p_supplierForest_actual_096296 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096296) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_096296
    g32p_supplierForest_actual_092789

def g32p_supplierForest_node_096312 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096312 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096312 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076355 := by
  decide +kernel

theorem g32p_supplierForest_actual_096312 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096312) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_096312
    g32p_supplierForest_actual_076355

def g32p_supplierForest_node_096386 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_096386 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096386 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_093371 := by
  decide +kernel

theorem g32p_supplierForest_actual_096386 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096386) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_096386
    g32p_supplierForest_actual_093371

def g32p_supplierForest_node_096407 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096407 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096407 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_021311 := by
  decide +kernel

theorem g32p_supplierForest_actual_096407 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096407) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_096407
    g32p_supplierForest_actual_021311

def g32p_supplierForest_node_096421 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096421 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096421 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_146643 := by
  decide +kernel

theorem g32p_supplierForest_actual_096421 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096421) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_096421
    g32p_supplierForest_actual_146643

def g32p_supplierForest_node_096438 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096438 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096438 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_150375 := by
  decide +kernel

theorem g32p_supplierForest_actual_096438 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096438) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 2 g32p_supplierForest_edge_096438
    g32p_supplierForest_actual_150375

def g32p_supplierForest_node_096439 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096439 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096439 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_146456 := by
  decide +kernel

theorem g32p_supplierForest_actual_096439 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096439) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 2 g32p_supplierForest_edge_096439
    g32p_supplierForest_actual_146456

def g32p_supplierForest_node_096454 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_096454 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096454 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_095246 := by
  decide +kernel

theorem g32p_supplierForest_actual_096454 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096454) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_096454
    g32p_supplierForest_actual_095246

def g32p_supplierForest_node_096473 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_096473 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096473 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_022942 := by
  decide +kernel

theorem g32p_supplierForest_actual_096473 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096473) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_096473
    g32p_supplierForest_actual_022942

def g32p_supplierForest_node_096486 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_096486 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096486 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_084427 := by
  decide +kernel

theorem g32p_supplierForest_actual_096486 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096486) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_096486
    g32p_supplierForest_actual_084427

def g32p_supplierForest_node_096510 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096510 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096510 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075065 := by
  decide +kernel

theorem g32p_supplierForest_actual_096510 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096510) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_096510
    g32p_supplierForest_actual_075065

def g32p_supplierForest_node_096548 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_096548 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096548 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076459 := by
  decide +kernel

theorem g32p_supplierForest_actual_096548 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096548) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_096548
    g32p_supplierForest_actual_076459

def g32p_supplierForest_node_096555 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096555 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096555 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_147315 := by
  decide +kernel

theorem g32p_supplierForest_actual_096555 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096555) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_096555
    g32p_supplierForest_actual_147315

def g32p_supplierForest_node_096563 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_096563 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096563 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100513 := by
  decide +kernel

theorem g32p_supplierForest_actual_096563 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096563) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_096563
    g32p_supplierForest_actual_100513

def g32p_supplierForest_node_096596 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096596 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096596 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_095769 := by
  decide +kernel

theorem g32p_supplierForest_actual_096596 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096596) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_096596
    g32p_supplierForest_actual_095769

def g32p_supplierForest_node_096606 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096606 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096606 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_096211 := by
  decide +kernel

theorem g32p_supplierForest_actual_096606 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096606) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_096606
    g32p_supplierForest_actual_096211

def g32p_supplierForest_node_096647 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_096647 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096647 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_096399 := by
  decide +kernel

theorem g32p_supplierForest_actual_096647 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096647) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_096647
    g32p_supplierForest_actual_096399

def g32p_supplierForest_node_096660 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096660 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096660 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020583 := by
  decide +kernel

theorem g32p_supplierForest_actual_096660 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096660) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_096660
    g32p_supplierForest_actual_020583

def g32p_supplierForest_node_096673 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096673 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096673 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_149149 := by
  decide +kernel

theorem g32p_supplierForest_actual_096673 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096673) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_096673
    g32p_supplierForest_actual_149149

def g32p_supplierForest_node_096674 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096674 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096674 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100688 := by
  decide +kernel

theorem g32p_supplierForest_actual_096674 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096674) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_096674
    g32p_supplierForest_actual_100688

def g32p_supplierForest_node_096679 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_096679 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096679 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_147340 := by
  decide +kernel

theorem g32p_supplierForest_actual_096679 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096679) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_096679
    g32p_supplierForest_actual_147340

def g32p_supplierForest_node_096691 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_096691 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096691 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_096341 := by
  decide +kernel

theorem g32p_supplierForest_actual_096691 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096691) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 3 g32p_supplierForest_edge_096691
    g32p_supplierForest_actual_096341

def g32p_supplierForest_node_096712 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_096712 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096712 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_072686 := by
  decide +kernel

theorem g32p_supplierForest_actual_096712 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096712) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_096712
    g32p_supplierForest_actual_072686

def g32p_supplierForest_node_096725 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_096725 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096725 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020108 := by
  decide +kernel

theorem g32p_supplierForest_actual_096725 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096725) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_096725
    g32p_supplierForest_actual_020108

def g32p_supplierForest_node_096793 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096793 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096793 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_098998 := by
  decide +kernel

theorem g32p_supplierForest_actual_096793 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096793) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_096793
    g32p_supplierForest_actual_098998

def g32p_supplierForest_node_096802 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096802 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096802 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_094178 := by
  decide +kernel

theorem g32p_supplierForest_actual_096802 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096802) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 2 g32p_supplierForest_edge_096802
    g32p_supplierForest_actual_094178

def g32p_supplierForest_node_096806 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096806 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096806 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_100529 := by
  decide +kernel

theorem g32p_supplierForest_actual_096806 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096806) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_096806
    g32p_supplierForest_actual_100529

def g32p_supplierForest_node_096808 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_096808 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096808 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_020802 := by
  decide +kernel

theorem g32p_supplierForest_actual_096808 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096808) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_096808
    g32p_supplierForest_actual_020802

def g32p_supplierForest_node_096814 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_096814 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096814 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_099021 := by
  decide +kernel

theorem g32p_supplierForest_actual_096814 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096814) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 1 g32p_supplierForest_edge_096814
    g32p_supplierForest_actual_099021

def g32p_supplierForest_node_096816 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096816 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096816 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_084905 := by
  decide +kernel

theorem g32p_supplierForest_actual_096816 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096816) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_096816
    g32p_supplierForest_actual_084905

def g32p_supplierForest_node_096859 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_096859 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096859 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_091179 := by
  decide +kernel

theorem g32p_supplierForest_actual_096859 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096859) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_096859
    g32p_supplierForest_actual_091179

def g32p_supplierForest_node_096869 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_096869 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096869 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097462 := by
  decide +kernel

theorem g32p_supplierForest_actual_096869 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096869) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_096869
    g32p_supplierForest_actual_097462

def g32p_supplierForest_node_096877 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_096877 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096877 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_084273 := by
  decide +kernel

theorem g32p_supplierForest_actual_096877 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096877) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_096877
    g32p_supplierForest_actual_084273

def g32p_supplierForest_node_096984 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_096984 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_096984 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_024313 := by
  decide +kernel

theorem g32p_supplierForest_actual_096984 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_096984) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_096984
    g32p_supplierForest_actual_024313

def g32p_supplierForest_node_097036 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_097036 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097036 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_147616 := by
  decide +kernel

theorem g32p_supplierForest_actual_097036 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097036) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_097036
    g32p_supplierForest_actual_147616

def g32p_supplierForest_node_097080 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097080 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097080 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077907 := by
  decide +kernel

theorem g32p_supplierForest_actual_097080 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097080) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_097080
    g32p_supplierForest_actual_077907

def g32p_supplierForest_node_097090 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_097090 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097090 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_080877 := by
  decide +kernel

theorem g32p_supplierForest_actual_097090 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097090) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_097090
    g32p_supplierForest_actual_080877

def g32p_supplierForest_node_097103 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_097103 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097103 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075011 := by
  decide +kernel

theorem g32p_supplierForest_actual_097103 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097103) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_097103
    g32p_supplierForest_actual_075011

def g32p_supplierForest_node_097112 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_097112 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097112 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_098685 := by
  decide +kernel

theorem g32p_supplierForest_actual_097112 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097112) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_097112
    g32p_supplierForest_actual_098685

def g32p_supplierForest_node_097136 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_097136 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097136 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_084838 := by
  decide +kernel

theorem g32p_supplierForest_actual_097136 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097136) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_097136
    g32p_supplierForest_actual_084838

def g32p_supplierForest_node_097158 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097158 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097158 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_151419 := by
  decide +kernel

theorem g32p_supplierForest_actual_097158 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097158) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_097158
    g32p_supplierForest_actual_151419

def g32p_supplierForest_node_097203 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097203 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097203 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095448 := by
  decide +kernel

theorem g32p_supplierForest_actual_097203 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097203) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_097203
    g32p_supplierForest_actual_095448

def g32p_supplierForest_node_097236 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097236 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097236 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091766 := by
  decide +kernel

theorem g32p_supplierForest_actual_097236 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097236) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_097236
    g32p_supplierForest_actual_091766

def g32p_supplierForest_node_097238 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097238 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097238 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_147730 := by
  decide +kernel

theorem g32p_supplierForest_actual_097238 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097238) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_097238
    g32p_supplierForest_actual_147730

def g32p_supplierForest_node_097252 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_097252 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097252 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_099878 := by
  decide +kernel

theorem g32p_supplierForest_actual_097252 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097252) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_097252
    g32p_supplierForest_actual_099878

def g32p_supplierForest_node_097264 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097264 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097264 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_100940 := by
  decide +kernel

theorem g32p_supplierForest_actual_097264 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097264) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 0 g32p_supplierForest_edge_097264
    g32p_supplierForest_actual_100940

def g32p_supplierForest_node_097279 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097279 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097279 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095329 := by
  decide +kernel

theorem g32p_supplierForest_actual_097279 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097279) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_097279
    g32p_supplierForest_actual_095329

def g32p_supplierForest_node_097280 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097280 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097280 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077882 := by
  decide +kernel

theorem g32p_supplierForest_actual_097280 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097280) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_097280
    g32p_supplierForest_actual_077882

def g32p_supplierForest_node_097312 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097312 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097312 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077935 := by
  decide +kernel

theorem g32p_supplierForest_actual_097312 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097312) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_097312
    g32p_supplierForest_actual_077935

def g32p_supplierForest_node_097314 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097314 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097314 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_147518 := by
  decide +kernel

theorem g32p_supplierForest_actual_097314 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097314) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_097314
    g32p_supplierForest_actual_147518

def g32p_supplierForest_node_097321 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097321 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097321 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_099579 := by
  decide +kernel

theorem g32p_supplierForest_actual_097321 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097321) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_097321
    g32p_supplierForest_actual_099579

def g32p_supplierForest_node_097341 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097341 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097341 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018046 := by
  decide +kernel

theorem g32p_supplierForest_actual_097341 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097341) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_097341
    g32p_supplierForest_actual_018046

def g32p_supplierForest_node_097346 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097346 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097346 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_081530 := by
  decide +kernel

theorem g32p_supplierForest_actual_097346 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097346) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_097346
    g32p_supplierForest_actual_081530

def g32p_supplierForest_node_097369 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097369 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097369 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_098589 := by
  decide +kernel

theorem g32p_supplierForest_actual_097369 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097369) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 1 g32p_supplierForest_edge_097369
    g32p_supplierForest_actual_098589

def g32p_supplierForest_node_097370 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097370 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097370 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_146942 := by
  decide +kernel

theorem g32p_supplierForest_actual_097370 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097370) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 2 g32p_supplierForest_edge_097370
    g32p_supplierForest_actual_146942

def g32p_supplierForest_node_097428 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097428 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097428 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076642 := by
  decide +kernel

theorem g32p_supplierForest_actual_097428 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097428) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_097428
    g32p_supplierForest_actual_076642

def g32p_supplierForest_node_097439 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097439 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097439 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_086828 := by
  decide +kernel

theorem g32p_supplierForest_actual_097439 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097439) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_097439
    g32p_supplierForest_actual_086828

def g32p_supplierForest_node_097480 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097480 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097480 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100257 := by
  decide +kernel

theorem g32p_supplierForest_actual_097480 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097480) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_097480
    g32p_supplierForest_actual_100257

def g32p_supplierForest_node_097490 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_097490 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097490 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075909 := by
  decide +kernel

theorem g32p_supplierForest_actual_097490 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097490) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_097490
    g32p_supplierForest_actual_075909

def g32p_supplierForest_node_097491 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097491 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097491 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075911 := by
  decide +kernel

theorem g32p_supplierForest_actual_097491 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097491) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_097491
    g32p_supplierForest_actual_075911

def g32p_supplierForest_node_097504 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_097504 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097504 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_024140 := by
  decide +kernel

theorem g32p_supplierForest_actual_097504 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097504) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_097504
    g32p_supplierForest_actual_024140

def g32p_supplierForest_node_097520 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097520 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097520 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085322 := by
  decide +kernel

theorem g32p_supplierForest_actual_097520 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097520) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_097520
    g32p_supplierForest_actual_085322

def g32p_supplierForest_node_097522 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_097522 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097522 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_093149 := by
  decide +kernel

theorem g32p_supplierForest_actual_097522 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097522) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_097522
    g32p_supplierForest_actual_093149

def g32p_supplierForest_node_097576 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_097576 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097576 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_145788 := by
  decide +kernel

theorem g32p_supplierForest_actual_097576 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097576) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_097576
    g32p_supplierForest_actual_145788

def g32p_supplierForest_node_097657 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097657 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097657 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097778 := by
  decide +kernel

theorem g32p_supplierForest_actual_097657 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097657) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_097657
    g32p_supplierForest_actual_097778

def g32p_supplierForest_node_097710 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097710 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097710 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076255 := by
  decide +kernel

theorem g32p_supplierForest_actual_097710 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097710) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 1 g32p_supplierForest_edge_097710
    g32p_supplierForest_actual_076255

def g32p_supplierForest_node_097716 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097716 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097716 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_099516 := by
  decide +kernel

theorem g32p_supplierForest_actual_097716 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097716) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 2 g32p_supplierForest_edge_097716
    g32p_supplierForest_actual_099516

def g32p_supplierForest_node_097717 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097717 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097717 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097050 := by
  decide +kernel

theorem g32p_supplierForest_actual_097717 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097717) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_097717
    g32p_supplierForest_actual_097050

def g32p_supplierForest_node_097728 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097728 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097728 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020861 := by
  decide +kernel

theorem g32p_supplierForest_actual_097728 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097728) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_097728
    g32p_supplierForest_actual_020861

def g32p_supplierForest_node_097755 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097755 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097755 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_097212 := by
  decide +kernel

theorem g32p_supplierForest_actual_097755 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097755) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 3 g32p_supplierForest_edge_097755
    g32p_supplierForest_actual_097212

def g32p_supplierForest_node_097766 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097766 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097766 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_092001 := by
  decide +kernel

theorem g32p_supplierForest_actual_097766 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097766) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_097766
    g32p_supplierForest_actual_092001

def g32p_supplierForest_node_097769 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097769 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097769 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_079788 := by
  decide +kernel

theorem g32p_supplierForest_actual_097769 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097769) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_097769
    g32p_supplierForest_actual_079788

def g32p_supplierForest_node_097787 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_097787 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097787 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_089085 := by
  decide +kernel

theorem g32p_supplierForest_actual_097787 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097787) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_097787
    g32p_supplierForest_actual_089085

def g32p_supplierForest_node_097789 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_097789 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097789 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_088896 := by
  decide +kernel

theorem g32p_supplierForest_actual_097789 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097789) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 1 g32p_supplierForest_edge_097789
    g32p_supplierForest_actual_088896

def g32p_supplierForest_node_097838 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097838 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097838 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_097066 := by
  decide +kernel

theorem g32p_supplierForest_actual_097838 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097838) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_097838
    g32p_supplierForest_actual_097066

def g32p_supplierForest_node_097867 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_097867 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097867 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_089522 := by
  decide +kernel

theorem g32p_supplierForest_actual_097867 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097867) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_097867
    g32p_supplierForest_actual_089522

def g32p_supplierForest_node_097885 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097885 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097885 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073834 := by
  decide +kernel

theorem g32p_supplierForest_actual_097885 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097885) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_097885
    g32p_supplierForest_actual_073834

def g32p_supplierForest_node_097888 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_097888 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097888 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073108 := by
  decide +kernel

theorem g32p_supplierForest_actual_097888 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097888) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_097888
    g32p_supplierForest_actual_073108

def g32p_supplierForest_node_097908 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_097908 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097908 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075204 := by
  decide +kernel

theorem g32p_supplierForest_actual_097908 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097908) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_097908
    g32p_supplierForest_actual_075204

def g32p_supplierForest_node_097920 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_097920 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097920 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075038 := by
  decide +kernel

theorem g32p_supplierForest_actual_097920 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097920) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_097920
    g32p_supplierForest_actual_075038

def g32p_supplierForest_node_097938 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_097938 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097938 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_084056 := by
  decide +kernel

theorem g32p_supplierForest_actual_097938 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097938) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 3 g32p_supplierForest_edge_097938
    g32p_supplierForest_actual_084056

def g32p_supplierForest_node_097957 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_097957 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097957 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_022176 := by
  decide +kernel

theorem g32p_supplierForest_actual_097957 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097957) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_097957
    g32p_supplierForest_actual_022176

def g32p_supplierForest_node_097989 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_097989 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_097989 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_149786 := by
  decide +kernel

theorem g32p_supplierForest_actual_097989 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_097989) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_097989
    g32p_supplierForest_actual_149786

def g32p_supplierForest_node_098037 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_098037 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098037 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091107 := by
  decide +kernel

theorem g32p_supplierForest_actual_098037 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098037) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_098037
    g32p_supplierForest_actual_091107

def g32p_supplierForest_node_098076 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098076 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098076 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085540 := by
  decide +kernel

theorem g32p_supplierForest_actual_098076 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098076) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_098076
    g32p_supplierForest_actual_085540

def g32p_supplierForest_node_098112 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098112 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098112 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_085280 := by
  decide +kernel

theorem g32p_supplierForest_actual_098112 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098112) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_098112
    g32p_supplierForest_actual_085280

def g32p_supplierForest_node_098130 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098130 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098130 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021644 := by
  decide +kernel

theorem g32p_supplierForest_actual_098130 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098130) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_098130
    g32p_supplierForest_actual_021644

def g32p_supplierForest_node_098157 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098157 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098157 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_081337 := by
  decide +kernel

theorem g32p_supplierForest_actual_098157 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098157) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_098157
    g32p_supplierForest_actual_081337

def g32p_supplierForest_node_098191 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098191 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098191 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014590 := by
  decide +kernel

theorem g32p_supplierForest_actual_098191 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098191) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_098191
    g32p_supplierForest_actual_014590

def g32p_supplierForest_node_098195 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_098195 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098195 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077476 := by
  decide +kernel

theorem g32p_supplierForest_actual_098195 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098195) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_098195
    g32p_supplierForest_actual_077476

def g32p_supplierForest_node_098205 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098205 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098205 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_081314 := by
  decide +kernel

theorem g32p_supplierForest_actual_098205 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098205) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_098205
    g32p_supplierForest_actual_081314

def g32p_supplierForest_node_098226 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098226 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098226 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_147141 := by
  decide +kernel

theorem g32p_supplierForest_actual_098226 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098226) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_098226
    g32p_supplierForest_actual_147141

def g32p_supplierForest_node_098292 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098292 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098292 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083309 := by
  decide +kernel

theorem g32p_supplierForest_actual_098292 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098292) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_098292
    g32p_supplierForest_actual_083309

def g32p_supplierForest_node_098304 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098304 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098304 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_151707 := by
  decide +kernel

theorem g32p_supplierForest_actual_098304 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098304) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_098304
    g32p_supplierForest_actual_151707

def g32p_supplierForest_node_098305 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_098305 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098305 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_146720 := by
  decide +kernel

theorem g32p_supplierForest_actual_098305 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098305) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_098305
    g32p_supplierForest_actual_146720

def g32p_supplierForest_node_098348 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098348 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098348 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_086191 := by
  decide +kernel

theorem g32p_supplierForest_actual_098348 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098348) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_098348
    g32p_supplierForest_actual_086191

def g32p_supplierForest_node_098391 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_098391 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098391 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083069 := by
  decide +kernel

theorem g32p_supplierForest_actual_098391 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098391) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 3 g32p_supplierForest_edge_098391
    g32p_supplierForest_actual_083069

def g32p_supplierForest_node_098415 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098415 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098415 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100644 := by
  decide +kernel

theorem g32p_supplierForest_actual_098415 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098415) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_098415
    g32p_supplierForest_actual_100644

def g32p_supplierForest_node_098447 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098447 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098447 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020228 := by
  decide +kernel

theorem g32p_supplierForest_actual_098447 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098447) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_098447
    g32p_supplierForest_actual_020228

def g32p_supplierForest_node_098489 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098489 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098489 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_101555 := by
  decide +kernel

theorem g32p_supplierForest_actual_098489 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098489) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_098489
    g32p_supplierForest_actual_101555

def g32p_supplierForest_node_098514 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098514 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098514 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_024113 := by
  decide +kernel

theorem g32p_supplierForest_actual_098514 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098514) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_098514
    g32p_supplierForest_actual_024113

def g32p_supplierForest_node_098525 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098525 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098525 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_148114 := by
  decide +kernel

theorem g32p_supplierForest_actual_098525 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098525) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_098525
    g32p_supplierForest_actual_148114

def g32p_supplierForest_node_098555 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_098555 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098555 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086473 := by
  decide +kernel

theorem g32p_supplierForest_actual_098555 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098555) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 3 g32p_supplierForest_edge_098555
    g32p_supplierForest_actual_086473

def g32p_supplierForest_node_098566 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_098566 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098566 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_147240 := by
  decide +kernel

theorem g32p_supplierForest_actual_098566 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098566) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_098566
    g32p_supplierForest_actual_147240

def g32p_supplierForest_node_098586 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098586 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098586 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_097347 := by
  decide +kernel

theorem g32p_supplierForest_actual_098586 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098586) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 3 g32p_supplierForest_edge_098586
    g32p_supplierForest_actual_097347

def g32p_supplierForest_node_098602 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098602 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098602 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_087738 := by
  decide +kernel

theorem g32p_supplierForest_actual_098602 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098602) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_098602
    g32p_supplierForest_actual_087738

def g32p_supplierForest_node_098613 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098613 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098613 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_099850 := by
  decide +kernel

theorem g32p_supplierForest_actual_098613 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098613) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 1 g32p_supplierForest_edge_098613
    g32p_supplierForest_actual_099850

def g32p_supplierForest_node_098616 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_098616 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098616 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_098777 := by
  decide +kernel

theorem g32p_supplierForest_actual_098616 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098616) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_098616
    g32p_supplierForest_actual_098777

def g32p_supplierForest_node_098645 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_098645 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098645 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_096231 := by
  decide +kernel

theorem g32p_supplierForest_actual_098645 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098645) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_098645
    g32p_supplierForest_actual_096231

def g32p_supplierForest_node_098658 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_098658 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098658 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_098054 := by
  decide +kernel

theorem g32p_supplierForest_actual_098658 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098658) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_098658
    g32p_supplierForest_actual_098054

def g32p_supplierForest_node_098678 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_098678 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098678 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021685 := by
  decide +kernel

theorem g32p_supplierForest_actual_098678 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098678) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_098678
    g32p_supplierForest_actual_021685

def g32p_supplierForest_node_098705 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098705 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098705 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_145937 := by
  decide +kernel

theorem g32p_supplierForest_actual_098705 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098705) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_098705
    g32p_supplierForest_actual_145937

def g32p_supplierForest_node_098715 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_098715 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098715 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100949 := by
  decide +kernel

theorem g32p_supplierForest_actual_098715 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098715) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_098715
    g32p_supplierForest_actual_100949

def g32p_supplierForest_node_098738 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098738 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098738 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_149189 := by
  decide +kernel

theorem g32p_supplierForest_actual_098738 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098738) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_098738
    g32p_supplierForest_actual_149189

def g32p_supplierForest_node_098783 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_098783 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098783 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_077184 := by
  decide +kernel

theorem g32p_supplierForest_actual_098783 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098783) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_098783
    g32p_supplierForest_actual_077184

def g32p_supplierForest_node_098786 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_098786 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098786 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_147240 := by
  decide +kernel

theorem g32p_supplierForest_actual_098786 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098786) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_098786
    g32p_supplierForest_actual_147240

def g32p_supplierForest_node_098798 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098798 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098798 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074450 := by
  decide +kernel

theorem g32p_supplierForest_actual_098798 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098798) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_098798
    g32p_supplierForest_actual_074450

def g32p_supplierForest_node_098811 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098811 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098811 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075919 := by
  decide +kernel

theorem g32p_supplierForest_actual_098811 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098811) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 1 g32p_supplierForest_edge_098811
    g32p_supplierForest_actual_075919

def g32p_supplierForest_node_098813 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098813 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098813 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_148586 := by
  decide +kernel

theorem g32p_supplierForest_actual_098813 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098813) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_098813
    g32p_supplierForest_actual_148586

def g32p_supplierForest_node_098841 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098841 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098841 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_092618 := by
  decide +kernel

theorem g32p_supplierForest_actual_098841 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098841) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_098841
    g32p_supplierForest_actual_092618

def g32p_supplierForest_node_098853 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098853 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098853 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085941 := by
  decide +kernel

theorem g32p_supplierForest_actual_098853 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098853) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_098853
    g32p_supplierForest_actual_085941

def g32p_supplierForest_node_098875 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_098875 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098875 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_072002 := by
  decide +kernel

theorem g32p_supplierForest_actual_098875 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098875) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_098875
    g32p_supplierForest_actual_072002

def g32p_supplierForest_node_098893 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098893 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098893 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_098832 := by
  decide +kernel

theorem g32p_supplierForest_actual_098893 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098893) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 1 g32p_supplierForest_edge_098893
    g32p_supplierForest_actual_098832

def g32p_supplierForest_node_098914 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_098914 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098914 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_092926 := by
  decide +kernel

theorem g32p_supplierForest_actual_098914 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098914) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_098914
    g32p_supplierForest_actual_092926

def g32p_supplierForest_node_098931 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_098931 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098931 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073399 := by
  decide +kernel

theorem g32p_supplierForest_actual_098931 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098931) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_098931
    g32p_supplierForest_actual_073399

def g32p_supplierForest_node_098969 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_098969 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098969 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_149749 := by
  decide +kernel

theorem g32p_supplierForest_actual_098969 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098969) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_098969
    g32p_supplierForest_actual_149749

def g32p_supplierForest_node_098987 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_098987 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_098987 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083367 := by
  decide +kernel

theorem g32p_supplierForest_actual_098987 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_098987) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_098987
    g32p_supplierForest_actual_083367

def g32p_supplierForest_node_099002 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_099002 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099002 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075480 := by
  decide +kernel

theorem g32p_supplierForest_actual_099002 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099002) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_099002
    g32p_supplierForest_actual_075480

def g32p_supplierForest_node_099006 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_099006 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099006 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_077534 := by
  decide +kernel

theorem g32p_supplierForest_actual_099006 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099006) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_099006
    g32p_supplierForest_actual_077534

def g32p_supplierForest_node_099061 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_099061 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099061 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_092298 := by
  decide +kernel

theorem g32p_supplierForest_actual_099061 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099061) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 2 g32p_supplierForest_edge_099061
    g32p_supplierForest_actual_092298

def g32p_supplierForest_node_099086 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_099086 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099086 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_091401 := by
  decide +kernel

theorem g32p_supplierForest_actual_099086 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099086) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_099086
    g32p_supplierForest_actual_091401

def g32p_supplierForest_node_099124 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_099124 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099124 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_094032 := by
  decide +kernel

theorem g32p_supplierForest_actual_099124 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099124) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 3 g32p_supplierForest_edge_099124
    g32p_supplierForest_actual_094032

def g32p_supplierForest_node_099151 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_099151 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099151 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097648 := by
  decide +kernel

theorem g32p_supplierForest_actual_099151 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099151) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_099151
    g32p_supplierForest_actual_097648

def g32p_supplierForest_node_099205 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_099205 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099205 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_100266 := by
  decide +kernel

theorem g32p_supplierForest_actual_099205 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099205) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_099205
    g32p_supplierForest_actual_100266

def g32p_supplierForest_node_099220 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_099220 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099220 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077789 := by
  decide +kernel

theorem g32p_supplierForest_actual_099220 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099220) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_099220
    g32p_supplierForest_actual_077789

def g32p_supplierForest_node_099223 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_099223 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099223 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_148796 := by
  decide +kernel

theorem g32p_supplierForest_actual_099223 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099223) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 0 g32p_supplierForest_edge_099223
    g32p_supplierForest_actual_148796

def g32p_supplierForest_node_099231 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_099231 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099231 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077522 := by
  decide +kernel

theorem g32p_supplierForest_actual_099231 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099231) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_099231
    g32p_supplierForest_actual_077522

def g32p_supplierForest_node_099254 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_099254 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099254 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_098830 := by
  decide +kernel

theorem g32p_supplierForest_actual_099254 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099254) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_099254
    g32p_supplierForest_actual_098830

def g32p_supplierForest_node_099258 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_099258 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099258 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_146345 := by
  decide +kernel

theorem g32p_supplierForest_actual_099258 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099258) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 3 g32p_supplierForest_edge_099258
    g32p_supplierForest_actual_146345

def g32p_supplierForest_node_099280 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_099280 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099280 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_081391 := by
  decide +kernel

theorem g32p_supplierForest_actual_099280 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099280) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_099280
    g32p_supplierForest_actual_081391

def g32p_supplierForest_node_099287 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_099287 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099287 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_095447 := by
  decide +kernel

theorem g32p_supplierForest_actual_099287 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099287) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_099287
    g32p_supplierForest_actual_095447

def g32p_supplierForest_node_099321 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_099321 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099321 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_098438 := by
  decide +kernel

theorem g32p_supplierForest_actual_099321 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099321) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_099321
    g32p_supplierForest_actual_098438

def g32p_supplierForest_node_099331 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_099331 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099331 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076533 := by
  decide +kernel

theorem g32p_supplierForest_actual_099331 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099331) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_099331
    g32p_supplierForest_actual_076533

def g32p_supplierForest_node_099350 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_099350 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099350 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096200 := by
  decide +kernel

theorem g32p_supplierForest_actual_099350 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099350) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_099350
    g32p_supplierForest_actual_096200

def g32p_supplierForest_node_099368 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_099368 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099368 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_146598 := by
  decide +kernel

theorem g32p_supplierForest_actual_099368 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099368) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_099368
    g32p_supplierForest_actual_146598

def g32p_supplierForest_node_099383 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_099383 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099383 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096221 := by
  decide +kernel

theorem g32p_supplierForest_actual_099383 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099383) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_099383
    g32p_supplierForest_actual_096221

def g32p_supplierForest_node_099396 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_099396 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099396 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021110 := by
  decide +kernel

theorem g32p_supplierForest_actual_099396 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099396) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_099396
    g32p_supplierForest_actual_021110

def g32p_supplierForest_node_099405 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_099405 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099405 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_098218 := by
  decide +kernel

theorem g32p_supplierForest_actual_099405 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099405) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 1 g32p_supplierForest_edge_099405
    g32p_supplierForest_actual_098218

def g32p_supplierForest_node_099413 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_099413 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099413 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_100395 := by
  decide +kernel

theorem g32p_supplierForest_actual_099413 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099413) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_099413
    g32p_supplierForest_actual_100395

def g32p_supplierForest_node_099417 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_099417 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099417 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_096147 := by
  decide +kernel

theorem g32p_supplierForest_actual_099417 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099417) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_099417
    g32p_supplierForest_actual_096147

def g32p_supplierForest_node_099419 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_099419 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099419 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_086725 := by
  decide +kernel

theorem g32p_supplierForest_actual_099419 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099419) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_099419
    g32p_supplierForest_actual_086725

def g32p_supplierForest_node_099452 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_099452 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_099452 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_095475 := by
  decide +kernel

theorem g32p_supplierForest_actual_099452 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_099452) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_099452
    g32p_supplierForest_actual_095475

end HodgeLean.Foundations.Program

end
end
